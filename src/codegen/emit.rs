use std::borrow::Cow;
use std::collections::{HashMap, HashSet};
use std::error::Error;

use cranelift_codegen::Context;
use cranelift_codegen::inline::{Inline, InlineCommand};
use cranelift_codegen::ir::{
    AbiParam, Function, InstBuilder, Opcode, StackSlotData, StackSlotKind, UserFuncName, types,
};
use cranelift_codegen::ir::{
    FuncRef, Inst, Value,
    condcodes::{FloatCC, IntCC},
};
use cranelift_codegen::isa;
use cranelift_codegen::settings::{self, Configurable};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule, ObjectProduct};
use target_lexicon::Triple;

use crate::ast::{AstWorld, BinOp, Builtin, NodeId, NodeKind};
use crate::codegen::OptLevel;
use crate::codegen::runtime::{RuntimeFn, declare_runtime};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ValType {
    I64,
    Float,
    Bool,
}

impl ValType {
    fn as_cranelift_type(self) -> types::Type {
        match self {
            ValType::I64 => types::I64,
            ValType::Float => types::F64,
            ValType::Bool => types::I8,
        }
    }
}

pub struct Compiler<'a, 'arena> {
    world: &'a AstWorld<'arena>,
    module: ObjectModule,
    runtime_ids: HashMap<RuntimeFn, FuncId>,
    user_funcs: HashMap<String, FuncId>,
    user_func_return_types: HashMap<String, Option<ValType>>,
    string_data: HashMap<String, (DataId, usize)>,
    inline_funcs: HashSet<String>,
    inline_bodies: HashMap<FuncId, Function>,
}

struct BuildCtx<'a> {
    builder: FunctionBuilder<'a>,
    vars: HashMap<String, (Variable, ValType)>,
    runtime: HashMap<RuntimeFn, FuncRef>,
    func_refs: HashMap<String, FuncRef>,
    return_type: Option<ValType>,
}

impl<'a, 'arena> Compiler<'a, 'arena> {
    pub fn new(world: &'a AstWorld<'arena>, opt_level: OptLevel) -> Result<Self, Box<dyn Error>> {
        let mut module = {
            let mut flag_builder = settings::builder();
            flag_builder.set("is_pic", "true")?;
            flag_builder.set("opt_level", opt_level.as_cranelift_str())?;

            let isa_builder = isa::lookup(Triple::host())?;
            let isa = isa_builder.finish(settings::Flags::new(flag_builder))?;

            let obj_builder = ObjectBuilder::new(
                isa,
                "ecsast_output",
                cranelift_module::default_libcall_names(),
            )?;

            ObjectModule::new(obj_builder)
        };

        let runtime_ids = declare_runtime(&mut module)?;

        Ok(Self {
            world,
            module,
            runtime_ids,
            user_funcs: HashMap::new(),
            user_func_return_types: HashMap::new(),
            string_data: HashMap::new(),
            inline_funcs: HashSet::new(),
            inline_bodies: HashMap::new(),
        })
    }

    fn resolve_type_name(&self, ty_id: NodeId) -> ValType {
        match self.world.kind(ty_id) {
            NodeKind::TypeName("int") => ValType::I64,
            NodeKind::TypeName("float") => ValType::Float,
            NodeKind::TypeName("bool") => ValType::Bool,
            other => panic!("unsupported type: {other:?}"),
        }
    }

    fn declare_functions(&mut self, items: &[NodeId]) -> Result<(), Box<dyn Error>> {
        for &id in items {
            if let NodeKind::FnDecl {
                name,
                params,
                ret_ty,
                inline,
                ..
            } = *self.world.kind(id)
            {
                if name == "main" {
                    continue; // main is handled specially (returns i32)
                }
                let mut sig = self.module.make_signature();
                for &param_id in params {
                    if let NodeKind::Param {
                        ty: Some(ty_id), ..
                    } = *self.world.kind(param_id)
                    {
                        sig.params.push(AbiParam::new(
                            self.resolve_type_name(ty_id).as_cranelift_type(),
                        ));
                    }
                }
                if let Some(ret_id) = ret_ty {
                    sig.returns.push(AbiParam::new(
                        self.resolve_type_name(ret_id).as_cranelift_type(),
                    ));
                }
                let func_id = self.module.declare_function(name, Linkage::Local, &sig)?;
                self.user_funcs.insert(name.to_string(), func_id);
                let ret_vt = ret_ty.map(|id| self.resolve_type_name(id));
                self.user_func_return_types.insert(name.to_string(), ret_vt);
                if inline {
                    self.inline_funcs.insert(name.to_string());
                }
            }
        }
        Ok(())
    }

    fn get_or_create_string_data(&mut self, s: &str) -> (DataId, usize) {
        if let Some(&existing) = self.string_data.get(s) {
            return existing;
        }
        let data_id = self
            .module
            .declare_data(
                &format!("str_{}", self.string_data.len()),
                Linkage::Local,
                false,
                false,
            )
            .expect("declare_data");
        let mut desc = DataDescription::new();
        let bytes = s.as_bytes().to_vec();
        let len = bytes.len();
        desc.define(bytes.into_boxed_slice());
        self.module
            .define_data(data_id, &desc)
            .expect("define_data");
        self.string_data.insert(s.to_string(), (data_id, len));
        (data_id, len)
    }

    pub fn compile(mut self, root: NodeId) -> Result<ObjectProduct, Box<dyn Error>> {
        let items = match self.world.kind(root) {
            NodeKind::Program(items) => *items,
            _ => return Err("root must be a Program node".into()),
        };

        // Pass 1: declare all user functions
        self.declare_functions(items)?;

        // Pass 2: define all functions
        let mut func_ctx = FunctionBuilderContext::new();
        for &id in items {
            if let NodeKind::FnDecl {
                name,
                params,
                ret_ty,
                body,
                ..
            } = *self.world.kind(id)
            {
                if name == "main" {
                    self.define_main(body, &mut func_ctx)?;
                } else {
                    self.define_user_func(name, params, ret_ty, body, &mut func_ctx)?;
                }
            }
        }

        return Ok(self.module.finish());
    }

    fn define_main(
        &mut self,
        body: NodeId,
        func_ctx: &mut FunctionBuilderContext,
    ) -> Result<(), Box<dyn Error>> {
        let (main_func_id, sig) = {
            let ptr_type = self.module.target_config().pointer_type();

            let mut sig = self.module.make_signature();
            sig.params.push(AbiParam::new(types::I32)); // argc
            sig.params.push(AbiParam::new(ptr_type)); // argv
            sig.returns.push(AbiParam::new(types::I32));

            let func_id = self
                .module
                .declare_function("main", Linkage::Export, &sig)?;

            (func_id, sig)
        };

        let mut func = Function::with_name_signature(UserFuncName::default(), sig);
        {
            let mut ctx = self.make_build_ctx(&mut func, func_ctx, None);
            let entry = ctx.builder.create_block();
            ctx.builder.append_block_params_for_function_params(entry);
            ctx.builder.switch_to_block(entry);
            ctx.builder.seal_block(entry);

            // Call ecsast_init_args(argc, argv) at entry
            let argc_param = ctx.builder.block_params(entry)[0];
            let argv_param = ctx.builder.block_params(entry)[1];
            ctx.builder
                .ins()
                .call(ctx.runtime[&RuntimeFn::InitArgs], &[argc_param, argv_param]);

            let terminated = self.compile_block(body, &mut ctx);

            if !terminated {
                let zero = ctx.builder.ins().iconst(types::I32, 0);
                ctx.builder.ins().return_(&[zero]);
            }
            ctx.builder.finalize();
        }

        let mut ctx = Context::for_function(func);
        if !self.inline_bodies.is_empty() {
            let mut inliner = Inliner {
                inline_bodies: &self.inline_bodies,
            };
            ctx.inline(&mut inliner)?;
        }

        self.module.define_function(main_func_id, &mut ctx)?;

        Ok(())
    }

    fn define_user_func(
        &mut self,
        name: &str,
        params: &[NodeId],
        ret_ty: Option<NodeId>,
        body: NodeId,
        func_ctx: &mut FunctionBuilderContext,
    ) -> Result<(), Box<dyn Error>> {
        let func_id = self.user_funcs[name];
        let sig = self
            .module
            .declarations()
            .get_function_decl(func_id)
            .signature
            .clone();

        let mut func = Function::with_name_signature(UserFuncName::default(), sig.clone());
        {
            let return_type = ret_ty.map(|id| self.resolve_type_name(id));
            let mut ctx = self.make_build_ctx(&mut func, func_ctx, return_type);
            let entry = ctx.builder.create_block();
            ctx.builder.append_block_params_for_function_params(entry);
            ctx.builder.switch_to_block(entry);
            ctx.builder.seal_block(entry);

            // Bind parameters to variables
            for (i, &param_id) in params.iter().enumerate() {
                if let NodeKind::Param {
                    name: pname,
                    ty: Some(ty_id),
                } = *self.world.kind(param_id)
                {
                    let vt = self.resolve_type_name(ty_id);
                    let var = ctx.builder.declare_var(vt.as_cranelift_type());
                    let val = ctx.builder.block_params(entry)[i];
                    ctx.builder.def_var(var, val);
                    ctx.vars.insert(pname.to_string(), (var, vt));
                }
            }

            let terminated = self.compile_block(body, &mut ctx);

            if !terminated {
                // void functions: return nothing (shouldn't happen for int-returning fns)
                ctx.builder.ins().return_(&[]);
            }
            ctx.builder.finalize();
        }

        let is_inline = self.inline_funcs.contains(name);
        if is_inline {
            self.inline_bodies.insert(func_id, func.clone());
        }

        let mut ctx = Context::for_function(func);
        if !self.inline_bodies.is_empty() {
            let mut inliner = Inliner {
                inline_bodies: &self.inline_bodies,
            };
            ctx.inline(&mut inliner)?;
        }

        self.module.define_function(func_id, &mut ctx)?;

        Ok(())
    }

    fn make_build_ctx<'b>(
        &mut self,
        func: &'b mut Function,
        func_ctx: &'b mut FunctionBuilderContext,
        return_type: Option<ValType>,
    ) -> BuildCtx<'b> {
        let builder = FunctionBuilder::new(func, func_ctx);
        let runtime = self
            .runtime_ids
            .iter()
            .map(|(&rfn, &fid)| (rfn, self.module.declare_func_in_func(fid, builder.func)))
            .collect();

        let mut func_refs = HashMap::new();
        for (name, &fid) in &self.user_funcs {
            let fref = self.module.declare_func_in_func(fid, builder.func);
            func_refs.insert(name.clone(), fref);
        }

        BuildCtx {
            builder,
            vars: HashMap::new(),
            runtime,
            func_refs,
            return_type,
        }
    }

    /// Compile a block. Returns true if the block is terminated (ends with return).
    fn compile_block(&mut self, block_id: NodeId, ctx: &mut BuildCtx) -> bool {
        let stmts = match self.world.kind(block_id) {
            NodeKind::Block(stmts) => *stmts,
            _ => panic!("expected Block node"),
        };

        for &stmt_id in stmts {
            let terminated = self.compile_stmt(stmt_id, ctx);
            if terminated {
                return true;
            }
        }

        false
    }

    /// Compile a statement. Returns true if the current block is terminated.
    fn compile_stmt(&mut self, id: NodeId, ctx: &mut BuildCtx) -> bool {
        match *self.world.kind(id) {
            NodeKind::LetStmt { name, ty, init } => self.compile_let_stmt(name, ty, init, ctx),
            NodeKind::AssignStmt { target, value } => self.compile_assign_stmt(target, value, ctx),
            NodeKind::ReturnStmt(expr) => self.compile_return_stmt(expr, ctx),
            NodeKind::IfStmt {
                cond,
                then_block,
                else_block,
            } => self.compile_if_stmt(cond, then_block, else_block, ctx),
            NodeKind::WhileStmt { cond, body } => self.compile_while_stmt(cond, body, ctx),
            NodeKind::Call { callee, args } => {
                self.compile_call(callee, args, ctx);
                false
            }
            NodeKind::BuiltinCall { builtin, args } => {
                self.compile_builtin_call(builtin, args, ctx);
                false
            }
            _ => panic!("unsupported statement: {:?}", self.world.kind(id)),
        }
    }

    fn compile_let_stmt(
        &mut self,
        name: &str,
        ty: Option<NodeId>,
        init: Option<NodeId>,
        ctx: &mut BuildCtx,
    ) -> bool {
        let vt = ty
            .map(|t| self.resolve_type_name(t))
            .unwrap_or(ValType::I64);
        let var = ctx.builder.declare_var(vt.as_cranelift_type());
        if let Some(init_id) = init {
            let (val, val_ty) = self.compile_expr(init_id, ctx);
            let coerced = self.coerce(val, val_ty, vt, ctx);
            ctx.builder.def_var(var, coerced);
        }
        ctx.vars.insert(name.to_string(), (var, vt));
        false
    }

    fn compile_assign_stmt(&mut self, target: NodeId, value: NodeId, ctx: &mut BuildCtx) -> bool {
        let name = match self.world.kind(target) {
            NodeKind::Ident(n) => *n,
            _ => panic!("assign target must be ident"),
        };
        let (var, vt) = ctx.vars[name];
        let (val, val_ty) = self.compile_expr(value, ctx);
        let coerced = self.coerce(val, val_ty, vt, ctx);
        ctx.builder.def_var(var, coerced);
        false
    }

    fn compile_return_stmt(&mut self, expr: Option<NodeId>, ctx: &mut BuildCtx) -> bool {
        if let Some(expr_id) = expr {
            let (val, val_ty) = self.compile_expr(expr_id, ctx);
            if let Some(ret_ty) = ctx.return_type {
                let coerced = self.coerce(val, val_ty, ret_ty, ctx);
                ctx.builder.ins().return_(&[coerced]);
            } else {
                ctx.builder.ins().return_(&[val]);
            }
        } else {
            ctx.builder.ins().return_(&[]);
        }
        true
    }

    fn compile_if_stmt(
        &mut self,
        cond: NodeId,
        then_block: NodeId,
        else_block: Option<NodeId>,
        ctx: &mut BuildCtx,
    ) -> bool {
        let (cond_val, cond_ty) = self.compile_expr(cond, ctx);
        let cond_i8 = self.coerce(cond_val, cond_ty, ValType::Bool, ctx);

        let then_bb = ctx.builder.create_block();
        let else_bb = ctx.builder.create_block();
        let merge_bb = ctx.builder.create_block();

        ctx.builder.ins().brif(cond_i8, then_bb, &[], else_bb, &[]);

        // Then branch
        ctx.builder.switch_to_block(then_bb);
        ctx.builder.seal_block(then_bb);
        let then_terminated = self.compile_block(then_block, ctx);
        if !then_terminated {
            ctx.builder.ins().jump(merge_bb, &[]);
        }

        // Else branch
        ctx.builder.switch_to_block(else_bb);
        ctx.builder.seal_block(else_bb);
        let else_terminated = if let Some(else_id) = else_block {
            let t = self.compile_block(else_id, ctx);
            if !t {
                ctx.builder.ins().jump(merge_bb, &[]);
            }
            t
        } else {
            ctx.builder.ins().jump(merge_bb, &[]);
            false
        };

        if then_terminated && else_terminated {
            // merge_bb is unreachable, but we still need to seal it
            ctx.builder.seal_block(merge_bb);
            true
        } else {
            ctx.builder.switch_to_block(merge_bb);
            ctx.builder.seal_block(merge_bb);
            false
        }
    }

    fn compile_while_stmt(&mut self, cond: NodeId, body: NodeId, ctx: &mut BuildCtx) -> bool {
        let header_bb = ctx.builder.create_block();
        let body_bb = ctx.builder.create_block();
        let exit_bb = ctx.builder.create_block();

        ctx.builder.ins().jump(header_bb, &[]);

        ctx.builder.switch_to_block(header_bb);
        // Don't seal header yet — back-edge from body not yet added

        let (cond_val, cond_ty) = self.compile_expr(cond, ctx);
        let cond_i8 = self.coerce(cond_val, cond_ty, ValType::Bool, ctx);
        ctx.builder.ins().brif(cond_i8, body_bb, &[], exit_bb, &[]);

        ctx.builder.switch_to_block(body_bb);
        ctx.builder.seal_block(body_bb);
        let body_terminated = self.compile_block(body, ctx);
        if !body_terminated {
            ctx.builder.ins().jump(header_bb, &[]);
        }

        // Now seal header (predecessors: entry jump + back-edge)
        ctx.builder.seal_block(header_bb);

        ctx.builder.switch_to_block(exit_bb);
        ctx.builder.seal_block(exit_bb);
        false
    }

    /// Compile a call to a user-defined function.
    fn compile_call(
        &mut self,
        callee: NodeId,
        args: &[NodeId],
        ctx: &mut BuildCtx,
    ) -> Option<(Value, ValType)> {
        let fn_name = match self.world.kind(callee) {
            NodeKind::Ident(name) => *name,
            _ => panic!("callee must be an identifier"),
        };

        if let Some(&fref) = ctx.func_refs.get(fn_name) {
            let mut arg_vals = Vec::new();
            for &arg_id in args {
                let (val, _val_ty) = self.compile_expr(arg_id, ctx);
                arg_vals.push(val);
            }
            let call = ctx.builder.ins().call(fref, &arg_vals);
            let results = ctx.builder.inst_results(call);
            if results.is_empty() {
                None
            } else {
                let ret_vt = self
                    .user_func_return_types
                    .get(fn_name)
                    .and_then(|opt| *opt)
                    .unwrap_or(ValType::I64);
                Some((results[0], ret_vt))
            }
        } else {
            panic!("undefined function: {fn_name}");
        }
    }

    /// Compile a call to a language built-in.
    /// Each variant matches on the `Builtin` enum — no string comparisons.
    fn compile_builtin_call(
        &mut self,
        builtin: Builtin,
        args: &[NodeId],
        ctx: &mut BuildCtx,
    ) -> Option<(Value, ValType)> {
        match builtin {
            Builtin::Print => {
                assert!(args.len() == 1, "print() takes exactly 1 argument");
                match *self.world.kind(args[0]) {
                    NodeKind::StringLit(s) => {
                        let s = s.to_string();
                        let (data_id, len) = self.get_or_create_string_data(&s);
                        let gv = self.module.declare_data_in_func(data_id, ctx.builder.func);
                        let ptr = ctx
                            .builder
                            .ins()
                            .symbol_value(self.module.target_config().pointer_type(), gv);
                        let len_val = ctx.builder.ins().iconst(types::I64, len as i64);
                        ctx.builder
                            .ins()
                            .call(ctx.runtime[&RuntimeFn::PrintStr], &[ptr, len_val]);
                    }
                    NodeKind::BuiltinCall {
                        builtin: Builtin::Arg,
                        args: inner_args,
                    } => {
                        assert!(inner_args.len() == 1, "arg() takes exactly 1 argument");
                        let (idx_val, idx_ty) = self.compile_expr(inner_args[0], ctx);
                        let idx_i64 = self.coerce(idx_val, idx_ty, ValType::I64, ctx);

                        let ptr_type = self.module.target_config().pointer_type();
                        let ptr_size = ptr_type.bytes();

                        // Allocate stack slots for out_ptr and out_len
                        let ptr_slot = ctx.builder.create_sized_stack_slot(StackSlotData::new(
                            StackSlotKind::ExplicitSlot,
                            ptr_size,
                            0,
                        ));
                        let len_slot = ctx.builder.create_sized_stack_slot(StackSlotData::new(
                            StackSlotKind::ExplicitSlot,
                            8, // i64 = 8 bytes
                            0,
                        ));

                        let ptr_addr = ctx.builder.ins().stack_addr(ptr_type, ptr_slot, 0);
                        let len_addr = ctx.builder.ins().stack_addr(ptr_type, len_slot, 0);
                        ctx.builder
                            .ins()
                            .call(ctx.runtime[&RuntimeFn::Arg], &[idx_i64, ptr_addr, len_addr]);

                        let str_ptr = ctx.builder.ins().stack_load(ptr_type, ptr_slot, 0);
                        let str_len = ctx.builder.ins().stack_load(types::I64, len_slot, 0);
                        ctx.builder
                            .ins()
                            .call(ctx.runtime[&RuntimeFn::PrintStr], &[str_ptr, str_len]);
                    }
                    _ => {
                        let (val, val_ty) = self.compile_expr(args[0], ctx);
                        if val_ty == ValType::Float {
                            ctx.builder
                                .ins()
                                .call(ctx.runtime[&RuntimeFn::PrintFloat], &[val]);
                        } else {
                            let int_val = self.coerce(val, val_ty, ValType::I64, ctx);
                            ctx.builder
                                .ins()
                                .call(ctx.runtime[&RuntimeFn::PrintInt], &[int_val]);
                        }
                    }
                }
                None
            }
            Builtin::Argc => {
                assert!(args.is_empty(), "argc() takes no arguments");
                let call = ctx.builder.ins().call(ctx.runtime[&RuntimeFn::Argc], &[]);
                let result = ctx.builder.inst_results(call)[0];
                Some((result, ValType::I64))
            }
            Builtin::Arg => {
                panic!(
                    "arg() can only be used inside print() — the language has no string variable type yet"
                );
            }
        }
    }

    fn compile_expr(&mut self, id: NodeId, ctx: &mut BuildCtx) -> (Value, ValType) {
        match *self.world.kind(id) {
            NodeKind::IntLit(n) => self.compile_int_lit(n, ctx),
            NodeKind::FloatLit(f) => self.compile_float_lit(f, ctx),
            NodeKind::BoolLit(b) => self.compile_bool_lit(b, ctx),
            NodeKind::Ident(name) => self.compile_ident(name, ctx),
            NodeKind::BinOp { op, lhs, rhs } => self.compile_bin_op(op, lhs, rhs, ctx),
            NodeKind::UnaryOp { op, operand } => self.compile_unary_op(op, operand, ctx),
            NodeKind::Call { callee, args } => self
                .compile_call(callee, args, ctx)
                .expect("call in expression position must return a value"),
            NodeKind::BuiltinCall { builtin, args } => self
                .compile_builtin_call(builtin, args, ctx)
                .expect("builtin call in expression position must return a value"),
            _ => panic!("unsupported expression: {:?}", self.world.kind(id)),
        }
    }

    fn compile_int_lit(&self, n: i64, ctx: &mut BuildCtx) -> (Value, ValType) {
        let val = ctx.builder.ins().iconst(types::I64, n);
        (val, ValType::I64)
    }

    fn compile_float_lit(&self, f: f64, ctx: &mut BuildCtx) -> (Value, ValType) {
        let val = ctx.builder.ins().f64const(f);
        (val, ValType::Float)
    }

    fn compile_bool_lit(&self, b: bool, ctx: &mut BuildCtx) -> (Value, ValType) {
        let val = ctx.builder.ins().iconst(types::I8, b as i64);
        (val, ValType::Bool)
    }

    fn compile_ident(&self, name: &str, ctx: &mut BuildCtx) -> (Value, ValType) {
        let (var, vt) = ctx.vars[name];
        let val = ctx.builder.use_var(var);
        (val, vt)
    }

    fn compile_bin_op(
        &mut self,
        op: BinOp,
        lhs: NodeId,
        rhs: NodeId,
        ctx: &mut BuildCtx,
    ) -> (Value, ValType) {
        let (l, l_ty) = self.compile_expr(lhs, ctx);
        let (r, r_ty) = self.compile_expr(rhs, ctx);

        let is_float = l_ty == ValType::Float || r_ty == ValType::Float;
        match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                if is_float {
                    if op == BinOp::Mod {
                        let call = ctx
                            .builder
                            .ins()
                            .call(ctx.runtime[&RuntimeFn::FMod], &[l, r]);
                        let result = ctx.builder.inst_results(call)[0];
                        return (result, ValType::Float);
                    }
                    let result = match op {
                        BinOp::Add => ctx.builder.ins().fadd(l, r),
                        BinOp::Sub => ctx.builder.ins().fsub(l, r),
                        BinOp::Mul => ctx.builder.ins().fmul(l, r),
                        BinOp::Div => ctx.builder.ins().fdiv(l, r),
                        _ => unreachable!(),
                    };
                    (result, ValType::Float)
                } else {
                    let l64 = self.coerce(l, l_ty, ValType::I64, ctx);
                    let r64 = self.coerce(r, r_ty, ValType::I64, ctx);
                    let result = match op {
                        BinOp::Add => ctx.builder.ins().iadd(l64, r64),
                        BinOp::Sub => ctx.builder.ins().isub(l64, r64),
                        BinOp::Mul => ctx.builder.ins().imul(l64, r64),
                        BinOp::Div => ctx.builder.ins().sdiv(l64, r64),
                        BinOp::Mod => ctx.builder.ins().srem(l64, r64),
                        _ => unreachable!(),
                    };
                    (result, ValType::I64)
                }
            }
            BinOp::Pow => {
                if is_float {
                    let call = ctx
                        .builder
                        .ins()
                        .call(ctx.runtime[&RuntimeFn::FPow], &[l, r]);
                    let result = ctx.builder.inst_results(call)[0];
                    (result, ValType::Float)
                } else {
                    let l64 = self.coerce(l, l_ty, ValType::I64, ctx);
                    let r64 = self.coerce(r, r_ty, ValType::I64, ctx);
                    let call = ctx
                        .builder
                        .ins()
                        .call(ctx.runtime[&RuntimeFn::IPow], &[l64, r64]);
                    let result = ctx.builder.inst_results(call)[0];
                    (result, ValType::I64)
                }
            }
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                if is_float {
                    let cc = match op {
                        BinOp::Eq => FloatCC::Equal,
                        BinOp::Ne => FloatCC::NotEqual,
                        BinOp::Lt => FloatCC::LessThan,
                        BinOp::Le => FloatCC::LessThanOrEqual,
                        BinOp::Gt => FloatCC::GreaterThan,
                        BinOp::Ge => FloatCC::GreaterThanOrEqual,
                        _ => unreachable!(),
                    };
                    let result = ctx.builder.ins().fcmp(cc, l, r);
                    (result, ValType::Bool)
                } else {
                    let l64 = self.coerce(l, l_ty, ValType::I64, ctx);
                    let r64 = self.coerce(r, r_ty, ValType::I64, ctx);
                    let cc = match op {
                        BinOp::Eq => IntCC::Equal,
                        BinOp::Ne => IntCC::NotEqual,
                        BinOp::Lt => IntCC::SignedLessThan,
                        BinOp::Le => IntCC::SignedLessThanOrEqual,
                        BinOp::Gt => IntCC::SignedGreaterThan,
                        BinOp::Ge => IntCC::SignedGreaterThanOrEqual,
                        _ => unreachable!(),
                    };
                    let result = ctx.builder.ins().icmp(cc, l64, r64);
                    (result, ValType::Bool)
                }
            }
            BinOp::And | BinOp::Or => {
                let lb = self.coerce(l, l_ty, ValType::Bool, ctx);
                let rb = self.coerce(r, r_ty, ValType::Bool, ctx);
                let result = match op {
                    BinOp::And => ctx.builder.ins().band(lb, rb),
                    BinOp::Or => ctx.builder.ins().bor(lb, rb),
                    _ => unreachable!(),
                };
                (result, ValType::Bool)
            }
            BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr => {
                let l64 = self.coerce(l, l_ty, ValType::I64, ctx);
                let r64 = self.coerce(r, r_ty, ValType::I64, ctx);
                let result = match op {
                    BinOp::BitAnd => ctx.builder.ins().band(l64, r64),
                    BinOp::BitOr => ctx.builder.ins().bor(l64, r64),
                    BinOp::BitXor => ctx.builder.ins().bxor(l64, r64),
                    BinOp::Shl => ctx.builder.ins().ishl(l64, r64),
                    BinOp::Shr => ctx.builder.ins().sshr(l64, r64),
                    _ => unreachable!(),
                };
                (result, ValType::I64)
            }
        }
    }

    fn compile_unary_op(
        &mut self,
        op: crate::ast::UnaryOp,
        operand: NodeId,
        ctx: &mut BuildCtx,
    ) -> (Value, ValType) {
        let (val, vt) = self.compile_expr(operand, ctx);
        match op {
            crate::ast::UnaryOp::Neg => {
                if vt == ValType::Float {
                    let result = ctx.builder.ins().fneg(val);
                    (result, ValType::Float)
                } else {
                    let v64 = self.coerce(val, vt, ValType::I64, ctx);
                    let result = ctx.builder.ins().ineg(v64);
                    (result, ValType::I64)
                }
            }
            crate::ast::UnaryOp::Not => {
                let vb = self.coerce(val, vt, ValType::Bool, ctx);
                let one = ctx.builder.ins().iconst(types::I8, 1);
                let result = ctx.builder.ins().bxor(vb, one);
                (result, ValType::Bool)
            }
            crate::ast::UnaryOp::BitNot => {
                let v64 = self.coerce(val, vt, ValType::I64, ctx);
                let result = ctx.builder.ins().bnot(v64);
                (result, ValType::I64)
            }
        }
    }

    fn coerce(&self, val: Value, from: ValType, to: ValType, ctx: &mut BuildCtx) -> Value {
        if from == to {
            return val;
        }
        match (from, to) {
            (ValType::Bool, ValType::I64) => ctx.builder.ins().uextend(types::I64, val),
            (ValType::I64, ValType::Bool) => ctx.builder.ins().ireduce(types::I8, val),
            _ => val,
        }
    }
}

impl OptLevel {
    fn as_cranelift_str(self) -> &'static str {
        match self {
            OptLevel::None => "none",
            OptLevel::Speed => "speed",
            OptLevel::SpeedAndSize => "speed_and_size",
        }
    }
}

struct Inliner<'a> {
    inline_bodies: &'a HashMap<FuncId, Function>,
}

impl Inline for Inliner<'_> {
    fn inline(
        &mut self,
        caller: &Function,
        _call_inst: Inst,
        _call_opcode: Opcode,
        callee: FuncRef,
        _call_args: &[Value],
    ) -> InlineCommand<'_> {
        // Resolve callee FuncRef → ExternalName → UserExternalName → FuncId
        let ext_data = &caller.stencil.dfg.ext_funcs[callee];
        if let cranelift_codegen::ir::ExternalName::User(name_ref) = ext_data.name {
            let user_name = &caller.params.user_named_funcs()[name_ref];
            let func_id = FuncId::from_u32(user_name.index);
            if let Some(body) = self.inline_bodies.get(&func_id) {
                return InlineCommand::Inline {
                    callee: Cow::Borrowed(body),
                    visit_callee: false,
                };
            }
        }
        InlineCommand::KeepCall
    }
}
