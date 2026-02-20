use std::borrow::Cow;
use std::collections::{HashMap, HashSet};
use std::error::Error;

use cranelift_codegen::Context;
use cranelift_codegen::inline::{Inline, InlineCommand};
use cranelift_codegen::ir::{
    AbiParam, Function, InstBuilder, Opcode, StackSlot, StackSlotData, StackSlotKind, UserFuncName,
    types,
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
    Str,
}

impl ValType {
    fn as_cranelift_type(self) -> types::Type {
        match self {
            ValType::I64 => types::I64,
            ValType::Float => types::F64,
            ValType::Bool => types::I8,
            ValType::Str => panic!("Str has no single cranelift type"),
        }
    }
}

/// Storage for a variable — scalars use one Cranelift variable, strings use two (ptr + len).
enum VarStorage {
    Scalar(Variable, ValType),
    Str {
        ptr_var: Variable,
        len_var: Variable,
    },
}

/// Result of compiling an expression — scalars produce one value, strings produce two.
enum ExprResult {
    Scalar(Value, ValType),
    Str { ptr: Value, len: Value },
}

impl ExprResult {
    fn into_scalar(self) -> (Value, ValType) {
        match self {
            ExprResult::Scalar(v, t) => (v, t),
            ExprResult::Str { .. } => panic!("expected scalar, got string"),
        }
    }
}

struct UserFunc {
    id: FuncId,
    return_type: Option<ValType>,
    /// Ordered source-level param types (needed for str ABI expansion).
    param_types: Vec<ValType>,
}

pub struct Compiler<'a, 'arena> {
    world: &'a AstWorld<'arena>,
    module: ObjectModule,
    runtime_ids: HashMap<RuntimeFn, FuncId>,
    user_funcs: HashMap<String, UserFunc>,
    string_data: HashMap<String, (DataId, usize)>,
    inline_funcs: HashSet<String>,
    inline_bodies: HashMap<FuncId, Function>,
}

struct BuildCtx<'a> {
    builder: FunctionBuilder<'a>,
    vars: HashMap<String, VarStorage>,
    runtime: HashMap<RuntimeFn, FuncRef>,
    func_refs: HashMap<String, FuncRef>,
    return_type: Option<ValType>,
}

impl BuildCtx<'_> {
    /// Define both variables of a string (ptr, len) pair.
    fn def_str_vars(&mut self, ptr_var: Variable, len_var: Variable, ptr: Value, len: Value) {
        self.builder.def_var(ptr_var, ptr);
        self.builder.def_var(len_var, len);
    }
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
            NodeKind::TypeName("str") => ValType::Str,
            other => panic!("unsupported type: {other:?}"),
        }
    }

    fn declare_functions(&mut self, items: &[NodeId]) -> Result<(), Box<dyn Error>> {
        let ptr_type = self.module.target_config().pointer_type();
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
                let mut param_types = Vec::new();
                for &param_id in params {
                    if let NodeKind::Param {
                        ty: Some(ty_id), ..
                    } = *self.world.kind(param_id)
                    {
                        let vt = self.resolve_type_name(ty_id);
                        param_types.push(vt);
                        match vt {
                            ValType::Str => {
                                // Strings are passed as (ptr, len) pair
                                sig.params.push(AbiParam::new(ptr_type));
                                sig.params.push(AbiParam::new(types::I64));
                            }
                            _ => {
                                sig.params.push(AbiParam::new(vt.as_cranelift_type()));
                            }
                        }
                    }
                }
                if let Some(ret_id) = ret_ty {
                    sig.returns.push(AbiParam::new(
                        self.resolve_type_name(ret_id).as_cranelift_type(),
                    ));
                }
                let func_id = self.module.declare_function(name, Linkage::Local, &sig)?;
                let ret_vt = ret_ty.map(|id| self.resolve_type_name(id));
                self.user_funcs.insert(
                    name.to_string(),
                    UserFunc {
                        id: func_id,
                        return_type: ret_vt,
                        param_types,
                    },
                );
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

        Ok(self.module.finish())
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
        let func_id = self.user_funcs[name].id;
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

            // Bind parameters to variables — track ABI index separately since
            // str params consume two ABI slots (ptr + len).
            let mut abi_idx = 0;
            for &param_id in params {
                if let NodeKind::Param {
                    name: pname,
                    ty: Some(ty_id),
                } = *self.world.kind(param_id)
                {
                    let vt = self.resolve_type_name(ty_id);
                    match vt {
                        ValType::Str => {
                            let (ptr_var, len_var) = self.declare_str_vars(&mut ctx);
                            let ptr_val = ctx.builder.block_params(entry)[abi_idx];
                            let len_val = ctx.builder.block_params(entry)[abi_idx + 1];

                            ctx.def_str_vars(ptr_var, len_var, ptr_val, len_val);
                            ctx.vars
                                .insert(pname.to_string(), VarStorage::Str { ptr_var, len_var });

                            abi_idx += 2;
                        }
                        _ => {
                            let var = ctx.builder.declare_var(vt.as_cranelift_type());
                            let val = ctx.builder.block_params(entry)[abi_idx];

                            ctx.builder.def_var(var, val);

                            ctx.vars
                                .insert(pname.to_string(), VarStorage::Scalar(var, vt));

                            abi_idx += 1;
                        }
                    }
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

    /// Allocate stack-backed out-parameter slots for a (ptr, len) string pair.
    /// Returns `(ptr_addr, len_addr, ptr_slot, len_slot)` — pass the addresses to
    /// a C function, then `stack_load` from the slots to read back the values.
    fn create_str_out_slots(&self, ctx: &mut BuildCtx) -> (Value, Value, StackSlot, StackSlot) {
        let ptr_type = self.module.target_config().pointer_type();

        let ptr_slot = ctx.builder.create_sized_stack_slot(StackSlotData::new(
            StackSlotKind::ExplicitSlot,
            ptr_type.bytes(),
            0,
        ));

        let len_slot = ctx.builder.create_sized_stack_slot(StackSlotData::new(
            StackSlotKind::ExplicitSlot,
            8,
            0,
        ));

        let ptr_addr = ctx.builder.ins().stack_addr(ptr_type, ptr_slot, 0);
        let len_addr = ctx.builder.ins().stack_addr(ptr_type, len_slot, 0);

        (ptr_addr, len_addr, ptr_slot, len_slot)
    }

    /// Declare a fresh (ptr, len) variable pair for a string value.
    fn declare_str_vars(&self, ctx: &mut BuildCtx) -> (Variable, Variable) {
        let ptr_type = self.module.target_config().pointer_type();

        let ptr_var = ctx.builder.declare_var(ptr_type);
        let len_var = ctx.builder.declare_var(types::I64);

        (ptr_var, len_var)
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
        for (name, uf) in &self.user_funcs {
            let fref = self.module.declare_func_in_func(uf.id, builder.func);
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

        match vt {
            ValType::Str => {
                let (ptr_var, len_var) = self.declare_str_vars(ctx);
                if let Some(init_id) = init {
                    let result = self.compile_expr(init_id, ctx);
                    match result {
                        ExprResult::Str { ptr, len } => {
                            ctx.def_str_vars(ptr_var, len_var, ptr, len);
                        }
                        ExprResult::Scalar(..) => {
                            panic!("expected string expression for str variable")
                        }
                    }
                }
                ctx.vars
                    .insert(name.to_string(), VarStorage::Str { ptr_var, len_var });
            }
            _ => {
                let var = ctx.builder.declare_var(vt.as_cranelift_type());
                if let Some(init_id) = init {
                    let (val, val_ty) = self.compile_expr(init_id, ctx).into_scalar();
                    let coerced = self.coerce(val, val_ty, vt, ctx);
                    ctx.builder.def_var(var, coerced);
                }
                ctx.vars
                    .insert(name.to_string(), VarStorage::Scalar(var, vt));
            }
        }
        false
    }

    fn compile_assign_stmt(&mut self, target: NodeId, value: NodeId, ctx: &mut BuildCtx) -> bool {
        let name = match self.world.kind(target) {
            NodeKind::Ident(n) => *n,
            _ => panic!("assign target must be ident"),
        };
        match ctx.vars.get(name) {
            Some(VarStorage::Str { ptr_var, len_var }) => {
                let ptr_var = *ptr_var;
                let len_var = *len_var;
                let result = self.compile_expr(value, ctx);
                match result {
                    ExprResult::Str { ptr, len } => {
                        ctx.def_str_vars(ptr_var, len_var, ptr, len);
                    }
                    ExprResult::Scalar(..) => {
                        panic!("expected string expression for str variable")
                    }
                }
            }
            Some(VarStorage::Scalar(var, vt)) => {
                let var = *var;
                let vt = *vt;
                let (val, val_ty) = self.compile_expr(value, ctx).into_scalar();
                let coerced = self.coerce(val, val_ty, vt, ctx);
                ctx.builder.def_var(var, coerced);
            }
            None => panic!("assignment to undefined variable: {name}"),
        }
        false
    }

    fn compile_return_stmt(&mut self, expr: Option<NodeId>, ctx: &mut BuildCtx) -> bool {
        if let Some(expr_id) = expr {
            let (val, val_ty) = self.compile_expr(expr_id, ctx).into_scalar();
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
        let (cond_val, cond_ty) = self.compile_expr(cond, ctx).into_scalar();
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

        let (cond_val, cond_ty) = self.compile_expr(cond, ctx).into_scalar();
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
    ) -> Option<ExprResult> {
        let fn_name = match self.world.kind(callee) {
            NodeKind::Ident(name) => *name,
            _ => panic!("callee must be an identifier"),
        };

        if let Some(&fref) = ctx.func_refs.get(fn_name) {
            let uf = &self.user_funcs[fn_name];
            let param_types = uf.param_types.clone();
            let return_type = uf.return_type;

            let mut arg_vals = Vec::new();
            for (i, &arg_id) in args.iter().enumerate() {
                let result = self.compile_expr(arg_id, ctx);
                let expected_ty = param_types.get(i).copied();
                match (result, expected_ty) {
                    (ExprResult::Str { ptr, len }, _) => {
                        arg_vals.push(ptr);
                        arg_vals.push(len);
                    }
                    (ExprResult::Scalar(_val, _), Some(ValType::Str)) => {
                        panic!("expected string argument for str parameter");
                    }
                    (ExprResult::Scalar(val, _val_ty), _) => {
                        arg_vals.push(val);
                    }
                }
            }
            let call = ctx.builder.ins().call(fref, &arg_vals);
            let results = ctx.builder.inst_results(call);
            if results.is_empty() {
                None
            } else {
                let ret_vt = return_type.unwrap_or(ValType::I64);
                Some(ExprResult::Scalar(results[0], ret_vt))
            }
        } else {
            panic!("undefined function: {fn_name}");
        }
    }

    /// Compile a call to a language built-in.
    fn compile_builtin_call(
        &mut self,
        builtin: Builtin,
        args: &[NodeId],
        ctx: &mut BuildCtx,
    ) -> Option<ExprResult> {
        match builtin {
            Builtin::Print => {
                assert!(args.len() == 1, "print() takes exactly 1 argument");
                let result = self.compile_expr(args[0], ctx);
                match result {
                    ExprResult::Str { ptr, len } => {
                        ctx.builder
                            .ins()
                            .call(ctx.runtime[&RuntimeFn::PrintStr], &[ptr, len]);
                    }
                    ExprResult::Scalar(val, val_ty) => {
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
                Some(ExprResult::Scalar(result, ValType::I64))
            }
            Builtin::Arg => {
                assert!(args.len() == 1, "arg() takes exactly 1 argument");

                let (idx_val, idx_ty) = self.compile_expr(args[0], ctx).into_scalar();
                let idx_i64 = self.coerce(idx_val, idx_ty, ValType::I64, ctx);

                let (ptr_addr, len_addr, ptr_slot, len_slot) = self.create_str_out_slots(ctx);

                // Call runtime function: void ecsast_arg(i64 idx, char** out_ptr, i64* out_len)
                ctx.builder
                    .ins()
                    .call(ctx.runtime[&RuntimeFn::Arg], &[idx_i64, ptr_addr, len_addr]);

                // Load the resulting string pointer and length from the out-parameter slots
                let ptr_type = self.module.target_config().pointer_type();
                let str_ptr = ctx.builder.ins().stack_load(ptr_type, ptr_slot, 0);
                let str_len = ctx.builder.ins().stack_load(types::I64, len_slot, 0);

                Some(ExprResult::Str {
                    ptr: str_ptr,
                    len: str_len,
                })
            }
        }
    }

    fn compile_expr(&mut self, id: NodeId, ctx: &mut BuildCtx) -> ExprResult {
        match *self.world.kind(id) {
            NodeKind::IntLit(n) => self.compile_int_lit(n, ctx),
            NodeKind::FloatLit(f) => self.compile_float_lit(f, ctx),
            NodeKind::BoolLit(b) => self.compile_bool_lit(b, ctx),
            NodeKind::StringLit(s) => self.compile_string_lit(s, ctx),
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

    fn compile_int_lit(&self, n: i64, ctx: &mut BuildCtx) -> ExprResult {
        let val = ctx.builder.ins().iconst(types::I64, n);
        ExprResult::Scalar(val, ValType::I64)
    }

    fn compile_float_lit(&self, f: f64, ctx: &mut BuildCtx) -> ExprResult {
        let val = ctx.builder.ins().f64const(f);
        ExprResult::Scalar(val, ValType::Float)
    }

    fn compile_bool_lit(&self, b: bool, ctx: &mut BuildCtx) -> ExprResult {
        let val = ctx.builder.ins().iconst(types::I8, b as i64);
        ExprResult::Scalar(val, ValType::Bool)
    }

    fn compile_string_lit(&mut self, s: &str, ctx: &mut BuildCtx) -> ExprResult {
        let (data_id, len) = self.get_or_create_string_data(s);
        let gv = self.module.declare_data_in_func(data_id, ctx.builder.func);
        let ptr = ctx
            .builder
            .ins()
            .symbol_value(self.module.target_config().pointer_type(), gv);
        let len_val = ctx.builder.ins().iconst(types::I64, len as i64);
        ExprResult::Str { ptr, len: len_val }
    }

    fn compile_ident(&self, name: &str, ctx: &mut BuildCtx) -> ExprResult {
        match &ctx.vars[name] {
            VarStorage::Scalar(var, vt) => {
                let val = ctx.builder.use_var(*var);
                ExprResult::Scalar(val, *vt)
            }
            VarStorage::Str { ptr_var, len_var } => {
                let ptr = ctx.builder.use_var(*ptr_var);
                let len = ctx.builder.use_var(*len_var);
                ExprResult::Str { ptr, len }
            }
        }
    }

    fn compile_bin_op(
        &mut self,
        op: BinOp,
        lhs: NodeId,
        rhs: NodeId,
        ctx: &mut BuildCtx,
    ) -> ExprResult {
        let (l, l_ty) = self.compile_expr(lhs, ctx).into_scalar();
        let (r, r_ty) = self.compile_expr(rhs, ctx).into_scalar();

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
                        return ExprResult::Scalar(result, ValType::Float);
                    }
                    let result = match op {
                        BinOp::Add => ctx.builder.ins().fadd(l, r),
                        BinOp::Sub => ctx.builder.ins().fsub(l, r),
                        BinOp::Mul => ctx.builder.ins().fmul(l, r),
                        BinOp::Div => ctx.builder.ins().fdiv(l, r),
                        _ => unreachable!(),
                    };
                    ExprResult::Scalar(result, ValType::Float)
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
                    ExprResult::Scalar(result, ValType::I64)
                }
            }
            BinOp::Pow => {
                if is_float {
                    let call = ctx
                        .builder
                        .ins()
                        .call(ctx.runtime[&RuntimeFn::FPow], &[l, r]);
                    let result = ctx.builder.inst_results(call)[0];
                    ExprResult::Scalar(result, ValType::Float)
                } else {
                    let l64 = self.coerce(l, l_ty, ValType::I64, ctx);
                    let r64 = self.coerce(r, r_ty, ValType::I64, ctx);
                    let call = ctx
                        .builder
                        .ins()
                        .call(ctx.runtime[&RuntimeFn::IPow], &[l64, r64]);
                    let result = ctx.builder.inst_results(call)[0];
                    ExprResult::Scalar(result, ValType::I64)
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
                    ExprResult::Scalar(result, ValType::Bool)
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
                    ExprResult::Scalar(result, ValType::Bool)
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
                ExprResult::Scalar(result, ValType::Bool)
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
                ExprResult::Scalar(result, ValType::I64)
            }
        }
    }

    fn compile_unary_op(
        &mut self,
        op: crate::ast::UnaryOp,
        operand: NodeId,
        ctx: &mut BuildCtx,
    ) -> ExprResult {
        let (val, vt) = self.compile_expr(operand, ctx).into_scalar();
        match op {
            crate::ast::UnaryOp::Neg => {
                if vt == ValType::Float {
                    let result = ctx.builder.ins().fneg(val);
                    ExprResult::Scalar(result, ValType::Float)
                } else {
                    let v64 = self.coerce(val, vt, ValType::I64, ctx);
                    let result = ctx.builder.ins().ineg(v64);
                    ExprResult::Scalar(result, ValType::I64)
                }
            }
            crate::ast::UnaryOp::Not => {
                let vb = self.coerce(val, vt, ValType::Bool, ctx);
                let one = ctx.builder.ins().iconst(types::I8, 1);
                let result = ctx.builder.ins().bxor(vb, one);
                ExprResult::Scalar(result, ValType::Bool)
            }
            crate::ast::UnaryOp::BitNot => {
                let v64 = self.coerce(val, vt, ValType::I64, ctx);
                let result = ctx.builder.ins().bnot(v64);
                ExprResult::Scalar(result, ValType::I64)
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
