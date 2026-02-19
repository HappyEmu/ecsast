use std::collections::HashMap;
use std::error::Error;
use std::fs;
use std::process::Command;

use cranelift_codegen::ir::{types, AbiParam, Function, InstBuilder, UserFuncName};
use cranelift_codegen::ir::{condcodes::IntCC, FuncRef, Value};
use cranelift_codegen::isa;
use cranelift_codegen::settings::{self, Configurable};
use cranelift_codegen::Context;
use cranelift_codegen::entity::EntityRef;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use target_lexicon::Triple;

use crate::ast::{AstWorld, BinOp, NodeId, NodeKind};

const RUNTIME_C: &str = r#"
#include <stdio.h>
void print_int(long n) { printf("%ld\n", n); }
void print_str(const char *s, long len) { fwrite(s, 1, len, stdout); fputc('\n', stdout); }
"#;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ValType {
    I64,
    Bool,
}

struct Compiler<'a, 'arena> {
    world: &'a AstWorld<'arena>,
    module: ObjectModule,
    print_int_id: FuncId,
    print_str_id: FuncId,
    user_funcs: HashMap<String, FuncId>,
    string_data: HashMap<String, (DataId, usize)>,
}

struct FnCtx {
    vars: HashMap<String, (Variable, ValType)>,
    next_var: usize,
    print_int_ref: FuncRef,
    print_str_ref: FuncRef,
    func_refs: HashMap<String, FuncRef>,
    return_type: Option<ValType>,
}

impl FnCtx {
    fn fresh_var(&mut self) -> Variable {
        let v = Variable::new(self.next_var);
        self.next_var += 1;
        v
    }
}

impl<'a, 'arena> Compiler<'a, 'arena> {
    fn new(world: &'a AstWorld<'arena>) -> Result<Self, Box<dyn Error>> {
        let mut flag_builder = settings::builder();
        flag_builder.set("is_pic", "true")?;
        let isa_builder = isa::lookup(Triple::host())?;
        let isa = isa_builder.finish(settings::Flags::new(flag_builder))?;

        let obj_builder = ObjectBuilder::new(
            isa,
            "ecsast_output",
            cranelift_module::default_libcall_names(),
        )?;
        let mut module = ObjectModule::new(obj_builder);

        // Declare print_int(i64) -> void
        let mut print_int_sig = module.make_signature();
        print_int_sig.params.push(AbiParam::new(types::I64));
        let print_int_id =
            module.declare_function("print_int", Linkage::Import, &print_int_sig)?;

        // Declare print_str(ptr, i64) -> void
        let mut print_str_sig = module.make_signature();
        print_str_sig
            .params
            .push(AbiParam::new(module.target_config().pointer_type()));
        print_str_sig.params.push(AbiParam::new(types::I64));
        let print_str_id =
            module.declare_function("print_str", Linkage::Import, &print_str_sig)?;

        Ok(Self {
            world,
            module,
            print_int_id,
            print_str_id,
            user_funcs: HashMap::new(),
            string_data: HashMap::new(),
        })
    }

    fn resolve_type_name(&self, ty_id: NodeId) -> ValType {
        match self.world.kind(ty_id) {
            NodeKind::TypeName("int") => ValType::I64,
            NodeKind::TypeName("bool") => ValType::Bool,
            other => panic!("unsupported type: {other:?}"),
        }
    }

    fn cranelift_type(&self, vt: ValType) -> types::Type {
        match vt {
            ValType::I64 => types::I64,
            ValType::Bool => types::I8,
        }
    }

    fn declare_functions(&mut self, items: &[NodeId]) -> Result<(), Box<dyn Error>> {
        for &id in items {
            if let NodeKind::FnDecl {
                name,
                params,
                ret_ty,
                ..
            } = *self.world.kind(id)
            {
                if name == "main" {
                    continue; // main is handled specially (returns i32)
                }
                let mut sig = self.module.make_signature();
                for &param_id in params {
                    if let NodeKind::Param { ty: Some(ty_id), .. } = *self.world.kind(param_id) {
                        sig.params
                            .push(AbiParam::new(self.cranelift_type(self.resolve_type_name(ty_id))));
                    }
                }
                if let Some(ret_id) = ret_ty {
                    sig.returns
                        .push(AbiParam::new(self.cranelift_type(self.resolve_type_name(ret_id))));
                }
                let func_id = self.module.declare_function(name, Linkage::Local, &sig)?;
                self.user_funcs.insert(name.to_string(), func_id);
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
        self.module.define_data(data_id, &desc).expect("define_data");
        self.string_data.insert(s.to_string(), (data_id, len));
        (data_id, len)
    }

    fn compile(mut self, root: NodeId, output_path: &str) -> Result<(), Box<dyn Error>> {
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
            } = *self.world.kind(id)
            {
                if name == "main" {
                    self.define_main(body, items, &mut func_ctx)?;
                } else {
                    self.define_user_func(name, params, ret_ty, body, items, &mut func_ctx)?;
                }
            }
        }

        // Emit object file
        let obj_product = self.module.finish();
        let obj_bytes = obj_product.emit()?;
        let obj_path = format!("{output_path}.o");
        fs::write(&obj_path, obj_bytes)?;

        // Write and compile C runtime
        let rt_c_path = format!("{output_path}_rt.c");
        let rt_o_path = format!("{output_path}_rt.o");
        fs::write(&rt_c_path, RUNTIME_C)?;
        let status = Command::new("cc")
            .args(["-c", &rt_c_path, "-o", &rt_o_path])
            .status()?;
        if !status.success() {
            return Err("compiling runtime failed".into());
        }

        let status = Command::new("cc")
            .args([&obj_path, &rt_o_path, "-o", output_path])
            .status()?;
        if !status.success() {
            return Err("linking failed".into());
        }

        fs::remove_file(&obj_path)?;
        fs::remove_file(&rt_c_path)?;
        fs::remove_file(&rt_o_path)?;

        Ok(())
    }

    fn define_main(
        &mut self,
        body: NodeId,
        items: &[NodeId],
        func_ctx: &mut FunctionBuilderContext,
    ) -> Result<(), Box<dyn Error>> {
        let mut sig = self.module.make_signature();
        sig.returns.push(AbiParam::new(types::I32));
        let main_func_id = self.module.declare_function("main", Linkage::Export, &sig)?;

        let mut func = Function::with_name_signature(UserFuncName::default(), sig);
        {
            let mut builder = FunctionBuilder::new(&mut func, func_ctx);
            let entry = builder.create_block();
            builder.append_block_params_for_function_params(entry);
            builder.switch_to_block(entry);
            builder.seal_block(entry);

            let mut fn_ctx = self.make_fn_ctx(&mut builder, items, None);

            let terminated = self.compile_block(body, &mut builder, &mut fn_ctx);

            if !terminated {
                let zero = builder.ins().iconst(types::I32, 0);
                builder.ins().return_(&[zero]);
            }
            builder.finalize();
        }

        let mut ctx = Context::for_function(func);
        self.module.define_function(main_func_id, &mut ctx)?;
        Ok(())
    }

    fn define_user_func(
        &mut self,
        name: &str,
        params: &[NodeId],
        ret_ty: Option<NodeId>,
        body: NodeId,
        items: &[NodeId],
        func_ctx: &mut FunctionBuilderContext,
    ) -> Result<(), Box<dyn Error>> {
        let func_id = self.user_funcs[name];
        let sig = self.module.declarations().get_function_decl(func_id).signature.clone();

        let mut func = Function::with_name_signature(UserFuncName::default(), sig.clone());
        {
            let mut builder = FunctionBuilder::new(&mut func, func_ctx);
            let entry = builder.create_block();
            builder.append_block_params_for_function_params(entry);
            builder.switch_to_block(entry);
            builder.seal_block(entry);

            let return_type = ret_ty.map(|id| self.resolve_type_name(id));
            let mut fn_ctx = self.make_fn_ctx(&mut builder, items, return_type);

            // Bind parameters to variables
            for (i, &param_id) in params.iter().enumerate() {
                if let NodeKind::Param {
                    name: pname,
                    ty: Some(ty_id),
                } = *self.world.kind(param_id)
                {
                    let vt = self.resolve_type_name(ty_id);
                    let var = fn_ctx.fresh_var();
                    builder.declare_var(var, self.cranelift_type(vt));
                    let val = builder.block_params(entry)[i];
                    builder.def_var(var, val);
                    fn_ctx.vars.insert(pname.to_string(), (var, vt));
                }
            }

            let terminated = self.compile_block(body, &mut builder, &mut fn_ctx);

            if !terminated {
                // void functions: return nothing (shouldn't happen for int-returning fns)
                builder.ins().return_(&[]);
            }
            builder.finalize();
        }

        let mut ctx = Context::for_function(func);
        self.module.define_function(func_id, &mut ctx)?;
        Ok(())
    }

    fn make_fn_ctx(
        &mut self,
        builder: &mut FunctionBuilder,
        _items: &[NodeId],
        return_type: Option<ValType>,
    ) -> FnCtx {
        let print_int_ref = self
            .module
            .declare_func_in_func(self.print_int_id, builder.func);
        let print_str_ref = self
            .module
            .declare_func_in_func(self.print_str_id, builder.func);

        let mut func_refs = HashMap::new();
        for (name, &fid) in &self.user_funcs {
            let fref = self.module.declare_func_in_func(fid, builder.func);
            func_refs.insert(name.clone(), fref);
        }

        FnCtx {
            vars: HashMap::new(),
            next_var: 0,
            print_int_ref,
            print_str_ref,
            func_refs,
            return_type,
        }
    }

    /// Compile a block. Returns true if the block is terminated (ends with return).
    fn compile_block(
        &mut self,
        block_id: NodeId,
        builder: &mut FunctionBuilder,
        fn_ctx: &mut FnCtx,
    ) -> bool {
        let stmts = match self.world.kind(block_id) {
            NodeKind::Block(stmts) => *stmts,
            _ => panic!("expected Block node"),
        };
        for &stmt_id in stmts {
            let terminated = self.compile_stmt(stmt_id, builder, fn_ctx);
            if terminated {
                return true;
            }
        }
        false
    }

    /// Compile a statement. Returns true if the current block is terminated.
    fn compile_stmt(
        &mut self,
        id: NodeId,
        builder: &mut FunctionBuilder,
        fn_ctx: &mut FnCtx,
    ) -> bool {
        match *self.world.kind(id) {
            NodeKind::LetStmt { name, ty, init } => {
                let vt = ty.map(|t| self.resolve_type_name(t)).unwrap_or(ValType::I64);
                let var = fn_ctx.fresh_var();
                builder.declare_var(var, self.cranelift_type(vt));
                if let Some(init_id) = init {
                    let (val, val_ty) = self.compile_expr(init_id, builder, fn_ctx);
                    let coerced = self.coerce(val, val_ty, vt, builder);
                    builder.def_var(var, coerced);
                }
                fn_ctx.vars.insert(name.to_string(), (var, vt));
                false
            }
            NodeKind::AssignStmt { target, value } => {
                let name = match self.world.kind(target) {
                    NodeKind::Ident(n) => *n,
                    _ => panic!("assign target must be ident"),
                };
                let (var, vt) = fn_ctx.vars[name];
                let (val, val_ty) = self.compile_expr(value, builder, fn_ctx);
                let coerced = self.coerce(val, val_ty, vt, builder);
                builder.def_var(var, coerced);
                false
            }
            NodeKind::ReturnStmt(expr) => {
                if let Some(expr_id) = expr {
                    let (val, val_ty) = self.compile_expr(expr_id, builder, fn_ctx);
                    if let Some(ret_ty) = fn_ctx.return_type {
                        let coerced = self.coerce(val, val_ty, ret_ty, builder);
                        builder.ins().return_(&[coerced]);
                    } else {
                        builder.ins().return_(&[val]);
                    }
                } else {
                    builder.ins().return_(&[]);
                }
                true
            }
            NodeKind::IfStmt {
                cond,
                then_block,
                else_block,
            } => {
                let (cond_val, cond_ty) = self.compile_expr(cond, builder, fn_ctx);
                let cond_i8 = self.coerce(cond_val, cond_ty, ValType::Bool, builder);

                let then_bb = builder.create_block();
                let else_bb = builder.create_block();
                let merge_bb = builder.create_block();

                builder.ins().brif(cond_i8, then_bb, &[], else_bb, &[]);

                // Then branch
                builder.switch_to_block(then_bb);
                builder.seal_block(then_bb);
                let then_terminated = self.compile_block(then_block, builder, fn_ctx);
                if !then_terminated {
                    builder.ins().jump(merge_bb, &[]);
                }

                // Else branch
                builder.switch_to_block(else_bb);
                builder.seal_block(else_bb);
                let else_terminated = if let Some(else_id) = else_block {
                    let t = self.compile_block(else_id, builder, fn_ctx);
                    if !t {
                        builder.ins().jump(merge_bb, &[]);
                    }
                    t
                } else {
                    builder.ins().jump(merge_bb, &[]);
                    false
                };

                if then_terminated && else_terminated {
                    // merge_bb is unreachable, but we still need to seal it
                    builder.seal_block(merge_bb);
                    true
                } else {
                    builder.switch_to_block(merge_bb);
                    builder.seal_block(merge_bb);
                    false
                }
            }
            NodeKind::WhileStmt { cond, body } => {
                let header_bb = builder.create_block();
                let body_bb = builder.create_block();
                let exit_bb = builder.create_block();

                builder.ins().jump(header_bb, &[]);

                builder.switch_to_block(header_bb);
                // Don't seal header yet — back-edge from body not yet added

                let (cond_val, cond_ty) = self.compile_expr(cond, builder, fn_ctx);
                let cond_i8 = self.coerce(cond_val, cond_ty, ValType::Bool, builder);
                builder.ins().brif(cond_i8, body_bb, &[], exit_bb, &[]);

                builder.switch_to_block(body_bb);
                builder.seal_block(body_bb);
                let body_terminated = self.compile_block(body, builder, fn_ctx);
                if !body_terminated {
                    builder.ins().jump(header_bb, &[]);
                }

                // Now seal header (predecessors: entry jump + back-edge)
                builder.seal_block(header_bb);

                builder.switch_to_block(exit_bb);
                builder.seal_block(exit_bb);
                false
            }
            NodeKind::Call { callee, args } => {
                self.compile_call(callee, args, builder, fn_ctx);
                false
            }
            _ => panic!("unsupported statement: {:?}", self.world.kind(id)),
        }
    }

    /// Compile a call expression. Returns Option<(Value, ValType)> for calls with return values.
    fn compile_call(
        &mut self,
        callee: NodeId,
        args: &[NodeId],
        builder: &mut FunctionBuilder,
        fn_ctx: &mut FnCtx,
    ) -> Option<(Value, ValType)> {
        let fn_name = match self.world.kind(callee) {
            NodeKind::Ident(name) => *name,
            _ => panic!("callee must be an identifier"),
        };

        if fn_name == "print" {
            assert!(args.len() == 1, "print() takes exactly 1 argument");
            // Check if the argument is a string literal
            match self.world.kind(args[0]) {
                NodeKind::StringLit(s) => {
                    let s = s.to_string();
                    let (data_id, len) = self.get_or_create_string_data(&s);
                    let gv = self
                        .module
                        .declare_data_in_func(data_id, builder.func);
                    let ptr = builder.ins().symbol_value(
                        self.module.target_config().pointer_type(),
                        gv,
                    );
                    let len_val = builder.ins().iconst(types::I64, len as i64);
                    builder.ins().call(fn_ctx.print_str_ref, &[ptr, len_val]);
                }
                _ => {
                    let (val, val_ty) = self.compile_expr(args[0], builder, fn_ctx);
                    let int_val = self.coerce(val, val_ty, ValType::I64, builder);
                    builder.ins().call(fn_ctx.print_int_ref, &[int_val]);
                }
            }
            None
        } else if let Some(&fref) = fn_ctx.func_refs.get(fn_name) {
            // User-defined function call
            let mut arg_vals = Vec::new();
            for &arg_id in args {
                let (val, _val_ty) = self.compile_expr(arg_id, builder, fn_ctx);
                arg_vals.push(val);
            }
            let call = builder.ins().call(fref, &arg_vals);
            let results = builder.inst_results(call);
            if results.is_empty() {
                None
            } else {
                // Determine return type from our user_funcs signature
                // For now assume i64 for non-void returns
                Some((results[0], ValType::I64))
            }
        } else {
            panic!("unsupported function call: {fn_name}");
        }
    }

    fn compile_expr(
        &mut self,
        id: NodeId,
        builder: &mut FunctionBuilder,
        fn_ctx: &mut FnCtx,
    ) -> (Value, ValType) {
        match *self.world.kind(id) {
            NodeKind::IntLit(n) => {
                let val = builder.ins().iconst(types::I64, n);
                (val, ValType::I64)
            }
            NodeKind::BoolLit(b) => {
                let val = builder.ins().iconst(types::I8, b as i64);
                (val, ValType::Bool)
            }
            NodeKind::Ident(name) => {
                let (var, vt) = fn_ctx.vars[name];
                let val = builder.use_var(var);
                (val, vt)
            }
            NodeKind::BinOp { op, lhs, rhs } => {
                let (l, l_ty) = self.compile_expr(lhs, builder, fn_ctx);
                let (r, r_ty) = self.compile_expr(rhs, builder, fn_ctx);

                match op {
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                        let l64 = self.coerce(l, l_ty, ValType::I64, builder);
                        let r64 = self.coerce(r, r_ty, ValType::I64, builder);
                        let result = match op {
                            BinOp::Add => builder.ins().iadd(l64, r64),
                            BinOp::Sub => builder.ins().isub(l64, r64),
                            BinOp::Mul => builder.ins().imul(l64, r64),
                            BinOp::Div => builder.ins().sdiv(l64, r64),
                            BinOp::Mod => builder.ins().srem(l64, r64),
                            _ => unreachable!(),
                        };
                        (result, ValType::I64)
                    }
                    BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                        let l64 = self.coerce(l, l_ty, ValType::I64, builder);
                        let r64 = self.coerce(r, r_ty, ValType::I64, builder);
                        let cc = match op {
                            BinOp::Eq => IntCC::Equal,
                            BinOp::Ne => IntCC::NotEqual,
                            BinOp::Lt => IntCC::SignedLessThan,
                            BinOp::Le => IntCC::SignedLessThanOrEqual,
                            BinOp::Gt => IntCC::SignedGreaterThan,
                            BinOp::Ge => IntCC::SignedGreaterThanOrEqual,
                            _ => unreachable!(),
                        };
                        let result = builder.ins().icmp(cc, l64, r64);
                        (result, ValType::Bool)
                    }
                    BinOp::And | BinOp::Or => {
                        let lb = self.coerce(l, l_ty, ValType::Bool, builder);
                        let rb = self.coerce(r, r_ty, ValType::Bool, builder);
                        let result = match op {
                            BinOp::And => builder.ins().band(lb, rb),
                            BinOp::Or => builder.ins().bor(lb, rb),
                            _ => unreachable!(),
                        };
                        (result, ValType::Bool)
                    }
                }
            }
            NodeKind::UnaryOp { op, operand } => {
                let (val, vt) = self.compile_expr(operand, builder, fn_ctx);
                match op {
                    crate::ast::UnaryOp::Neg => {
                        let v64 = self.coerce(val, vt, ValType::I64, builder);
                        let result = builder.ins().ineg(v64);
                        (result, ValType::I64)
                    }
                    crate::ast::UnaryOp::Not => {
                        let vb = self.coerce(val, vt, ValType::Bool, builder);
                        let one = builder.ins().iconst(types::I8, 1);
                        let result = builder.ins().bxor(vb, one);
                        (result, ValType::Bool)
                    }
                }
            }
            NodeKind::Call { callee, args } => {
                self.compile_call(callee, args, builder, fn_ctx)
                    .expect("call in expression position must return a value")
            }
            _ => panic!("unsupported expression: {:?}", self.world.kind(id)),
        }
    }

    fn coerce(&self, val: Value, from: ValType, to: ValType, builder: &mut FunctionBuilder) -> Value {
        if from == to {
            return val;
        }
        match (from, to) {
            (ValType::Bool, ValType::I64) => builder.ins().uextend(types::I64, val),
            (ValType::I64, ValType::Bool) => builder.ins().ireduce(types::I8, val),
            _ => val,
        }
    }
}

pub fn compile_to_executable(
    world: &AstWorld<'_>,
    root: NodeId,
    output_path: &str,
) -> Result<(), Box<dyn Error>> {
    let compiler = Compiler::new(world)?;
    compiler.compile(root, output_path)
}
