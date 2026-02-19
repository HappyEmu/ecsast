use std::error::Error;
use std::fs;
use std::process::Command;

use cranelift_codegen::ir::{types, AbiParam, Function, InstBuilder, UserFuncName};
use cranelift_codegen::isa;
use cranelift_codegen::settings::{self, Configurable};
use cranelift_codegen::Context;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use target_lexicon::Triple;

use crate::ast::{AstWorld, BinOp, NodeId, NodeKind};

/// C runtime source that provides `print_int` (avoids variadic printf ABI issues).
const RUNTIME_C: &str = r#"
#include <stdio.h>
void print_int(long n) { printf("%ld\n", n); }
"#;

pub fn compile_to_executable(
    world: &AstWorld<'_>,
    root: NodeId,
    output_path: &str,
) -> Result<(), Box<dyn Error>> {
    // Set up Cranelift ISA for the host target
    let mut flag_builder = settings::builder();
    flag_builder.set("is_pic", "true")?;
    let isa_builder = isa::lookup(Triple::host())?;
    let isa = isa_builder.finish(settings::Flags::new(flag_builder))?;

    // Create the object module
    let obj_builder =
        ObjectBuilder::new(isa.clone(), "ecsast_output", cranelift_module::default_libcall_names())?;
    let mut module = ObjectModule::new(obj_builder);

    // Declare print_int as an imported function: (i64) -> void
    let mut print_int_sig = module.make_signature();
    print_int_sig.params.push(AbiParam::new(types::I64));
    let print_int_id = module.declare_function("print_int", Linkage::Import, &print_int_sig)?;

    // Find the main function in the AST
    let items = match world.kind(root) {
        NodeKind::Program(items) => *items,
        _ => return Err("root must be a Program node".into()),
    };
    let main_body = items
        .iter()
        .copied()
        .find_map(|id| match world.kind(id) {
            NodeKind::FnDecl { name: "main", body, .. } => Some(*body),
            _ => None,
        })
        .ok_or("no main function found")?;

    // Build the main function signature: () -> i32
    let mut main_sig = module.make_signature();
    main_sig.returns.push(AbiParam::new(types::I32));
    let main_func_id = module.declare_function("main", Linkage::Export, &main_sig)?;

    // Generate IR for main
    let mut func = Function::with_name_signature(UserFuncName::default(), main_sig.clone());
    let mut func_ctx = FunctionBuilderContext::new();
    {
        let mut builder = FunctionBuilder::new(&mut func, &mut func_ctx);
        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);

        let print_int_ref = module.declare_func_in_func(print_int_id, &mut builder.func);

        compile_block(world, main_body, &mut builder, print_int_ref);

        // return 0
        let zero = builder.ins().iconst(types::I32, 0);
        builder.ins().return_(&[zero]);
        builder.finalize();
    }

    // Define the function in the module
    let mut ctx = Context::for_function(func);
    module.define_function(main_func_id, &mut ctx)?;

    // Emit the object file
    let obj_product = module.finish();
    let obj_bytes = obj_product.emit()?;
    let obj_path = format!("{output_path}.o");
    fs::write(&obj_path, obj_bytes)?;

    // Write and compile the C runtime
    let rt_c_path = format!("{output_path}_rt.c");
    let rt_o_path = format!("{output_path}_rt.o");
    fs::write(&rt_c_path, RUNTIME_C)?;
    let status = Command::new("cc")
        .args(["-c", &rt_c_path, "-o", &rt_o_path])
        .status()?;
    if !status.success() {
        return Err("compiling runtime failed".into());
    }

    // Link both object files into an executable
    let status = Command::new("cc")
        .args([&obj_path, &rt_o_path, "-o", output_path])
        .status()?;
    if !status.success() {
        return Err("linking failed".into());
    }

    // Clean up temporary files
    fs::remove_file(&obj_path)?;
    fs::remove_file(&rt_c_path)?;
    fs::remove_file(&rt_o_path)?;

    Ok(())
}

fn compile_block(
    world: &AstWorld<'_>,
    block_id: NodeId,
    builder: &mut FunctionBuilder,
    print_int_ref: cranelift_codegen::ir::FuncRef,
) {
    let stmts = match world.kind(block_id) {
        NodeKind::Block(stmts) => *stmts,
        _ => panic!("expected Block node"),
    };
    for &stmt_id in stmts {
        compile_stmt(world, stmt_id, builder, print_int_ref);
    }
}

fn compile_stmt(
    world: &AstWorld<'_>,
    id: NodeId,
    builder: &mut FunctionBuilder,
    print_int_ref: cranelift_codegen::ir::FuncRef,
) {
    match *world.kind(id) {
        NodeKind::Call { callee, args } => {
            let fn_name = match world.kind(callee) {
                NodeKind::Ident(name) => *name,
                _ => panic!("callee must be an identifier"),
            };
            if fn_name == "print" {
                assert!(args.len() == 1, "print() takes exactly 1 argument");
                let val = compile_expr(world, args[0], builder);
                builder.ins().call(print_int_ref, &[val]);
            } else {
                panic!("unsupported function call: {fn_name}");
            }
        }
        _ => panic!("unsupported statement: {:?}", world.kind(id)),
    }
}

fn compile_expr(
    world: &AstWorld<'_>,
    id: NodeId,
    builder: &mut FunctionBuilder,
) -> cranelift_codegen::ir::Value {
    match *world.kind(id) {
        NodeKind::IntLit(n) => builder.ins().iconst(types::I64, n),
        NodeKind::BinOp { op, lhs, rhs } => {
            let l = compile_expr(world, lhs, builder);
            let r = compile_expr(world, rhs, builder);
            match op {
                BinOp::Add => builder.ins().iadd(l, r),
                BinOp::Sub => builder.ins().isub(l, r),
                BinOp::Mul => builder.ins().imul(l, r),
                _ => panic!("unsupported binary operator: {op:?}"),
            }
        }
        _ => panic!("unsupported expression: {:?}", world.kind(id)),
    }
}
