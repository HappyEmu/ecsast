use cranelift_codegen::ir::{AbiParam, types};
use cranelift_module::{FuncId, Linkage, Module};
use cranelift_object::ObjectModule;
use std::{collections::HashMap, error::Error};

/// Identifies a C runtime function imported by the compiler.
/// Adding a new runtime function only requires a new variant here and one
/// entry in `Compiler::declare_runtime()`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RuntimeFn {
    PrintInt,
    PrintFloat,
    PrintStr,
    InitArgs,
    Argc,
    Arg,
    IPow,
    FPow,
    FMod,
}

type FunctionRuntime = HashMap<RuntimeFn, FuncId>;

/// Declare all C runtime functions and return a map from `RuntimeFn` to `FuncId`.
/// To add a new runtime function: add a variant to `RuntimeFn` and one arm here.
pub fn declare_runtime(module: &mut ObjectModule) -> Result<FunctionRuntime, Box<dyn Error>> {
    let ptr = module.target_config().pointer_type();
    let mut ids = HashMap::new();

    // print_int(i64) -> void
    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    ids.insert(
        RuntimeFn::PrintInt,
        module.declare_function("print_int", Linkage::Import, &sig)?,
    );

    // print_float(f64) -> void
    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::F64));
    ids.insert(
        RuntimeFn::PrintFloat,
        module.declare_function("print_float", Linkage::Import, &sig)?,
    );

    // print_str(ptr, i64) -> void
    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(ptr));
    sig.params.push(AbiParam::new(types::I64));
    ids.insert(
        RuntimeFn::PrintStr,
        module.declare_function("print_str", Linkage::Import, &sig)?,
    );

    // ecsast_init_args(i32, ptr) -> void
    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::I32));
    sig.params.push(AbiParam::new(ptr));
    ids.insert(
        RuntimeFn::InitArgs,
        module.declare_function("ecsast_init_args", Linkage::Import, &sig)?,
    );

    // ecsast_argc() -> i64
    let mut sig = module.make_signature();
    sig.returns.push(AbiParam::new(types::I64));
    ids.insert(
        RuntimeFn::Argc,
        module.declare_function("ecsast_argc", Linkage::Import, &sig)?,
    );

    // ecsast_arg(i64, ptr, ptr) -> void
    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(ptr));
    sig.params.push(AbiParam::new(ptr));
    ids.insert(
        RuntimeFn::Arg,
        module.declare_function("ecsast_arg", Linkage::Import, &sig)?,
    );

    // ecsast_ipow(i64, i64) -> i64
    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    ids.insert(
        RuntimeFn::IPow,
        module.declare_function("ecsast_ipow", Linkage::Import, &sig)?,
    );

    // ecsast_fpow(f64, f64) -> f64
    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::F64));
    sig.params.push(AbiParam::new(types::F64));
    sig.returns.push(AbiParam::new(types::F64));
    ids.insert(
        RuntimeFn::FPow,
        module.declare_function("ecsast_fpow", Linkage::Import, &sig)?,
    );

    // ecsast_fmod(f64, f64) -> f64
    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::F64));
    sig.params.push(AbiParam::new(types::F64));
    sig.returns.push(AbiParam::new(types::F64));
    ids.insert(
        RuntimeFn::FMod,
        module.declare_function("ecsast_fmod", Linkage::Import, &sig)?,
    );

    Ok(ids)
}
