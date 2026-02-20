mod emit;
mod link;
mod runtime;

use crate::{
    ast::{AstWorld, NodeId},
    codegen::emit::Compiler,
};
use std::error::Error;

#[derive(Clone, Copy, Debug, Default)]
pub enum OptLevel {
    #[default]
    None,
    Speed,
    SpeedAndSize,
}

pub fn compile_to_executable(
    world: &AstWorld<'_>,
    root: NodeId,
    output_path: &str,
    opt_level: OptLevel,
) -> Result<(), Box<dyn Error>> {
    let compiler = Compiler::new(world, opt_level)?;
    let program = compiler.compile(root)?;

    return link::link_program(program, output_path);
}
