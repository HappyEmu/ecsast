mod emit;
mod link;
mod runtime;

use crate::{ast::AstWorld, codegen::emit::Compiler, modules::ModuleGraph};
use std::error::Error;

#[derive(Clone, Copy, Debug, Default)]
pub enum OptLevel {
    #[default]
    None,
    Speed,
    SpeedAndSize,
}

pub fn compile(
    world: &AstWorld<'_>,
    graph: &ModuleGraph,
    output_path: &str,
    opt_level: OptLevel,
) -> Result<(), Box<dyn Error>> {
    let compiler = Compiler::new(world, opt_level)?;
    let program = compiler.compile(graph)?;

    link::link_program(program, output_path)
}
