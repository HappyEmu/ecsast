#![allow(dead_code)]

pub mod ast;
pub mod codegen;
pub mod lexer;
pub mod parser;
pub mod span;

mod interpreter;
mod passes;
mod printer;
