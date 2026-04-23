#![allow(dead_code)]

pub mod ast;
pub mod codegen;
pub mod lexer;
pub mod parser;
pub mod passes;
pub mod span;

pub mod interpreter;
mod printer;
