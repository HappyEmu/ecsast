mod ast;
mod codegen;
mod interpreter;
mod lexer;
mod parser;
mod passes;
mod printer;
mod span;

use bumpalo::Bump;
use lexer::Lexer;
use parser::Parser;

fn main() {
    let src = r#"
fn main() {
    print(1 + 2);
}
"#;

    let tokens = Lexer::new(src).tokenize();

    let arena = Bump::new();
    let mut parser = Parser::new(&tokens, &arena);
    let root = parser.parse_program();
    let world = parser.world;

    codegen::compile_to_executable(&world, root, "output").expect("compilation failed");
}
