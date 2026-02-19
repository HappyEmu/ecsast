mod ast;
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
fn fibonacci(n: int) -> int {
    if n <= 1 {
        return n;
    }
    return fibonacci(n - 1) + fibonacci(n - 2);
}

fn main() {
    let result: int = fibonacci(10);
    let is_even: bool = result % 2 == 0;
    print(result);
    while result > 0 {
        result = result - 1;
    }
    print("Done!");
}
"#;

    let tokens = Lexer::new(src).tokenize();

    let arena = Bump::new();
    let mut parser = Parser::new(&tokens, &arena);
    let root = parser.parse_program();
    let mut world = parser.world;

    passes::annotate_literal_types(&mut world);
    passes::compute_parents(&mut world, root, None);

    interpreter::run_program(&world, root);
}
