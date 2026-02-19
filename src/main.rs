use bumpalo::Bump;
use ecsast::codegen;
use ecsast::lexer::Lexer;
use ecsast::parser::Parser;

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
