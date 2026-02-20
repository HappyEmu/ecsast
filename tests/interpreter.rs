use std::fs;

use bumpalo::Bump;
use ecsast::interpreter;
use ecsast::lexer::Lexer;
use ecsast::parser::Parser;

fn run_interpreter_test(name: &str) {
    let base = format!("tests/programs/{name}");
    let source = fs::read_to_string(format!("{base}/source.ecs"))
        .unwrap_or_else(|e| panic!("failed to read source for {name}: {e}"));
    let expected = fs::read_to_string(format!("{base}/expected_output"))
        .unwrap_or_else(|e| panic!("failed to read expected_output for {name}: {e}"));

    let tokens = Lexer::new(&source).tokenize();

    let arena = Bump::new();
    let mut parser = Parser::new(&tokens, &arena);
    let root = parser.parse_program();
    let world = parser.world;

    let mut output = Vec::new();
    interpreter::run_program_with_output(&world, root, &mut output);

    let stdout = String::from_utf8(output).expect("non-UTF8 output");
    assert_eq!(stdout, expected, "output mismatch for program '{name}'");
}

#[test]
fn fibonacci() {
    run_interpreter_test("fibonacci");
}

#[test]
fn hello() {
    run_interpreter_test("hello");
}

#[test]
fn arithmetic() {
    run_interpreter_test("arithmetic");
}

#[test]
fn precedence() {
    run_interpreter_test("precedence");
}

#[test]
fn fizzbuzz() {
    run_interpreter_test("fizzbuzz");
}

#[test]
fn collatz() {
    run_interpreter_test("collatz");
}

#[test]
fn boolean_logic() {
    run_interpreter_test("boolean_logic");
}

#[test]
fn mutual_recursion() {
    run_interpreter_test("mutual_recursion");
}

#[test]
fn nested_loops() {
    run_interpreter_test("nested_loops");
}

#[test]
fn add() {
    run_interpreter_test("add");
}

#[test]
fn stress() {
    run_interpreter_test("stress");
}
