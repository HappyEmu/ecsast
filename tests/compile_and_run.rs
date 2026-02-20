use std::fs;
use std::process::Command;

use bumpalo::Bump;
use ecsast::codegen::{self, OptLevel};
use ecsast::lexer::Lexer;
use ecsast::parser::Parser;
use tempfile::TempDir;

fn run_program_test(name: &str) {
    run_program_test_with_args(name, &[]);
}

fn run_program_test_with_args(name: &str, args: &[&str]) {
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

    let tmp_dir = TempDir::new().expect("failed to create temp dir");
    let output_path = tmp_dir.path().join("output");
    let output_str = output_path.to_str().expect("non-UTF8 temp path");

    codegen::compile_to_executable(&world, root, output_str, OptLevel::None).expect("compilation failed");

    let result = Command::new(&output_path)
        .args(args)
        .output()
        .expect("failed to execute compiled binary");

    assert!(
        result.status.success(),
        "binary exited with non-zero status for {name}: {:?}",
        result.status
    );

    let stdout = String::from_utf8(result.stdout).expect("non-UTF8 stdout");
    assert_eq!(stdout, expected, "output mismatch for program '{name}'");
}

#[test]
fn fibonacci() {
    run_program_test("fibonacci");
}

#[test]
fn hello() {
    run_program_test("hello");
}

#[test]
fn arithmetic() {
    run_program_test("arithmetic");
}

#[test]
fn precedence() {
    run_program_test("precedence");
}

#[test]
fn fizzbuzz() {
    run_program_test("fizzbuzz");
}

#[test]
fn collatz() {
    run_program_test("collatz");
}

#[test]
fn boolean_logic() {
    run_program_test("boolean_logic");
}

#[test]
fn mutual_recursion() {
    run_program_test("mutual_recursion");
}

#[test]
fn nested_loops() {
    run_program_test("nested_loops");
}

#[test]
fn add() {
    run_program_test("add");
}

#[test]
fn args() {
    run_program_test_with_args("args", &["hello", "world"]);
}

#[test]
fn power() {
    run_program_test("power");
}

#[test]
fn float_arithmetic() {
    run_program_test("float_arithmetic");
}

#[test]
fn bitwise() {
    run_program_test("bitwise");
}

#[ignore]
#[test]
fn stress() {
    run_program_test("stress");
}

#[test]
fn stress_big_blocks() {
    run_program_test("stress_big_blocks");
}
