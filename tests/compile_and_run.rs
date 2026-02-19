use std::fs;
use std::process::Command;

use bumpalo::Bump;
use ecsast::codegen;
use ecsast::lexer::Lexer;
use ecsast::parser::Parser;
use tempfile::TempDir;

fn run_program_test(name: &str) {
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

    codegen::compile_to_executable(&world, root, output_str).expect("compilation failed");

    let result = Command::new(&output_path)
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
