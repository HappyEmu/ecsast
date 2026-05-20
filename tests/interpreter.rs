use std::fs;
use std::path::PathBuf;

use bumpalo::Bump;
use ecsast::ast::AstWorld;
use ecsast::interpreter;
use ecsast::modules;
use ecsast::passes;

fn entry_for(name: &str) -> PathBuf {
    let base = PathBuf::from(format!("tests/programs/{name}"));
    let main = base.join("main.ecs");
    if main.exists() {
        main
    } else {
        base.join("source.ecs")
    }
}

fn run_interpreter_test(name: &str) {
    let entry = entry_for(name);
    let expected = fs::read_to_string(format!("tests/programs/{name}/expected_output"))
        .unwrap_or_else(|e| panic!("failed to read expected_output for {name}: {e}"));

    let arena = Bump::new();
    let mut world = AstWorld::new();
    let mut graph = modules::ModuleGraph::load(&entry, &arena, &mut world)
        .unwrap_or_else(|e| panic!("module load failed for {name}: {e}"));
    passes::analyze(&mut world, &mut graph).expect("analysis failed");

    let mut output = Vec::new();
    interpreter::run_with_output(&world, &graph, &mut output);

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
fn power() {
    run_interpreter_test("power");
}

#[test]
fn float_arithmetic() {
    run_interpreter_test("float_arithmetic");
}

#[test]
fn bitwise() {
    run_interpreter_test("bitwise");
}

#[test]
fn stress() {
    run_interpreter_test("stress");
}

#[test]
fn strings() {
    run_interpreter_test("strings");
}

#[test]
fn module_basic() {
    run_interpreter_test("module_basic");
}

#[test]
fn module_nested() {
    run_interpreter_test("module_nested");
}

#[test]
fn module_alias() {
    run_interpreter_test("module_alias");
}

#[test]
fn module_diamond() {
    run_interpreter_test("module_diamond");
}
