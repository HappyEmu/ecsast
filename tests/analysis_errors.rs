use std::fs;
use std::path::PathBuf;

use bumpalo::Bump;
use ecsast::ast::AstWorld;
use ecsast::modules;
use ecsast::passes;

/// Load + analyze a multi-file fixture and assert the error message
/// contains the expected substring. Errors from either `ModuleGraph::load`
/// (e.g. cycles) or `passes::analyze` (e.g. private import) both qualify.
fn run_failure(name: &str) {
    let base = PathBuf::from(format!("tests/analysis_failures/{name}"));
    let entry = base.join("main.ecs");
    let expected = fs::read_to_string(base.join("expected_error"))
        .unwrap_or_else(|e| panic!("failed to read expected_error for {name}: {e}"))
        .trim_end()
        .to_string();

    let arena = Bump::new();
    let mut world = AstWorld::new();

    let actual = match modules::ModuleGraph::load(&entry, &arena, &mut world) {
        Err(e) => e.to_string(),
        Ok(mut graph) => match passes::analyze(&mut world, &mut graph) {
            Err(e) => e.to_string(),
            Ok(()) => panic!("expected {name} to fail but it succeeded"),
        },
    };

    assert!(
        actual.contains(&expected),
        "expected error containing '{expected}', got '{actual}'",
    );
}

#[test]
fn private_rejected() {
    run_failure("private_rejected");
}

#[test]
fn cycle() {
    run_failure("cycle");
}

#[test]
fn not_found() {
    run_failure("not_found");
}

#[test]
fn main_in_non_entry() {
    run_failure("main_in_non_entry");
}

#[test]
fn glob_rejected() {
    run_failure("glob_rejected");
}

#[test]
fn duplicate_import() {
    run_failure("duplicate_import");
}
