use bumpalo::Bump;
use ecsast::ast::{AstWorld, NodeKind, TypeInfo};
use ecsast::lexer::Lexer;
use ecsast::parser::Parser;
use ecsast::passes;

fn analyze<'arena>(
    src: &str,
    arena: &'arena Bump,
) -> Result<AstWorld<'arena>, passes::AnalysisError> {
    let tokens = Lexer::new(src).tokenize();
    let mut parser = Parser::new(&tokens, arena);
    let root = parser.parse_program();
    let mut world = parser.world;
    passes::analyze_program(&mut world, root)?;
    Ok(world)
}

fn analysis_error(src: &str) -> String {
    let arena = Bump::new();
    match analyze(src, &arena) {
        Ok(_) => panic!("program should fail analysis"),
        Err(err) => err.to_string(),
    }
}

#[test]
fn resolves_local_bindings_and_annotates_expression_types() {
    let arena = Bump::new();
    let world = analyze(
        r#"
        fn main() {
            let x: int = 41;
            print(x + 1);
        }
        "#,
        &arena,
    )
    .expect("analysis should pass");

    let mut saw_resolved_ident = false;
    let mut saw_int_binop = false;
    for (id, kind) in world.kinds.iter() {
        match kind {
            NodeKind::Ident("x") if world.resolved.contains_key(id) => {
                saw_resolved_ident = true;
                assert_eq!(world.types[id], TypeInfo::Int);
            }
            NodeKind::BinOp { .. } if world.types.get(id) == Some(&TypeInfo::Int) => {
                saw_int_binop = true;
            }
            _ => {}
        }
    }

    assert!(saw_resolved_ident);
    assert!(saw_int_binop);
}

#[test]
fn rejects_undefined_variables() {
    let err = analysis_error(
        r#"
        fn main() {
            print(missing);
        }
        "#,
    );
    assert!(err.contains("undefined variable `missing`"));
}

#[test]
fn rejects_let_type_mismatches() {
    let err = analysis_error(
        r#"
        fn main() {
            let x: int = "nope";
        }
        "#,
    );
    assert!(err.contains("expected int, got str"));
}

#[test]
fn rejects_bad_function_arity() {
    let err = analysis_error(
        r#"
        fn add(a: int, b: int) -> int {
            return a + b;
        }

        fn main() {
            print(add(1));
        }
        "#,
    );
    assert!(err.contains("function `add` expects 2 argument(s), got 1"));
}

#[test]
fn rejects_missing_return_paths() {
    let err = analysis_error(
        r#"
        fn f(x: int) -> int {
            if x > 0 {
                return x;
            }
        }

        fn main() {
            print(f(1));
        }
        "#,
    );
    assert!(err.contains("function `f` may exit without returning int"));
}

#[test]
fn rejects_string_concat_until_codegen_supports_it() {
    let err = analysis_error(
        r#"
        fn main() {
            print("a" + "b");
        }
        "#,
    );
    assert!(err.contains("operator `+` requires int or float operands"));
}

#[test]
fn rejects_string_return_types_until_codegen_supports_them() {
    let err = analysis_error(
        r#"
        fn f() -> str {
            return "hi";
        }

        fn main() {}
        "#,
    );
    assert!(err.contains("functions cannot return str yet"));
}

#[test]
fn accepts_if_else_when_both_branches_return() {
    let arena = Bump::new();
    analyze(
        r#"
        fn f(x: int) -> int {
            if x > 0 {
                return x;
            } else {
                return 0;
            }
        }

        fn main() {
            print(f(1));
        }
        "#,
        &arena,
    )
    .expect("analysis should pass");
}
