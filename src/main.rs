mod ast;
mod interpreter;
mod lexer;
mod parser;
mod passes;
mod printer;
mod span;

use ast::NodeKind;
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
}
"#;

    // ---- Lex ---------------------------------------------------------------
    let tokens = Lexer::new(src).tokenize();

    // ---- Parse (eagerly fills `kinds` and `spans`) -------------------------
    let arena = Bump::new();
    let mut parser = Parser::new(&tokens, &arena);
    let root = parser.parse_program();
    let mut world = parser.world;

    println!("=== AST (before lazy passes) ===");
    printer::print_ast(&world, root, 0);

    // ---- Lazy pass 1: annotate literal types -------------------------------
    //
    // Only the `types` store is touched.  `parents` and `resolved` are still
    // empty — they have not been requested yet.
    passes::annotate_literal_types(&mut world);

    println!("\n=== AST (after literal-type pass) ===");
    printer::print_ast(&world, root, 0);

    // ---- Lazy pass 2: compute parent links ---------------------------------
    passes::compute_parents(&mut world, root, None);

    // ---- Component store statistics ----------------------------------------
    println!("\n=== Component store population ===");
    println!(
        "  kinds    (always full): {}/{}",
        world.kinds.len(),
        world.kinds.len()
    );
    println!(
        "  spans    (always full): {}/{}",
        world.spans.len(),
        world.kinds.len()
    );
    println!(
        "  types    (lazy — only literals): {}/{}",
        world.types.len(),
        world.kinds.len()
    );
    println!(
        "  parents  (lazy — all but root):  {}/{}",
        world.parents.len(),
        world.kinds.len()
    );
    println!(
        "  resolved (lazy — not computed):  {}/{}",
        world.resolved.len(),
        world.kinds.len()
    );

    // ---- Interpreter -------------------------------------------------------
    println!("\n=== Interpreter output ===");
    let result = interpreter::run_program(&world, root);
    println!("main() returned: {result}");

    // ---- Spot-check: walk up from a known node -----------------------------
    // Find the first IntLit and walk its parent chain to root.
    if let Some((&int_node, _)) = world
        .kinds
        .iter()
        .find(|(_, k)| matches!(k, NodeKind::IntLit(_)))
    {
        print!("\nParent chain from {int_node:?}: ");
        let mut cur = int_node;
        loop {
            print!("{cur:?} ");
            match world.parents.get(&cur) {
                Some(&p) => cur = p,
                None => break,
            }
        }
        println!("(root)");
    }
}
