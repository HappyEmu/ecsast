# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Commands

```bash
cargo build          # build debug binary
cargo build --release
cargo test           # run all 23 parser tests
cargo test -- <name> # run a single test by name substring
cargo run            # run main.rs (lex → parse → passes → interpret)
cargo clippy         # lint
```

## Architecture

ECSAST is a language implementation that uses an **Entity-Component-System (ECS) pattern for the AST**. Every AST node is identified by a `NodeId(u32)`, and data about nodes is stored in separate `HashMap<NodeId, X>` component stores rather than in the nodes themselves.

### Pipeline

```
Source → Lexer → Vec<Token> → Parser → AstWorld{kinds,spans} → Passes → Interpreter
```

### Module Roles

| Module | Role |
|---|---|
| `lexer.rs` | Hand-written tokenizer; produces `Vec<(TokenKind, Span)>` |
| `parser.rs` | Recursive-descent parser with precedence climbing; populates `AstWorld.kinds` and `.spans`, returns root `NodeId` |
| `ast.rs` | `NodeId`, `NodeKind` (Copy enum), `TypeInfo`, and `AstWorld` (the ECS store) |
| `passes.rs` | Independent tree-walk passes that annotate `AstWorld` in-place (`annotate_literal_types`, `compute_parents`) |
| `interpreter.rs` | Tree-walking evaluator; `Env` holds scoped variables + function registry; `Flow` signals early returns |
| `printer.rs` | Debug pretty-printer for the AST (reads `kinds`, `spans`, `types`) |
| `span.rs` | Byte-range `Span` struct for source locations |

### AstWorld Component Stores

```rust
pub struct AstWorld<'arena> {
    pub kinds:    HashMap<NodeId, NodeKind<'arena>>,  // filled by parser
    pub spans:    HashMap<NodeId, Span>,               // filled by parser
    pub types:    HashMap<NodeId, TypeInfo>,           // filled by annotate_literal_types pass
    pub parents:  HashMap<NodeId, NodeId>,             // filled by compute_parents pass
    pub resolved: HashMap<NodeId, NodeId>,             // reserved for name-resolution (unused)
}
```

Passes are lazy and independent: the parser only fills `kinds`/`spans`; each pass adds to other stores without touching earlier ones. New passes can be added without modifying existing code.

### Key Design Details

- **`NodeKind` is `Copy`** — cheap to read from the store without borrowing issues.
- **Arena allocation** (`bumpalo::Bump`) is used for string/slice data inside `NodeKind<'arena>`. The arena is owned by `main` and outlives the world.
- **Precedence climbing** in the parser handles binary operator precedence (`||`=1, `&&`=3, `==`/`!=`=5, comparisons=7, `+`/`-`=9, `*`/`/`/`%`=11).
- **Interpreter built-ins**: only `print()` is currently implemented.
- **`run_program`** looks up and calls a zero-argument `main()` function.

### Language Grammar

The language is statically typed with C-like syntax. Example program:

```
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
```

Supported constructs:
- **Types**: `int`, `float`, `bool`, `str` (annotated on `let` bindings and function signatures)
- **Literals**: integers, floats, booleans (`true`/`false`), double-quoted strings
- **Operators**: `+ - * / %`, `== != < <= > >=`, `&& ||`, unary `! -`
- **Statements**: `let x: T = expr;`, `x = expr;`, `return expr;`, `if`/`else`, `while`
- **Functions**: `fn name(params) -> ReturnType { body }` (return type optional)
- **Entry point**: program must define a `fn main()` with no parameters

### Tests

All tests live in `src/parser.rs` (inline `#[cfg(test)]` module). They test parse-tree structure by querying `AstWorld` after parsing.
