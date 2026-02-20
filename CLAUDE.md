# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Commands

```bash
cargo build          # build debug binary
cargo build --release
cargo test           # run all tests (parser + codegen + interpreter)
cargo test -- <name> # run a single test by name substring
cargo clippy         # lint
```

### Running the compiler

The compiler accepts a `.ecs` source file as a positional argument and produces a native binary:

```bash
cargo run -- <FILE>              # compile to ./output
cargo run -- <FILE> -o <NAME>    # compile to custom output path
cargo run -- <FILE> -O speed     # compile with optimizations
```

Examples:

```bash
cargo run -- examples/hello.ecs && ./output           # prints "Hello, world!"
cargo run -- examples/fizzbuzz.ecs -o fizz && ./fizz   # prints fizzbuzz
cargo run -- examples/add.ecs -o add -O speed          # inline fn demo
```

The CLI is built with `clap` (derive mode). See `src/main.rs` for the `Cli` struct.

## Architecture

ECSAST is a language implementation that uses an **Entity-Component-System (ECS) pattern for the AST**. Every AST node is identified by a `NodeId(u32)`, and data about nodes is stored in separate `HashMap<NodeId, X>` component stores rather than in the nodes themselves.

### Pipeline

```
Source file (.ecs) → Lexer → Vec<Token> → Parser → AstWorld{kinds,spans} → Cranelift Codegen → Native Binary
```

The interpreter (`interpreter.rs`) is a tree-walking evaluator that runs programs directly without compilation. It is tested against the same `tests/programs/` fixtures as the codegen path. Passes (`passes.rs`) exist but are currently unused. `main.rs` drives the Cranelift codegen path.

### Module Roles

| Module | Role |
|---|---|
| `lexer.rs` | Hand-written tokenizer; produces `Vec<(TokenKind, Span)>` |
| `parser.rs` | Recursive-descent parser with precedence climbing; populates `AstWorld.kinds` and `.spans`, returns root `NodeId` |
| `ast.rs` | `NodeId`, `NodeKind` (Copy enum), `TypeInfo`, and `AstWorld` (the ECS store) |
| `codegen.rs` | Cranelift-based native compiler; `Compiler` struct with two-pass function compilation (declare then define), emits object file and links with C runtime |
| `passes.rs` | Independent tree-walk passes that annotate `AstWorld` in-place (`annotate_literal_types`, `compute_parents`) — currently unused |
| `interpreter.rs` | Tree-walking evaluator; `Env` holds scoped variables, function registry, and `&mut dyn Write` for output capture; `Flow` signals early returns. Tested against the same fixtures as codegen |
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

### Cranelift Codegen Details

The `Compiler` struct in `codegen.rs` holds the `ObjectModule`, declared function IDs, string data sections, and inline function tracking. Compilation is two-pass:

1. **Declaration pass**: iterate all `FnDecl` nodes, build Cranelift signatures, call `module.declare_function()`, populate `user_funcs` map. This enables forward references and recursion. Inline functions are tracked in `inline_funcs`.
2. **Definition pass**: for each `FnDecl`, generate IR via `FunctionBuilder` and `module.define_function()`. For inline functions, the compiled `Function` IR is saved in `inline_bodies`. Before defining any function, `ctx.inline()` is called with the `Inliner` to inline marked callees.

Key internal types:
- **`FnCtx`** — per-function context holding `Variable` map, function refs, and return type
- **`ValType`** — `{ I64, Bool }` enum for type tracking; `compile_expr` returns `(Value, ValType)` and `coerce()` inserts `uextend`/`ireduce` as needed
- **`Inliner`** — implements Cranelift's `Inline` trait; resolves `FuncRef` → `FuncId` via `UserExternalName` and returns `InlineCommand::Inline` with the saved function body for inline-marked callees

Control flow patterns:
- **if/else**: `brif` → then/else blocks → merge block; tracks termination to avoid emitting jumps after `return`
- **while**: header block (sealed after back-edge) → body → back-edge jump; exit block
- **return**: emits `return_` instruction and marks block as terminated

C runtime (`RUNTIME_C`): compiled and linked automatically; provides `print_int(long)`, `print_str(const char*, long)`, `ecsast_init_args(int, char**)`, `ecsast_argc()`, and `ecsast_arg(long, const char**, long*)`.

### Cranelift API Notes (v0.128)

- **`FunctionBuilder::declare_var(ty) -> Variable`** — allocates and returns a new variable. Unlike older versions, you do not pass a `Variable` in; the builder assigns one for you.
- **`Context::inline(&mut impl Inline)`** — performs function inlining on the IR before `define_function()`. The `Inline` trait has a single method that returns `InlineCommand::Inline` or `InlineCommand::KeepCall`.
- **`FuncRef` → `FuncId` resolution** — access `caller.stencil.dfg.ext_funcs[callee].name` to get the `ExternalName::User(name_ref)`, then resolve via `caller.params.user_named_funcs()[name_ref].index` which equals `FuncId::as_u32()`.

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
    print(1 + 2);
}
```

Supported constructs:
- **Types**: `int`, `float`, `bool`, `str` (annotated on `let` bindings and function signatures)
- **Literals**: integers, floats, booleans (`true`/`false`), double-quoted strings
- **Operators**: `+ - * / %`, `== != < <= > >=`, `&& ||`, unary `! -`
- **Statements**: `let x: T = expr;`, `x = expr;`, `return expr;`, `if`/`else`, `while`
- **Functions**: `fn name(params) -> ReturnType { body }` (return type optional)
- **Inline functions**: `inline fn name(params) -> ReturnType { body }` — inlined at call sites by Cranelift
- **Built-ins**: `print()` (int, bool, str), `argc()`, `arg(i)` (command-line arguments)
- **Entry point**: program must define a `fn main()` with no parameters

### Tests

- **Parser unit tests** live in `src/parser.rs` (inline `#[cfg(test)]` module). They test parse-tree structure by querying `AstWorld` after parsing.
- **End-to-end codegen tests** live in `tests/compile_and_run.rs`. They compile example programs from `tests/programs/`, run the resulting binaries, and assert on stdout output.
- **Interpreter tests** live in `tests/interpreter.rs`. They parse and interpret the same `tests/programs/` fixtures in-process using `run_program_with_output` with a `Vec<u8>` buffer, asserting output matches expected. All programs except `args` (which needs `argc`/`arg` built-ins not yet in the interpreter) are covered.
- **Example programs** in `examples/` (`.ecs` files) can be compiled directly with `cargo run -- examples/<name>.ecs`.

### Adding a New Language Feature

Typical workflow for adding a new keyword or construct:

1. **Lexer** (`lexer.rs`): add a `TokenKind` variant and a keyword match arm in `lex_ident_or_keyword`
2. **AST** (`ast.rs`): add or extend a `NodeKind` variant with new fields
3. **Parser** (`parser.rs`): update `parse_item`/`parse_stmt`/`parse_expr` to handle the new token and produce the new `NodeKind`
4. **Codegen** (`codegen.rs`): update pattern matches on `NodeKind` in `compile_stmt`/`compile_expr` and add IR generation
5. **Other modules**: update pattern matches in `printer.rs`, `passes.rs`, `interpreter.rs` (use `..` in patterns to avoid breakage from new fields)
6. **Tests**: add a test program in `tests/programs/<name>/` with `source.ecs` and `expected_output`, add a test function in both `tests/compile_and_run.rs` and `tests/interpreter.rs`
