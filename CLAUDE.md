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
cargo run -- <FILE> --print-ast  # dump post-analysis AST instead of compiling
cargo run -- <FILE> --time       # report per-phase timing diagnostics
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
Entry .ecs file
   │
   ▼
modules::ModuleGraph::load
   │   Lex + parse the entry file, follow every `use` decl, lex+parse each
   │   sibling/nested file into the same arena + AstWorld.
   ▼
AstWorld {kinds, spans}            (populated eagerly by parser)
   │
   ▼
passes::analyze
   │   1. compute_parents
   │   2. collect_signatures (per module: param/return types, mangling)
   │   3. resolve_use_decls (each module's `bindings: name → Module|Func`)
   │   4. type-check every function body (populates `types`, `resolved`)
   ▼
AstWorld {kinds, spans, types, parents, resolved, mangled_names}
   │
   ├──► codegen::compile  → object file + linked native binary
   └──► interpreter::run* → direct tree-walking evaluator
```

The interpreter (`interpreter.rs`) is a tree-walking evaluator that runs programs directly without compilation. It is tested against the same `tests/programs/` fixtures as the codegen path and supports `argc()`/`arg(i)` via the `run_with_args_and_output` entry point.

### Module Roles

| Module | Role |
|---|---|
| `lexer.rs` | Hand-written tokenizer; produces `Vec<Token<'src>>` borrowing identifier/string slices from the source (`Cow<'src, str>` for strings to handle escapes) |
| `parser.rs` | Recursive-descent parser with precedence climbing; populates `AstWorld.kinds` and `.spans`, returns root `NodeId` |
| `ast.rs` | `NodeId` (slotmap key), `NodeKind` (Copy enum), `TypeInfo`, and `AstWorld` (the ECS store) |
| `modules.rs` | Multi-file loader; transitive `use` resolution; `ModuleGraph` with `by_path: HashMap<String, ModuleId>` and `namespaces: HashSet<String>` for O(1) prefix lookups |
| `passes.rs` | `analyze()` drives parent linking, signature collection, mangling, `use` resolution, and per-function type checking |
| `codegen.rs` / `codegen/emit.rs` | Cranelift-based native compiler; `Compiler` struct with two-pass function compilation (declare then define), emits object file and links with C runtime |
| `codegen/link.rs` | Embedded C runtime + `cc` invocation |
| `codegen/runtime.rs` | `RuntimeFn` enum + Cranelift declarations for the C runtime functions |
| `interpreter.rs` | Tree-walking evaluator; `Env<'_, 'arena>` holds scoped variables, mangled-name → function table, `args`, and `&mut dyn Write` for output capture; `Flow` signals early returns |
| `printer.rs` | Debug pretty-printer used by `--print-ast`; renders `types`, `resolved`, and `mangled_names` annotations when populated |
| `span.rs` | Byte-range `Span` struct for source locations |

### AstWorld Component Stores

```rust
pub struct AstWorld<'arena> {
    // Eagerly populated during parsing
    pub kinds:         SlotMap<NodeId, NodeKind<'arena>>,
    pub spans:         SecondaryMap<NodeId, Span>,

    // Lazily populated by passes::analyze
    pub types:         SparseSecondaryMap<NodeId, TypeInfo>,        // type checker
    pub parents:       SecondaryMap<NodeId, NodeId>,                // parent-link pass
    pub resolved:      SecondaryMap<NodeId, NodeId>,                // Ident/Path → decl
    pub mangled_names: SparseSecondaryMap<NodeId, &'arena str>,     // FnDecl → linker symbol
}
```

Passes are lazy and independent: the parser only fills `kinds`/`spans`; subsequent passes add to other stores without touching earlier ones. Mangled names are arena-allocated so downstream readers (codegen, interpreter) can use them as `Copy` keys without cloning.

### Key Design Details

- **`NodeKind` is `Copy`** — cheap to read from the store without borrowing issues.
- **Arena allocation** (`bumpalo::Bump`) is used for string/slice data inside `NodeKind<'arena>`. The arena is owned by `main` and outlives the world.
- **Precedence climbing** in the parser handles binary operator precedence (`||`=1, `&&`=3, `==`/`!=`=5, comparisons=7, `+`/`-`=9, `*`/`/`/`%`=11).

### Cranelift Codegen Details

The `Compiler` struct in `codegen.rs` holds the `ObjectModule`, declared function IDs, string data sections, and inline function tracking. Compilation is two-pass:

1. **Declaration pass**: iterate all `FnDecl` nodes, build Cranelift signatures, call `module.declare_function()`, populate `user_funcs` map. This enables forward references and recursion. Inline functions are tracked in `inline_funcs`.
2. **Definition pass**: for each `FnDecl`, generate IR via `FunctionBuilder` and `module.define_function()`. For inline functions, the compiled `Function` IR is saved in `inline_bodies`. Before defining any function, `ctx.inline()` is called with the `Inliner` to inline marked callees.

Key internal types:
- **`BuildCtx`** — per-function context holding `Variable` map, function refs, and return type
- **`ValType`** — `{ I64, Float, Bool, Str }` enum for type tracking
- **`ExprResult`** — `Scalar(Value, ValType)` or `Str { ptr, len }` for compile_expr results; strings are represented as (pointer, length) pairs throughout the codegen
- **`VarStorage`** — `Scalar(Variable, ValType)` or `Str { ptr_var, len_var }` for variable storage; string variables use two Cranelift variables
- **`Inliner`** — implements Cranelift's `Inline` trait; resolves `FuncRef` → `FuncId` via `UserExternalName` and returns `InlineCommand::Inline` with the saved function body for inline-marked callees

Control flow patterns:
- **if/else**: `brif` → then/else blocks → merge block; tracks termination to avoid emitting jumps after `return`
- **while**: header block (sealed after back-edge) → body → back-edge jump; exit block
- **return**: emits `return_` instruction and marks block as terminated

C runtime (`RUNTIME_C` in `codegen/link.rs`): compiled and linked automatically. Provides `ecsast_print_int(long)`, `ecsast_print_float(double)`, `ecsast_print_bool(signed char)`, `ecsast_print_str(const char*, long)`, `ecsast_init_args(int, char**)`, `ecsast_argc()`, `ecsast_arg(long, const char**, long*)`, `ecsast_ipow(long, long)`, `ecsast_fpow(double, double)`, and `ecsast_fmod(double, double)`. All runtime functions use the `ecsast_` prefix to avoid collisions with user-defined function names.

Codegen reads types from `world.types` (populated by the semantic pass) rather than re-deriving them from `NodeKind::TypeName` strings. The `valtype_of(node)` helper in `codegen/emit.rs` projects `TypeInfo → ValType`.

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
- **Built-ins**: `print()` (int, float, bool, str), `argc()`, `arg(i)` → `str` (command-line arguments)
- **Entry point**: program must define a `fn main()` with no parameters

### Multi-file modules

A program may span multiple `.ecs` files. `use a::b::c;` imports the trailing name into local scope; `pub fn name` exposes a function across module boundaries. The loader walks `use` decls from the entry file, loading whichever prefix has a backing `.ecs` file:

- `["math"]`           → `<entry_dir>/math.ecs`
- `["math","geometry"]`→ `<entry_dir>/math/geometry.ecs`

`ModuleGraph::is_namespace` is O(1) — every loaded module's path and proper prefixes are pre-inserted into a `HashSet<String>` namespace set.

### Tests

- **Parser unit tests** live in `src/parser.rs` (inline `#[cfg(test)]` module). They test parse-tree structure by querying `AstWorld` after parsing.
- **End-to-end codegen tests** live in `tests/compile_and_run.rs`. They compile example programs from `tests/programs/`, run the resulting binaries, and assert on stdout output.
- **Interpreter tests** live in `tests/interpreter.rs`. They parse and interpret the same `tests/programs/` fixtures in-process using `run_with_args_and_output` with a `Vec<u8>` buffer, asserting output matches expected. The `args` and `string_args` fixtures are covered because the interpreter implements `argc()`/`arg(i)` via a configurable argv slot on `Env`.
- **Semantic-error tests** live in `tests/analysis.rs` (typed-pass behavior) and `tests/analysis_errors.rs` (loader + analyzer error messages).
- **Example programs** in `examples/` (`.ecs` files) can be compiled directly with `cargo run -- examples/<name>.ecs`.

### Adding a New Language Feature

Typical workflow for adding a new keyword or construct:

1. **Lexer** (`lexer.rs`): add a `TokenKind` variant and a keyword match arm in `lex_ident_or_keyword`
2. **AST** (`ast.rs`): add or extend a `NodeKind` variant with new fields
3. **Parser** (`parser.rs`): update `parse_item`/`parse_stmt`/`parse_expr` to handle the new token and produce the new `NodeKind`
4. **Semantic** (`passes.rs`): if the construct introduces new typing rules or name resolution, extend `Analyzer::check_*` and (for top-level items) `collect_signatures`/`resolve_use_decls`
5. **Codegen** (`codegen/emit.rs`): update pattern matches on `NodeKind` in `compile_stmt`/`compile_expr` and add IR generation. Read types from `world.types[node]` via `valtype_of` rather than re-parsing `TypeName`.
6. **Interpreter** (`interpreter.rs`): mirror the new behavior in `eval`/`eval_*` so codegen and interpreter stay aligned
7. **Printer** (`printer.rs`): extend the match so `--print-ast` keeps working
8. **Tests**: add a test program in `tests/programs/<name>/` with `source.ecs` and `expected_output`; wire it into `tests/compile_and_run.rs` and `tests/interpreter.rs`

When pattern-matching `NodeKind` in code that doesn't care about new fields, use `..` so future variant extensions don't break it.
