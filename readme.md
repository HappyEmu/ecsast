ECSAST - A Language Compiler Using ECS for the AST
====================================================

ECSAST is a small compiled language implemented in Rust. Its distinguishing
feature is that the Abstract Syntax Tree uses an Entity-Component-System (ECS)
pattern: every AST node is just an ID, and all data about nodes lives in
separate slotmap stores (kinds, spans, types, etc.).

The compiler produces native binaries via Cranelift.


Prerequisites
-------------

- Rust toolchain (rustup.rs) — edition 2024, rustc 1.90+
- A C compiler (cc) on your PATH — used to link the output binary
- macOS or Linux


Quick Start
-----------

1. Build the compiler:

    cargo build

2. Compile and run an example program:

    cargo run -- examples/hello.ecs
    ./output

   You should see: Hello, world!

3. Use -o to choose the output binary name:

    cargo run -- examples/fizzbuzz.ecs -o fizz
    ./fizz

4. Enable optimizations with -O:

    cargo run -- examples/add.ecs -o add -O speed
    ./add


Writing Programs
----------------

Source files use the .ecs extension. The language is statically typed with
C-like syntax. Every program needs a fn main() entry point.

Example (examples/fibonacci.ecs):

    fn fibonacci(n: int) -> int {
        if n <= 1 {
            return n;
        }
        return fibonacci(n - 1) + fibonacci(n - 2);
    }

    fn main() {
        print(fibonacci(10));
    }

Supported features:
  - Types: int, bool, str (float is parsed but not yet in codegen)
  - Arithmetic: + - * / %
  - Comparison: == != < <= > >=
  - Logical: && || !
  - Variables: let x: int = 42;
  - Assignment: x = x + 1;
  - Control flow: if/else, while, return
  - Functions: fn name(params) -> ReturnType { body }
  - Inline functions: inline fn name(params) -> ReturnType { body }
  - Built-ins: print() works with int, bool, and str values
  - Command-line args: argc() returns argument count, arg(i) for use in print()

Inline Functions
----------------

Mark a function with the `inline` keyword to have Cranelift inline it at
every call site. This eliminates call overhead for small helper functions:

    inline fn add(a: int, b: int) -> int {
        return a + b;
    }

    fn main() {
        print(add(3, 4));
    }

When compiled with -O speed, the add call is fully inlined and the optimizer
can constant-fold the result.

Optimization Levels
-------------------

The compiler supports three optimization levels via the -O flag:

    cargo run -- <FILE> -O none           # no optimizations (default)
    cargo run -- <FILE> -O speed          # optimize for execution speed
    cargo run -- <FILE> -O speed-and-size # optimize for speed and code size


Project Layout
--------------

    src/
      main.rs         CLI entry point (clap-based argument parsing)
      lib.rs          Library root, re-exports modules
      lexer.rs        Tokenizer: source text -> Vec<Token>
      parser.rs       Recursive-descent parser with precedence climbing
      ast.rs          NodeId, NodeKind, AstWorld (the ECS store)
      codegen.rs      Cranelift-based native code generation
      passes.rs       Tree-walk annotation passes (currently unused)
      interpreter.rs  Tree-walking interpreter (alternative to codegen)
      printer.rs      Debug pretty-printer for the AST
      span.rs         Byte-range source locations

    examples/         Example .ecs programs you can compile and run
    tests/
      compile_and_run.rs  End-to-end codegen tests (compile + run binary)
      interpreter.rs      Interpreter tests (parse + interpret in-process)
      programs/           Shared test fixtures (source.ecs + expected_output)


Running Tests
-------------

    cargo test           # run all tests (parser + codegen + interpreter)
    cargo test -- <name> # run a single test by name substring
    cargo clippy         # check for lint warnings


How the Compiler Works
----------------------

The pipeline is:

    .ecs source file
         |
         v
    Lexer (lexer.rs) -- produces a list of tokens
         |
         v
    Parser (parser.rs) -- builds AstWorld with node kinds and spans
         |
         v
    Codegen (codegen.rs) -- two-pass Cranelift compilation:
       1. Declare all functions (enables forward references)
       2. Define each function body as Cranelift IR
       3. Inline marked functions at call sites via ctx.inline()
         |
         v
    Linker (cc) -- links object file with a small C runtime
         |
         v
    Native binary (./output or custom name via -o)

The C runtime provides print_int(), print_str(), and argument access functions
so the built-ins work. It is compiled and linked automatically — you don't
need to do anything special.


Architecture Note: Why ECS?
----------------------------

Traditional compilers store AST data directly in tree nodes. ECSAST instead
gives each node just an integer ID (NodeId) and stores all properties in
separate slotmap "component stores":

    kinds:    SlotMap<NodeId, NodeKind>          — what kind of node it is
    spans:    SecondaryMap<NodeId, Span>          — source location (byte range)
    types:    SparseSecondaryMap<NodeId, TypeInfo>— type info (filled by passes)
    parents:  SecondaryMap<NodeId, NodeId>        — parent pointers (filled by passes)

SlotMap is used instead of HashMap for two reasons:

  1. Performance: SlotMap uses a dense array indexed by the slot's integer
     index, so lookups are O(1) without any hashing. SecondaryMap (used for
     eagerly-populated stores like spans) shares the same layout and is
     equally fast. SparseSecondaryMap (used for sparsely-populated stores
     like types) falls back to a hash map internally but is still keyed by
     the same NodeId type.

  2. Safety: SlotMap keys carry a generation counter. If a node were ever
     removed and its slot reused, any old NodeId would be detected as stale
     rather than silently returning the wrong node. This prevents a class of
     dangling-reference bugs at zero runtime cost for the common (no-removal)
     case.

This makes it easy to add new compiler passes without modifying existing
data structures — each pass just writes to its own store.
