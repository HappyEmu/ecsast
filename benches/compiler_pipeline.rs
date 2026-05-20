use std::hint::black_box;

use bumpalo::Bump;
use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use ecsast::ast::AstWorld;
use ecsast::lexer::Lexer;
use ecsast::parser::Parser;
use ecsast::passes;

const PROGRAMS: &[(&str, &str)] = &[
    (
        "fibonacci",
        include_str!("../tests/programs/fibonacci/source.ecs"),
    ),
    ("strings", include_str!("../tests/programs/strings/source.ecs")),
    (
        "stress_big_blocks",
        include_str!("../tests/programs/stress_big_blocks/source.ecs"),
    ),
];

fn lex_source(src: &str) -> usize {
    Lexer::new(black_box(src)).tokenize().len()
}

fn parse_source(src: &str) -> usize {
    let tokens = Lexer::new(src).tokenize();
    let arena = Bump::new();
    let mut world = AstWorld::new();
    let mut parser = Parser::new(black_box(&tokens), &arena, &mut world);
    let root = parser.parse_file();
    black_box(root);
    world.kinds.len()
}

fn analyze_source(src: &str) -> usize {
    // Synthesize a one-module graph in-memory so we can drive `analyze` without
    // touching the filesystem.
    use ecsast::modules::{Module, ModuleGraph, ModuleId};
    use std::collections::HashMap;
    use std::path::PathBuf;

    let tokens = Lexer::new(src).tokenize();
    let arena = Bump::new();
    let mut world = AstWorld::new();
    let mut parser = Parser::new(&tokens, &arena, &mut world);
    let root = parser.parse_file();

    let mut by_path = HashMap::new();
    by_path.insert(Vec::<String>::new(), ModuleId(0));
    let mut graph = ModuleGraph {
        modules: vec![Module {
            id: ModuleId(0),
            file_path: PathBuf::from("<bench>"),
            mod_path: Vec::new(),
            root,
            imports: HashMap::new(),
            module_aliases: HashMap::new(),
        }],
        by_path,
        entry: ModuleId(0),
    };
    passes::analyze(&mut world, &mut graph).expect("analysis failed");
    world.types.len() + world.resolved.len() + world.parents.len()
}

fn compiler_pipeline(c: &mut Criterion) {
    let mut group = c.benchmark_group("compiler_pipeline");

    for &(name, src) in PROGRAMS {
        group.bench_with_input(BenchmarkId::new("lex", name), src, |b, src| {
            b.iter(|| lex_source(src));
        });
        group.bench_with_input(BenchmarkId::new("parse", name), src, |b, src| {
            b.iter(|| parse_source(src));
        });
        group.bench_with_input(BenchmarkId::new("parse_analyze", name), src, |b, src| {
            b.iter(|| analyze_source(src));
        });
    }

    group.finish();
}

criterion_group!(benches, compiler_pipeline);
criterion_main!(benches);
