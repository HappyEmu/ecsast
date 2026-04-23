use std::hint::black_box;

use bumpalo::Bump;
use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
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
    let mut parser = Parser::new(black_box(&tokens), &arena);
    let root = parser.parse_program();
    black_box(root);
    parser.world.kinds.len()
}

fn analyze_source(src: &str) -> usize {
    let tokens = Lexer::new(src).tokenize();
    let arena = Bump::new();
    let mut parser = Parser::new(&tokens, &arena);
    let root = parser.parse_program();
    let mut world = parser.world;
    passes::analyze_program(&mut world, root).expect("analysis failed");
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
