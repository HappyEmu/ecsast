use std::path::PathBuf;
use std::time::Instant;

use bumpalo::Bump;
use clap::{Parser as ClapParser, ValueEnum};
use ecsast::ast::AstWorld;
use ecsast::codegen::{self, OptLevel};
use ecsast::modules;
use ecsast::passes;

#[derive(Clone, Copy, Debug, Default, ValueEnum)]
enum CliOptLevel {
    /// No optimizations
    #[default]
    None,
    /// Optimize for execution speed
    Speed,
    /// Optimize for both speed and code size
    SpeedAndSize,
}

impl From<CliOptLevel> for OptLevel {
    fn from(level: CliOptLevel) -> Self {
        match level {
            CliOptLevel::None => OptLevel::None,
            CliOptLevel::Speed => OptLevel::Speed,
            CliOptLevel::SpeedAndSize => OptLevel::SpeedAndSize,
        }
    }
}

#[derive(ClapParser)]
#[command(name = "ecsast", about = "ECSAST language compiler")]
struct Cli {
    /// Source file to compile (.ecs)
    file: PathBuf,

    /// Output binary path
    #[arg(short, long, default_value = "output")]
    output: PathBuf,

    /// Optimization level
    #[arg(short = 'O', long = "opt-level", default_value = "none")]
    opt_level: CliOptLevel,

    /// Print timing diagnostics for each compilation phase
    #[arg(long)]
    time: bool,
}

fn print_timings(
    load_time: std::time::Duration,
    analysis_time: std::time::Duration,
    codegen_time: std::time::Duration,
) {
    let total = load_time + analysis_time + codegen_time;
    eprintln!("  load:    {load_time:>10.3?}");
    eprintln!("  analyze: {analysis_time:>10.3?}");
    eprintln!("  codegen: {codegen_time:>10.3?}");
    eprintln!("  total:   {total:>10.3?}");
}

fn main() {
    let cli = Cli::parse();

    let arena = Bump::new();
    let mut world = AstWorld::new();

    let t0 = Instant::now();
    let mut graph = modules::ModuleGraph::load(&cli.file, &arena, &mut world).unwrap_or_else(|e| {
        eprintln!("{e}");
        std::process::exit(1);
    });
    let load_time = t0.elapsed();

    let t1 = Instant::now();
    if let Err(err) = passes::analyze(&mut world, &mut graph) {
        eprintln!("Analysis error: {err}");
        std::process::exit(1);
    }
    let analysis_time = t1.elapsed();

    let output = cli.output.to_str().expect("invalid output path");
    let t2 = Instant::now();
    codegen::compile(&world, &graph, output, cli.opt_level.into()).expect("compilation failed");
    let codegen_time = t2.elapsed();

    println!("Compiled {} -> {output}", cli.file.display());

    if cli.time {
        print_timings(load_time, analysis_time, codegen_time);
    }
}
