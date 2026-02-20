use std::path::PathBuf;
use std::time::Instant;

use bumpalo::Bump;
use clap::{Parser as ClapParser, ValueEnum};
use ecsast::codegen::{self, OptLevel};
use ecsast::lexer::Lexer;
use ecsast::parser::Parser;

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
    lex_time: std::time::Duration,
    parse_time: std::time::Duration,
    codegen_time: std::time::Duration,
    src_len: usize,
) {
    let src_bytes = src_len as f64;
    let mb = |d: std::time::Duration| src_bytes / d.as_secs_f64() / (1024.0 * 1024.0);
    let total = lex_time + parse_time + codegen_time;
    eprintln!("  lex:     {lex_time:>10.3?}  ({:>8.2} MB/s)", mb(lex_time));
    eprintln!("  parse:   {parse_time:>10.3?}  ({:>8.2} MB/s)", mb(parse_time));
    eprintln!("  codegen: {codegen_time:>10.3?}  ({:>8.2} MB/s)", mb(codegen_time));
    eprintln!("  total:   {:>10.3?}  ({:>8.2} MB/s)", total, mb(total));
}

fn main() {
    let cli = Cli::parse();

    let src = std::fs::read_to_string(&cli.file).unwrap_or_else(|e| {
        eprintln!("Error reading {}: {e}", cli.file.display());
        std::process::exit(1);
    });

    let t0 = Instant::now();
    let tokens = Lexer::new(&src).tokenize();
    let lex_time = t0.elapsed();

    let arena = Bump::new();
    let mut parser = Parser::new(&tokens, &arena);
    let t1 = Instant::now();
    let root = parser.parse_program();
    let parse_time = t1.elapsed();
    let world = parser.world;

    let output = cli.output.to_str().expect("invalid output path");
    let t2 = Instant::now();
    codegen::compile_to_executable(&world, root, output, cli.opt_level.into())
        .expect("compilation failed");
    let codegen_time = t2.elapsed();

    println!("Compiled {} -> {output}", cli.file.display());

    if cli.time {
        print_timings(lex_time, parse_time, codegen_time, src.len());
    }
}
