use std::path::PathBuf;

use bumpalo::Bump;
use clap::Parser as ClapParser;
use ecsast::codegen;
use ecsast::lexer::Lexer;
use ecsast::parser::Parser;

#[derive(ClapParser)]
#[command(name = "ecsast", about = "ECSAST language compiler")]
struct Cli {
    /// Source file to compile (.ecs)
    file: PathBuf,

    /// Output binary path
    #[arg(short, long, default_value = "output")]
    output: PathBuf,
}

fn main() {
    let cli = Cli::parse();

    let src = std::fs::read_to_string(&cli.file).unwrap_or_else(|e| {
        eprintln!("Error reading {}: {e}", cli.file.display());
        std::process::exit(1);
    });

    let tokens = Lexer::new(&src).tokenize();

    let arena = Bump::new();
    let mut parser = Parser::new(&tokens, &arena);
    let root = parser.parse_program();
    let world = parser.world;

    let output = cli.output.to_str().expect("invalid output path");
    codegen::compile_to_executable(&world, root, output).expect("compilation failed");

    println!("Compiled {} -> {output}", cli.file.display());
}
