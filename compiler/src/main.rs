use clap::Parser;
use std::fs;

#[derive(Parser)]
#[clap(author, version, about, long_about = None)]
enum Cli {
    Typecheck { filename: String },
    Compile { filename: String },
}

fn main() {
    let cli = Cli::parse();
    match &cli {
        Cli::Compile { filename } => {
            let contents = fs::read_to_string(filename).expect("unable to read file");
            let ast = elderberry_compiler::parse(&contents);
            elderberry_compiler::typecheck(&ast);
            let js = elderberry_compiler::generate(ast);
            println!("{}", js);
        }
        Cli::Typecheck { filename } => {
            let contents = fs::read_to_string(filename).expect("unable to read file");
            let ast = elderberry_compiler::parse(&contents);
            let type_of_ast = elderberry_compiler::typecheck(&ast);
            println!("Type of ast: {:?}", type_of_ast);
        }
    }
}
