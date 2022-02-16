use std::env;
use std::fs;

fn main() {
    let args = env::args().collect::<Vec<String>>();
    let filename = &args[1];
    let contents = fs::read_to_string(filename).expect("unable to read file");
    let ast = elderberry_compiler::parse(&contents);
    let js = elderberry_compiler::generate(ast);
    println!("{}", js);
}
