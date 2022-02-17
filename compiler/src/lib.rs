mod ast;
mod generator;
mod parser;
mod typechecker;

pub use generator::generate;
pub use parser::parse;
pub use typechecker::typecheck;