mod ast;
mod generator;
mod parser;
mod typechecker;
mod typechecker_tests;
mod types;

pub use generator::generate;
pub use parser::parse;
pub use typechecker::typecheck_modules;
