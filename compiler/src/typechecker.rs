use crate::ast::*;
use std::collections::HashMap;
use RecFlag::*;


#[derive(Debug, Clone)]
enum Primitive {
    Int,
    Float,
    String,
    Bool,
} 

#[derive(Debug, Clone)]
enum SimpleType {
    Variable(VariableState),
    Primitive(Primitive),
    Function(Box<SimpleType>, Box<SimpleType>),
    Record(Vec<(String, SimpleType)>),
}

use SimpleType::*;

#[derive(Debug, Clone)]
struct VariableState {
    lower_bounds: Vec<SimpleType>,
    upper_bounds: Vec<SimpleType>,
}

fn fresh_var() -> SimpleType {
    Variable(VariableState {lower_bounds: vec![], upper_bounds: vec![]})
}

fn error(str : String) -> ! {
    panic!(
        "type error: {}",
        str
    )
}

fn typecheck_expr<'a>(expr: &Expr, mut var_ctx : &'a HashMap<String, SimpleType>) -> &'a SimpleType {
    use crate::ast::Constant::*;
    use Expr::*;
    match expr {
        Constant(Bool(_)) => &Primitive(Primitive::Bool),
        Constant(Int(_)) => &Primitive(Primitive::Int),
        Constant(String(_)) => &Primitive(Primitive::String),
        Var(name) => match var_ctx.get(name) {
            Some(simpletype) => simpletype,
            None => error(format!("variable \"{}\" not found", name))

        },
        _ => unimplemented!(),
    }
}

pub fn typecheck(ast: &Program) {
    let mut var_ctx = HashMap::new();
    assert_eq!(ast.len(), 1);
    match ast.first() {
        Some(Item::ItemLet(Nonrecursive, _name, expr)) => {
            let simple_type = typecheck_expr(&**expr, &mut var_ctx);
            println!("{:?}", simple_type)

        },
        _ => unimplemented!()
    }
}
