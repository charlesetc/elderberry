use crate::ast::*;
use std::cell::RefCell;
use im::HashMap;
use std::rc::Rc;
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
    Variable(Rc<RefCell<VariableState>>),
    Primitive(Primitive),
    Function(Vec<SimpleType>, Box<SimpleType>),
    Record(Vec<(String, SimpleType)>),
}

use SimpleType::*;

#[derive(Debug, Clone)]
struct VariableState {
    lower_bounds: Vec<SimpleType>,
    upper_bounds: Vec<SimpleType>,
}

fn fresh_var() -> SimpleType {
    let state = RefCell::new(VariableState {
        lower_bounds: vec![],
        upper_bounds: vec![],
    });
    Variable(Rc::new(state))
}

fn error(str: String) -> ! {
    panic!("type error: {}", str)
}

fn constrain(type1 : SimpleType, type2 : SimpleType) {
    unimplemented!()
}

fn typecheck_expr(expr: &Expr, var_ctx: &HashMap<String, SimpleType>) -> SimpleType {
    use crate::ast::Constant::*;
    use Expr::*;
    match expr {
        Constant(Bool(_)) => Primitive(Primitive::Bool),
        Constant(Int(_)) => Primitive(Primitive::Int),
        Constant(String(_)) => Primitive(Primitive::String),
        Constant(Float(_)) => Primitive(Primitive::Float),
        Var(name) => match var_ctx.get(name) {
            Some(simpletype) => simpletype.clone(),
            None => error(format!("variable \"{}\" not found", name)),
        },
        Lambda(args, expr) => {
            match args.first() {
                Some(Pattern::Var(name)) => {
                    let var_ctx = var_ctx.update(name.clone(), fresh_var());
                    typecheck_expr(expr, &var_ctx)},
                _ => 
                    // TODO: This should be able to typecheck all the patterns
                    unimplemented!()
            } 
        }
        Apply(f, args) => {
            let return_type = fresh_var();
            let arg_types = args.iter().map(|arg| typecheck_expr(arg, var_ctx)).collect::<Vec<_>>();
            let f_type = Function(arg_types, Box::new(return_type.clone()));
            constrain(typecheck_expr(f, var_ctx), f_type);
            return_type
        }
        Record(fields) => SimpleType::Record(
            fields
                .iter()
                .map(|(name, expr)| (name.clone(), typecheck_expr(expr, &var_ctx)))
                .collect::<Vec<_>>(),
        ),
        FieldAccess(expr, name) => {
            let return_type = fresh_var();
            constrain(typecheck_expr(expr, var_ctx), SimpleType::Record(vec![(name.clone(), return_type.clone())]));
            return_type
        }
        _ => unimplemented!(),
    }
}

pub fn typecheck(ast: &Program) {
    assert_eq!(ast.len(), 1);
    match ast.first() {
        Some(Item::ItemLet(Nonrecursive, _name, expr)) => {
            let simple_type = typecheck_expr(&**expr, &HashMap::new());
            println!("{:?}", simple_type)
        }
        _ => unimplemented!(),
    }
}
