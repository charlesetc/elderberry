use crate::ast::*;
use im::HashMap;
use std::cell::RefCell;
use std::collections::BTreeSet;
use std::rc::Rc;
use RecFlag::*;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Primitive {
    Int,
    Float,
    String,
    Bool,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum SimpleType {
    Variable(Rc<RefCell<VariableState>>),
    Primitive(Primitive),
    Function(Vec<SimpleType>, Box<SimpleType>),
    Record(HashMap<String, SimpleType>),
}

use SimpleType::*;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
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

fn type_error(str: String) -> ! {
    panic!("type error: {}", str)
}

struct Typechecker {
    constraint_cache: RefCell<BTreeSet<(SimpleType, SimpleType)>>,
}

impl Typechecker {
    fn new() -> Self {
        Typechecker {
            constraint_cache: RefCell::new(BTreeSet::new()),
        }
    }

    fn constrain(&self, subtype: &SimpleType, supertype: &SimpleType) {
        if self
            .constraint_cache
            .borrow_mut()
            .insert((subtype.clone(), supertype.clone()))
        {
            match (subtype, supertype) {
                (Primitive(n1), Primitive(n2)) if n1 == n2 => (), // all good
                (Function(args1, ret1), Function(args2, ret2)) => {
                    if args1.len() != args2.len() {
                        type_error(format!(
                            "called function with {} arguments, but it only takes {}",
                            args2.len(),
                            args1.len()
                        ));
                    }
                    for (arg1, arg2) in args1.iter().zip(args2.iter()) {
                        self.constrain(arg2, arg1);
                    }
                    self.constrain(ret1, ret2);
                }
                (Record(fields1), Record(fields2)) => {
                    for (field, value2) in fields2.iter() {
                        match fields1.get(field) {
                            Some(value1) => self.constrain(value1, value2),
                            None => type_error(format!("missing field {}", field))
                        }
                    }
                }
                _ => unimplemented!(),
            }
        }
    }

    fn typecheck_expr(&self, expr: &Expr, var_ctx: &HashMap<String, SimpleType>) -> SimpleType {
        use crate::ast::Constant::*;
        use Expr::*;
        match expr {
            Constant(Bool(_)) => Primitive(Primitive::Bool),
            Constant(Int(_)) => Primitive(Primitive::Int),
            Constant(String(_)) => Primitive(Primitive::String),
            Constant(Float(_)) => Primitive(Primitive::Float),
            Var(name) => match var_ctx.get(name) {
                Some(simpletype) => simpletype.clone(),
                None => type_error(format!("variable \"{}\" not found", name)),
            },
            Lambda(args, expr) => {
                match args.first() {
                    Some(Pattern::Var(name)) => {
                        let var_ctx = var_ctx.update(name.clone(), fresh_var());
                        self.typecheck_expr(expr, &var_ctx)
                    }
                    _ =>
                    // TODO: This should be able to typecheck all the patterns
                    {
                        unimplemented!()
                    }
                }
            }
            Apply(f, args) => {
                let return_type = fresh_var();
                let arg_types = args
                    .iter()
                    .map(|arg| self.typecheck_expr(arg, var_ctx))
                    .collect::<Vec<_>>();
                let f_type = Function(arg_types, Box::new(return_type.clone()));
                self.constrain(&self.typecheck_expr(f, var_ctx), &f_type);
                return_type
            }
            Record(fields) => SimpleType::Record(
                fields
                    .iter()
                    .map(|(name, expr)| (name.clone(), self.typecheck_expr(expr, &var_ctx)))
                    .collect::<HashMap<_, _>>(),
            ),
            FieldAccess(expr, name) => {
                let return_type = fresh_var();
                self.constrain(
                    &self.typecheck_expr(expr, var_ctx),
                    &SimpleType::Record(im::hashmap!{name.clone() => return_type.clone()}),
                );
                return_type
            }
            _ => unimplemented!(),
        }
    }
}

pub fn typecheck(ast: &Program) {
    assert_eq!(ast.len(), 1);
    let typechecker = Typechecker::new();
    match ast.first() {
        Some(Item::ItemLet(Nonrecursive, _name, expr)) => {
            let simple_type = typechecker.typecheck_expr(&**expr, &HashMap::new());
            println!("{:?}", simple_type)
        }
        _ => unimplemented!(),
    }
}
