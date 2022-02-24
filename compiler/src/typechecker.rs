use crate::ast::*;
use im::HashMap as ImMap;
use std::cell::RefCell;
use std::collections::BTreeSet as MutSet;
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
    Function(Vec<Rc<SimpleType>>, Rc<SimpleType>),
    Record(ImMap<String, Rc<SimpleType>>),
}

use SimpleType::*;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct VariableState {
    lower_bounds: MutSet<Rc<SimpleType>>,
    upper_bounds: MutSet<Rc<SimpleType>>,
}

fn fresh_var() -> Rc<SimpleType> {
    let state = RefCell::new(VariableState {
        lower_bounds: MutSet::new(),
        upper_bounds: MutSet::new()
    });
    Rc::new(Variable(Rc::new(state)))
}

fn type_error(str: String) -> ! {
    panic!("type error: {}", str)
}

struct Typechecker {
    constraint_cache: RefCell<MutSet<(Rc<SimpleType>, Rc<SimpleType>)>>,
}

impl Typechecker {
    fn new() -> Self {
        Typechecker {
            constraint_cache: RefCell::new(MutSet::new()),
        }
    }

    fn constrain(&self, subtype: Rc<SimpleType>, supertype: Rc<SimpleType>) {
        if self
            .constraint_cache
            .borrow_mut()
            .insert((subtype.clone(), supertype.clone()))
        {
            match (&*subtype, &*supertype) {
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
                        self.constrain(arg2.clone(), arg1.clone());
                    }
                    self.constrain(ret1.clone(), ret2.clone());
                }
                (Record(fields1), Record(fields2)) => {
                    for (field, value2) in fields2.iter() {
                        match fields1.get(field) {
                            Some(value1) => self.constrain(value1.clone(), value2.clone()),
                            None => type_error(format!("missing field {}", field))
                        }
                    }
                }
                (Variable(subtype_state), supertype) => {
                    subtype_state.borrow_mut().lower_bounds.insert(Rc::new(supertype.clone()));
                }
                _ => unimplemented!(),
            }
        }
    }

    fn typecheck_expr(&self, expr: &Expr, var_ctx: &ImMap<String, Rc<SimpleType>>) -> Rc<SimpleType> {
        use crate::ast::Constant::*;
        use Expr::*;
        match expr {
            Constant(Bool(_)) => Rc::new(Primitive(Primitive::Bool)),
            Constant(Int(_)) => Rc::new(Primitive(Primitive::Int)),
            Constant(String(_)) => Rc::new(Primitive(Primitive::String)),
            Constant(Float(_)) => Rc::new(Primitive(Primitive::Float)),
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
                let f_type = Rc::new(Function(arg_types, return_type.clone()));
                self.constrain(self.typecheck_expr(f, var_ctx), f_type);
                return_type
            }
            Record(fields) => Rc::new(SimpleType::Record(
                fields
                    .iter()
                    .map(|(name, expr)| (name.clone(), self.typecheck_expr(expr, &var_ctx)))
                    .collect::<ImMap<_, _>>(),
            )),
            FieldAccess(expr, name) => {
                let return_type = fresh_var();
                self.constrain(
                    self.typecheck_expr(expr, var_ctx),
                    Rc::new(SimpleType::Record(im::hashmap!{name.clone() => return_type.clone()})),
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
            let simple_type = typechecker.typecheck_expr(&**expr, &ImMap::new());
            println!("{:?}", simple_type)
        }
        _ => unimplemented!(),
    }
}
