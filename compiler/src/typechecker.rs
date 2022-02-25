use crate::ast::*;
use crate::types::{AstType, SimpleType, Primitive};
use im::HashMap as ImMap;
use std::collections::BTreeSet as MutSet;
use std::cell::RefCell;
use std::rc::Rc;
use RecFlag::*;

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
        use SimpleType::*;
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
                (Variable(variable_state), _) => {
                    println!("hi there {:?} <: {:?}", subtype, supertype);
                    variable_state.borrow_mut().upper_bounds.insert(supertype.clone());
                    for lower_bound in variable_state.borrow().lower_bounds.iter() {
                        self.constrain(lower_bound.clone(), supertype.clone())
                    }
                }
                (_, Variable(variable_state)) => {
                    variable_state.borrow_mut().lower_bounds.insert(subtype.clone());
                    for upper_bound in variable_state.borrow().upper_bounds.iter() {
                        self.constrain(subtype.clone(), upper_bound.clone())
                    }

                }
                _ => type_error(format!("cannot constrain {:?} <: {:?}", subtype, supertype)),
            }
        }
    }

    fn typecheck_expr(&self, expr: &Expr, var_ctx: &ImMap<String, Rc<SimpleType>>) -> Rc<SimpleType> {
        use crate::ast::Constant::*;
        use Expr::*;
        match expr {
            Constant(Bool(_)) => Rc::new(SimpleType::Primitive(Primitive::Bool)),
            Constant(Int(_)) => Rc::new(SimpleType::Primitive(Primitive::Int)),
            Constant(String(_)) => Rc::new(SimpleType::Primitive(Primitive::String)),
            Constant(Float(_)) => Rc::new(SimpleType::Primitive(Primitive::Float)),
            Var(name) => match var_ctx.get(name) {
                Some(simpletype) => simpletype.clone(),
                None => type_error(format!("variable \"{}\" not found", name)),
            },
            Lambda(args, expr) => {
                match args.first() {
                    Some(Pattern::Var(name)) => {
                        let param = SimpleType::fresh_var();
                        let var_ctx = var_ctx.update(name.clone(), param.clone());
                        Rc::new(SimpleType::Function(vec![param],self.typecheck_expr(expr, &var_ctx)))
                    }
                    _ =>
                    // TODO: This should be able to typecheck all the patterns
                    {
                        unimplemented!()
                    }
                }
            }
            Apply(f, args) => {
                let return_type = SimpleType::fresh_var();
                let arg_types = args
                    .iter()
                    .map(|arg| self.typecheck_expr(arg, var_ctx))
                    .collect::<Vec<_>>();
                let f_type = Rc::new(SimpleType::Function(arg_types, return_type.clone()));
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
                let return_type = SimpleType::fresh_var();
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

pub fn typecheck(ast: &Program) -> AstType {
    assert_eq!(ast.len(), 1);
    let typechecker = Typechecker::new();
    match ast.first() {
        Some(Item::ItemLet(Nonrecursive, _name, expr)) => {
            let simple_type = typechecker.typecheck_expr(&**expr, &ImMap::new());
            println!("Simple type: {:?}", simple_type);
            SimpleType::coalesce(simple_type)
        }
        _ => unimplemented!(),
    }
}

mod test {
    use crate::types::*;
    use crate::typechecker::*;
    use crate::parser::*;

    #[allow(dead_code)]
    fn test(source: &str) -> AstType {
        let ast = parse(source);
        typecheck(&ast)
    }

    #[test]
    fn test_primitives() {
        insta::assert_debug_snapshot!(test("let x = 2"), @r###"
            Primitive(
                Int,
            )
            "###);
        insta::assert_debug_snapshot!(test("let x = \"hi there\""), @r###"
        Primitive(
            String,
        )
        "###);
        insta::assert_debug_snapshot!(test("let x = true"), @r###"
        Primitive(
            Bool,
        )
        "###);
    }

    #[test]
    fn test_record() {
        insta::assert_debug_snapshot!(test("let x = {:}"), @r###"
        Record(
            [],
        )
        "###);
        insta::assert_debug_snapshot!(test("let x = {name: \"Alfred\"}"), @r###"
        Record(
            [
                (
                    "name",
                    Primitive(
                        String,
                    ),
                ),
            ],
        )
        "###);
    }

    #[test]
    fn test_most_basic_apply() {
        insta::assert_debug_snapshot!(test("let x = |y| |x| y(x)"), @r###"
        Function(
            [
                Intersection(
                    TypeVariable(
                        "a0",
                    ),
                    Function(
                        [
                            TypeVariable(
                                "a1",
                            ),
                        ],
                        TypeVariable(
                            "a2",
                        ),
                    ),
                ),
            ],
            Function(
                [
                    TypeVariable(
                        "a1",
                    ),
                ],
                TypeVariable(
                    "a2",
                ),
            ),
        )
        "###);
    }

    #[test]
    fn test_twice() {
        insta::assert_debug_snapshot!(test("let x = |f| |x| f(f(x))"), @r###"
        Function(
            [
                Intersection(
                    Intersection(
                        TypeVariable(
                            "a0",
                        ),
                        Function(
                            [
                                TypeVariable(
                                    "a1",
                                ),
                            ],
                            TypeVariable(
                                "a3",
                            ),
                        ),
                    ),
                    Function(
                        [
                            TypeVariable(
                                "a3",
                            ),
                        ],
                        TypeVariable(
                            "a2",
                        ),
                    ),
                ),
            ],
            Function(
                [
                    TypeVariable(
                        "a1",
                    ),
                ],
                TypeVariable(
                    "a2",
                ),
            ),
        )
        "###);
    }
}
