use crate::ast::*;
use crate::types::{unique_name, AstType, MaybeQuantified, Primitive, SimpleType, VariableState};
use im::HashMap as ImMap;
use std::cell::RefCell;
use std::collections::BTreeSet as MutSet;
use std::collections::HashMap as MutMap;
use std::rc::Rc;
use RecFlag::*;

fn type_error(str: String) -> ! {
    panic!("type error: {}", str)
}

fn constrain_(
    subtype: Rc<SimpleType>,
    supertype: Rc<SimpleType>,
    constraint_cache: Rc<RefCell<MutSet<(Rc<SimpleType>, Rc<SimpleType>)>>>,
) {
    use SimpleType::*;
    if constraint_cache
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
                    constrain_(arg2.clone(), arg1.clone(), constraint_cache.clone());
                }
                constrain_(ret1.clone(), ret2.clone(), constraint_cache);
            }
            (Record(fields1), Record(fields2)) => {
                for (field, value2) in fields2.iter() {
                    match fields1.get(field) {
                        Some(value1) => {
                            constrain_(value1.clone(), value2.clone(), constraint_cache.clone())
                        }
                        None => type_error(format!("missing field {}", field)),
                    }
                }
            }
            (Variable(variable_state), _) => {
                println!("hi there {:?} <: {:?}", subtype, supertype);
                variable_state
                    .borrow_mut()
                    .upper_bounds
                    .insert(supertype.clone());
                for lower_bound in variable_state.borrow().lower_bounds.iter() {
                    constrain_(
                        lower_bound.clone(),
                        supertype.clone(),
                        constraint_cache.clone(),
                    )
                }
            }
            (_, Variable(variable_state)) => {
                variable_state
                    .borrow_mut()
                    .lower_bounds
                    .insert(subtype.clone());
                for upper_bound in variable_state.borrow().upper_bounds.iter() {
                    constrain_(
                        subtype.clone(),
                        upper_bound.clone(),
                        constraint_cache.clone(),
                    )
                }
            }
            _ => type_error(format!("cannot constrain {:?} <: {:?}", subtype, supertype)),
        }
    }
}

fn constrain(subtype: Rc<SimpleType>, supertype: Rc<SimpleType>) {
    let constraint_cache = Rc::new(RefCell::new(MutSet::new()));
    constrain_(subtype, supertype, constraint_cache)
}

fn typecheck_statements(
    statements: &Statements,
    var_ctx: &ImMap<String, Rc<dyn MaybeQuantified>>,
) -> Rc<SimpleType> {
    use Statements::*;
    match statements {
        Empty => Rc::new(SimpleType::Primitive(Primitive::Unit)),
        Sequence(expr, rest) => {
            let expr_type = typecheck_expr(expr, var_ctx);
            match &**rest {
                Empty => expr_type,
                _ => typecheck_statements(rest, var_ctx),
            }
        }
        Let(Nonrecursive, name, expr, rest) => {
            let expr_type = typecheck_expr(expr, var_ctx);
            let var_ctx = var_ctx.update(name.clone(), expr_type);
            typecheck_statements(rest, &var_ctx)
        }
        Let(Recursive, _, _, _) => unimplemented!(),
    }
}

fn typecheck_expr(expr: &Expr, var_ctx: &ImMap<String, Rc<dyn MaybeQuantified>>) -> Rc<SimpleType> {
    use crate::ast::Constant::*;
    use Expr::*;
    match expr {
        Constant(Bool(_)) => Rc::new(SimpleType::Primitive(Primitive::Bool)),
        Constant(Int(_)) => Rc::new(SimpleType::Primitive(Primitive::Int)),
        Constant(String(_)) => Rc::new(SimpleType::Primitive(Primitive::String)),
        Constant(Float(_)) => Rc::new(SimpleType::Primitive(Primitive::Float)),
        Constant(Unit) => Rc::new(SimpleType::Primitive(Primitive::Unit)),
        Var(name) => match var_ctx.get(name) {
            Some(maybe_quantified) => maybe_quantified.clone().instantiate(),
            None => type_error(format!("variable \"{}\" not found", name)),
        },
        Lambda(args, expr) => {
            match args.first() {
                Some(Pattern::Var(name)) => {
                    let param = SimpleType::fresh_var();
                    let var_ctx = var_ctx.update(name.clone(), param.clone());
                    Rc::new(SimpleType::Function(
                        vec![param],
                        typecheck_expr(expr, &var_ctx),
                    ))
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
                .map(|arg| typecheck_expr(arg, var_ctx))
                .collect::<Vec<_>>();
            let f_type = Rc::new(SimpleType::Function(arg_types, return_type.clone()));
            constrain(typecheck_expr(f, var_ctx), f_type);
            return_type
        }
        Record(fields) => Rc::new(SimpleType::Record(
            fields
                .iter()
                .map(|(name, expr)| (name.clone(), typecheck_expr(expr, &var_ctx)))
                .collect::<ImMap<_, _>>(),
        )),
        FieldAccess(expr, name) => {
            let return_type = SimpleType::fresh_var();
            constrain(
                typecheck_expr(expr, var_ctx),
                Rc::new(SimpleType::Record(
                    im::hashmap! {name.clone() => return_type.clone()},
                )),
            );
            return_type
        }
        Block(statements) => typecheck_statements(statements, &var_ctx),
        If(condition, true_branch, false_branch) => {
            let condition_type = typecheck_expr(condition, &var_ctx);
            constrain(
                condition_type,
                Rc::new(SimpleType::Primitive(Primitive::Bool)),
            );
            let return_type = SimpleType::fresh_var();
            let true_type = typecheck_expr(true_branch, &var_ctx);
            let false_type = match false_branch {
                Some(false_branch) => typecheck_expr(false_branch, &var_ctx),
                None => Rc::new(SimpleType::Primitive(Primitive::Unit)),
            };
            constrain(true_type, return_type.clone());
            constrain(false_type, return_type.clone());
            return_type
        }
        _ => unimplemented!(),
    }
}

pub struct PolymorphicType(Rc<SimpleType>);

fn freshen_type(
    simple_type: &Rc<SimpleType>,
    qvar_context: Rc<RefCell<MutMap<String, String>>>,
) -> Rc<SimpleType> {
    use SimpleType::*;
    match *simple_type.clone() {
        Variable(ref state) => {
            let mut qvar_context = qvar_context.borrow_mut();
            let new_name = qvar_context
                .entry(state.borrow().unique_name.clone())
                .or_insert_with(|| unique_name());
            let new_state = VariableState {
                lower_bounds: state.borrow().lower_bounds.clone(),
                upper_bounds: state.borrow().upper_bounds.clone(),
                unique_name: new_name.clone(),
            };
            Rc::new(Variable(Rc::new(RefCell::new(new_state))))
        }
        Primitive(_) => simple_type.clone(),
        Function(ref args, ref ret) => {
            let args = args
                .iter()
                .map(|arg| freshen_type(arg, qvar_context.clone()))
                .collect();
            Rc::new(Function(args, freshen_type(ret, qvar_context.clone())))
        }
        Record(ref fields) => {
            let fields = fields
                .iter()
                .map(|(name, simple_type)| {
                    (
                        name.clone(),
                        freshen_type(simple_type, qvar_context.clone()),
                    )
                })
                .collect();
            Rc::new(Record(fields))
        }
    }
}

impl MaybeQuantified for PolymorphicType {
    fn instantiate(self: Rc<Self>) -> Rc<SimpleType> {
        let qvar_context = MutMap::new();
        freshen_type(&self.0, Rc::new(RefCell::new(qvar_context)))
    }
}

pub fn typecheck(items: &Program) -> AstType {
    let mut var_ctx = ImMap::new();
    let last_type = items
        .into_iter()
        .map(|item| {
            match item {
                Item::ItemLet(Nonrecursive, name, expr) => {
                    let simple_type = typecheck_expr(expr, &var_ctx);
                    let ptype = PolymorphicType(simple_type.clone());
                    var_ctx.insert(name.clone(), Rc::new(ptype));
                    simple_type
                    // println!("Simple type: {:?}", simple_type);
                }
                _ => unimplemented!(),
            }
        })
        .last()
        .unwrap();
    SimpleType::coalesce(last_type)
}

mod test {
    use crate::parser::*;
    use crate::typechecker::*;
    use crate::types::*;

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

    #[test]
    fn test_apply_to_object() {
        insta::assert_debug_snapshot!(test("let x = {let a = {x: 2, y:3}; let b =  {x:2, y:\"hi\", z:true}; let f = |o| o.x; f(a); f(b); }"), @r###"
        Union(
            TypeVariable(
                "a3",
            ),
            Primitive(
                Int,
            ),
        )
        "###);
    }

    #[test]
    fn test_if_statement() {
        insta::assert_debug_snapshot!(test("let x = if true 2 else \"hi\" "), @r###"
        Union(
            Union(
                TypeVariable(
                    "a0",
                ),
                Primitive(
                    Int,
                ),
            ),
            Primitive(
                String,
            ),
        )
        "###);
        insta::assert_debug_snapshot!(test("let x = |x| if x x else x"), @r###"
        Function(
            [
                Intersection(
                    Intersection(
                        TypeVariable(
                            "a1",
                        ),
                        TypeVariable(
                            "a2",
                        ),
                    ),
                    Primitive(
                        Bool,
                    ),
                ),
            ],
            TypeVariable(
                "a2",
            ),
        )
        "###)
    }

    #[test]
    fn test_polymorphism() {
        insta::assert_debug_snapshot!(test("let id = |y| y"), @r###"
        Function(
            [
                TypeVariable(
                    "a0",
                ),
            ],
            TypeVariable(
                "a0",
            ),
        )
        "###);
        // This is wrong
        insta::assert_debug_snapshot!(test("let id = |x| x let x = { id(2); id(\"3\"); id; }"), @r###"
        Function(
            [
                TypeVariable(
                    "a6",
                ),
            ],
            TypeVariable(
                "a6",
            ),
        )
        "###);
        // This is wrong
        insta::assert_debug_snapshot!(test("let id = |x| x let x = { id(2); id(\"3\"); }"), @r###"
        TypeVariable(
            "a4",
        )
        "###);
    }
}
