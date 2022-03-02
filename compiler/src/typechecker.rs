use crate::ast::*;
use crate::types::{
    unique_name, AstType, ConcreteType, MaybeQuantified, Primitive, SimpleType, VariableState,
};
use im::HashMap as ImMap;
use im::OrdSet as ImSet;
use std::cell::RefCell;
use std::collections::BTreeMap as MutMap;
use std::collections::BTreeSet as MutSet;
use std::rc::Rc;
use RecFlag::*;

fn type_error(str: String) -> ! {
    panic!("type error: {}", str)
}

type ConstraintCache = Rc<RefCell<MutSet<(Rc<SimpleType>, Rc<SimpleType>)>>>;

fn new_lower_bound(
    state: Rc<RefCell<VariableState>>,
    lower_bound: Rc<ConcreteType>,
    cache: ConstraintCache,
) {
    let existing_lower_bound = state.borrow().lower_bound.clone();
    state.borrow_mut().lower_bound = least_upper_bound_concrete(
        existing_lower_bound,
        lower_bound.clone(),
        cache.clone(),
    );
    constrain_concrete_types(lower_bound, state.borrow().upper_bound.clone(), cache);
}
fn new_upper_bound(
    state: Rc<RefCell<VariableState>>,
    upper_bound: Rc<ConcreteType>,
    cache: ConstraintCache,
) {
    let existing_upper_bound = state.borrow().upper_bound.clone();
    state.borrow_mut().upper_bound = greatest_lower_bound_concrete(
        existing_upper_bound,
        upper_bound.clone(),
        cache.clone(),
    );
    constrain_concrete_types(state.borrow().lower_bound.clone(), upper_bound, cache);
}

fn unify_and_replace(
    a: Rc<RefCell<VariableState>>,
    b: Rc<RefCell<VariableState>>,
    cache: ConstraintCache,
) -> Rc<RefCell<VariableState>> {
    new_lower_bound(a.clone(), b.borrow().lower_bound.clone(), cache.clone());
    new_upper_bound(a.clone(), b.borrow().upper_bound.clone(), cache);
    b.replace(a.borrow().clone());
    a
}

fn greatest_lower_bound_concrete(
    a: Rc<ConcreteType>,
    b: Rc<ConcreteType>,
    cache: ConstraintCache,
) -> Rc<ConcreteType> {
    use ConcreteType::*;
    match (&*a, &*b) {
        (Top, _) => b,
        (_, Top) => a,
        (Bottom, _) | (_, Bottom) => Rc::new(Bottom),
        (Function(args1, ret1), Function(args2, ret2)) => {
            assert_eq!(args1.len(), args2.len());
            Rc::new(Function(
                args1
                    .iter()
                    .zip(args2.iter())
                    .map(|(arg1, arg2)| {
                        least_upper_bound(arg1.clone(), arg2.clone(), cache.clone())
                    })
                    .collect(),
                greatest_lower_bound(ret1.clone(), ret2.clone(), cache),
            ))
        }
        (Primitive(a), Primitive(b)) if a == b => Rc::new(Primitive(a.clone())),
        (Record(a_fields), Record(b_fields)) => {
            let all_keys: ImSet<String> = a_fields.keys().chain(b_fields.keys()).collect();
            let fields = all_keys
                .iter()
                .map(|key| {
                    let value = match (a_fields.get(key), b_fields.get(key)) {
                        (None, None) => panic!("at least one of these should have each key"),
                        (None, Some(value)) | (Some(value), None) => value.clone(),
                        (Some(a_value), Some(b_value)) => {
                            greatest_lower_bound(a_value.clone(), b_value.clone(), cache.clone())
                        }
                    };
                    (key.clone(), value)
                })
                .collect();
            Rc::new(Record(fields))
        }
        _ => panic!(
            "type error, cannot unify least upper bounds: {:?} {:?}",
            a, b
        ),
    }
}

fn least_upper_bound_concrete(
    a: Rc<ConcreteType>,
    b: Rc<ConcreteType>,
    cache: ConstraintCache,
) -> Rc<ConcreteType> {
    use ConcreteType::*;
    match (&*a, &*b) {
        (Bottom, _) => b,
        (_, Bottom) => a,
        (Top, _) | (_, Top) => Rc::new(Top),
        (Function(args1, ret1), Function(args2, ret2)) => {
            assert_eq!(
                args1.len(),
                args2.len(),
                "function called with the wrong number of arguments"
            );
            Rc::new(Function(
                args1
                    .iter()
                    .zip(args2.iter())
                    .map(|(arg1, arg2)| {
                        greatest_lower_bound(arg1.clone(), arg2.clone(), cache.clone())
                    })
                    .collect(),
                least_upper_bound(ret1.clone(), ret2.clone(), cache),
            ))
        }
        (Primitive(a), Primitive(b)) if a == b => Rc::new(Primitive(a.clone())),
        (Record(a_fields), Record(b_fields)) => {
            let all_keys: ImSet<String> = a_fields.keys().chain(b_fields.keys()).collect();
            let fields = all_keys
                .iter()
                .map(|key| {
                    let value = match (a_fields.get(key), b_fields.get(key)) {
                        (None, None) => panic!("at least one of these should have each key"),
                        (None, Some(value)) | (Some(value), None) => value.clone(),
                        (Some(a_value), Some(b_value)) => {
                            least_upper_bound(a_value.clone(), b_value.clone(), cache.clone())
                        }
                    };
                    (key.clone(), value)
                })
                .collect();
            Rc::new(Record(fields))
        }
        _ => panic!(
            "type error, cannot unify least upper bounds: {:?} {:?}",
            a, b
        ),
    }
}

fn greatest_lower_bound(
    a: Rc<SimpleType>,
    b: Rc<SimpleType>,
    cache: ConstraintCache,
) -> Rc<SimpleType> {
    use SimpleType::*;
    match (&*a, &*b) {
        (Concrete(a), Concrete(b)) => {
            let c = greatest_lower_bound_concrete(a.clone(), b.clone(), cache);
            Rc::new(Concrete(c))
        }
        (Variable(a), Variable(b)) => {
            Rc::new(Variable(unify_and_replace(a.clone(), b.clone(), cache)))
        }
        (Variable(v), Concrete(c)) => {
            new_upper_bound(v.clone(), c.clone(), cache);
            a
        }
        (Concrete(c), Variable(v)) => {
            new_upper_bound(v.clone(), c.clone(), cache);
            b
        }
    }
}

fn least_upper_bound(
    a: Rc<SimpleType>,
    b: Rc<SimpleType>,
    cache: ConstraintCache,
) -> Rc<SimpleType> {
    use SimpleType::*;
    match (&*a, &*b) {
        (Concrete(a), Concrete(b)) => {
            let c = least_upper_bound_concrete(a.clone(), b.clone(), cache);
            Rc::new(Concrete(c))
        }
        (Variable(a), Variable(b)) => {
            Rc::new(Variable(unify_and_replace(a.clone(), b.clone(), cache)))
        }
        (Variable(v), Concrete(c)) => {
            new_lower_bound(v.clone(), c.clone(), cache);
            a
        }
        (Concrete(c), Variable(v)) => {
            new_lower_bound(v.clone(), c.clone(), cache);
            b
        }
    }
}

fn constrain_concrete_types(
    subtype: Rc<ConcreteType>,
    supertype: Rc<ConcreteType>,
    cache: ConstraintCache,
) {
    use ConcreteType::*;
    match (&*subtype, &*supertype) {
        (Bottom, _) | (_, Top) => (),
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
                constrain_(arg2.clone(), arg1.clone(), cache.clone());
            }
            constrain_(ret1.clone(), ret2.clone(), cache);
        }
        (Record(fields1), Record(fields2)) => {
            for (field, value2) in fields2.iter() {
                match fields1.get(field) {
                    Some(value1) => constrain_(value1.clone(), value2.clone(), cache.clone()),
                    None => type_error(format!("missing field {}", field)),
                }
            }
        }
        _ => type_error(format!("cannot constrain {:?} <: {:?}", subtype, supertype)),
    }
}

fn constrain_(subtype: Rc<SimpleType>, supertype: Rc<SimpleType>, cache: ConstraintCache) {
    use SimpleType::*;

    if cache.borrow_mut().insert((subtype.clone(), supertype.clone())) {
        match (&*subtype, &*supertype) {
            (Concrete(subtype_c), Concrete(supertype_c)) => {
                constrain_concrete_types(subtype_c.clone(), supertype_c.clone(), cache)
            }
            (Variable(state1), Variable(state2)) => {
                unify_and_replace(state1.clone(), state2.clone(), cache);
            }
            (Variable(v), Concrete(supertype)) => {
                new_upper_bound(v.clone(), supertype.clone(), cache);
            }
            (Concrete(subtype), Variable(v)) => {
                new_lower_bound(v.clone(), subtype.clone(), cache);
            }
        }
    }
}

fn constrain(subtype: Rc<SimpleType>, supertype: Rc<SimpleType>) {
    let cache = Rc::new(RefCell::new(MutSet::new()));
    constrain_(subtype, supertype, cache)
}

fn primitive_simple_type(p: Primitive) -> Rc<SimpleType> {
    Rc::new(SimpleType::Concrete(Rc::new(ConcreteType::Primitive(p))))
}

fn typecheck_statements(
    statements: &Statements,
    var_ctx: &ImMap<String, Rc<dyn MaybeQuantified>>,
) -> Rc<SimpleType> {
    use Statements::*;
    match statements {
        Empty => primitive_simple_type(Primitive::Unit),
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
    let simple_type = match expr {
        Constant(Bool(_)) => primitive_simple_type(Primitive::Bool),
        Constant(Int(_)) => primitive_simple_type(Primitive::Int),
        Constant(String(_)) => primitive_simple_type(Primitive::String),
        Constant(Float(_)) => primitive_simple_type(Primitive::Float),
        Constant(Unit) => primitive_simple_type(Primitive::Unit),
        Var(name) => match var_ctx.get(name) {
            Some(maybe_quantified) => maybe_quantified.clone().instantiate(),
            None => type_error(format!("variable \"{}\" not found", name)),
        },
        Lambda(args, expr) => {
            match args.first() {
                Some(Pattern::Var(name)) => {
                    let param = SimpleType::fresh_var();
                    let var_ctx = var_ctx.update(name.clone(), param.clone());
                    Rc::new(SimpleType::Concrete(Rc::new(ConcreteType::Function(
                        vec![param],
                        typecheck_expr(expr, &var_ctx),
                    ))))
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
            let f_type = Rc::new(SimpleType::Concrete(Rc::new(ConcreteType::Function(
                arg_types,
                return_type.clone(),
            ))));
            constrain(typecheck_expr(f, var_ctx), f_type);
            return_type
        }
        Record(fields) => Rc::new(SimpleType::Concrete(Rc::new(ConcreteType::Record(
            fields
                .iter()
                .map(|(name, expr)| (name.clone(), typecheck_expr(expr, &var_ctx)))
                .collect::<ImMap<_, _>>(),
        )))),
        FieldAccess(expr, name) => {
            let return_type = SimpleType::fresh_var();
            constrain(
                typecheck_expr(expr, var_ctx),
                Rc::new(SimpleType::Concrete(Rc::new(ConcreteType::Record(
                    im::hashmap! {name.clone() => return_type.clone()},
                )))),
            );
            return_type
        }
        Block(statements) => typecheck_statements(statements, &var_ctx),
        If(condition, true_branch, false_branch) => {
            let condition_type = typecheck_expr(condition, &var_ctx);
            constrain(condition_type, primitive_simple_type(Primitive::Bool));
            let return_type = SimpleType::fresh_var();
            let true_type = typecheck_expr(true_branch, &var_ctx);
            let false_type = match false_branch {
                Some(false_branch) => typecheck_expr(false_branch, &var_ctx),
                None => primitive_simple_type(Primitive::Unit),
            };
            constrain(true_type, return_type.clone());
            constrain(false_type, return_type.clone());
            return_type
        }
        Variant(_, _) => unimplemented!(),
        Match(_, _) => unimplemented!(),
    };
    simple_type
}

pub struct PolymorphicType(Rc<SimpleType>);

fn freshen_concrete_type(
    c: Rc<ConcreteType>,
    qvar_context: Rc<RefCell<MutMap<String, Rc<RefCell<VariableState>>>>>,
) -> Rc<ConcreteType> {
    use ConcreteType::*;
    match &*c {
        Top | Bottom | Primitive(_) => c.clone(),
        Function(ref args, ref ret) => {
            let args = args
                .iter()
                .map(|arg| freshen_simple_type(arg.clone(), qvar_context.clone()))
                .collect();
            Rc::new(Function(
                args,
                freshen_simple_type(ret.clone(), qvar_context.clone()),
            ))
        }
        Record(ref fields) => {
            let fields = fields
                .iter()
                .map(|(name, simple_type)| {
                    (
                        name.clone(),
                        freshen_simple_type(simple_type.clone(), qvar_context.clone()),
                    )
                })
                .collect();
            Rc::new(Record(fields))
        }
    }
}

fn freshen_simple_type(
    simple_type: Rc<SimpleType>,
    qvar_context: Rc<RefCell<MutMap<String, Rc<RefCell<VariableState>>>>>,
) -> Rc<SimpleType> {
    use SimpleType::*;
    match &*simple_type.clone() {
        Variable(ref state) => {
            let existing_name = state.borrow().unique_name.clone();
            let new_state = {
                let qvar_context = qvar_context.borrow();
                qvar_context.get(&existing_name).map(|x| x.clone())
            };
            // Freshen the constraints as well - a bit wordy.
            let new_state = match new_state {
                None => {
                    let new_state = Rc::new(RefCell::new(VariableState {
                        lower_bound: freshen_concrete_type(
                            state.borrow().lower_bound.clone(),
                            qvar_context.clone(),
                        ),
                        upper_bound: freshen_concrete_type(
                            state.borrow().upper_bound.clone(),
                            qvar_context.clone(),
                        ),
                        unique_name: unique_name(),
                    }));
                    qvar_context
                        .borrow_mut()
                        .insert(existing_name, new_state.clone());
                    new_state
                }
                Some(new_state) => new_state.clone(),
            };
            Rc::new(Variable(new_state.clone()))
        }
        Concrete(c) => Rc::new(Concrete(freshen_concrete_type(c.clone(), qvar_context))),
    }
}

impl MaybeQuantified for PolymorphicType {
    fn instantiate(self: Rc<Self>) -> Rc<SimpleType> {
        let qvar_context = MutMap::new();
        freshen_simple_type(self.0.clone(), Rc::new(RefCell::new(qvar_context)))
    }
}

type PolarVariable = (VariableState, bool);

fn coalesce_concrete_type(
    concrete_type: Rc<ConcreteType>,
    recursive_variables: Rc<RefCell<MutMap<PolarVariable, String>>>,
    polarity: bool,
    in_process: ImSet<PolarVariable>,
) -> AstType {
    match &*concrete_type {
        ConcreteType::Top => AstType::Top,
        ConcreteType::Bottom => AstType::Bottom,
        ConcreteType::Primitive(p) => AstType::Primitive(p.clone()),
        ConcreteType::Function(args, ret) => {
            let args = args
                .iter()
                .map(|arg| {
                    coalesce_simple_type_(
                        arg.clone(),
                        recursive_variables.clone(),
                        !polarity,
                        in_process.clone(),
                    )
                })
                .collect::<Vec<_>>();
            let ret = coalesce_simple_type_(ret.clone(), recursive_variables, polarity, in_process);
            AstType::Function(args, Rc::new(ret))
        }
        ConcreteType::Record(fields) => {
            let fields = fields
                .iter()
                .map(|(name, field_type)| {
                    (
                        name.clone(),
                        coalesce_simple_type_(
                            field_type.clone(),
                            recursive_variables.clone(),
                            polarity,
                            in_process.clone(),
                        ),
                    )
                })
                .collect::<Vec<_>>();
            AstType::Record(fields)
        }
    }
}

fn coalesce_simple_type_(
    simple_type: Rc<SimpleType>,
    recursive_variables: Rc<RefCell<MutMap<PolarVariable, String>>>,
    polarity: bool,
    in_process: ImSet<PolarVariable>,
) -> AstType {
    use SimpleType::*;
    match &*simple_type {
        Concrete(c) => coalesce_concrete_type(c.clone(), recursive_variables, polarity, in_process),
        Variable(state) => {
            let polar_var = (state.borrow().clone(), polarity);
            if in_process.contains(&polar_var) {
                let name = recursive_variables
                    .borrow_mut()
                    .entry(polar_var)
                    .or_insert_with(|| unique_name())
                    .clone();
                AstType::TypeVariable(name)
            } else {
                let in_process = in_process.update(polar_var.clone());
                let bounded_type = if polarity {
                    state.borrow().lower_bound.clone()
                } else {
                    state.borrow().upper_bound.clone()
                };
                let ast_type = coalesce_concrete_type(
                    bounded_type,
                    recursive_variables.clone(),
                    polarity,
                    in_process,
                );
                let this_var = AstType::TypeVariable(state.borrow().unique_name.clone());
                let ast_type =
                    if polarity && ast_type == AstType::Bottom || ast_type == AstType::Top {
                        this_var
                    } else {
                        if polarity {
                            AstType::Union(Rc::new(this_var), Rc::new(ast_type))
                        } else {
                            AstType::Intersection(Rc::new(this_var), Rc::new(ast_type))
                        }
                    };
                match recursive_variables.borrow().get(&polar_var) {
                    Some(name) => AstType::Recursive(name.clone(), Rc::new(ast_type)),
                    None => ast_type,
                }
            }
        }
    }
}

fn coalesce_simple_type(simple_type: Rc<SimpleType>) -> AstType {
    let recursive_variables = Rc::new(RefCell::new(MutMap::new()));
    coalesce_simple_type_(simple_type, recursive_variables, true, ImSet::new())
}

pub fn typecheck(items: &Program) -> AstType {
    let mut var_ctx = ImMap::new();
    let last_type = items
        .into_iter()
        .map(|item| match item {
            Item::ItemLet(Nonrecursive, name, expr) => {
                let simple_type = typecheck_expr(expr, &var_ctx);
                let ptype = PolymorphicType(simple_type.clone());
                var_ctx.insert(name.clone(), Rc::new(ptype));
                simple_type
            }
            _ => unimplemented!(),
        })
        .last()
        .unwrap();
    coalesce_simple_type(last_type).simplify()
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
        insta::assert_debug_snapshot!(test("let f = |r| { r.hi; r.there; r; }"), @r###"
        Function(
            [
                Intersection(
                    TypeVariable(
                        "a0",
                    ),
                    Record(
                        [
                            (
                                "hi",
                                Bottom,
                            ),
                            (
                                "there",
                                Bottom,
                            ),
                        ],
                    ),
                ),
            ],
            TypeVariable(
                "a0",
            ),
        )
        "###);
    }

    #[test]
    fn test_most_basic_apply() {
        insta::assert_debug_snapshot!(test("let x = |y| |x| y(x)"), @r###"
        Function(
            [
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
                Function(
                    [
                        TypeVariable(
                            "a1",
                        ),
                    ],
                    TypeVariable(
                        "a1",
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
                    "a1",
                ),
            ),
        )
        "###);
    }

    #[test]
    fn test_apply_to_object() {
        insta::assert_debug_snapshot!(test("let f = |o| o.y let x = {let a = {x: 2, y:3}; let b =  {x:2, y:\"hi\", z:true}; f(a); f(b); }"), @r###"
        Primitive(
            String,
        )
        "###);
    }

    #[test]
    fn test_if_statement() {
        insta::assert_debug_snapshot!(test("let x = if true 2 else 3 "), @r###"
        Primitive(
            Int,
        )
        "###);
        insta::assert_debug_snapshot!(test("let x = |x| if x x else x"), @r###"
        Function(
            [
                Intersection(
                    TypeVariable(
                        "a1",
                    ),
                    Primitive(
                        Bool,
                    ),
                ),
            ],
            TypeVariable(
                "a1",
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
        Primitive(
            String,
        )
        "###);
    }
}
