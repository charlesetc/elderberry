use crate::ast::*;
use crate::types::{
    unique_name, AstType, ConcreteType, ItemType, MaybeQuantified, Primitive, Signature,
    SimpleType, VariableStates,
};
use im::OrdMap as ImMap;
use im::OrdSet as ImSet;
use std::cell::RefCell;
use std::collections::BTreeMap as MutMap;
use std::collections::BTreeSet as MutSet;
use std::collections::VecDeque;
use std::rc::Rc;
use RecFlag::*;

fn type_error(str: String) -> ! {
    panic!("type error: {}", str)
}

type ConstraintCache = Rc<RefCell<MutSet<(Rc<SimpleType>, Rc<SimpleType>)>>>;

fn new_lower_bound(
    v: &VarName,
    lower_bound: Rc<ConcreteType>,
    variable_states: Rc<RefCell<VariableStates>>,
    cache: ConstraintCache,
) {
    let existing_lower_bound = variable_states.borrow().lower_bound(v);
    let new_lower_bound = least_upper_bound_concrete(
        existing_lower_bound.clone(),
        lower_bound.clone(),
        variable_states.clone(),
        cache.clone(),
    );
    // println!(
    //     "LOWER BOUNDING {} WHICH_HAS {:?} WITH {:?} TO GET {:?}",
    //     v, existing_lower_bound, lower_bound, new_lower_bound
    // );
    variable_states
        .borrow_mut()
        .set_lower_bound(v, new_lower_bound);
    let upper_bound = variable_states.borrow().upper_bound(v);
    constrain_concrete_types(lower_bound, upper_bound, variable_states, cache);
}

fn new_upper_bound(
    v: &VarName,
    upper_bound: Rc<ConcreteType>,
    variable_states: Rc<RefCell<VariableStates>>,
    cache: ConstraintCache,
) {
    // println!("UPPER BOUNDING {} with {:?}", v, upper_bound);
    let existing_upper_bound = variable_states.borrow().upper_bound(v);
    let new_upper_bound = greatest_lower_bound_concrete(
        existing_upper_bound,
        upper_bound.clone(),
        variable_states.clone(),
        cache.clone(),
    );
    variable_states
        .borrow_mut()
        .set_upper_bound(v, new_upper_bound);
    let lower_bound = variable_states.borrow().lower_bound(v);
    constrain_concrete_types(lower_bound, upper_bound, variable_states, cache);
}

fn unify_and_replace(
    a: &VarName,
    b: &VarName,
    variable_states: Rc<RefCell<VariableStates>>,
    cache: ConstraintCache,
) -> VarName {
    if a == b {
        // this just saves some work - everything below should have been a no-op
        return a.clone();
    }
    let lower_bound = variable_states.borrow().lower_bound(b);
    new_lower_bound(a, lower_bound, variable_states.clone(), cache.clone());
    let upper_bound = variable_states.borrow().upper_bound(b);
    new_upper_bound(a, upper_bound, variable_states.clone(), cache);
    variable_states.borrow_mut().link_to(b, a);
    a.clone()
}

fn greatest_lower_bound_concrete(
    a: Rc<ConcreteType>,
    b: Rc<ConcreteType>,
    variable_states: Rc<RefCell<VariableStates>>,
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
                        least_upper_bound(
                            arg1.clone(),
                            arg2.clone(),
                            variable_states.clone(),
                            cache.clone(),
                        )
                    })
                    .collect(),
                greatest_lower_bound(ret1.clone(), ret2.clone(), variable_states.clone(), cache),
            ))
        }
        (Primitive(a), Primitive(b)) if a == b => Rc::new(Primitive(a.clone())),
        (Variant(a_variants), Variant(b_variants)) => {
            let all_keys: ImSet<String> = a_variants.keys().chain(b_variants.keys()).collect();
            let variants = all_keys
                .into_iter()
                .map(|key| {
                    let value = match (a_variants.get(&key), b_variants.get(&key)) {
                        (None, None) => panic!("bug: at least one of these should have each key"),
                        (None, Some(args)) | (Some(args), None) => args.clone(),
                        (Some(a_args), Some(b_args)) => {
                            if a_args.len() != b_args.len() {
                                panic!("variant {} has been used with {} arguments and also {} arguments", key.clone(), a_args.len(), b_args.len())
                            }
                            let mut args = vec![];
                            for i in 0..a_args.len() {
                                let a_arg = &a_args[i];
                                let b_arg = &b_args[i];
                                let arg = least_upper_bound(a_arg.clone(), b_arg.clone(), variable_states.clone(), cache.clone());
                                args.push(arg)
                            }
                            args
                        }
                    };
                    (key, value)
                })
                .collect();
            Rc::new(Variant(variants))
        }
        (Record(a_fields), Record(b_fields)) => {
            let all_keys: ImSet<String> = a_fields.keys().chain(b_fields.keys()).collect();
            let fields = all_keys
                .into_iter()
                .map(|key| {
                    let value = match (a_fields.get(&key), b_fields.get(&key)) {
                        (None, None) => panic!("bug: at least one of these should have each key"),
                        (None, Some(value)) | (Some(value), None) => value.clone(),
                        (Some(a_value), Some(b_value)) => least_upper_bound(
                            a_value.clone(),
                            b_value.clone(),
                            variable_states.clone(),
                            cache.clone(),
                        ),
                    };
                    (key, value)
                })
                .collect();
            Rc::new(Record(fields))
        }
        _ => panic!(
            "type error: cannot unify greatest lower bounds: {:?} and {:?}",
            a, b
        ),
    }
}

fn least_upper_bound_concrete(
    a: Rc<ConcreteType>,
    b: Rc<ConcreteType>,
    variable_states: Rc<RefCell<VariableStates>>,
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
                        greatest_lower_bound(
                            arg1.clone(),
                            arg2.clone(),
                            variable_states.clone(),
                            cache.clone(),
                        )
                    })
                    .collect(),
                least_upper_bound(ret1.clone(), ret2.clone(), variable_states, cache),
            ))
        }
        (Primitive(a), Primitive(b)) if a == b => Rc::new(Primitive(a.clone())),
        (Variant(a_variants), Variant(b_variants)) => {
            let all_keys: ImSet<String> = a_variants.keys().chain(b_variants.keys()).collect();
            let variants = all_keys
                .into_iter()
                .filter_map(|key| match (a_variants.get(&key), b_variants.get(&key)) {
                    (None, None) => panic!("bug: at least one of these should have each key"),
                    (None, Some(args)) | (Some(args), None) => Some((key, args.clone())),
                    (Some(a_args), Some(b_args)) => {
                        if a_args.len() != b_args.len() {
                            panic!(
                                "variant {} has been used with {} arguments and also {} arguments",
                                key.clone(),
                                a_args.len(),
                                b_args.len()
                            )
                        }
                        let mut args = vec![];
                        for i in 0..a_args.len() {
                            let a_arg = &a_args[i];
                            let b_arg = &b_args[i];
                            let arg = least_upper_bound(
                                a_arg.clone(),
                                b_arg.clone(),
                                variable_states.clone(),
                                cache.clone(),
                            );
                            args.push(arg)
                        }
                        Some((key, args))
                    }
                })
                .collect();
            Rc::new(Variant(variants))
        }
        (Record(a_fields), Record(b_fields)) => {
            let all_keys: ImSet<String> = a_fields.keys().chain(b_fields.keys()).collect();
            let fields = all_keys
                .iter()
                .filter_map(|key| match (a_fields.get(key), b_fields.get(key)) {
                    (None, None) => panic!("at least one of these should have each key"),
                    (None, Some(_)) | (Some(_), None) => None,
                    (Some(a_value), Some(b_value)) => Some((
                        key.clone(),
                        greatest_lower_bound(
                            a_value.clone(),
                            b_value.clone(),
                            variable_states.clone(),
                            cache.clone(),
                        ),
                    )),
                })
                .collect();
            Rc::new(Record(fields))
        }
        _ => panic!(
            "type error: cannot unify least upper bounds: {:?} and {:?}",
            a, b
        ),
    }
}

fn greatest_lower_bound(
    a: Rc<SimpleType>,
    b: Rc<SimpleType>,
    variable_states: Rc<RefCell<VariableStates>>,
    cache: ConstraintCache,
) -> Rc<SimpleType> {
    use SimpleType::*;
    match (&*a, &*b) {
        (Concrete(a), Concrete(b)) => {
            let c = greatest_lower_bound_concrete(a.clone(), b.clone(), variable_states, cache);
            Rc::new(Concrete(c))
        }
        (Variable(a), Variable(b)) => {
            Rc::new(Variable(unify_and_replace(&a, &b, variable_states, cache)))
        }
        (Variable(v), Concrete(c)) => {
            new_upper_bound(v, c.clone(), variable_states, cache);
            a
        }
        (Concrete(c), Variable(v)) => {
            new_upper_bound(v, c.clone(), variable_states, cache);
            b
        }
    }
}

fn least_upper_bound(
    a: Rc<SimpleType>,
    b: Rc<SimpleType>,
    variable_states: Rc<RefCell<VariableStates>>,
    cache: ConstraintCache,
) -> Rc<SimpleType> {
    use SimpleType::*;
    match (&*a, &*b) {
        (Concrete(a), Concrete(b)) => {
            let c = least_upper_bound_concrete(a.clone(), b.clone(), variable_states, cache);
            Rc::new(Concrete(c))
        }
        (Variable(a), Variable(b)) => {
            Rc::new(Variable(unify_and_replace(a, b, variable_states, cache)))
        }
        (Variable(v), Concrete(c)) => {
            new_lower_bound(v, c.clone(), variable_states, cache);
            a
        }
        (Concrete(c), Variable(v)) => {
            new_lower_bound(v, c.clone(), variable_states, cache);
            b
        }
    }
}

fn constrain_concrete_types(
    subtype: Rc<ConcreteType>,
    supertype: Rc<ConcreteType>,
    variable_states: Rc<RefCell<VariableStates>>,
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
                constrain_(
                    arg2.clone(),
                    arg1.clone(),
                    variable_states.clone(),
                    cache.clone(),
                );
            }
            constrain_(ret1.clone(), ret2.clone(), variable_states, cache);
        }
        (Record(fields1), Record(fields2)) => {
            for (field, value2) in fields2.iter() {
                match fields1.get(field) {
                    Some(value1) => constrain_(
                        value1.clone(),
                        value2.clone(),
                        variable_states.clone(),
                        cache.clone(),
                    ),
                    None => type_error(format!("missing field {}", field)),
                }
            }
        }
        (Variant(variants1), Variant(variants2)) => {
            for (name, args2) in variants1.iter() {
                match variants2.get(name) {
                    // Similar to function definition
                    Some(args1) => {
                        if args1.len() != args2.len() {
                            type_error(format!(
                                "matched against variant {} with {} arguments, but it only takes {}",
                                name,
                                args2.len(),
                                args1.len()
                            ));
                        }
                        for (arg1, arg2) in args1.iter().zip(args2.iter()) {
                            constrain_(
                                arg1.clone(),
                                arg2.clone(),
                                variable_states.clone(),
                                cache.clone(),
                            );
                        }
                    }
                    None => type_error(format!("missing variant {}", name)),
                }
            }
        }
        _ => type_error(format!(
            "cannot constrain {:#?} <: {:#?}",
            subtype, supertype
        )),
    }
}

fn constrain_(
    subtype: Rc<SimpleType>,
    supertype: Rc<SimpleType>,
    variable_states: Rc<RefCell<VariableStates>>,
    cache: ConstraintCache,
) {
    use SimpleType::*;
    if cache
        .borrow_mut()
        .insert((subtype.clone(), supertype.clone()))
    {
        match (&*subtype, &*supertype) {
            (Concrete(subtype_c), Concrete(supertype_c)) => constrain_concrete_types(
                subtype_c.clone(),
                supertype_c.clone(),
                variable_states,
                cache,
            ),
            (Variable(state1), Variable(state2)) => {
                unify_and_replace(state1, state2, variable_states, cache);
            }
            (Variable(v), Concrete(supertype)) => {
                new_upper_bound(v, supertype.clone(), variable_states, cache);
            }
            (Concrete(subtype), Variable(v)) => {
                new_lower_bound(v, subtype.clone(), variable_states, cache);
            }
        }
    }
}

fn constrain(
    subtype: Rc<SimpleType>,
    supertype: Rc<SimpleType>,
    variable_states: Rc<RefCell<VariableStates>>,
) {
    let cache = Rc::new(RefCell::new(MutSet::new()));
    constrain_(subtype, supertype, variable_states, cache)
}

fn primitive_simple_type(p: Primitive) -> Rc<SimpleType> {
    Rc::new(SimpleType::Concrete(Rc::new(ConcreteType::Primitive(p))))
}

fn typecheck_statements(
    statements: &Statements,
    var_ctx: &ImMap<String, Rc<dyn MaybeQuantified>>,
    variable_states: Rc<RefCell<VariableStates>>,
) -> Rc<SimpleType> {
    use Statements::*;
    match statements {
        Empty => primitive_simple_type(Primitive::Unit),
        Sequence(expr, rest) => {
            let expr_type = typecheck_expr(expr, var_ctx, variable_states.clone());
            match &**rest {
                Empty => expr_type,
                _ => typecheck_statements(rest, var_ctx, variable_states),
            }
        }
        Let(Nonrecursive, name, expr, rest) => {
            let expr_type = typecheck_expr(expr, var_ctx, variable_states.clone());
            let var_ctx = var_ctx.update(name.clone(), expr_type);
            typecheck_statements(rest, &var_ctx, variable_states)
        }
        Let(Recursive, name, expr, rest) => {
            // TODO: Maybe only allow this for functions?
            let name_type = variable_states.borrow_mut().fresh_var();
            let var_ctx = var_ctx.update(name.clone(), name_type.clone());
            constrain(
                typecheck_expr(expr, &var_ctx, variable_states.clone()),
                name_type,
                variable_states.clone(),
            );
            typecheck_statements(rest, &var_ctx, variable_states)
        }
    }
}

fn typecheck_constant(constant: &Constant) -> Rc<SimpleType> {
    use crate::ast::Constant::*;
    match constant {
        Bool(_) => primitive_simple_type(Primitive::Bool),
        Int(_) => primitive_simple_type(Primitive::Int),
        String(_) => primitive_simple_type(Primitive::String),
        Float(_) => primitive_simple_type(Primitive::Float),
        Unit => primitive_simple_type(Primitive::Unit),
    }
}

fn typecheck_pattern(
    pat: &Pattern,
    var_ctx: &ImMap<String, Rc<dyn MaybeQuantified>>,
    variable_states: Rc<RefCell<VariableStates>>,
) -> (Rc<SimpleType>, ImMap<String, Rc<dyn MaybeQuantified>>) {
    use Pattern::*;
    match pat {
        Constant(c) => (typecheck_constant(c), var_ctx.clone()),
        Variant(name, patterns) => {
            let mut var_ctx = var_ctx.clone();
            let pattern_types = patterns
                .iter()
                .map(|pattern| {
                    let (pattern_type, new_var_ctx) =
                        typecheck_pattern(pattern, &var_ctx, variable_states.clone());
                    var_ctx = new_var_ctx;
                    pattern_type
                })
                .collect();
            (
                Rc::new(SimpleType::Concrete(Rc::new(ConcreteType::Variant(
                    im::ordmap! {name.clone() => pattern_types},
                )))),
                var_ctx,
            )
        }
        Record(fields) => {
            let mut var_ctx = var_ctx.clone();
            let fields = fields
                .iter()
                .map(|(name, pattern)| {
                    let (pattern_type, new_var_ctx) =
                        typecheck_pattern(pattern, &var_ctx, variable_states.clone());
                    var_ctx = new_var_ctx;
                    (name, pattern_type)
                })
                .collect();
            (
                Rc::new(SimpleType::Concrete(Rc::new(ConcreteType::Record(fields)))),
                var_ctx,
            )
        }
        Var(name) => {
            let var_type = variable_states.borrow_mut().fresh_var();
            (var_type.clone(), var_ctx.update(name.clone(), var_type))
        }
        Wildcard => (variable_states.borrow_mut().fresh_var(), var_ctx.clone()),
    }
}

fn typecheck_expr(
    expr: &Expr,
    var_ctx: &ImMap<String, Rc<dyn MaybeQuantified>>,
    variable_states: Rc<RefCell<VariableStates>>,
) -> Rc<SimpleType> {
    use Expr::*;
    let simple_type = match expr {
        Constant(c) => typecheck_constant(c),
        Var(None, name) => match var_ctx.get(name) {
            Some(maybe_quantified) => maybe_quantified.clone().instantiate(variable_states),
            None => type_error(format!("variable \"{}\" not found", name)),
        },
        Var(Some(_path), _name) => unimplemented!(),
        Lambda(args, expr) => {
            let (arg_types, var_ctx) = {
                let mut arg_types = vec![];
                let var_ctx = args.iter().fold(var_ctx.clone(), |var_ctx, arg| {
                    let (arg_type, var_ctx) =
                        typecheck_pattern(arg, &var_ctx, variable_states.clone());
                    arg_types.push(arg_type);
                    var_ctx
                });
                (arg_types, var_ctx)
            };
            Rc::new(SimpleType::Concrete(Rc::new(ConcreteType::Function(
                arg_types,
                typecheck_expr(expr, &var_ctx, variable_states),
            ))))
        }
        Apply(f, args) => {
            let return_type = variable_states.borrow_mut().fresh_var();
            let arg_types = args
                .iter()
                .map(|arg| typecheck_expr(arg, var_ctx, variable_states.clone()))
                .collect::<Vec<_>>();
            let f_type = Rc::new(SimpleType::Concrete(Rc::new(ConcreteType::Function(
                arg_types,
                return_type.clone(),
            ))));
            constrain(
                typecheck_expr(f, var_ctx, variable_states.clone()),
                f_type,
                variable_states,
            );
            return_type
        }
        Record(fields) => Rc::new(SimpleType::Concrete(Rc::new(ConcreteType::Record(
            fields
                .iter()
                .map(|(name, expr)| {
                    (
                        name.clone(),
                        typecheck_expr(expr, &var_ctx, variable_states.clone()),
                    )
                })
                .collect::<ImMap<_, _>>(),
        )))),
        FieldAccess(expr, name) => {
            let return_type = variable_states.borrow_mut().fresh_var();
            constrain(
                typecheck_expr(expr, var_ctx, variable_states.clone()),
                Rc::new(SimpleType::Concrete(Rc::new(ConcreteType::Record(
                    im::ordmap! {name.clone() => return_type.clone()},
                )))),
                variable_states,
            );
            return_type
        }
        Block(statements) => typecheck_statements(statements, &var_ctx, variable_states),
        If(condition, true_branch, false_branch) => {
            let condition_type = typecheck_expr(condition, &var_ctx, variable_states.clone());
            constrain(
                condition_type,
                primitive_simple_type(Primitive::Bool),
                variable_states.clone(),
            );
            let return_type = variable_states.borrow_mut().fresh_var();
            let true_branch_type = typecheck_expr(true_branch, &var_ctx, variable_states.clone());
            let false_branch_type = match false_branch {
                Some(false_branch) => {
                    typecheck_expr(false_branch, &var_ctx, variable_states.clone())
                }
                None => primitive_simple_type(Primitive::Unit),
            };
            constrain(
                true_branch_type,
                return_type.clone(),
                variable_states.clone(),
            );
            constrain(false_branch_type, return_type.clone(), variable_states);
            return_type
        }
        Match(expr, branches) => {
            let return_type = variable_states.borrow_mut().fresh_var();
            let expr_type = typecheck_expr(expr, var_ctx, variable_states.clone());
            for (pattern, branch_expr) in branches.iter() {
                let (pattern_type, var_ctx) =
                    typecheck_pattern(pattern, var_ctx, variable_states.clone());
                constrain(expr_type.clone(), pattern_type, variable_states.clone());
                let branch_type = typecheck_expr(branch_expr, &var_ctx, variable_states.clone());
                constrain(branch_type, return_type.clone(), variable_states.clone());
            }
            return_type
        }
        Variant(name, args) => {
            let arg_types = args
                .iter()
                .map(|arg| typecheck_expr(arg, var_ctx, variable_states.clone()))
                .collect();
            Rc::new(SimpleType::Concrete(Rc::new(ConcreteType::Variant(
                im::ordmap! {name.clone() => arg_types},
            ))))
        }
    };
    // println!("TYPECHECK EXPR {:?}", expr);
    // println!("TYPECHECK GOT  {:?}", simple_type);
    simple_type
}

fn freshen_concrete_type(
    c: Rc<ConcreteType>,
    variable_states: Rc<RefCell<VariableStates>>,
    qvar_context: Rc<RefCell<MutMap<VarName, VarName>>>,
) -> Rc<ConcreteType> {
    use ConcreteType::*;
    match &*c {
        Top | Bottom | Primitive(_) => c.clone(),
        Function(ref args, ref ret) => {
            let args = args
                .iter()
                .map(|arg| {
                    freshen_simple_type(arg.clone(), variable_states.clone(), qvar_context.clone())
                })
                .collect();
            Rc::new(Function(
                args,
                freshen_simple_type(ret.clone(), variable_states.clone(), qvar_context.clone()),
            ))
        }
        Variant(ref variants) => {
            let variants = variants
                .iter()
                .map(|(name, simple_types)| {
                    let simple_types: Vec<_> = simple_types
                        .iter()
                        .map(|simple_type| {
                            freshen_simple_type(
                                simple_type.clone(),
                                variable_states.clone(),
                                qvar_context.clone(),
                            )
                        })
                        .collect();
                    (name.clone(), simple_types)
                })
                .collect();
            Rc::new(Variant(variants))
        }
        Record(ref fields) => {
            let fields = fields
                .iter()
                .map(|(name, simple_type)| {
                    (
                        name.clone(),
                        freshen_simple_type(
                            simple_type.clone(),
                            variable_states.clone(),
                            qvar_context.clone(),
                        ),
                    )
                })
                .collect();
            Rc::new(Record(fields))
        }
    }
}

fn freshen_simple_type(
    simple_type: Rc<SimpleType>,
    variable_states: Rc<RefCell<VariableStates>>,
    qvar_context: Rc<RefCell<MutMap<VarName, VarName>>>,
) -> Rc<SimpleType> {
    use SimpleType::*;
    match &*simple_type.clone() {
        Variable(ref existing_name) => {
            let cached_v = {
                let qvar_context = qvar_context.borrow();
                qvar_context.get(existing_name).map(|x| x.clone())
            };
            // Freshen the constraints as well - a bit wordy.
            let v = match cached_v {
                None => {
                    let existing_lower_bound = variable_states.borrow().lower_bound(existing_name);
                    let existing_upper_bound = variable_states.borrow().upper_bound(existing_name);
                    let new_lower_bound = freshen_concrete_type(
                        existing_lower_bound,
                        variable_states.clone(),
                        qvar_context.clone(),
                    );
                    let new_upper_bound = freshen_concrete_type(
                        existing_upper_bound,
                        variable_states.clone(),
                        qvar_context.clone(),
                    );
                    let new_name = variable_states.borrow_mut().fresh_var_name();
                    variable_states
                        .borrow_mut()
                        .set_lower_bound(&new_name, new_lower_bound);
                    variable_states
                        .borrow_mut()
                        .set_upper_bound(&new_name, new_upper_bound);
                    qvar_context
                        .borrow_mut()
                        .insert(existing_name.clone(), new_name.clone());
                    new_name
                }
                Some(v) => v.clone(),
            };
            Rc::new(Variable(v.clone()))
        }
        Concrete(c) => Rc::new(Concrete(freshen_concrete_type(
            c.clone(),
            variable_states,
            qvar_context,
        ))),
    }
}

#[derive(Debug, Clone)]
pub struct PolymorphicType(Rc<SimpleType>);

impl MaybeQuantified for PolymorphicType {
    fn instantiate(self: Rc<Self>, variable_states: Rc<RefCell<VariableStates>>) -> Rc<SimpleType> {
        let qvar_context = MutMap::new();
        freshen_simple_type(
            self.0.clone(),
            variable_states,
            Rc::new(RefCell::new(qvar_context)),
        )
    }
}

type PolarVariable = (String, bool);

fn coalesce_concrete_type_after_recursion_check(
    concrete_type: Rc<ConcreteType>,
    variable_states: Rc<RefCell<VariableStates>>,
    recursive_variables_vars: Rc<RefCell<MutMap<PolarVariable, String>>>,
    recursive_variables_types: Rc<RefCell<MutMap<Rc<ConcreteType>, String>>>,
    in_process_vars: ImSet<PolarVariable>,
    in_process_types: ImSet<Rc<ConcreteType>>,
    polarity: bool,
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
                        variable_states.clone(),
                        recursive_variables_vars.clone(),
                        recursive_variables_types.clone(),
                        in_process_vars.clone(),
                        in_process_types.clone(),
                        !polarity,
                    )
                })
                .collect::<Vec<_>>();
            let ret = coalesce_simple_type_(
                ret.clone(),
                variable_states,
                recursive_variables_vars,
                recursive_variables_types,
                in_process_vars,
                in_process_types,
                polarity,
            );
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
                            variable_states.clone(),
                            recursive_variables_vars.clone(),
                            recursive_variables_types.clone(),
                            in_process_vars.clone(),
                            in_process_types.clone(),
                            polarity,
                        ),
                    )
                })
                .collect::<Vec<_>>();
            AstType::Record(fields)
        }
        ConcreteType::Variant(variants) => {
            let variants = variants
                .iter()
                .map(|(name, variant_types)| {
                    let variant_types = variant_types
                        .iter()
                        .map(|variant_type| {
                            coalesce_simple_type_(
                                variant_type.clone(),
                                variable_states.clone(),
                                recursive_variables_vars.clone(),
                                recursive_variables_types.clone(),
                                in_process_vars.clone(),
                                in_process_types.clone(),
                                polarity,
                            )
                        })
                        .collect();
                    (name.clone(), variant_types)
                })
                .collect::<Vec<_>>();
            AstType::Variant(variants)
        }
    }
}

fn coalesce_concrete_type(
    concrete_type: Rc<ConcreteType>,
    variable_states: Rc<RefCell<VariableStates>>,
    recursive_variables_vars: Rc<RefCell<MutMap<PolarVariable, String>>>,
    recursive_variables_types: Rc<RefCell<MutMap<Rc<ConcreteType>, String>>>,
    in_process_vars: ImSet<PolarVariable>,
    in_process_types: ImSet<Rc<ConcreteType>>,
    polarity: bool,
) -> AstType {
    // This might be a point of optimization in the future
    if in_process_types.contains(&concrete_type.clone()) {
        let name = recursive_variables_types
            .borrow_mut()
            .entry(concrete_type.into())
            .or_insert_with(|| unique_name())
            .clone();
        AstType::TypeVariable(name)
    } else {
        let in_process_types = in_process_types.update(concrete_type.clone());
        let ast_type = coalesce_concrete_type_after_recursion_check(
            concrete_type.clone(),
            variable_states,
            recursive_variables_vars,
            recursive_variables_types.clone(),
            in_process_vars,
            in_process_types,
            polarity,
        );
        match recursive_variables_types.borrow().get(&concrete_type) {
            Some(name) => AstType::Recursive(name.clone(), Rc::new(ast_type)),
            None => ast_type,
        }
    }
}

fn coalesce_simple_type_(
    simple_type: Rc<SimpleType>,
    variable_states: Rc<RefCell<VariableStates>>,
    recursive_variables_vars: Rc<RefCell<MutMap<PolarVariable, String>>>,
    recursive_variables_types: Rc<RefCell<MutMap<Rc<ConcreteType>, String>>>,
    in_process_vars: ImSet<PolarVariable>,
    in_process_types: ImSet<Rc<ConcreteType>>,
    polarity: bool,
) -> AstType {
    use SimpleType::*;
    match &*simple_type {
        Concrete(c) => coalesce_concrete_type(
            c.clone(),
            variable_states,
            recursive_variables_vars,
            recursive_variables_types,
            in_process_vars,
            in_process_types,
            polarity,
        ),
        Variable(v) => {
            let v = variable_states.borrow_mut().find(v);
            let polar_var = (v.clone(), polarity);
            if in_process_vars.contains(&polar_var) {
                let name = recursive_variables_vars
                    .borrow_mut()
                    .entry(polar_var)
                    .or_insert_with(|| unique_name())
                    .clone();
                AstType::TypeVariable(name)
            } else {
                let in_process = in_process_vars.update(polar_var.clone());
                let bounded_type = if polarity {
                    variable_states.borrow().lower_bound(&v)
                } else {
                    variable_states.borrow().upper_bound(&v)
                };
                let ast_type = coalesce_concrete_type(
                    bounded_type,
                    variable_states,
                    recursive_variables_vars.clone(),
                    recursive_variables_types.clone(),
                    in_process,
                    in_process_types,
                    polarity,
                );
                let this_var = AstType::TypeVariable(v.clone());
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
                match recursive_variables_vars.borrow().get(&polar_var) {
                    Some(name) => AstType::Recursive(name.clone(), Rc::new(ast_type)),
                    None => ast_type,
                }
            }
        }
    }
}

fn coalesce_simple_type(
    simple_type: Rc<SimpleType>,
    variable_states: Rc<RefCell<VariableStates>>,
) -> AstType {
    coalesce_simple_type_(
        simple_type,
        variable_states,
        Rc::new(RefCell::new(MutMap::new())),
        Rc::new(RefCell::new(MutMap::new())),
        ImSet::new(),
        ImSet::new(),
        true,
    )
}

fn get_inner_signature(
    signature: Signature<PolymorphicType>,
    mut path: VecDeque<VarName>,
) -> Signature<PolymorphicType> {
    match path.remove(0) {
        Some(name) => match signature.borrow().iter().find(|(name2, _)| name2 == &name) {
            Some((_, ItemType::Module(signature))) => get_inner_signature(signature.clone(), path),
            Some((_, ItemType::Let(_))) => {
                panic!("bug: should not be able to index into modules to get let statements")
            }
            Some((_, ItemType::QualifiedImport(_))) => {
                unimplemented!()
            }
            None => {
                panic!("tried to get module {:?}, but no module was found", path,)
            }
        },
        None => signature,
    }
}

fn new_signature<T>() -> Signature<T> {
    Rc::new(RefCell::new(vec![]))
}

fn typecheck_item(
    var_ctx: Rc<RefCell<ImMap<String, Rc<dyn MaybeQuantified>>>>,
    variable_states: Rc<RefCell<VariableStates>>,
    module_ctx: Signature<PolymorphicType>,
    path: &Vec<VarName>,
    item: &Item,
) {
    // The .clone() here might be removable
    let my_module = get_inner_signature(module_ctx.clone(), VecDeque::from(path.clone()));
    match item {
        Item::Let(Nonrecursive, name, expr) => {
            let expr_type = typecheck_expr(expr, &var_ctx.borrow(), variable_states);
            let ptype = PolymorphicType(expr_type);
            // Maybe this should just be dyn MaybeQuantified not Rc<dyn MaybeQuantified>
            var_ctx
                .borrow_mut()
                .insert(name.clone(), Rc::new(ptype.clone()));
            my_module
                .borrow_mut()
                .push((name.clone(), ItemType::Let(ptype)));
        }
        Item::Let(Recursive, name, expr) => {
            let name_type = variable_states.borrow_mut().fresh_var();
            var_ctx.borrow_mut().insert(name.clone(), name_type.clone());
            let expr_type = typecheck_expr(expr, &var_ctx.borrow(), variable_states.clone());
            constrain(expr_type.clone(), name_type, variable_states);
            let ptype = PolymorphicType(expr_type);
            var_ctx
                .borrow_mut()
                .insert(name.clone(), Rc::new(ptype.clone()));
            my_module
                .borrow_mut()
                .push((name.clone(), ItemType::Let(ptype)));
        }
        Item::QualifiedImport(import_path, name) => {
            my_module
                .borrow_mut()
                .push((name.clone(), ItemType::QualifiedImport(import_path.clone())));
        }
        Item::Module(name, items) => {
            let var_ctx = Rc::new(RefCell::new(var_ctx.borrow().clone()));
            my_module
                .borrow_mut()
                .push((name.clone(), ItemType::Module(new_signature())));
            let mut path = path.clone();
            path.push(name.clone());
            for item in items {
                typecheck_item(
                    var_ctx.clone(),
                    variable_states.clone(),
                    module_ctx.clone(),
                    &path,
                    item,
                );
            }
        }
    }
}

fn coalesce_signature(
    signature: Signature<PolymorphicType>,
    variable_states: Rc<RefCell<VariableStates>>,
) -> Signature<Rc<AstType>> {
    // This is probably a pretty slow function
    let signature = signature
        .borrow()
        .iter()
        .filter_map(|(name, item)| {
            match item {
                ItemType::Module(signature) => Some((
                    name.clone(),
                    ItemType::Module(coalesce_signature(
                        signature.clone(),
                        variable_states.clone(),
                    )),
                )),
                ItemType::Let(pexpr) => Some((
                    name.clone(),
                    ItemType::Let(Rc::new(coalesce_simple_type(
                        pexpr.0.clone(),
                        variable_states.clone(),
                    ))),
                )),
                ItemType::QualifiedImport(_) => None, // we don't need these in our ast signature
            }
        })
        .collect();
    Rc::new(RefCell::new(signature))
}

fn simplify_signature(signature: Signature<Rc<AstType>>) -> Signature<Rc<AstType>> {
    let signature = signature
        .borrow()
        .iter()
        .map(|(name, item)| {
            let item = match item {
                ItemType::Module(signature) => {
                    ItemType::Module(simplify_signature(signature.clone()))
                }
                ItemType::Let(ast_type) => ItemType::Let(Rc::new(ast_type.simplify())),
                ItemType::QualifiedImport(_) => {
                    panic!("bug: These should be filtered out in [coalesce_signature]")
                }
            };
            (name.clone(), item)
        })
        .collect();
    Rc::new(RefCell::new(signature))
}

pub fn typecheck_modules(items: Program) -> Signature<Rc<AstType>> {
    let var_ctx = Rc::new(RefCell::new(ImMap::new()));
    let variable_states = Rc::new(RefCell::new(VariableStates::new()));
    let module_ctx = new_signature();

    // Choice for the initial version: Only evaluate modules in a lexical, top-to-bottom, way.
    // This saves time and maybe is good enough since the editor can perform a topological sort when
    // writing out to disk.

    // The reason we evaluate all toplevel let statements later is just because the tests are easier that way.
    // At some point, I should refactor to have a function for getting a simple type from an expression instead of a Program
    // and then convert most of the tests to use that. TODO: Eventually, we should remove toplevel lets outside of modules.
    for item in items.iter() {
        typecheck_item(
            var_ctx.clone(),
            variable_states.clone(),
            module_ctx.clone(),
            &vec![],
            item,
        );
    }

    let signature = coalesce_signature(module_ctx, variable_states.clone());
    let signature = simplify_signature(signature);
    signature
}
