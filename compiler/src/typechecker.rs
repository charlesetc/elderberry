use crate::ast::*;
use crate::types::{
    unique_name, AstType, ConcreteType, Fields, ItemType, MaybeQuantified, Primitive, Signature,
    SimpleType, VariableStates, VariantType,
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

fn greatest_lower_bound_for_fields(
    a_fields: &Fields,
    b_fields: &Fields,
    variable_states: Rc<RefCell<VariableStates>>,
    cache: ConstraintCache,
) -> Fields {
    let all_keys: ImSet<String> = a_fields.keys().chain(b_fields.keys()).collect();
    all_keys
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
        .collect()
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
        (Record(record_fields), Variant(variants)) | (Variant(variants), Record(record_fields)) => {
            let variants = variants
                .iter()
                .map(|(name, variant_type)| {
                    let VariantType {
                        args,
                        fields: variant_fields,
                    } = variant_type;
                    let fields = greatest_lower_bound_for_fields(
                        variant_fields,
                        record_fields,
                        variable_states.clone(),
                        cache.clone(),
                    );
                    (
                        name,
                        VariantType {
                            args: args.clone(),
                            fields,
                        },
                    )
                })
                .collect();
            Rc::new(Variant(variants))
        }
        (Variant(a_variants), Variant(b_variants)) => {
            let all_keys: ImSet<String> = a_variants.keys().chain(b_variants.keys()).collect();
            let variants = all_keys
                .into_iter()
                .map(|key| {
                    let value = match (a_variants.get(&key), b_variants.get(&key)) {
                        (None, None) => panic!("bug: at least one of these should have each key"),
                        (None, Some(args)) | (Some(args), None) => args.clone(),
                        (Some(VariantType { args: a_args, fields : a_fields }), Some(VariantType { args : b_args, fields : b_fields})) => {
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
                            let fields = greatest_lower_bound_for_fields(a_fields, b_fields, variable_states.clone(), cache.clone());
                            VariantType { args: args , fields: fields }
                        }
                    };
                    (key, value)
                })
                .collect();
            Rc::new(Variant(variants))
        }
        (Record(a_fields), Record(b_fields)) => {
            let fields =
                greatest_lower_bound_for_fields(a_fields, b_fields, variable_states, cache);
            Rc::new(Record(fields))
        }
        _ => panic!(
            "type error: cannot unify greatest lower bounds: {:?} and {:?}",
            a, b
        ),
    }
}

fn least_upper_bound_for_fields(
    a_fields: &Fields,
    b_fields: &Fields,
    variable_states: Rc<RefCell<VariableStates>>,
    cache: ConstraintCache,
) -> Fields {
    let all_keys: ImSet<String> = a_fields.keys().chain(b_fields.keys()).collect();
    all_keys
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
        .collect()
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
                    (
                        Some(VariantType {
                            args: a_args,
                            fields: a_fields,
                        }),
                        Some(VariantType {
                            args: b_args,
                            fields: b_fields,
                        }),
                    ) => {
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
                        let fields = least_upper_bound_for_fields(
                            a_fields,
                            b_fields,
                            variable_states.clone(),
                            cache.clone(),
                        );
                        let variant_type = VariantType { args, fields };
                        Some((key, variant_type))
                    }
                })
                .collect();
            Rc::new(Variant(variants))
        }
        (Record(a_fields), Record(b_fields)) => {
            let fields = least_upper_bound_for_fields(a_fields, b_fields, variable_states, cache);
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

fn constrain_fields(
    subfields: &Fields,
    superfields: &Fields,
    variable_states: Rc<RefCell<VariableStates>>,
    cache: ConstraintCache,
) {
    for (field, supervalue) in superfields.iter() {
        match subfields.get(field) {
            Some(subvalue) => constrain_(
                subvalue.clone(),
                supervalue.clone(),
                variable_states.clone(),
                cache.clone(),
            ),
            None => type_error(format!("missing field {}", field)),
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
        (Record(subfields), Record(superfields)) => {
            constrain_fields(subfields, superfields, variable_states, cache)
        }
        (Variant(subvariants), Record(superfields)) => {
            for (
                _name,
                VariantType {
                    args: _,
                    fields: subfields,
                },
            ) in subvariants.iter()
            {
                println!("constraining here! {:?} {:?}", subvariants, superfields);
                constrain_fields(
                    subfields,
                    superfields,
                    variable_states.clone(),
                    cache.clone(),
                );
            }
        }
        (Variant(subvariants), Variant(supervariants)) => {
            for (
                name,
                VariantType {
                    args: subargs,
                    fields: subfields,
                },
            ) in subvariants.iter()
            {
                match supervariants.get(name) {
                    // Similar to function definition
                    Some(VariantType {
                        args: superargs,
                        fields: superfields,
                    }) => {
                        if subargs.len() != superargs.len() {
                            type_error(format!(
                                "matched against variant {} with {} arguments, but it only takes {}",
                                name,
                                subargs.len(),
                                superargs.len()
                            ));
                        }
                        for (subarg, superarg) in subargs.iter().zip(superargs.iter()) {
                            constrain_(
                                subarg.clone(),
                                superarg.clone(),
                                variable_states.clone(),
                                cache.clone(),
                            );
                        }
                        constrain_fields(
                            subfields,
                            superfields,
                            variable_states.clone(),
                            cache.clone(),
                        );
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

fn new_constraint_cache() -> ConstraintCache {
    Rc::new(RefCell::new(MutSet::new()))
}

fn constrain(
    subtype: Rc<SimpleType>,
    supertype: Rc<SimpleType>,
    variable_states: Rc<RefCell<VariableStates>>,
) {
    constrain_(subtype, supertype, variable_states, new_constraint_cache())
}

fn primitive_simple_type(p: Primitive) -> Rc<SimpleType> {
    Rc::new(SimpleType::Concrete(Rc::new(ConcreteType::Primitive(p))))
}

// global for now - should be module-scoped in the future.
//
//     use MyModule.Some;
//
// or:
//
//     use MyModule.Option // a type alias
//
// a mapping from Variant Name to Type Variable.
//
// TODO: Get more descriptive types for these parameters

struct VariantState {
    var: VarName,
    fields: Fields,
}

impl VariantState {
    fn new(vs: Rc<RefCell<VariableStates>>) -> Self {
        let var = vs.borrow_mut().fresh_var_name();
        VariantState {
            var,
            fields: ImMap::new(),
        }
    }
}

type VariantContext = MutMap<VarName, VariantState>;

fn typecheck_statements(
    statements: &Statements,
    var_ctx: &ImMap<String, Rc<dyn MaybeQuantified>>,
    variable_states: Rc<RefCell<VariableStates>>,
    module_ctx: Signature<Rc<PolymorphicType>>,
    variant_ctx: &VariantContext,
    module_path: &Vec<VarName>,
) -> Rc<SimpleType> {
    use Statements::*;
    match statements {
        Empty => primitive_simple_type(Primitive::Unit),
        Sequence(expr, rest) => {
            let expr_type = typecheck_expr(
                expr,
                var_ctx,
                variable_states.clone(),
                module_ctx.clone(),
                variant_ctx,
                module_path,
            );
            match &**rest {
                Empty => expr_type,
                _ => typecheck_statements(
                    rest,
                    var_ctx,
                    variable_states,
                    module_ctx,
                    variant_ctx,
                    module_path,
                ),
            }
        }
        Let(Nonrecursive, name, expr, rest) => {
            let expr_type = typecheck_expr(
                expr,
                var_ctx,
                variable_states.clone(),
                module_ctx.clone(),
                variant_ctx,
                module_path,
            );
            let var_ctx = var_ctx.update(name.clone(), expr_type);
            typecheck_statements(
                rest,
                &var_ctx,
                variable_states,
                module_ctx,
                variant_ctx,
                module_path,
            )
        }
        Let(Recursive, name, expr, rest) => {
            let name_type = variable_states.borrow_mut().fresh_var();
            let var_ctx = var_ctx.update(name.clone(), name_type.clone());
            constrain(
                typecheck_expr(
                    expr,
                    &var_ctx,
                    variable_states.clone(),
                    module_ctx.clone(),
                    variant_ctx,
                    module_path,
                ),
                name_type,
                variable_states.clone(),
            );
            typecheck_statements(
                rest,
                &var_ctx,
                variable_states,
                module_ctx,
                variant_ctx,
                module_path,
            )
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
    variant_ctx: &VariantContext,
    variable_states: Rc<RefCell<VariableStates>>,
) -> (Rc<SimpleType>, ImMap<String, Rc<dyn MaybeQuantified>>) {
    use Pattern::*;
    match pat {
        Constant(c) => (typecheck_constant(c), var_ctx.clone()),
        Variant(name, arg_patterns) => {
            let mut var_ctx = var_ctx.clone();
            let arg_types = arg_patterns
                .iter()
                .map(|arg_pattern| {
                    let (arg_type, new_var_ctx) = typecheck_pattern(
                        arg_pattern,
                        &var_ctx,
                        variant_ctx,
                        variable_states.clone(),
                    );
                    var_ctx = new_var_ctx;
                    arg_type
                })
                .collect();

            let fields = match variant_ctx.get(name) {
                Some(variant_state) => variant_state.fields.clone(),
                None => ImMap::new(),
            };
            let variant_type = VariantType {
                args: arg_types,
                fields,
            };
            (
                Rc::new(SimpleType::Concrete(Rc::new(ConcreteType::Variant(
                    im::ordmap! {name.clone() => variant_type},
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
                        typecheck_pattern(pattern, &var_ctx, variant_ctx, variable_states.clone());
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

enum IndexResult {
    Done(Signature<Rc<PolymorphicType>>),
    Alias(Vec<VarName>),
    NotFound,
}

fn index_into_item(
    item: ItemType<Rc<PolymorphicType>>,
    lookup_path: &mut VecDeque<VarName>,
) -> IndexResult {
    use IndexResult::*;

    match item {
        ItemType::Let(_) => {
            panic!("bug: Module paths shouldn't be able to reference let statements!")
        }
        ItemType::QualifiedImport(path) => Alias(path),
        ItemType::Module(signature) => match lookup_path.pop_front() {
            None => Done(signature),
            Some(lookup_name) => {
                for (item_name, item) in signature.borrow().iter() {
                    if item_name == &lookup_name {
                        return index_into_item(item.clone(), lookup_path);
                    }
                }
                NotFound
            }
        },
    }
}

#[derive(Debug)]
struct ModuleSeeker {
    current_path: VecDeque<VarName>,
    lookup_path: VecDeque<VarName>,
    toplevel_module: Signature<Rc<PolymorphicType>>,
}

impl ModuleSeeker {
    fn seek(&mut self) -> Signature<Rc<PolymorphicType>> {
        use IndexResult::*;
        let current_module = match index_into_item(
            ItemType::Module(self.toplevel_module.clone()),
            &mut self.current_path.clone(),
        ) {
            Done(item) => item,
            Alias(_) | NotFound => {
                panic!("bug: the current path should only ever point to a module")
            }
        };
        let mut new_lookup_path = self.lookup_path.clone();
        match index_into_item(ItemType::Module(current_module), &mut new_lookup_path) {
            Done(signature) => signature,
            NotFound => match self.current_path.pop_back() {
                None => panic!(
                    "tried to get module {:?}, but no module was found",
                    self.lookup_path
                ),
                Some(_) => self.seek(),
            },
            Alias(path) => {
                // add the path in place of the name of the alias - this has already been removed by [index_into_item]
                for name in path.into_iter().rev() {
                    new_lookup_path.push_front(name);
                }
                self.lookup_path = new_lookup_path;
                self.current_path.pop_back();
                self.seek()
            }
        }
    }
}

fn get_signature_at_path(
    toplevel_module: Signature<Rc<PolymorphicType>>,
    current_path: VecDeque<VarName>,
    lookup_path: VecDeque<VarName>,
) -> Signature<Rc<PolymorphicType>> {
    let mut seeker = ModuleSeeker {
        toplevel_module,
        current_path,
        lookup_path,
    };
    seeker.seek()
}

fn get_value_in_signature(
    current_module: Signature<Rc<PolymorphicType>>,
    name: &VarName,
) -> Rc<PolymorphicType> {
    for (item_name, item) in current_module.borrow().iter() {
        if name == item_name {
            match item {
                ItemType::Let(ptype) => return ptype.clone(),
                ItemType::QualifiedImport(_) | ItemType::Module(_) => {
                    panic!("bug: module names and variable names should be separate")
                }
            }
        }
    }
    panic!("module doesn't have item {}", name)
}

fn typecheck_expr(
    expr: &Expr,
    var_ctx: &ImMap<String, Rc<dyn MaybeQuantified>>,
    variable_states: Rc<RefCell<VariableStates>>,
    module_ctx: Signature<Rc<PolymorphicType>>,
    variant_ctx: &VariantContext,
    module_path: &Vec<VarName>,
) -> Rc<SimpleType> {
    use Expr::*;
    let simple_type = match expr {
        Constant(c) => typecheck_constant(c),
        Var(None, name) => match var_ctx.get(name) {
            Some(maybe_quantified) => maybe_quantified.clone().instantiate(variable_states),
            None => type_error(format!("variable \"{}\" not found", name)),
        },
        Var(Some(lookup_path), name) => {
            let signature_at_path = get_signature_at_path(
                module_ctx,
                VecDeque::from(module_path.clone()),
                VecDeque::from(lookup_path.clone()),
            );
            get_value_in_signature(signature_at_path, name).instantiate(variable_states)
        }
        JsVar(_name) => {
            let var = variable_states.borrow_mut().fresh_var();
            var
        }
        Lambda(args, expr) => {
            let (arg_types, var_ctx) = {
                let mut arg_types = vec![];
                let var_ctx = args.iter().fold(var_ctx.clone(), |var_ctx, arg| {
                    let (arg_type, var_ctx) =
                        typecheck_pattern(arg, &var_ctx, variant_ctx, variable_states.clone());
                    arg_types.push(arg_type);
                    var_ctx
                });
                (arg_types, var_ctx)
            };
            Rc::new(SimpleType::Concrete(Rc::new(ConcreteType::Function(
                arg_types,
                typecheck_expr(
                    expr,
                    &var_ctx,
                    variable_states,
                    module_ctx,
                    variant_ctx,
                    module_path,
                ),
            ))))
        }
        Apply(f, args) => {
            let return_type = variable_states.borrow_mut().fresh_var();
            let arg_types = args
                .iter()
                .map(|arg| {
                    typecheck_expr(
                        arg,
                        var_ctx,
                        variable_states.clone(),
                        module_ctx.clone(),
                        variant_ctx,
                        module_path,
                    )
                })
                .collect::<Vec<_>>();
            let f_type = Rc::new(SimpleType::Concrete(Rc::new(ConcreteType::Function(
                arg_types,
                return_type.clone(),
            ))));
            constrain(
                typecheck_expr(
                    f,
                    var_ctx,
                    variable_states.clone(),
                    module_ctx,
                    variant_ctx,
                    module_path,
                ),
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
                        typecheck_expr(
                            expr,
                            &var_ctx,
                            variable_states.clone(),
                            module_ctx.clone(),
                            variant_ctx,
                            module_path,
                        ),
                    )
                })
                .collect::<ImMap<_, _>>(),
        )))),
        FieldAccess(expr, name) => {
            let return_type = variable_states.borrow_mut().fresh_var();
            constrain(
                typecheck_expr(
                    expr,
                    var_ctx,
                    variable_states.clone(),
                    module_ctx,
                    variant_ctx,
                    module_path,
                ),
                Rc::new(SimpleType::Concrete(Rc::new(ConcreteType::Record(
                    im::ordmap! {name.clone() => return_type.clone()},
                )))),
                variable_states,
            );
            return_type
        }
        Block(statements) => typecheck_statements(
            statements,
            &var_ctx,
            variable_states,
            module_ctx,
            variant_ctx,
            module_path,
        ),
        If(condition, true_branch, false_branch) => {
            let condition_type = typecheck_expr(
                condition,
                &var_ctx,
                variable_states.clone(),
                module_ctx.clone(),
                variant_ctx,
                module_path,
            );
            constrain(
                condition_type,
                primitive_simple_type(Primitive::Bool),
                variable_states.clone(),
            );
            let return_type = variable_states.borrow_mut().fresh_var();
            let true_branch_type = typecheck_expr(
                true_branch,
                &var_ctx,
                variable_states.clone(),
                module_ctx.clone(),
                variant_ctx,
                module_path,
            );
            let false_branch_type = match false_branch {
                Some(false_branch) => typecheck_expr(
                    false_branch,
                    &var_ctx,
                    variable_states.clone(),
                    module_ctx,
                    variant_ctx,
                    module_path,
                ),
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
            let expr_type = typecheck_expr(
                expr,
                var_ctx,
                variable_states.clone(),
                module_ctx.clone(),
                variant_ctx,
                module_path,
            );
            for (pattern, branch_expr) in branches.iter() {
                let (pattern_type, var_ctx) =
                    typecheck_pattern(pattern, var_ctx, variant_ctx, variable_states.clone());
                constrain(expr_type.clone(), pattern_type, variable_states.clone());
                let branch_type = typecheck_expr(
                    branch_expr,
                    &var_ctx,
                    variable_states.clone(),
                    module_ctx.clone(),
                    variant_ctx,
                    module_path,
                );
                constrain(branch_type, return_type.clone(), variable_states.clone());
            }
            return_type
        }
        Variant(name, args) => {
            let arg_types = args
                .iter()
                .map(|arg| {
                    typecheck_expr(
                        arg,
                        var_ctx,
                        variable_states.clone(),
                        module_ctx.clone(),
                        variant_ctx,
                        module_path,
                    )
                })
                .collect();
            let variant_type = match variant_ctx.get(name) {
                Some(variant_state) => {
                    let variant_type = VariantType {
                        args: arg_types,
                        fields: variant_state.fields.clone(),
                    };
                    let variant_simple_type = Rc::new(SimpleType::Concrete(Rc::new(
                        ConcreteType::Variant(im::ordmap! {name.clone() => variant_type.clone()}),
                    )));
                    // TODO it's unclear to me if this is correct
                    constrain(
                        variant_simple_type,
                        Rc::new(SimpleType::Variable(variant_state.var.clone())),
                        variable_states,
                    );
                    variant_type
                }
                None => VariantType {
                    args: arg_types,
                    fields: ImMap::new(),
                },
            };
            Rc::new(SimpleType::Concrete(Rc::new(ConcreteType::Variant(
                im::ordmap! {name.clone() => variant_type},
            ))))
        }
    };
    println!("TYPECHECK EXPR {:?}", expr);
    println!("TYPECHECK GOT  {:?}", simple_type);
    simple_type
}

fn freshen_fields(
    fields: &Fields,
    variable_states: Rc<RefCell<VariableStates>>,
    qvar_context: Rc<RefCell<MutMap<VarName, VarName>>>,
) -> Fields {
    fields
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
        .collect()
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
                .map(|(name, VariantType { args, fields })| {
                    let args: Vec<_> = args
                        .iter()
                        .map(|simple_type| {
                            freshen_simple_type(
                                simple_type.clone(),
                                variable_states.clone(),
                                qvar_context.clone(),
                            )
                        })
                        .collect();
                    let fields =
                        freshen_fields(fields, variable_states.clone(), qvar_context.clone());
                    let variant_type = VariantType { args, fields };
                    (name.clone(), variant_type)
                })
                .collect();
            Rc::new(Variant(variants))
        }
        Record(ref fields) => {
            let fields = freshen_fields(fields, variable_states, qvar_context);
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
                .map(
                    |(
                        name,
                        VariantType {
                            args: arg_types,
                            // We're not including the fields into the user-facing AstType. Maybe we could in some UI in the future.
                            fields: _,
                        },
                    )| {
                        let arg_types = arg_types
                            .iter()
                            .map(|arg| {
                                coalesce_simple_type_(
                                    arg.clone(),
                                    variable_states.clone(),
                                    recursive_variables_vars.clone(),
                                    recursive_variables_types.clone(),
                                    in_process_vars.clone(),
                                    in_process_types.clone(),
                                    polarity,
                                )
                            })
                            .collect();
                        (name.clone(), arg_types)
                    },
                )
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

fn new_signature<T>() -> Signature<Rc<T>> {
    Rc::new(RefCell::new(vec![]))
}

// TODO: bundle all these contexts into a single type.
fn typecheck_item(
    var_ctx: Rc<RefCell<ImMap<String, Rc<dyn MaybeQuantified>>>>,
    variable_states: Rc<RefCell<VariableStates>>,
    module_ctx: Signature<Rc<PolymorphicType>>,
    variant_ctx: &VariantContext,
    path: &Vec<VarName>,
    item: &Item,
) {
    use IndexResult::*;
    // The .clone() here might be removable
    let my_module = match index_into_item(
        ItemType::Module(module_ctx.clone()),
        &mut VecDeque::from(path.clone()),
    ) {
        Done(signature) => signature,
        Alias(_) | NotFound => {
            panic!("bug: path should always point to modules")
        }
    };
    match item {
        Item::Let(Nonrecursive, name, expr) => {
            let expr_type = typecheck_expr(
                expr,
                &var_ctx.borrow(),
                variable_states,
                module_ctx,
                variant_ctx,
                path,
            );
            let ptype = Rc::new(PolymorphicType(expr_type));
            // Maybe this should just be dyn MaybeQuantified not Rc<dyn MaybeQuantified>
            var_ctx.borrow_mut().insert(name.clone(), ptype.clone());
            my_module
                .borrow_mut()
                .push((name.clone(), ItemType::Let(ptype)));
        }
        Item::Let(Recursive, name, expr) => {
            let name_type = variable_states.borrow_mut().fresh_var();
            var_ctx.borrow_mut().insert(name.clone(), name_type.clone());
            let expr_type = typecheck_expr(
                expr,
                &var_ctx.borrow(),
                variable_states.clone(),
                module_ctx,
                variant_ctx,
                path,
            );
            constrain(expr_type.clone(), name_type, variable_states);
            let ptype = Rc::new(PolymorphicType(expr_type));
            var_ctx.borrow_mut().insert(name.clone(), ptype.clone());
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
                    variant_ctx,
                    &path,
                    item,
                );
            }
        }
        Item::Method(method_name, receiver, args, expr) => {
            let var_ctx = var_ctx.borrow().clone();
            let (receiver_type, var_ctx) =
                typecheck_pattern(receiver, &var_ctx, variant_ctx, variable_states.clone());
            let (arg_types, var_ctx) = {
                let mut arg_types = vec![];
                let var_ctx = args.iter().fold(var_ctx, |var_ctx, arg| {
                    let (arg_type, var_ctx) =
                        typecheck_pattern(arg, &var_ctx, variant_ctx, variable_states.clone());
                    arg_types.push(arg_type);
                    var_ctx
                });
                (arg_types, var_ctx)
            };
            let return_type = typecheck_expr(
                expr,
                &var_ctx,
                variable_states.clone(),
                module_ctx,
                variant_ctx,
                &path,
            );
            let function_type = Rc::new(SimpleType::Concrete(Rc::new(ConcreteType::Function(
                arg_types,
                return_type,
            ))));
            let method_access_type = Rc::new(SimpleType::Concrete(Rc::new(ConcreteType::Record(
                im::ordmap! {method_name.clone() => function_type},
            ))));
            // TODO: Decide if we should do this instead of the 2nd constraint down below:
            //
            // constrain(
            //     receiver_type.clone(),
            //     method_access_type,
            //     variable_states.clone(),
            // );
            match &*receiver_type {
                SimpleType::Concrete(concrete) => {
                    match &**concrete {
                        ConcreteType::Variant(variants) => {
                            for (variant_name, receiver_variant_type) in variants {
                                let variant_state = variant_ctx
                                    .get(variant_name)
                                    .expect("we're defining a method on it, so it should be scanned ahead of time and put in the varaints list");
                                // I might be able to constrain each variant_state.var against the whole set of variants in the pattern above.
                                let variant_var = Rc::new(SimpleType::Variable(variant_state.var.clone()));
                                constrain(
                                    variant_var.clone(),
                                    Rc::new(SimpleType::Concrete(Rc::new(ConcreteType::Variant(im::ordmap!{ variant_name.clone() => receiver_variant_type.clone() })))),
                                    variable_states.clone(),
                                );
                                constrain(
                                    variant_var,
                                    method_access_type.clone(),
                                    variable_states.clone(),
                                );
                            }
                        }
                        _ => panic!("bug: methods must be defined on variants, and we should have asserted that in [scan_for_variant_context]"),
                    }
                }
                _ => panic!("methods must be defined on variants"),
            }
            // TODO: have to keep track of whether I'm within a method
            // definition when evaluating an expression so that we can
            // generalize when we're out of one.
        }
    }
}

fn coalesce_signature(
    signature: Signature<Rc<PolymorphicType>>,
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

fn scan_for_variant_context(
    item: &Item,
    variant_ctx: &mut VariantContext,
    variable_states: Rc<RefCell<VariableStates>>,
) {
    match item {
        Item::QualifiedImport(_, _) | Item::Let(_, _, _) => (),
        Item::Module(_, items) => {
            for item in items.iter() {
                scan_for_variant_context(item, variant_ctx, variable_states.clone())
            }
        }
        Item::Method(method_name, receiver, _args, _body) => {
            let var_ctx = ImMap::new();
            let (receiver_pattern_type, _var_ctx) =
                typecheck_pattern(receiver, &var_ctx, variant_ctx, variable_states.clone());
            match &*receiver_pattern_type {
                SimpleType::Concrete(concrete) => match &**concrete {
                    ConcreteType::Variant(variant_types) => {
                        for (variant_name, _variant_type) in variant_types {
                            let variant_state = variant_ctx
                                .entry(variant_name.clone())
                                .or_insert_with(|| VariantState::new(variable_states.clone()));
                            let method_var = variable_states.borrow_mut().fresh_var();
                            if variant_state.fields.contains_key(method_name) {
                                panic!(
                                    "method {} is already defined on variant {}",
                                    method_name, variant_name
                                )
                            }
                            // Is this actually mutating? Why is it allowed if variant_state is not mutable?
                            // I guess we have ownership of variant_state so we could borrow it as mutable if we want
                            // to. Weird.
                            variant_state.fields.insert(method_name.clone(), method_var);
                        }
                    }
                    _ => panic!("methods should be defined on variants"),
                },
                _ => panic!("methods should be defined on variants"),
            }
        }
    }
}

pub fn typecheck_modules(items: Program) -> Signature<Rc<AstType>> {
    let var_ctx = Rc::new(RefCell::new(ImMap::new()));
    let variable_states = Rc::new(RefCell::new(VariableStates::new()));
    let module_ctx = new_signature();
    let mut variant_ctx = MutMap::new();
    for item in items.iter() {
        scan_for_variant_context(&item, &mut variant_ctx, variable_states.clone());
    }
    let variant_ctx = variant_ctx; // remove mutability

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
            &variant_ctx,
            &vec![],
            item,
        );
    }

    let signature = coalesce_signature(module_ctx, variable_states.clone());
    let signature = simplify_signature(signature);
    signature
}
