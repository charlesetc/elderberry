use im::OrdMap as ImMap;
use im::OrdSet as ImSet;
use std::cell::RefCell;
use std::collections::BTreeSet as MutSet;
use std::collections::HashMap as MutMap;
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Primitive {
    Int,
    Float,
    String,
    Bool,
    Unit,
}

type VarName = String;
type FieldName = String;
type VariantName = String;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ConcreteType {
    Top,
    Bottom,
    Primitive(Primitive),
    Function(Vec<Rc<SimpleType>>, Rc<SimpleType>),
    Record(ImMap<FieldName, Rc<SimpleType>>),
    Variant(ImMap<VariantName, Vec<Rc<SimpleType>>>),
}

// We have two refcells here so we can "unify" vars by replacing one
// This way future edits to the VariableState affect all occurrences of the variable.
// A different way to do this would be to have these variable names be indexes into a
// 'global' hashmap of "variable state". Either way, we needed another layer of indirection.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum SimpleType {
    Variable(VarName),
    Concrete(Rc<ConcreteType>),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum AstType {
    Top,
    Bottom,
    Function(Vec<AstType>, Rc<AstType>),
    Variant(Vec<(VariantName, Vec<AstType>)>),
    Record(Vec<(FieldName, AstType)>),
    Recursive(VarName, Rc<AstType>),
    TypeVariable(VarName),
    Primitive(Primitive),
    Union(Rc<AstType>, Rc<AstType>),
    Intersection(Rc<AstType>, Rc<AstType>),
}

impl AstType {
    pub fn simplify(self) -> AstType {
        let polar_vars = self.polar_vars();
        let polarity = true;
        self.drop_vars(&polar_vars, polarity)
    }

    fn polar_vars(&self) -> ImSet<VarName> {
        let positive = Rc::new(RefCell::new(MutSet::new()));
        let negative = Rc::new(RefCell::new(MutSet::new()));

        fn walk_polar_vars(
            ast_type: &AstType,
            positive: Rc<RefCell<MutSet<VarName>>>,
            negative: Rc<RefCell<MutSet<VarName>>>,
            polarity: bool,
        ) {
            use AstType::*;
            match ast_type {
                Top | Bottom | Primitive(_) => (),
                Function(args, ret) => {
                    for arg in args.iter() {
                        walk_polar_vars(arg, positive.clone(), negative.clone(), !polarity);
                    }
                    walk_polar_vars(ret, positive, negative, polarity);
                }
                Record(fields) => {
                    for (_, ast_type) in fields {
                        walk_polar_vars(ast_type, positive.clone(), negative.clone(), polarity);
                    }
                }
                Variant(variants) => {
                    for (_, ast_types) in variants {
                        for ast_type in ast_types {
                            walk_polar_vars(ast_type, positive.clone(), negative.clone(), polarity);
                        }
                    }
                }
                Recursive(var, expr) => {
                    positive.borrow_mut().insert(var.clone());
                    negative.borrow_mut().insert(var.clone());
                    walk_polar_vars(expr, positive, negative, polarity);
                }
                TypeVariable(var) => {
                    let set = if polarity { positive } else { negative };
                    set.borrow_mut().insert(var.clone());
                }
                Intersection(a, b) | Union(a, b) => {
                    walk_polar_vars(a, positive.clone(), negative.clone(), polarity);
                    walk_polar_vars(b, positive, negative, polarity);
                }
            }
        }

        walk_polar_vars(self, positive.clone(), negative.clone(), true);

        let polar_vars: ImSet<_> = positive
            .borrow()
            .symmetric_difference(&negative.borrow())
            .collect();
        polar_vars.clone()
    }

    fn drop_vars(&self, polar_vars: &ImSet<VarName>, polarity: bool) -> AstType {
        use AstType::*;
        match self {
            Top | Bottom | Primitive(_) => self.clone(),
            Function(args, ret) => Function(
                args.iter()
                    .map(|arg| arg.drop_vars(polar_vars, !polarity))
                    .collect(),
                Rc::new(ret.drop_vars(polar_vars, polarity)),
            ),
            Record(fields) => Record(
                fields
                    .iter()
                    .map(|(name, field)| (name.clone(), field.drop_vars(polar_vars, polarity)))
                    .collect(),
            ),
            Variant(variants) => Variant(
                variants
                    .iter()
                    .map(|(name, ast_types)| {
                        let ast_types = ast_types
                            .iter()
                            .map(|ast_type| ast_type.drop_vars(polar_vars, polarity))
                            .collect();
                        (name.clone(), ast_types)
                    })
                    .collect(),
            ),
            Recursive(var, ast_type) => Recursive(
                var.clone(),
                Rc::new(ast_type.drop_vars(polar_vars, polarity)),
            ),
            TypeVariable(name) => {
                if polar_vars.contains(name) {
                    if polarity {
                        Top
                    } else {
                        Bottom
                    }
                } else {
                    TypeVariable(name.clone())
                }
            }
            Union(a, b) => match (&**a, &**b) {
                (TypeVariable(a_name), TypeVariable(b_name))
                    if polar_vars.contains(a_name) && polar_vars.contains(b_name) =>
                {
                    unreachable!("bug (u): if this happens we need to re-think how to drop vars.")
                }
                (TypeVariable(name), _) if polar_vars.contains(name) => {
                    b.drop_vars(polar_vars, polarity)
                }
                (_, TypeVariable(name)) if polar_vars.contains(name) => {
                    a.drop_vars(polar_vars, polarity)
                }
                (_, _) => Union(
                    Rc::new(a.drop_vars(polar_vars, polarity)),
                    Rc::new(b.drop_vars(polar_vars, polarity)),
                ),
            },
            Intersection(a, b) => match (&**a, &**b) {
                (TypeVariable(a_name), TypeVariable(b_name))
                    if polar_vars.contains(a_name) && polar_vars.contains(b_name) =>
                {
                    unreachable!("bug (i): if this happens we need to re-think how to drop vars.")
                }
                (TypeVariable(name), _) if polar_vars.contains(name) => {
                    b.drop_vars(polar_vars, polarity)
                }
                (_, TypeVariable(name)) if polar_vars.contains(name) => {
                    a.drop_vars(polar_vars, polarity)
                }
                (_, _) => Intersection(
                    Rc::new(a.drop_vars(polar_vars, polarity)),
                    Rc::new(b.drop_vars(polar_vars, polarity)),
                ),
            },
        }
    }
}

pub trait MaybeQuantified {
    fn instantiate(self: Rc<Self>, variable_states: Rc<RefCell<VariableStates>>) -> Rc<SimpleType>;
}

impl MaybeQuantified for SimpleType {
    fn instantiate(
        self: Rc<Self>,
        _variable_states: Rc<RefCell<VariableStates>>,
    ) -> Rc<SimpleType> {
        self
    }
}

thread_local!(static UNIQUE_NAME_COUNTER : RefCell<usize> = RefCell::new(0));

pub fn unique_name() -> VarName {
    UNIQUE_NAME_COUNTER.with(|unique_name_counter| {
        let mut ret = String::from("a");
        ret.push_str(&unique_name_counter.borrow().clone().to_string());
        unique_name_counter.replace_with(|&mut i| i + 1usize);
        ret
    })
}

#[derive(Debug)]
pub struct VariableState {
    lower_bound: Rc<ConcreteType>,
    upper_bound: Rc<ConcreteType>,
}

impl VariableState {
    fn new() -> Self {
        VariableState {
            lower_bound: Rc::new(ConcreteType::Bottom),
            upper_bound: Rc::new(ConcreteType::Top),
        }
    }
}

#[derive(Debug)]
enum VarLink<T> {
    Value(T),
    Link(VarName),
}

// TODO: Make VarName a newtype here
#[derive(Debug)]
pub struct VariableStates(MutMap<VarName, VarLink<VariableState>>);

impl VariableStates {
    pub fn new() -> Self {
        VariableStates(MutMap::new())
    }

    pub fn link_to(&mut self, link_from: &VarName, link_to: &VarName) {
        let link_to = self.find(link_to);
        let link_from = self.find(link_from);
        if &link_from == &link_to {
            return;
        }
        self.0
            .insert(link_from.clone(), VarLink::Link(link_to.clone()));
    }

    pub fn fresh_var_name(&mut self) -> String {
        let name = unique_name();
        let varlink = VarLink::Value(VariableState::new());
        self.0.insert(name.clone(), varlink);
        name
    }

    pub fn fresh_var(&mut self) -> Rc<SimpleType> {
        Rc::new(SimpleType::Variable(self.fresh_var_name()))
    }

    pub fn upper_bound(&self, v: &VarName) -> Rc<ConcreteType> {
        self[v].upper_bound.clone()
    }

    pub fn lower_bound(&self, v: &VarName) -> Rc<ConcreteType> {
        self[v].lower_bound.clone()
    }

    pub fn set_lower_bound(&mut self, v: &VarName, value: Rc<ConcreteType>) {
        self.find_and_map(v, |state| state.lower_bound = value);
    }

    pub fn set_upper_bound(&mut self, v: &VarName, value: Rc<ConcreteType>) {
        self.find_and_map(v, |state| state.upper_bound = value);
    }

    fn find_with_references(
        &self,
        v: &VarName,
        references: MutSet<VarName>,
    ) -> (VarName, MutSet<VarName>) {
        match &self.0[v] {
            VarLink::Value(_) => (v.clone(), references),
            VarLink::Link(to_) => {
                let (found, mut references) = self.find_with_references(to_, references);
                references.insert(to_.clone());
                (found, references)
            }
        }
    }

    pub fn find(&mut self, v: &VarName) -> VarName {
        let (found, references) = self.find_with_references(v, MutSet::new());
        for reference in references {
            self.0.insert(v.clone(), VarLink::Link(reference));
        }
        found
    }

    fn find_and_map<F>(&mut self, v: &VarName, f: F)
    where
        F: FnOnce(&mut VariableState),
    {
        let found = self.find(v);
        match self.0.get_mut(&found) {
            Some(VarLink::Value(state)) => f(state),
            _ => panic!("bug: we just found it!"),
        }
    }
}
impl std::ops::Index<&str> for VariableStates {
    type Output = VariableState;
    fn index(&self, index: &str) -> &VariableState {
        match &self.0[index] {
            VarLink::Value(v) => v,
            VarLink::Link(name) => &self[name],
        }
    }
}
