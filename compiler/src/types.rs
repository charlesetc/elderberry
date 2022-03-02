use im::HashMap as ImMap;
use im::OrdSet as ImSet;
use std::cell::RefCell;
use std::collections::BTreeSet as MutSet;
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ConcreteType {
    Top,
    Bottom,
    Primitive(Primitive),
    Function(Vec<Rc<SimpleType>>, Rc<SimpleType>),
    Record(ImMap<FieldName, Rc<SimpleType>>),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct VariableState {
    pub lower_bound: Rc<ConcreteType>,
    pub upper_bound: Rc<ConcreteType>,
    pub unique_name: VarName,
}

pub type DoubleRef<T> = Rc<RefCell<T>>;

pub fn new_double_ref<T>(t: T) -> DoubleRef<T> {
    Rc::new(RefCell::new(t))
}

// We have two refcells here so we can "unify" vars by replacing one
// This way future edits to the VariableState affect all occurrences of the variable.
// A different way to do this would be to have these variable names be indexes into a
// 'global' hashmap of "variable state". Either way, we needed another layer of indirection.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum SimpleType {
    Variable(DoubleRef<VariableState>),
    Concrete(Rc<ConcreteType>),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum AstType {
    Top,
    Bottom,
    Function(Vec<AstType>, Rc<AstType>),
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
                Recursive(var, expr) => {
                    positive.borrow_mut().insert(var.clone());
                    negative.borrow_mut().insert(var.clone());
                    walk_polar_vars(expr, positive, negative, polarity);
                }
                TypeVariable(var) => {
                    let set = if polarity { positive } else { negative };
                    set.borrow_mut().insert(var.clone());
                }
                Intersection(a,b) | Union(a, b) => {
                    walk_polar_vars(a, positive.clone(), negative.clone(), polarity);
                    walk_polar_vars(b, positive, negative, polarity);
                }
            }
        }

        walk_polar_vars(self, positive.clone(), negative.clone(), true);
        
        let polar_vars : ImSet<_> = positive.borrow().symmetric_difference(&negative.borrow()).collect();
        polar_vars.clone()
    }

    fn drop_vars(&self, polar_vars: &ImSet<VarName>, polarity : bool) -> AstType {
        use AstType::*;
        match self {
            Top | Bottom | Primitive(_) => self.clone(),
            Function(args, ret) => Function(
                args.iter().map(|arg| arg.drop_vars(polar_vars, !polarity)).collect(),
                Rc::new(ret.drop_vars(polar_vars, polarity)),
            ),
            Record(fields) => Record(
                fields
                    .iter()
                    .map(|(name, arg)| (name.clone(), arg.drop_vars(polar_vars, polarity)))
                    .collect(),
            ),
            Recursive(var, ast_type) => {
                Recursive(var.clone(), Rc::new(ast_type.drop_vars(polar_vars, polarity)))
            }
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
                    unimplemented!("bug (u): if this happens we need to re-think how to drop vars.")
                }
                (TypeVariable(name), _) if polar_vars.contains(name) => b.drop_vars(polar_vars, polarity),
                (_, TypeVariable(name)) if polar_vars.contains(name) => a.drop_vars(polar_vars, polarity),
                (_, _) => Union(
                    Rc::new(a.drop_vars(polar_vars, polarity)),
                    Rc::new(b.drop_vars(polar_vars, polarity)),
                ),
            },
            Intersection(a, b) => match (&**a, &**b) {
                (TypeVariable(a_name), TypeVariable(b_name))
                    if polar_vars.contains(a_name) && polar_vars.contains(b_name) =>
                {
                    unimplemented!("bug (i): if this happens we need to re-think how to drop vars.")
                }
                (TypeVariable(name), _) if polar_vars.contains(name) => b.drop_vars(polar_vars, polarity),
                (_, TypeVariable(name)) if polar_vars.contains(name) => a.drop_vars(polar_vars, polarity),
                (_, _) => Intersection(
                    Rc::new(a.drop_vars(polar_vars, polarity)),
                    Rc::new(b.drop_vars(polar_vars, polarity)),
                ),
            },
        }
    }
}

pub trait MaybeQuantified {
    fn instantiate(self: Rc<Self>) -> Rc<SimpleType>;
}

impl MaybeQuantified for SimpleType {
    fn instantiate(self: Rc<Self>) -> Rc<SimpleType> {
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

impl VariableState {
    fn new() -> Self {
        VariableState {
            lower_bound: Rc::new(ConcreteType::Bottom),
            upper_bound: Rc::new(ConcreteType::Top),
            unique_name: unique_name(),
        }
    }
}

impl SimpleType {
    pub fn fresh_var() -> Rc<Self> {
        let state = new_double_ref(VariableState::new());
        Rc::new(SimpleType::Variable(state))
    }
}
