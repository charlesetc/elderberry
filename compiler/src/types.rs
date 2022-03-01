use im::HashMap as ImMap;
use std::cell::RefCell;
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
    // Union(Rc<AstType>, Rc<AstType>),
    // Intersection(Rc<AstType>, Rc<AstType>),
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