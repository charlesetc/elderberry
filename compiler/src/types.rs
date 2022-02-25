use im::HashMap as ImMap;
use im::OrdSet as ImSet;
use std::cell::RefCell;
use std::collections::BTreeMap as MutMap;
use std::collections::BTreeSet as MutSet;
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Primitive {
    Int,
    Float,
    String,
    Bool,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct VariableState {
    pub lower_bounds: MutSet<Rc<SimpleType>>,
    pub upper_bounds: MutSet<Rc<SimpleType>>,
    unique_name: String,
}

type VarName = String;
type FieldName = String;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum SimpleType {
    Variable(Rc<RefCell<VariableState>>),
    Primitive(Primitive),
    Function(Vec<Rc<SimpleType>>, Rc<SimpleType>),
    Record(ImMap<FieldName, Rc<SimpleType>>),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum AstType {
    Top,
    Bottom,
    Union(Rc<AstType>, Rc<AstType>),
    Intersection(Rc<AstType>, Rc<AstType>),
    Function(Vec<AstType>, Rc<AstType>),
    Record(Vec<(FieldName, AstType)>),
    Recursive(VarName, Rc<AstType>),
    TypeVariable(VarName),
    Primitive(Primitive),
}

type PolarVariable = (VariableState, bool);

thread_local!(static UNIQUE_NAME_COUNTER : RefCell<usize> = RefCell::new(0));

impl VariableState {
    fn new() -> Self {
        let unique_name = UNIQUE_NAME_COUNTER.with(|unique_name_counter| {
            let mut ret = String::from("a");
            ret.push_str(&unique_name_counter.borrow().clone().to_string());
            unique_name_counter.replace_with(|&mut i| i + 1usize);
            ret
        });
        VariableState {
            lower_bounds: MutSet::new(),
            upper_bounds: MutSet::new(),
            unique_name: unique_name,
        }
    }
}

impl SimpleType {
    pub fn fresh_var() -> Rc<Self> {
        let state = RefCell::new(VariableState::new());
        Rc::new(SimpleType::Variable(Rc::new(state)))
    }

    fn coalesce_(
        simple_type: Rc<Self>,
        recursive_variables: Rc<RefCell<MutMap<PolarVariable, String>>>,
        polar: bool,
        in_process: ImSet<PolarVariable>,
    ) -> AstType {
        match &*simple_type {
            SimpleType::Primitive(p) => AstType::Primitive(p.clone()),
            SimpleType::Record(fields) => {
                let fields = fields
                    .iter()
                    .map(|(name, field_type)| {
                        (
                            name.clone(),
                            SimpleType::coalesce_(
                                field_type.clone(),
                                recursive_variables.clone(),
                                polar,
                                in_process.clone(),
                            ),
                        )
                    })
                    .collect::<Vec<_>>();
                AstType::Record(fields)
            }
            SimpleType::Function(args, ret) => {
                let args = args
                    .iter()
                    .map(|arg| {
                        SimpleType::coalesce_(
                            arg.clone(),
                            recursive_variables.clone(),
                            !polar,
                            in_process.clone(),
                        )
                    })
                    .collect::<Vec<_>>();
                let ret =
                    SimpleType::coalesce_(ret.clone(), recursive_variables, polar, in_process);
                AstType::Function(args, Rc::new(ret))
            }
            SimpleType::Variable(state) => {
                let polar_var = (state.borrow().clone(), polar);
                if in_process.contains(&polar_var) {
                    let name = recursive_variables
                        .borrow_mut()
                        .entry(polar_var)
                        .or_insert(state.borrow().unique_name.clone())
                        .clone();
                    AstType::TypeVariable(name)
                } else {
                    if polar {
                        let lower_bounds = &state.borrow().lower_bounds;
                        let lower_bound_types = lower_bounds
                            .iter()
                            .map(|lower_bound| {
                                let in_process = in_process.update(polar_var.clone());
                                SimpleType::coalesce_(
                                    lower_bound.clone(),
                                    recursive_variables.clone(),
                                    polar,
                                    in_process,
                                )
                            })
                            .collect::<Vec<_>>();
                        let ast_type = lower_bound_types
                            .iter()
                            .fold(AstType::TypeVariable(state.borrow().unique_name.clone()), |acc, a| {
                                AstType::Union(Rc::new(acc), Rc::new(a.clone()))
                            });
                        match recursive_variables.borrow().get(&polar_var) {
                            Some(name) => AstType::Recursive(name.clone(), Rc::new(ast_type)),
                            None => ast_type
                        }
                    } else {
                        let upper_bounds = &state.borrow().upper_bounds;
                        let upper_bound_types = upper_bounds
                            .iter()
                            .map(|upper_bound| {
                                let in_process = in_process.update(polar_var.clone());
                                SimpleType::coalesce_(
                                    upper_bound.clone(),
                                    recursive_variables.clone(),
                                    polar,
                                    in_process,
                                )
                            })
                            .collect::<Vec<_>>();
                        let ast_type = upper_bound_types
                            .iter()
                            .fold(AstType::TypeVariable(state.borrow().unique_name.clone()), |acc, a| {
                                AstType::Intersection(Rc::new(acc), Rc::new(a.clone()))
                            });
                        match recursive_variables.borrow().get(&polar_var) {
                            Some(name) => AstType::Recursive(name.clone(), Rc::new(ast_type)),
                            None => ast_type
                        }
                    }
                }
            }
        }
    }

    pub fn coalesce(simple_type: Rc<Self>) -> AstType {
        let recursive_variables = Rc::new(RefCell::new(MutMap::new()));
        SimpleType::coalesce_(simple_type, recursive_variables, false, ImSet::new())
    }
}
