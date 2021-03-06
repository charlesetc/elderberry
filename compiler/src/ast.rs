use std::collections::HashSet;

#[derive(Debug, Clone)]
pub enum Constant {
    Int(i64),
    Float(f64),
    String(String),
    Bool(bool),
    Unit,
}

// Used for module names, variable names, and type variable names
pub type VarName = String;
pub type FieldName = String;
pub type VariantName = String;

#[derive(Debug, Clone)]
pub enum Pattern {
    Constant(Constant),
    Variant(VariantName, Vec<Pattern>),
    Record(Vec<(FieldName, Pattern)>),
    Var(VarName),
    Wildcard,
}

#[derive(Debug, Clone)]
pub enum RecFlag {
    Recursive,
    Nonrecursive,
}

#[derive(Debug, Clone)]
pub enum Statements {
    Empty,
    Sequence(Box<Expr>, Box<Statements>),
    Let(RecFlag, VarName, Box<Expr>, Box<Statements>),
}

type ModulePath = Vec<String>;

#[derive(Debug, Clone)]
pub enum Expr {
    Constant(Constant),
    Record(Vec<(FieldName, Expr)>),
    FieldAccess(Box<Expr>, FieldName),
    Variant(VariantName, Vec<Expr>),
    Match(Box<Expr>, Vec<(Pattern, Expr)>),
    Lambda(Vec<Pattern>, Box<Expr>),
    Apply(Box<Expr>, Vec<Expr>),
    Block(Statements),
    Var(Option<ModulePath>, VarName),
    JsVar(VarName),
    If(Box<Expr>, Box<Expr>, Option<Box<Expr>>),
}

#[derive(Debug, Clone)]
pub enum Item {
    Module(VarName, Vec<Item>),
    QualifiedImport(Vec<VarName>, VarName),
    Let(RecFlag, VarName, Expr),
    Method(VarName, Pattern, Vec<Pattern>, Expr),
}

impl Item {
    pub fn name_for_generator(&self) -> Option<VarName> {
        match self {
            Item::Module(name, _) => Some(name.clone()),
            Item::QualifiedImport(_, name) => Some(name.clone()),
            Item::Let(_, name, _) => Some(name.clone()),
            Item::Method(_, _, _, _) => None,
        }
    }
}

impl Pattern {
    fn captures_in_order_<'a>(
        self: &'a Self,
        mut out_vec: Vec<&'a VarName>,
        mut out_set: HashSet<&'a VarName>,
    ) -> (Vec<&'a VarName>, HashSet<&'a VarName>) {
        let res = match self {
            Pattern::Variant(_, pats) => pats
                .into_iter()
                .fold((out_vec, out_set), |(out_vec, out_set), pat| {
                    pat.captures_in_order_(out_vec, out_set)
                }),
            Pattern::Record(fields) => fields
                .into_iter()
                .fold((out_vec, out_set), |(out_vec, out_set), (_, pat)| {
                    pat.captures_in_order_(out_vec, out_set)
                }),
            Pattern::Var(name) => {
                if out_set.contains(name) {
                    panic!("error: cannot bind the same name twice in a match statement!")
                }
                out_vec.push(name);
                out_set.insert(name);
                (out_vec, out_set)
            }
            Pattern::Wildcard | Pattern::Constant(_) => (out_vec, out_set),
        };
        res
    }

    pub fn captures_in_order<'a>(self: &'a Self) -> Vec<&'a VarName> {
        let (out_vec, _) = self.captures_in_order_(vec![], HashSet::new());
        out_vec
    }
}

pub type Program = Vec<Item>;
