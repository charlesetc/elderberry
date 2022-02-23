use std::collections::HashSet;

#[derive(Debug, Clone)]
pub enum Constant {
    Int(i64),
    Float(f64),
    String(String),
    Bool(bool),
}

pub type VarName = String;
pub type FieldName = String;
pub type VariantName = String;

#[derive(Debug, Clone)]
pub struct RecordFieldPattern(pub FieldName, pub Pattern);

#[derive(Debug, Clone)]
pub enum Pattern {
    Constant(Constant),
    Variant(VariantName, Vec<Pattern>),
    Record(Vec<RecordFieldPattern>),
    Var(VarName),
    Wildcard,
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
            Pattern::Record(fields) => fields.into_iter().fold(
                (out_vec, out_set),
                |(out_vec, out_set), RecordFieldPattern(_, pat)| {
                    pat.captures_in_order_(out_vec, out_set)
                },
            ),
            Pattern::Var(name) => {
                if out_set.contains(name) {
                    panic!("error: cannot bind the same name twice in a match statement!")
                }
                out_vec.push(name);
                out_set.insert(name);
                (out_vec, out_set)
            }
            (Pattern::Wildcard | Pattern::Constant(_)) => (out_vec, out_set),
        };
        res
    }

    pub fn captures_in_order<'a>(self: &'a Self) -> Vec<&'a VarName> {
        let (out_vec, _) = self.captures_in_order_(vec![], HashSet::new());
        out_vec
    }
}

#[derive(Debug, Clone)]
pub struct RecordField(pub FieldName, pub Expr);

#[derive(Debug, Clone)]
pub struct MatchBranch(pub Pattern, pub Expr);

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

#[derive(Debug, Clone)]
pub enum Expr {
    Constant(Constant),
    Record(Vec<RecordField>),
    FieldAccess(Box<Expr>, FieldName),
    Variant(VariantName, Vec<Expr>),
    Match(Box<Expr>, Vec<MatchBranch>),
    Lambda(Vec<Pattern>, Box<Expr>),
    Apply(Box<Expr>, Vec<Expr>),
    Block(Statements),
    Var(VarName),
}

#[derive(Debug, Clone)]
pub enum Item {
    Module(VarName, Vec<Item>),
    Alias(VarName, Vec<VarName>),
    ItemLet(RecFlag, VarName, Box<Expr>),
}

impl Item {
    pub fn name(self) -> VarName {
        match self {
            Item::Module(name, _) => name,
            Item::Alias(name, _) => name,
            Item::ItemLet(_, name, _) => name,
        }
    }
}

pub type Program = Vec<Item>;
