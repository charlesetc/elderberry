#[derive(Debug, Clone)]
pub enum Constant {
    Int(i64),
    Float(f64),
    String(String),
}

pub type VarName = String;
pub type FieldName = String;
pub type VariantName = String;

#[derive(Debug, Clone)]
pub struct RecordFieldPattern(pub FieldName, pub Pattern);

#[derive(Debug, Clone)]
pub enum Pattern {
    Variant(VariantName, Vec<Pattern>),
    Record(Vec<RecordFieldPattern>),
    Var(VarName),
    Wildcard,
}

impl Pattern {
    fn captures_in_order_<'a>(self: &'a Self, mut out: Vec<&'a VarName>) -> Vec<&'a VarName> {
        match self {
            Pattern::Variant(_, pats) => pats
                .into_iter()
                .fold(out, |out, pat| pat.captures_in_order_(out)),
            Pattern::Record(fields) => fields
                .into_iter()
                .fold(out, |out, RecordFieldPattern(_, pat)| {
                    pat.captures_in_order_(out)
                }),
            Pattern::Var(name) => { out.push(name); out},
            Pattern::Wildcard => out,
        }
    }

    pub fn captures_in_order<'a>(self: &'a Self) -> Vec<&'a VarName> {
        self.captures_in_order_(vec![])
    }
}

#[derive(Debug, Clone)]
pub struct RecordField(pub FieldName, pub Expr);

#[derive(Debug, Clone)]
pub struct MatchBranch(pub Pattern, pub Expr);

#[derive(Debug, Clone)]
pub enum Statements {
    Empty,
    Sequence(Box<Expr>, Box<Statements>),
    Let(Pattern, Box<Expr>, Box<Statements>),
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
    ItemLet(VarName, Box<Expr>),
}

impl Item {
    pub fn name(self) -> VarName {
        match self {
            Item::Module(name, _) => name,
            Item::Alias(name, _) => name,
            Item::ItemLet(name, _) => name,
        }
    }
}

pub type Program = Vec<Item>;
