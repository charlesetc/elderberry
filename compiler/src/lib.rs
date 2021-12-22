#[derive(Debug)]
enum Constant {
    Int(i32),
    String(String),
}

type VarName = String;
type FieldName = String;
type VariantName = String;

#[derive(Debug)]
struct RecordFieldPattern(FieldName, Pattern);

#[derive(Debug)]
enum Pattern {
    Variant(VariantName, Vec<Pattern>),
    Record(Vec<RecordFieldPattern>),
    Var(VarName),
}

#[derive(Debug)]
struct RecordField(FieldName, Expr);

#[derive(Debug)]
struct MatchBranch(Pattern, Expr);

#[derive(Debug)]
enum Expr {
    Constant(Constant),
    Record(Vec<RecordField>),
    FieldAccess(Box<Expr>, FieldName),
    Variant(VariantName, Vec<Expr>),
    Match(Box<Expr>, Vec<MatchBranch>),
    Lambda(Pattern, Box<Expr>),
    Apply(Box<Expr>, Vec<Expr>),
    Let(Pattern, Box<Expr>, Box<Expr>),
    Var(VarName),
}

#[derive(Debug)]
enum Item {
    Module(VarName, Vec<Item>),
    Alias(VarName, Vec<VarName>),
    ItemLet(VarName, Box<Expr>),
}

type Program = Vec<Item>;

use logos::{Lexer, Logos};
#[derive(Logos, Debug, Clone, PartialEq)]
enum Token {
    #[token("module")]
    Module,

    #[token("let")]
    Let,

    #[token("(")]
    OpenParen,

    #[token(")")]
    CloseParen,

    #[token("{")]
    OpenBrace,

    #[token("}")]
    CloseBrace,

    #[token("->")]
    Arrow,

    #[token("=")]
    Equals,

    #[token(".")]
    Dot,

    #[regex(r#""([^"\\]|\\t|\\u|\\n|\\")*""#)]
    String,

    #[regex("[a-zA-Z]+")]
    Var,

    #[error]
    #[regex(r"[ \t\n\f]+", logos::skip)]
    Error,
}

trait ParseFailure {
    fn expected(&self, string: &str) -> !;
}

impl<'a> ParseFailure for Lexer<'a, Token> {
    fn expected(&self, string: &str) -> ! {
        panic!(
            "parse error at {:#?}: expected {}, but got {}",
            self.span(),
            string,
            self.slice()
        )
    }
}

fn parse_module_path(lex: &mut Lexer<Token>) -> Vec<VarName> {
    match lex.next() {
        Some(Token::Var) => {
            let var = lex.slice().to_string();
            // TODO: Calling peek mutates the underling iterator!
            // Instead you should switch to using a vector and pattern matching on a slice.
            match lex.peekable().peek() {
                Some(&Token::Dot) => {
                    lex.next();
                    let mut ret = parse_module_path(lex);
                    ret.push(var);
                    ret
                }
                _ => vec![var],
            }
        }
        _ => lex.expected("module path"),
    }
}

fn parse_expression(lex: &mut Lexer<Token>) -> Expr {
    unimplemented!()
}

fn parse_module_body(lex: &mut Lexer<Token>) -> Vec<Item> {
    let error_statement =
        "module alias (=), let statement, or module definition ({), or module end (})";
    match lex.peekable().peek() {
        None => lex.expected(error_statement),
        Some(&Token::CloseBrace) => {
            lex.next();
            vec![]
        }
        _ => {
            let item = parse_item(lex).unwrap_or_else(|| lex.expected(error_statement));
            let mut ret = parse_module_body(lex);
            ret.push(item);
            ret
        }
    }
}

fn parse_item(lex: &mut Lexer<Token>) -> Option<Item> {
    match lex.next() {
        None => None,
        Some(Token::Module) => match lex.next() {
            Some(Token::Var) => {
                let name = lex.slice().to_string();
                match lex.next() {
                    Some(Token::Equals) => {
                        let path = parse_module_path(lex);
                        Some(Item::Alias(name, path))
                    }
                    Some(Token::OpenBrace) => {
                        let items = parse_module_body(lex);
                        Some(Item::Module(name, items))
                    }
                    _ => lex.expected("module alias (=), let statement, or module definition ({)"),
                }
            }
            _ => lex.expected("module name after `module` keyword"),
        },
        _ => lex.expected("either `module` or `let`"),
    }
}

fn parse(source: &str) -> Program {
    let mut items = vec![];
    let mut lex = Token::lexer(source);
    while let Some(item) = parse_item(&mut lex) {
        items.push(item)
    }
    items
}

#[test]
fn test_parse_module_alias() {
    insta::assert_debug_snapshot!(parse("module X = B module C = B.Y"), @r###"
    [
        Alias(
            "X",
            [],
        ),
    ]
    "###)
}
