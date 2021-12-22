#[derive(Debug)]
pub enum Constant {
    Int(i32),
    String(String),
}

type VarName = String;
type FieldName = String;
type VariantName = String;

#[derive(Debug)]
pub struct RecordFieldPattern(FieldName, Pattern);

#[derive(Debug)]
pub enum Pattern {
    Variant(VariantName, Vec<Pattern>),
    Record(Vec<RecordFieldPattern>),
    Var(VarName),
}

#[derive(Debug)]
pub struct RecordField(FieldName, Expr);

#[derive(Debug)]
pub struct MatchBranch(Pattern, Expr);

#[derive(Debug)]
pub enum Expr {
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
pub enum Item {
    Module(VarName, Vec<Item>),
    Alias(VarName, Vec<VarName>),
    ItemLet(VarName, Box<Expr>),
}

type Program = Vec<Item>;

use logos::Logos;
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

    #[token(",")]
    Comma,

    #[token(":")]
    Colon,

    #[regex(r#""([^"\\]|\\t|\\u|\\n|\\")*""#)]
    String,

    #[regex("[a-z][a-zA-Z]*")]
    LowerVar,

    #[regex("[A-Z][a-zA-Z]*")]
    CapitalVar,

    #[error]
    #[regex(r"[ \t\n\f]+", logos::skip)]
    Error,
}

type TokenWithContext<'source> = (Token, &'source str, std::ops::Range<usize>);

impl Token {
    fn tokenize<'source>(source: &'source str) -> Vec<TokenWithContext> {
        use substring::Substring;
        let lexer = Token::lexer(source);
        lexer
            .spanned()
            .map(|(token, span)| (token, source.substring(span.start, span.end), span))
            .collect()
    }
}

fn expected(string: &str, n: usize, tokens: &[TokenWithContext]) -> ! {
    panic!(
        "parse error: expected {}, but got {:#?}",
        string,
        tokens.iter().take(n).collect::<Vec<&TokenWithContext>>()
    )
}

fn parse_record_body_in_reverse(tokens: &mut &[TokenWithContext]) -> Vec<RecordField> {
    match tokens {
        [(Token::CloseBrace, _, _), rest @ ..] => {
            *tokens = rest;
            vec![]
        }
        [(Token::LowerVar, field_name, _), (Token::Colon, _, _), rest @ ..] => {
            *tokens = rest;
            let expr = parse_expression(tokens);
            let field = RecordField(field_name.to_string(), expr);
            // gotta eagerly grab that comma
            match tokens {
                [(Token::CloseBrace, _, _), rest @ ..] => {
                    *tokens = rest;
                    vec![field]
                }
                [(Token::Comma, _, _), rest @ ..] => {
                    *tokens = rest;
                    let mut ret = parse_record_body(tokens);
                    ret.push(field);
                    ret
                }
                _ => expected("record field separator (,) or record end (})", 3, tokens)
            }
        }
        _ => expected("record field or record end (})", 5, tokens),
    }
}

fn parse_record_body(tokens: &mut &[TokenWithContext]) -> Vec<RecordField> {
    let mut ret = parse_record_body_in_reverse(tokens);
    ret.reverse();
    ret
}

fn parse_expression(tokens: &mut &[TokenWithContext]) -> Expr {
    match tokens {
        [(Token::String, str, _), rest @ ..] => {
            *tokens = rest;
            Expr::Constant(Constant::String(str.to_string()))
        }
        [(Token::OpenBrace, _, _), rest @ ..] => {
            *tokens = rest;
            let fields = parse_record_body(tokens);
            Expr::Record(fields)
        }
        _ => expected("string, ...", 5, tokens),
    }
}

fn parse_module_path_in_reverse(tokens: &mut &[TokenWithContext]) -> Vec<VarName> {
    match tokens {
        [(Token::CapitalVar, name, _), (Token::Dot, _, _), rest @ ..] => {
            *tokens = rest;
            let mut ret = parse_module_path(tokens);
            ret.push(name.to_string());
            ret
        }
        [(Token::CapitalVar, name, _), rest @ ..] => {
            *tokens = rest;
            vec![name.to_string()]
        }
        _ => expected("module path", 3, tokens),
    }
}

fn parse_module_path(tokens: &mut &[TokenWithContext]) -> Vec<VarName> {
    let mut ret = parse_module_path_in_reverse(tokens);
    ret.reverse();
    ret
}

fn parse_module_body_in_reverse(tokens: &mut &[TokenWithContext]) -> Vec<Item> {
    let error_statement =
        "module alias (=), let statement, or module definition ({), or module end (})";
    match tokens {
        [] => expected(error_statement, 5, tokens),
        [(Token::CloseBrace, _, _), rest @ ..] => {
            *tokens = rest;
            vec![]
        }
        _ => {
            let item = parse_item(tokens).unwrap_or_else(|| expected(error_statement, 5, tokens));
            let mut ret = parse_module_body(tokens);
            ret.push(item);
            ret
        }
    }
}

fn parse_module_body(tokens: &mut &[TokenWithContext]) -> Vec<Item> {
    let mut ret = parse_module_body_in_reverse(tokens);
    ret.reverse();
    ret
}

fn parse_item(tokens: &mut &[TokenWithContext]) -> Option<Item> {
    match tokens {
        [] => None,
        [(Token::Module, _, _), (Token::CapitalVar, name, _), (Token::Equals, _, _), (Token::OpenBrace, _, _), rest @ ..] =>
        {
            *tokens = rest;
            let items = parse_module_body(tokens);
            Some(Item::Module(name.to_string(), items))
        }
        [(Token::Module, _, _), (Token::CapitalVar, name, _), (Token::Equals, _, _), rest @ ..] => {
            *tokens = rest;
            let path = parse_module_path(tokens);
            Some(Item::Alias(name.to_string(), path))
        }
        [(Token::Let, _, _), (Token::LowerVar, name, _), (Token::Equals, _, _), rest @ ..] => {
            *tokens = rest;
            let expr = parse_expression(tokens);
            Some(Item::ItemLet(name.to_string(), Box::new(expr)))
        }
        _ => expected(
            "module alias, let statement, or module definition",
            5,
            tokens,
        ),
    }
}

pub fn parse(source: &str) -> Program {
    let tokens = Token::tokenize(source);
    let mut items = vec![];
    let mut tokens = &tokens[..];
    while let Some(item) = parse_item(&mut tokens) {
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
            [
                "B",
            ],
        ),
        Alias(
            "C",
            [
                "B",
                "Y",
            ],
        ),
    ]
    "###);
    insta::assert_debug_snapshot!(parse("module X = B \n module C = B.Y"), @r###"
    [
        Alias(
            "X",
            [
                "B",
            ],
        ),
        Alias(
            "C",
            [
                "B",
                "Y",
            ],
        ),
    ]
    "###);
    insta::assert_debug_snapshot!(parse("module A = { \n module B = C\n }"), @r###"
    [
        Module(
            "A",
            [
                Alias(
                    "B",
                    [
                        "C",
                    ],
                ),
            ],
        ),
    ]
    "###);
    insta::assert_debug_snapshot!(parse("let x = \"hi\""), @r###"
    [
        ItemLet(
            "x",
            Constant(
                String(
                    "\"hi\"",
                ),
            ),
        ),
    ]
    "###)
}

#[test]
fn test_parse_record() {
    insta::assert_debug_snapshot!(parse("let x = { a: \"wow\", b: {} }"), @r###"
    [
        ItemLet(
            "x",
            Record(
                [
                    RecordField(
                        "a",
                        Constant(
                            String(
                                "\"wow\"",
                            ),
                        ),
                    ),
                    RecordField(
                        "b",
                        Record(
                            [],
                        ),
                    ),
                ],
            ),
        ),
    ]
    "###);
}
