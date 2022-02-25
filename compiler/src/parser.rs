use logos::{Lexer, Logos};
use std::str::Chars;

use crate::ast::*;
use RecFlag::*;

fn unescape_chars(mut chars: Chars) -> String {
    let mut ret = String::new();
    while let Some(c) = chars.next() {
        match c {
            '\\' => match chars.next() {
                None => ret.push('\\'),
                Some('\\') => ret.push('\\'),
                Some('n') => ret.push('\n'),
                Some('t') => ret.push('\t'),
                Some('"') => ret.push('\"'),
                Some(d) => {
                    ret.push('\\');
                    ret.push(d);
                }
            },
            _ => ret.push(c),
        }
    }
    ret
}

fn unescape_string(lexer: &mut Lexer<Token>) -> Option<String> {
    let str: String = lexer.slice().parse().unwrap();
    let mut chars = str.chars();
    // remove first and last `"` characters
    chars.next();
    chars.next_back();
    Some(unescape_chars(chars))
}

#[derive(Logos, Debug, Clone, PartialEq)]
enum Token {
    #[token("module")]
    Module,

    #[token("match")]
    Match,

    #[token("let")]
    Let,

    #[token("rec")]
    Rec,

    #[token("true")]
    True,

    #[token("false")]
    False,

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

    #[token("|")]
    Pipe,

    #[token(",")]
    Comma,

    #[token(":")]
    Colon,

    #[token("_")]
    Undescore,

    #[token("/*")]
    OpenComment,

    #[token("*/")]
    CloseComment,

    #[regex(r#""(?:[^"]|\\")*""#, unescape_string)]
    String(String),

    #[regex("(\\+|-)?[0-9]+", |lex| lex.slice().parse())]
    Int(i64),

    #[regex("[0-9]+\\.[0-9]+", |lex| lex.slice().parse())]
    Float(f64),

    #[regex("[a-z][a-zA-Z]*", |lex| lex.slice().parse())]
    LowerVar(String),

    #[regex("[A-Z][a-zA-Z]*", |lex| lex.slice().parse())]
    CapitalVar(String),

    #[regex(r"[ \t\n\f]+", logos::skip)]
    Space,

    #[error]
    Error,
}

type TokenWithSpan<'source> = (Token, std::ops::Range<usize>);

impl Token {
    fn tokenize<'source>(source: &'source str) -> Vec<TokenWithSpan> {
        let lexer = Token::lexer(source);
        lexer.spanned().map(|(token, span)| (token, span)).collect()
    }
}

fn expected(string: &str, n: usize, tokens: &[TokenWithSpan]) -> ! {
    panic!(
        "parse error: expected {}, but got {:#?}",
        string,
        tokens.iter().take(n).collect::<Vec<&TokenWithSpan>>()
    )
}

fn expect_and_consume(tokens: &mut &[TokenWithSpan], token: Token) {
    match tokens {
        [(first_token, _), rest @ ..] if &token == first_token => *tokens = rest,
        _ => expected(&format!("{:?}", token), 3, tokens),
    }
}

fn parse_record_body_in_reverse(tokens: &mut &[TokenWithSpan]) -> Vec<(FieldName, Expr)> {
    match tokens {
        [(Token::CloseBrace, _), rest @ ..] => {
            *tokens = rest;
            vec![]
        }
        [(Token::LowerVar(field_name), _), (Token::Colon, _), rest @ ..] => {
            *tokens = rest;
            let expr = parse_expression(tokens);
            let field = (field_name.to_string(), expr);
            // gotta eagerly grab that comma
            match tokens {
                [(Token::CloseBrace, _), rest @ ..] => {
                    *tokens = rest;
                    vec![field]
                }
                [(Token::Comma, _), rest @ ..] => {
                    *tokens = rest;
                    let mut ret = parse_record_body_in_reverse(tokens);
                    ret.push(field);
                    ret
                }
                _ => expected("record field separator (,) or record end (})", 3, tokens),
            }
        }
        _ => expected("record field or record end (})", 5, tokens),
    }
}

fn parse_record_body(tokens: &mut &[TokenWithSpan]) -> Vec<(FieldName, Expr)> {
    let mut ret = parse_record_body_in_reverse(tokens);
    ret.reverse();
    ret
}

fn parse_record_pattern_body_in_reverse(
    tokens: &mut &[TokenWithSpan],
) -> Vec<(FieldName, Pattern)> {
    match tokens {
        [(Token::CloseBrace, _), rest @ ..] => {
            *tokens = rest;
            vec![]
        }
        [(Token::LowerVar(field_name), _), (Token::Colon, _), rest @ ..] => {
            *tokens = rest;
            let pat = parse_pattern(tokens);
            let field = (field_name.to_string(), pat);
            // gotta eagerly grab that comma
            match tokens {
                [(Token::CloseBrace, _), rest @ ..] => {
                    *tokens = rest;
                    vec![field]
                }
                [(Token::Comma, _), rest @ ..] => {
                    *tokens = rest;
                    let mut ret = parse_record_pattern_body_in_reverse(tokens);
                    ret.push(field);
                    ret
                }
                _ => expected("record field separator (,) or record end (})", 3, tokens),
            }
        }
        _ => expected("record field or record end (})", 5, tokens),
    }
}

fn parse_record_pattern_body(tokens: &mut &[TokenWithSpan]) -> Vec<(FieldName, Pattern)> {
    let mut ret = parse_record_pattern_body_in_reverse(tokens);
    ret.reverse();
    ret
}

fn parse_variant_body_in_reverse(tokens: &mut &[TokenWithSpan]) -> Vec<Expr> {
    match tokens {
        [(Token::CloseParen, _), rest @ ..] => {
            *tokens = rest;
            vec![]
        }
        _ => {
            let expr = parse_expression(tokens);
            // gotta eagerly grab that comma
            match tokens {
                [(Token::CloseParen, _), rest @ ..] => {
                    *tokens = rest;
                    vec![expr]
                }
                [(Token::Comma, _), rest @ ..] => {
                    *tokens = rest;
                    let mut ret = parse_variant_body_in_reverse(tokens);
                    ret.push(expr);
                    ret
                }
                _ => expected("argument separator (,) or variant end ())", 3, tokens),
            }
        }
    }
}

fn parse_variant_body(tokens: &mut &[TokenWithSpan]) -> Vec<Expr> {
    let mut ret = parse_variant_body_in_reverse(tokens);
    ret.reverse();
    ret
}

fn parse_comma_separated_patterns_in_reverse(
    tokens: &mut &[TokenWithSpan],
    until: Token,
) -> Vec<Pattern> {
    match tokens {
        [(first_token, _), rest @ ..] if first_token == &until => {
            *tokens = rest;
            vec![]
        }
        _ => {
            let pat = parse_pattern(tokens);
            // gotta eagerly grab that comma
            match tokens {
                [(first_token, _), rest @ ..] if first_token == &until => {
                    *tokens = rest;
                    vec![pat]
                }
                [(Token::Comma, _), rest @ ..] => {
                    *tokens = rest;
                    let mut ret = parse_comma_separated_patterns_in_reverse(tokens, until);
                    ret.push(pat);
                    ret
                }
                _ => expected(&format!("argument separator (,) or {:?}", until), 3, tokens),
            }
        }
    }
}

fn parse_comma_separated_patterns(tokens: &mut &[TokenWithSpan], until: Token) -> Vec<Pattern> {
    let mut ret = parse_comma_separated_patterns_in_reverse(tokens, until);
    ret.reverse();
    ret
}

fn parse_constant(tokens: &mut &[TokenWithSpan]) -> Option<Constant> {
    match tokens {
        [(Token::String(str), _), rest @ ..] => {
            *tokens = rest;
            Some(Constant::String(str.to_string()))
        }
        [(Token::Int(i), _), rest @ ..] => {
            *tokens = rest;
            Some(Constant::Int(i.clone()))
        }
        [(Token::Float(f), _), rest @ ..] => {
            *tokens = rest;
            Some(Constant::Float(f.clone()))
        }
        [(Token::True, _), rest @ ..] => {
            *tokens = rest;
            Some(Constant::Bool(true))
        }
        [(Token::False, _), rest @ ..] => {
            *tokens = rest;
            Some(Constant::Bool(false))
        }
        _ => None,
    }
}

fn parse_pattern(tokens: &mut &[TokenWithSpan]) -> Pattern {
    match tokens {
        [(Token::LowerVar(name), _), rest @ ..] => {
            *tokens = rest;
            Pattern::Var(name.to_string())
        }
        [(Token::CapitalVar(name), _), (Token::OpenParen, _), rest @ ..] => {
            *tokens = rest;
            let pats = parse_comma_separated_patterns(tokens, Token::CloseParen);
            Pattern::Variant(name.to_string(), pats)
        }
        [(Token::CapitalVar(name), _), rest @ ..] => {
            *tokens = rest;
            Pattern::Variant(name.to_string(), vec![])
        }
        [(Token::OpenBrace, _), rest @ ..] => {
            *tokens = rest;
            let fields = parse_record_pattern_body(tokens);
            Pattern::Record(fields)
        }
        [(Token::Undescore, _), rest @ ..] => {
            *tokens = rest;
            Pattern::Wildcard
        }
        _ => match parse_constant(tokens) {
            Some(constant) => Pattern::Constant(constant),
            None => expected(
                "pattern of either a binding, a variant, or a record",
                3,
                tokens,
            ),
        },
    }
}

fn parse_match_branch(tokens: &mut &[TokenWithSpan]) -> (Pattern, Expr) {
    let pattern = parse_pattern(tokens);
    expect_and_consume(tokens, Token::Arrow);
    let expr = parse_expression(tokens);
    (pattern, expr)
}

fn parse_match_body_in_reverse(tokens: &mut &[TokenWithSpan]) -> Vec<(Pattern, Expr)> {
    match tokens {
        [(Token::CloseBrace, _), rest @ ..] => {
            *tokens = rest;
            vec![]
        }
        _ => {
            let branch = parse_match_branch(tokens);
            // gotta eagerly grab that comma
            match tokens {
                [(Token::CloseBrace, _), rest @ ..] => {
                    *tokens = rest;
                    vec![branch]
                }
                [(Token::Comma, _), rest @ ..] => {
                    *tokens = rest;
                    let mut ret = parse_match_body_in_reverse(tokens);
                    ret.push(branch);
                    ret
                }
                _ => expected("argument separator (,) or variant end ())", 3, tokens),
            }
        }
    }
}

fn parse_match_body(tokens: &mut &[TokenWithSpan]) -> Vec<(Pattern, Expr)> {
    let mut ret = parse_match_body_in_reverse(tokens);
    ret.reverse();
    ret
}

fn parse_statements(tokens: &mut &[TokenWithSpan]) -> Statements {
    match tokens {
        [(Token::Let, _), (Token::LowerVar(var), _), rest @ ..] => {
            *tokens = rest;
            expect_and_consume(tokens, Token::Equals);
            let expr = parse_expression(tokens);
            let statements = parse_statements(tokens);
            Statements::Let(
                Nonrecursive,
                var.to_string(),
                Box::new(expr),
                Box::new(statements),
            )
        }
        [(Token::Let, _), (Token::Rec, _), (Token::LowerVar(var), _), rest @ ..] => {
            *tokens = rest;
            expect_and_consume(tokens, Token::Equals);
            let expr = parse_expression(tokens);
            let statements = parse_statements(tokens);
            Statements::Let(
                Recursive,
                var.to_string(),
                Box::new(expr),
                Box::new(statements),
            )
        }
        [(Token::CloseBrace, _), rest @ ..] => {
            *tokens = rest;
            Statements::Empty
        }
        _ => {
            let expr = parse_expression(tokens);
            let statements = parse_statements(tokens);
            Statements::Sequence(Box::new(expr), Box::new(statements))
        }
    }
}

fn parse_expression_without_operators(tokens: &mut &[TokenWithSpan]) -> Expr {
    match tokens {
        [(Token::LowerVar(name), _), rest @ ..] => {
            *tokens = rest;
            Expr::Var(name.to_string())
        }
        [(Token::OpenBrace, _), rest @ ..] if
            match rest { [(Token::LowerVar(_), _), (Token::Colon, _), ..] => true, _ => false }
         => {
            *tokens = rest;
            let fields = parse_record_body(tokens);
            Expr::Record(fields)
        }
        [(Token::OpenBrace, _), (Token::Colon, _), (Token::CloseBrace, _), rest @ ..] => {
            *tokens = rest;
            Expr::Record(vec![])
        }
        [(Token::OpenBrace, _), rest @ ..] => {
            *tokens = rest;
            let statements = parse_statements(tokens);
            Expr::Block(statements)
        }
        [(Token::CapitalVar(name), _), (Token::OpenParen, _), rest @ ..] => {
            *tokens = rest;
            let exprs = parse_variant_body(tokens);
            Expr::Variant(name.to_string(), exprs)
        }
        [(Token::CapitalVar(name), _), rest @ ..] => {
            *tokens = rest;
            Expr::Variant(name.to_string(), vec![])
        }
        [(Token::Pipe, _), rest @ ..] => {
            *tokens = rest;
            let patterns = parse_comma_separated_patterns(tokens, Token::Pipe);
            let expression = parse_expression(tokens);
            Expr::Lambda(patterns, Box::new(expression))
        }
        [(Token::Match, _), rest @ ..] => {
            *tokens = rest;
            let match_expr = parse_expression(tokens);
            expect_and_consume(tokens, Token::OpenBrace);
            let branches = parse_match_body(tokens);
            Expr::Match(Box::new(match_expr), branches)
        }
        _ => {
            match parse_constant(tokens) {
                Some(constant) => Expr::Constant(constant),
                _ =>
                expected("the start of an expression expression (one of `match`, `{`, `|`, a variable name, or a constant.)", 5, tokens),
            }

        }
    }
}

fn parse_comma_separated_expressions_in_reverse(
    tokens: &mut &[TokenWithSpan],
    until: Token,
) -> Vec<Expr> {
    match tokens {
        [(first_token, _), rest @ ..] if first_token == &until => {
            *tokens = rest;
            vec![]
        }
        _ => {
            let expr = parse_expression(tokens);
            // gotta eagerly grab that comma
            match tokens {
                [(first_token, _), rest @ ..] if first_token == &until => {
                    *tokens = rest;
                    vec![expr]
                }
                [(Token::Comma, _), rest @ ..] => {
                    *tokens = rest;
                    let mut ret = parse_comma_separated_expressions_in_reverse(tokens, until);
                    ret.push(expr);
                    ret
                }
                _ => expected(&format!("argument separator (,) or {:?}", until), 3, tokens),
            }
        }
    }
}

fn parse_comma_separated_expressions(tokens: &mut &[TokenWithSpan], until: Token) -> Vec<Expr> {
    let mut ret = parse_comma_separated_expressions_in_reverse(tokens, until);
    ret.reverse();
    ret
}

fn parse_operators(tokens: &mut &[TokenWithSpan], expr: Expr) -> Expr {
    match tokens {
        [(Token::Dot, _), (Token::LowerVar(field_name), _), rest @ ..] => {
            *tokens = rest;
            let expr = Expr::FieldAccess(Box::new(expr), field_name.to_string());
            parse_operators(tokens, expr)
        }
        [(Token::OpenParen, _), rest @ ..] => {
            *tokens = rest;
            let args = parse_comma_separated_expressions(tokens, Token::CloseParen);
            let expr = Expr::Apply(Box::new(expr), args);
            parse_operators(tokens, expr)
        }
        _ => expr,
    }
}

fn parse_expression(tokens: &mut &[TokenWithSpan]) -> Expr {
    let expr = parse_expression_without_operators(tokens);
    parse_operators(tokens, expr)
}

fn parse_module_path_in_reverse(tokens: &mut &[TokenWithSpan]) -> Vec<VarName> {
    match tokens {
        [(Token::CapitalVar(name), _), (Token::Dot, _), rest @ ..] => {
            *tokens = rest;
            let mut ret = parse_module_path_in_reverse(tokens);
            ret.push(name.to_string());
            ret
        }
        [(Token::CapitalVar(name), _), rest @ ..] => {
            *tokens = rest;
            vec![name.to_string()]
        }
        _ => expected("module path", 3, tokens),
    }
}

fn parse_module_path(tokens: &mut &[TokenWithSpan]) -> Vec<VarName> {
    let mut ret = parse_module_path_in_reverse(tokens);
    ret.reverse();
    ret
}

fn parse_module_body_in_reverse(tokens: &mut &[TokenWithSpan]) -> Vec<Item> {
    let error_statement =
        "module alias (=), let statement, or module definition ({), or module end (})";
    match tokens {
        [] => expected(error_statement, 5, tokens),
        [(Token::CloseBrace, _), rest @ ..] => {
            *tokens = rest;
            vec![]
        }
        _ => {
            let item = parse_item(tokens).unwrap_or_else(|| expected(error_statement, 5, tokens));
            let mut ret = parse_module_body_in_reverse(tokens);
            ret.push(item);
            ret
        }
    }
}

fn parse_module_body(tokens: &mut &[TokenWithSpan]) -> Vec<Item> {
    let mut ret = parse_module_body_in_reverse(tokens);
    ret.reverse();
    ret
}

fn parse_item(tokens: &mut &[TokenWithSpan]) -> Option<Item> {
    match tokens {
        [] => None,
        [(Token::Module, _), (Token::CapitalVar(name), _), (Token::Equals, _), (Token::OpenBrace, _), rest @ ..] =>
        {
            *tokens = rest;
            let items = parse_module_body(tokens);
            Some(Item::Module(name.to_string(), items))
        }
        [(Token::Module, _), (Token::CapitalVar(name), _), (Token::Equals, _), rest @ ..] => {
            *tokens = rest;
            let path = parse_module_path(tokens);
            Some(Item::Alias(name.to_string(), path))
        }
        [(Token::Let, _), (Token::LowerVar(name), _), (Token::Equals, _), rest @ ..] => {
            *tokens = rest;
            let expr = parse_expression(tokens);
            Some(Item::ItemLet(
                Nonrecursive,
                name.to_string(),
                Box::new(expr),
            ))
        }
        [(Token::Let, _), (Token::Rec, _), (Token::LowerVar(name), _), (Token::Equals, _), rest @ ..] =>
        {
            *tokens = rest;
            let expr = parse_expression(tokens);
            Some(Item::ItemLet(Recursive, name.to_string(), Box::new(expr)))
        }
        _ => expected(
            "module alias, let statement, or module definition",
            5,
            tokens,
        ),
    }
}

fn remove_comments(tokens: Vec<TokenWithSpan>) -> Vec<TokenWithSpan> {
    let mut depth = 0;
    tokens
        .into_iter()
        .filter_map(|token_with_span| {
            match token_with_span {
                (Token::OpenComment, _) => {
                    depth += 1;
                    None
                }
                (Token::CloseComment, _) => {
                    depth -= 1;
                    None
                }
                (token, span) => if depth > 0 {
                    None
                } else { Some((token, span)) }
            }
        })
        .collect()
}

pub fn parse(source: &str) -> Program {
    let tokens = Token::tokenize(source);
    let tokens = remove_comments(tokens);
    let mut items = vec![];
    let mut tokens = &tokens[..];
    while let Some(item) = parse_item(&mut tokens) {
        items.push(item)
    }
    items
}

#[test]
fn test_module_alias() {
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
            Nonrecursive,
            "x",
            Constant(
                String(
                    "hi",
                ),
            ),
        ),
    ]
    "###)
}

#[test]
fn test_record() {
    insta::assert_debug_snapshot!(parse("let x = { a: wow, b: {:} }"), @r###"
    [
        ItemLet(
            Nonrecursive,
            "x",
            Record(
                [
                    (
                        "a",
                        Var(
                            "wow",
                        ),
                    ),
                    (
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

#[test]
fn test_field_access() {
    insta::assert_debug_snapshot!(parse("let x = {:}.bar.baz"), @r###"
    [
        ItemLet(
            Nonrecursive,
            "x",
            FieldAccess(
                FieldAccess(
                    Record(
                        [],
                    ),
                    "bar",
                ),
                "baz",
            ),
        ),
    ]
    "###);
}

#[test]
fn test_numbers() {
    insta::assert_debug_snapshot!(parse(r#"let s = 2"#), @r###"
    [
        ItemLet(
            Nonrecursive,
            "s",
            Constant(
                Int(
                    2,
                ),
            ),
        ),
    ]
    "###)
}

#[test]
fn test_string() {
    insta::assert_debug_snapshot!(parse(r#"let s =  "beginning \"of\" \\the string\\ \n \t right? " "#), @r###"
    [
        ItemLet(
            Nonrecursive,
            "s",
            Constant(
                String(
                    "beginning \"of\" \\the string\\ \n \t right? ",
                ),
            ),
        ),
    ]
    "###)
}

#[test]
fn test_variant() {
    insta::assert_debug_snapshot!(parse(r#"let a = Apple({}, "hi", Sweet(wow), Blue)"#), @r###"
    [
        ItemLet(
            Nonrecursive,
            "a",
            Variant(
                "Apple",
                [
                    Block(
                        Empty,
                    ),
                    Constant(
                        String(
                            "hi",
                        ),
                    ),
                    Variant(
                        "Sweet",
                        [
                            Var(
                                "wow",
                            ),
                        ],
                    ),
                    Variant(
                        "Blue",
                        [],
                    ),
                ],
            ),
        ),
    ]
    "###)
}

#[test]
fn test_match() {
    insta::assert_debug_snapshot!(parse("let a = match b {}"), @r###"
    [
        ItemLet(
            Nonrecursive,
            "a",
            Match(
                Var(
                    "b",
                ),
                [],
            ),
        ),
    ]
    "###);
    insta::assert_debug_snapshot!(parse("let a = match b { x -> {:} , Nice({ this: a }) -> {:} }"), @r###"
    [
        ItemLet(
            Nonrecursive,
            "a",
            Match(
                Var(
                    "b",
                ),
                [
                    (
                        Var(
                            "x",
                        ),
                        Record(
                            [],
                        ),
                    ),
                    (
                        Variant(
                            "Nice",
                            [
                                Record(
                                    [
                                        (
                                            "this",
                                            Var(
                                                "a",
                                            ),
                                        ),
                                    ],
                                ),
                            ],
                        ),
                        Record(
                            [],
                        ),
                    ),
                ],
            ),
        ),
    ]
    "###)
}


#[test]
fn test_comment() {
    insta::assert_debug_snapshot!(parse("let fst = |x, /* 2 \"hithere\" */ y| x "), @r###"
    [
        ItemLet(
            Nonrecursive,
            "fst",
            Lambda(
                [
                    Var(
                        "x",
                    ),
                    Var(
                        "y",
                    ),
                ],
                Var(
                    "x",
                ),
            ),
        ),
    ]
    "###)
}

#[test]
fn test_lambda() {
    insta::assert_debug_snapshot!(parse("let fst = |x, y| x "), @r###"
    [
        ItemLet(
            Nonrecursive,
            "fst",
            Lambda(
                [
                    Var(
                        "x",
                    ),
                    Var(
                        "y",
                    ),
                ],
                Var(
                    "x",
                ),
            ),
        ),
    ]
    "###)
}

#[test]
fn test_apply() {
    insta::assert_debug_snapshot!(parse("let a = x(y).test({:}, Test)"), @r###"
    [
        ItemLet(
            Nonrecursive,
            "a",
            Apply(
                FieldAccess(
                    Apply(
                        Var(
                            "x",
                        ),
                        [
                            Var(
                                "y",
                            ),
                        ],
                    ),
                    "test",
                ),
                [
                    Record(
                        [],
                    ),
                    Variant(
                        "Test",
                        [],
                    ),
                ],
            ),
        ),
    ]
    "###)
}

#[test]
fn test_block() {
    let parsed = parse(
        "
    let a = |x| {
        let y = A
        wow
        let x = B
        x(y) 
    }
    ",
    );
    insta::assert_debug_snapshot!(parsed, @r###"
    [
        ItemLet(
            Nonrecursive,
            "a",
            Lambda(
                [
                    Var(
                        "x",
                    ),
                ],
                Block(
                    Let(
                        Nonrecursive,
                        "y",
                        Variant(
                            "A",
                            [],
                        ),
                        Sequence(
                            Var(
                                "wow",
                            ),
                            Let(
                                Nonrecursive,
                                "x",
                                Variant(
                                    "B",
                                    [],
                                ),
                                Sequence(
                                    Apply(
                                        Var(
                                            "x",
                                        ),
                                        [
                                            Var(
                                                "y",
                                            ),
                                        ],
                                    ),
                                    Empty,
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    ]
    "###)
}
