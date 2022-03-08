use crate::parser::*;
use crate::typechecker::*;
use crate::types::*;

#[allow(dead_code)]
fn test(source: &str) -> AstType {
    let ast = parse(source);
    typecheck(ast)
}

#[test]
fn test_primitives() {
    insta::assert_debug_snapshot!(test("let x = 2"), @r###"
            Primitive(
                Int,
            )
            "###);
    insta::assert_debug_snapshot!(test("let x = \"hi there\""), @r###"
        Primitive(
            String,
        )
        "###);
    insta::assert_debug_snapshot!(test("let x = true"), @r###"
        Primitive(
            Bool,
        )
        "###);
}

#[test]
fn test_record() {
    insta::assert_debug_snapshot!(test("let x = {:}"), @r###"
        Record(
            [],
        )
        "###);
    insta::assert_debug_snapshot!(test("let x = {name: \"Alfred\"}"), @r###"
        Record(
            [
                (
                    "name",
                    Primitive(
                        String,
                    ),
                ),
            ],
        )
        "###);
    insta::assert_debug_snapshot!(test("let f = |r| { r.hi; r.there; r }"), @r###"
        Function(
            [
                Intersection(
                    TypeVariable(
                        "a0",
                    ),
                    Record(
                        [
                            (
                                "hi",
                                Bottom,
                            ),
                            (
                                "there",
                                Bottom,
                            ),
                        ],
                    ),
                ),
            ],
            TypeVariable(
                "a0",
            ),
        )
        "###);
}

#[test]
fn test_most_basic_apply() {
    insta::assert_debug_snapshot!(test("let x = |y| |x| y(x)"), @r###"
        Function(
            [
                Function(
                    [
                        TypeVariable(
                            "a1",
                        ),
                    ],
                    TypeVariable(
                        "a2",
                    ),
                ),
            ],
            Function(
                [
                    TypeVariable(
                        "a1",
                    ),
                ],
                TypeVariable(
                    "a2",
                ),
            ),
        )
        "###);
    insta::assert_debug_snapshot!(test("let f = |y, x| y(x, x)"), @r###"
        Function(
            [
                Function(
                    [
                        TypeVariable(
                            "a4",
                        ),
                        TypeVariable(
                            "a4",
                        ),
                    ],
                    TypeVariable(
                        "a5",
                    ),
                ),
                TypeVariable(
                    "a4",
                ),
            ],
            TypeVariable(
                "a5",
            ),
        )
        "###);
}

#[test]
fn test_twice() {
    insta::assert_debug_snapshot!(test("let x = |f| |x| f(f(x))"), @r###"
        Function(
            [
                Function(
                    [
                        TypeVariable(
                            "a1",
                        ),
                    ],
                    TypeVariable(
                        "a1",
                    ),
                ),
            ],
            Function(
                [
                    TypeVariable(
                        "a1",
                    ),
                ],
                TypeVariable(
                    "a1",
                ),
            ),
        )
        "###);
}

#[test]
fn test_apply_to_object() {
    insta::assert_debug_snapshot!(test("let f = |o| o.y let x = {let a = {x: 2, y:3}; let b =  {x:2, y:\"hi\", z:true}; f(a); f(b) }"), @r###"
        Primitive(
            String,
        )
        "###);
}

#[test]
fn test_if_statement() {
    insta::assert_debug_snapshot!(test("let x = if true 2 else 3 "), @r###"
        Primitive(
            Int,
        )
        "###);
    insta::assert_debug_snapshot!(test("let x = |x| if x x else x"), @r###"
        Function(
            [
                Intersection(
                    TypeVariable(
                        "a1",
                    ),
                    Primitive(
                        Bool,
                    ),
                ),
            ],
            TypeVariable(
                "a1",
            ),
        )
        "###)
}

#[test]
fn test_polymorphism() {
    insta::assert_debug_snapshot!(test("let id = |y| y"), @r###"
        Function(
            [
                TypeVariable(
                    "a0",
                ),
            ],
            TypeVariable(
                "a0",
            ),
        )
        "###);
    insta::assert_debug_snapshot!(test("let id = |x| x let x = { id(2); id(\"3\"); id }"), @r###"
        Function(
            [
                TypeVariable(
                    "a6",
                ),
            ],
            TypeVariable(
                "a6",
            ),
        )
        "###);
    insta::assert_debug_snapshot!(test("let id = |x| x let x = { id(2); id(\"3\") }"), @r###"
        Primitive(
            String,
        )
        "###);
}

#[test]
fn test_recursion() {
    insta::assert_debug_snapshot!(test("let rec f = |x| f(x)"), @r###"
        Function(
            [
                Bottom,
            ],
            Top,
        )
        "###);

    insta::assert_debug_snapshot!(test("let rec f = |x| f(f(x))"), @r###"
        Function(
            [
                TypeVariable(
                    "a4",
                ),
            ],
            TypeVariable(
                "a4",
            ),
        )
        "###);
    insta::assert_debug_snapshot!(test("let rec produce = |arg| { head: produce(arg) }"), @r###"
    Function(
        [
            Bottom,
        ],
        Recursive(
            "a10",
            Record(
                [
                    (
                        "head",
                        TypeVariable(
                            "a10",
                        ),
                    ),
                ],
            ),
        ),
    )
    "###);

    insta::assert_debug_snapshot!(test("let rec f = |x| { left: x , right: f(x) }"), @r###"
    Function(
        [
            TypeVariable(
                "a12",
            ),
        ],
        Recursive(
            "a14",
            Record(
                [
                    (
                        "left",
                        TypeVariable(
                            "a12",
                        ),
                    ),
                    (
                        "right",
                        TypeVariable(
                            "a14",
                        ),
                    ),
                ],
            ),
        ),
    )
    "###);
}

#[test]
fn test_if_record() {
    insta::assert_debug_snapshot!(test("let z = if true { wow: 2 } else { that: 2 } "), @r###"
        Record(
            [],
        )
        "###);
}

#[test]
fn test_variants() {
    insta::assert_debug_snapshot!(test("let z = Hi(2)"), @r###"
        Variant(
            [
                (
                    "Hi",
                    [
                        Primitive(
                            Int,
                        ),
                    ],
                ),
            ],
        )
        "###);
    insta::assert_debug_snapshot!(test("let f = |x| Hi(x) let z = f(2) let m = f(This)"), @r###"
        Variant(
            [
                (
                    "Hi",
                    [
                        Variant(
                            [
                                (
                                    "This",
                                    [],
                                ),
                            ],
                        ),
                    ],
                ),
            ],
        )
        "###);
}

#[test]
fn test_variant_patterns() {
    insta::assert_debug_snapshot!(test("let f = |x| match x { Wow(a,b) -> 2, Foo(c) -> 3 }"), @r###"
        Function(
            [
                Variant(
                    [
                        (
                            "Foo",
                            [
                                Bottom,
                            ],
                        ),
                        (
                            "Wow",
                            [
                                Bottom,
                                Bottom,
                            ],
                        ),
                    ],
                ),
            ],
            Primitive(
                Int,
            ),
        )
        "###);
    insta::assert_debug_snapshot!(test("let f = |x| Hi(x) let z = f(2) let m = f(This)"), @r###"
        Variant(
            [
                (
                    "Hi",
                    [
                        Variant(
                            [
                                (
                                    "This",
                                    [],
                                ),
                            ],
                        ),
                    ],
                ),
            ],
        )
        "###);
}

#[test]
fn test_match() {
    insta::assert_debug_snapshot!(test("let f = |x| match x { a -> a }"), @r###"
        Function(
            [
                TypeVariable(
                    "a0",
                ),
            ],
            TypeVariable(
                "a0",
            ),
        )
        "###);
    insta::assert_debug_snapshot!(test("let f = |a| match a { { name: a } -> { wow: a, pool: 2 }, { this: 3 } -> { foo: a, pool: a.name }}"), @r###"
        Function(
            [
                Record(
                    [
                        (
                            "name",
                            Intersection(
                                TypeVariable(
                                    "a5",
                                ),
                                Primitive(
                                    Int,
                                ),
                            ),
                        ),
                        (
                            "this",
                            Primitive(
                                Int,
                            ),
                        ),
                    ],
                ),
            ],
            Record(
                [
                    (
                        "pool",
                        TypeVariable(
                            "a5",
                        ),
                    ),
                ],
            ),
        )
        "###);
    insta::assert_debug_snapshot!(test("let f = |x| match x { { name: a } -> { wow: a }, { this: a } -> { wow: a }} let a = f({name: 2, this: 3}).wow"), @r###"
        Primitive(
            Int,
        )
        "###);
}

#[test]
fn test_match_and_apply() {
    insta::assert_debug_snapshot!(
        test(" \
        let unwrap_default = |x| match x { Some(a) -> a, None -> 2 }  \
        let z = unwrap_default(None) \
        "), @r###"
        Primitive(
            Int,
        )
        "###);
    insta::assert_debug_snapshot!(test("
        let map = |o, f| {
            match o {
                None -> None,
                Some(a) -> Some(f(a)),
            }
        }

        let z = map(Some(\"hi\"), |x| 2)
        "), @r###"
    Variant(
        [
            (
                "None",
                [],
            ),
            (
                "Some",
                [
                    Primitive(
                        Int,
                    ),
                ],
            ),
        ],
    )
    "###);
}
