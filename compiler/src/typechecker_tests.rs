use crate::parser::*;
use crate::typechecker::*;
use crate::types::*;
use std::rc::Rc;

#[allow(dead_code)]
fn test(source: &str) -> Rc<AstType> {
    let ast = parse(source);
    let signature = typecheck_modules(ast);
    let item = signature.borrow().iter().last().unwrap().1.clone();
    match item {
        ItemType::Let(ast_type) => ast_type.clone(),
        ItemType::Module(_) | ItemType::QualifiedImport(_) => {
            panic!("these tests all should have a final let statement to typecheck")
        }
    }
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
                        "b1",
                    ),
                ],
                TypeVariable(
                    "c2",
                ),
            ),
        ],
        Function(
            [
                TypeVariable(
                    "b1",
                ),
            ],
            TypeVariable(
                "c2",
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
                        "e4",
                    ),
                    TypeVariable(
                        "e4",
                    ),
                ],
                TypeVariable(
                    "f5",
                ),
            ),
            TypeVariable(
                "e4",
            ),
        ],
        TypeVariable(
            "f5",
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
                        "b1",
                    ),
                ],
                TypeVariable(
                    "b1",
                ),
            ),
        ],
        Function(
            [
                TypeVariable(
                    "b1",
                ),
            ],
            TypeVariable(
                "b1",
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
                    "b1",
                ),
                Primitive(
                    Bool,
                ),
            ),
        ],
        TypeVariable(
            "b1",
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
                "g6",
            ),
        ],
        TypeVariable(
            "g6",
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
                "e4",
            ),
        ],
        TypeVariable(
            "e4",
        ),
    )
    "###);
    insta::assert_debug_snapshot!(test("let rec produce = |arg| { head: produce(arg) }"), @r###"
    Function(
        [
            Bottom,
        ],
        Recursive(
            "k10",
            Record(
                [
                    (
                        "head",
                        TypeVariable(
                            "k10",
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
                "m12",
            ),
        ],
        Recursive(
            "o14",
            Record(
                [
                    (
                        "left",
                        TypeVariable(
                            "m12",
                        ),
                    ),
                    (
                        "right",
                        TypeVariable(
                            "o14",
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
                                "f5",
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
                        "f5",
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

#[test]
fn test_module_indirection() {
    insta::assert_debug_snapshot!(test("
        module A {
            module B {
                    let foo = 2
            }
        }

        let bar = A.B.foo
        "), @r###"
    Primitive(
        Int,
    )
    "###);
    insta::assert_debug_snapshot!(test("
        module A {
            module B {
                    let foo = 2
            }
        }

        import A.B as C

        let bar = C.foo
        "), @r###"
    Primitive(
        Int,
    )
    "###);
    insta::assert_debug_snapshot!(test("
        module A {
            module B {
                module C {
                    let foo = 2
                }
            }
            module X {
                module Y { 
                    let bar = B.C.foo
                }
            }
        }

        let baz = A.X.Y.bar
        "), @r###"
    Primitive(
        Int,
    )
    "###);
    insta::assert_debug_snapshot!(test("
        module A {
            module A {
                module A {
                    let foo = 2
                }
            }
            module A {
                module A { 
                    let bar = A.A.foo
                }
            }
            import A.A as A

            module A {
                let bar = A.bar 
            }
        }

        let baz = A.A.bar
        "), @r###"
    Primitive(
        Int,
    )
    "###);
}

#[test]
fn test_basic_methods() {
    insta::assert_debug_snapshot!(test("
        method foo(Bar) { 2 }

        let b = Bar
        "), @r###"
    Variant(
        [
            (
                "Bar",
                [],
            ),
        ],
    )
    "###);

    insta::assert_debug_snapshot!(test("
        method foo(Bar) { 2 }

        let b = { Bar }.foo
        "), @r###"
    Function(
        [],
        Primitive(
            Int,
        ),
    )
    "###);

    insta::assert_debug_snapshot!(test("
        method foo(Bar) { 2 }

        let b = { Bar }.foo()
        "), @r###"
    Primitive(
        Int,
    )
    "###);
}

#[test]
fn test_polymorphic_methods() {
    insta::assert_debug_snapshot!(test("
        method foo(Bar, x) { x }

        let a = Bar

        let b = a.foo(2)

        let c = a.foo(\"hi\")
        "), @r###"
    Primitive(
        String,
    )
    "###);
    insta::assert_debug_snapshot!(test("
        method foo(Bar, x) { x }

        let a = { Bar }.foo(2)

        let b = { Bar }.foo(\"hi\")
        "), @r###"
    Primitive(
        String,
    )
    "###);
    insta::assert_debug_snapshot!(test("
        method box(Some(x)) = Box(x)

        method box(None) = None

        let a = if true { Some(2) } else { None }

        let b = a.box()
        "), @r###"
    Variant(
        [
            (
                "Box",
                [
                    Primitive(
                        Int,
                    ),
                ],
            ),
            (
                "None",
                [],
            ),
        ],
    )
    "###);
}
