use crate::ast::*;
use RecFlag::*;

// analogous to parser::unescape_chars
fn escape(s: &String) -> String {
    let mut ret = String::new();
    for c in s.chars() {
        match c {
            '\t' => {
                ret.push('\\');
                ret.push('t')
            }
            '\n' => {
                ret.push('\\');
                ret.push('n')
            }
            '\"' => {
                ret.push('\\');
                ret.push('"')
            }
            '\\' => {
                ret.push('\\');
                ret.push('\\')
            }
            _ => ret.push(c),
        }
    }
    ret
}

fn generate_let(out: &mut String, name : &str, expr: &Expr) {
    out.push_str("let ");
    out.push_str(name);
    out.push_str("=");
    generate_expr(out, expr);
    out.push_str("; ");
}

fn generate_unit(out: &mut String) {
    out.push_str("_eldb.unit")
}

fn generate_statements_(out: &mut String, statements: &Statements) {
    match statements {
        Statements::Empty => (),
        Statements::Let(Nonrecursive, name, expr, substatements)
            // TODO: How efficient is this?
            if (match **substatements {
                Statements::Empty => true,
                _ => false,
            }) =>
        {
            generate_let(out, name, expr);
            out.push_str("return");
            generate_unit(out);
            out.push_str(";");
        }
        Statements::Let(Nonrecursive, name, expr, statements) => {
            generate_let(out, name, &expr);
            generate_statements_(out, &statements);
        }
        Statements::Let(Recursive, _, _, _) => {
            unimplemented!()
        }
        Statements::Sequence(expr, substatements)
            if (match **substatements {
                Statements::Empty => true,
                _ => false,
            }) =>
        {
            out.push_str("return ");
            generate_expr(out, expr)
        }
        Statements::Sequence(expr, statements) => {
            generate_expr(out, &expr);
            out.push_str("; ");
            generate_statements_(out, &statements);
        }
    }
}

fn generate_statements(out: &mut String, statements: &Statements) {
    out.push_str("(() => {");
    generate_statements_(out, statements);
    out.push_str("})()");
}

fn generate_pattern(out: &mut String, pattern: &Pattern) {
    match pattern {
        Pattern::Variant(name, args) => {
            out.push_str("{");
            out.push_str(name);
            out.push_str(":[");
            for arg in args {
                generate_pattern(out, arg);
                out.push_str(",");
            }
            out.push_str("]}");
        }
        Pattern::Record(fields) => {
            out.push_str("{");
            for (name, pattern) in fields {
                out.push_str(&name);
                out.push_str(":");
                generate_pattern(out, &pattern);
            }
            out.push_str("}");
        }
        Pattern::Var(_name) => out.push_str("\"__eldb_pat\""),
        Pattern::Wildcard => out.push_str("\"__eldb_wildcard\""),
        Pattern::Constant(_) => unimplemented!(),
    }
}

mod helpers {
    pub fn push_var(out: &mut String, i: usize) {
        out.push_str("_eldb_a");
        out.push_str(&i.to_string());
    }
}

fn generate_expr(out: &mut String, expr: &Expr) {
    match expr {
        Expr::Constant(Constant::Int(i)) => out.push_str(&i.to_string()),
        Expr::Constant(Constant::Float(f)) => out.push_str(&f.to_string()),
        Expr::Constant(Constant::Bool(b)) => out.push_str(&b.to_string()),
        Expr::Constant(Constant::Unit) => out.push_str("_eldb.unit"),
        Expr::Constant(Constant::String(s)) => {
            out.push_str("\"");
            out.push_str(&escape(s));
            out.push_str("\"");
        }
        Expr::Var(x) => out.push_str(&x),
        Expr::Record(fields) => {
            out.push_str("{");
            for (name, expr) in fields {
                out.push_str(name);
                out.push_str(":");
                generate_expr(out, expr);
                out.push_str(",");
            }
            out.push_str("}");
        }
        Expr::Variant(name, fields) => {
            out.push_str("{");
            out.push_str(name);
            out.push_str(": [");
            for expr in fields {
                generate_expr(out, expr);
                out.push_str(",");
            }
            out.push_str("]}");
        }
        Expr::FieldAccess(expr, name) => {
            // TODO: Maybe these "("'s are not necessary.
            out.push_str("(");
            generate_expr(out, expr);
            out.push_str(").");
            out.push_str(name);
        }
        Expr::Apply(f, args) => {
            generate_expr(out, f);
            out.push_str("(");
            for expr in args {
                generate_expr(out, expr);
                out.push_str(",");
            }
            out.push_str(")");
        }
        Expr::Block(statements) => generate_statements(out, statements),
        Expr::Lambda(patterns, body) => {
            out.push_str("((");
            for (i, _pattern) in patterns.into_iter().enumerate() {
                helpers::push_var(out, i);
                out.push_str(",");
            }
            out.push_str(") => {");
            out.push_str("let _eldb_res;");
            for (i, pattern) in patterns.into_iter().enumerate() {
                let captures = pattern.captures_in_order();
                out.push_str("if (_eldb_res = _eldb.matches(");
                generate_pattern(out, pattern);
                out.push_str(",");
                helpers::push_var(out, i);
                out.push_str(")) { let [");
                for capture in captures {
                    out.push_str(capture);
                    out.push_str(",");
                }
                out.push_str("] = _eldb_res;");
            }
            out.push_str("return ");
            generate_expr(out, body);
            out.push_str(";");
            for (_, _) in patterns.into_iter().enumerate() {
                out.push_str("}");
            }
            out.push_str("_eldb.unhandled_match()");
            out.push_str("})");
        }
        Expr::If(condition, true_branch, false_branch) => {
            out.push_str("(() => {");
            out.push_str("if (");
            generate_expr(out, condition); // typechecked to result in a bool!
            out.push_str(") {");
            out.push_str("return");
            generate_expr(out, true_branch);
            out.push_str(";");
            out.push_str("} else {");
            out.push_str("return");
            match false_branch {
                Some(false_branch) => generate_expr(out, false_branch),
                None => generate_unit(out),
            }
            out.push_str(";");
            out.push_str("})()");
        }
        Expr::Match(matched_expr, branches) => {
            out.push_str("(() => {");
            out.push_str("let _eldb_matched_expr =");
            generate_expr(out, matched_expr);
            out.push_str(";");
            out.push_str("let _eldb_res;");
            for (pattern, body) in branches {
                let captures = pattern.captures_in_order();
                out.push_str("if (_eldb_res = _eldb.matches(");
                generate_pattern(out, pattern);
                out.push_str(", _eldb_matched_expr)) { let [");
                for capture in captures {
                    out.push_str(capture);
                    out.push_str(",");
                }
                out.push_str("] = _eldb_res; return ");
                generate_expr(out, body);
                out.push_str("} else ")
            }
            out.push_str("{_eldb.unhandled_match()}})()");
        }
    }
}

fn generate_toplevel_item(out: &mut String, item: &Item) {
    match item {
        Item::Module(name, items) => {
            out.push_str("let ");
            out.push_str(&name);
            out.push_str("= {");
            for item in items {
                out.push_str("let ");
                out.push_str(&name);
                out.push_str("= ");
                generate_toplevel_item(out, item);
                out.push_str(";");
            }
            out.push_str("{");
            for item in items {
                let name = item.clone().name();
                out.push_str(&name);
                out.push_str(":");
                out.push_str(&name);
            }
            out.push_str("}");
            out.push_str("};");
        }
        Item::Alias(name, path) => {
            out.push_str("let ");
            out.push_str(&name);
            out.push_str("=");
            out.push_str(&path.join("."));
            out.push_str(";")
        }
        Item::ItemLet(Nonrecursive, name, expr) => {
            out.push_str("let ");
            out.push_str(&name);
            out.push_str("=");
            generate_expr(out, &expr);
            out.push_str(";")
        }
        Item::ItemLet(Recursive, _, _) => {
            unimplemented!()
        }
    }
}

pub fn generate(ast: Program) -> String {
    let mut out = String::new();
    out.push_str("import * as _eldb from \"./runtime/main.js\"");
    for item in ast {
        generate_toplevel_item(&mut out, &item)
    }
    out
}
