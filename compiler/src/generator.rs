use crate::ast::*;

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
        ret.push(c)
    }
    ret
}

fn generate_statements(out: &mut String, statements: &Statements) {
    match statements {
        Statements::Empty => (),
        Statements::Let(pattern, expr, substatements)
            if (match **substatements {
                Statements::Empty => true,
                _ => false,
            }) =>
        {
            unimplemented!()
        }
        Statements::Let(pattern, expr, statements) => {
            unimplemented!()
        }
        Statements::Sequence(expr, substatements)
            if (match **substatements {
                Statements::Empty => true,
                _ => false,
            }) =>
        {
            generate_expr(out, expr)
        }
        Statements::Sequence(expr, statements) => {
            out.push_str("(() => {");
            generate_expr(out, &expr);
            out.push_str("; ");
            generate_statements(out, &statements);
            out.push_str("})");
        }
    }
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
            for RecordFieldPattern(name, pattern) in fields {
                out.push_str(&name);
                out.push_str(":");
                generate_pattern(out, &pattern);
            }
            out.push_str("}");
        }
        Pattern::Var(_name) => out.push_str("\"__eldb_pat\""),
        Pattern::Wildcard => out.push_str("\"__eldb_wildcard\""),
    }
}

fn generate_expr(out: &mut String, expr: &Expr) {
    match expr {
        Expr::Constant(Constant::Int(i)) => out.push_str(&i.to_string()),
        Expr::Constant(Constant::Float(f)) => out.push_str(&f.to_string()),
        Expr::Constant(Constant::String(s)) => {
            out.push_str("\"");
            out.push_str(&escape(s));
            out.push_str("\"");
        }
        Expr::Var(x) => out.push_str(&x),
        Expr::Record(fields) => {
            out.push_str("{");
            for RecordField(name, expr) in fields {
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
        Expr::Lambda(pats, body) => {
            unimplemented!()
        }
        Expr::Match(matched_expr, branches) => {
            out.push_str("(() => {");
            out.push_str("let _eldb_matched_expr =");
            generate_expr(out, matched_expr);
            out.push_str(";");
            for MatchBranch(pattern, body_expr) in branches {
                let captures = pattern.captures_in_order();
                out.push_str("if (let [");
                for capture in captures {
                    out.push_str(capture);
                    out.push_str(",");
                }
                out.push_str("] = _eldb.matches(");
                generate_pattern(out, pattern);
                out.push_str(", _eldb_matched_expr)) {");
                generate_expr(out, body_expr);
                out.push_str("} else")
                // if (result = _eldb.matches()) {} else {}
            }
            out.push_str("{_eldb.unhandled_match()}})");
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
        Item::ItemLet(name, expr) => {
            out.push_str("let ");
            out.push_str(&name);
            out.push_str("=");
            generate_expr(out, &expr);
            out.push_str(";")
        }
    }
}

pub fn generate(ast: Program) -> String {
    let mut out = String::new();
    for item in ast {
        generate_toplevel_item(&mut out, &item)
    }
    out
}
