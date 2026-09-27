use crate::diagnostics::{Diagnostic, Result};
use crate::kernel;
use crate::surface;
use std::collections::HashMap;

pub struct TypeScope<'a> {
    pub parameters: &'a [surface::ast::Ident],
    pub aliases: &'a HashMap<String, kernel::Scheme>,
}

pub fn lower_type_parameters(parameters: &[surface::ast::Ident]) -> Result<Vec<String>> {
    let mut seen = HashMap::new();
    let mut params = Vec::new();

    for param in parameters {
        // If the seen set already contained the parameter
        if let Some(prev_span) = seen.insert(&param.text, param.span) {
            return Err(Diagnostic::error(
                format!("duplicate parameter {}", param.text),
                param.span,
            )
            .with_label(prev_span, format!("previous declaration of {}", param.text)));
        }

        params.push(param.text.clone());
    }

    Ok(params)
}

pub fn lower_type(typ: &surface::ast::Type, scope: &TypeScope) -> Result<kernel::Type> {
    match typ {
        surface::ast::Type::Equiv(equiv) => lower_type_equiv(equiv, scope),
        surface::ast::Type::Lambda(lambda) => lower_type_lambda(lambda, scope),
        surface::ast::Type::Or(or) => lower_type_or(or, scope),
        surface::ast::Type::And(and) => lower_type_and(and, scope),
        surface::ast::Type::Not(not) => lower_type_not(not, scope),
        surface::ast::Type::App(app) => lower_type_app(app, scope),
        surface::ast::Type::True(t) => lower_type_true(t, scope),
        surface::ast::Type::False(f) => lower_type_false(f, scope),
        surface::ast::Type::Atom(atom) => lower_type_atom(atom, scope),
    }
}

fn lower_type_equiv(equiv: &surface::ast::Equiv, scope: &TypeScope) -> Result<kernel::Type> {
    let left_type = Box::new(lower_type(&equiv.left, scope)?);
    let right_type = Box::new(lower_type(&equiv.right, scope)?);
    Ok(kernel::Type::Pair {
        left_type: Box::new(kernel::Type::Lambda {
            argument_type: left_type.clone(),
            result_type: right_type.clone(),
        }),
        right_type: Box::new(kernel::Type::Lambda {
            argument_type: right_type,
            result_type: left_type,
        }),
    })
}

fn lower_type_lambda(lambda: &surface::ast::Lambda, scope: &TypeScope) -> Result<kernel::Type> {
    let argument_type = Box::new(lower_type(&lambda.argument_type, scope)?);
    let result_type = Box::new(lower_type(&lambda.result_type, scope)?);
    Ok(kernel::Type::Lambda {
        argument_type,
        result_type,
    })
}

fn lower_type_or(or: &surface::ast::Or, scope: &TypeScope) -> Result<kernel::Type> {
    let left_type = Box::new(lower_type(&or.left, scope)?);
    let right_type = Box::new(lower_type(&or.right, scope)?);
    Ok(kernel::Type::Either {
        left_type,
        right_type,
    })
}

fn lower_type_and(and: &surface::ast::And, scope: &TypeScope) -> Result<kernel::Type> {
    let left_type = Box::new(lower_type(&and.left, scope)?);
    let right_type = Box::new(lower_type(&and.right, scope)?);
    Ok(kernel::Type::Pair {
        left_type,
        right_type,
    })
}

fn lower_type_not(not: &surface::ast::Not, scope: &TypeScope) -> Result<kernel::Type> {
    let argument_type = Box::new(lower_type(&not.operand, scope)?);
    let result_type = Box::new(kernel::Type::False);
    Ok(kernel::Type::Lambda {
        argument_type,
        result_type,
    })
}

fn lower_type_app(app: &surface::ast::TypeApp, scope: &TypeScope) -> Result<kernel::Type> {
    let found_param = scope
        .parameters
        .iter()
        .any(|ident| ident.text == app.name.text);
    if found_param {
        return Err(Diagnostic::error(
            format!("{} is a parameter and takes no arguments", app.name.text),
            app.span,
        ));
    }

    match scope.aliases.get(&app.name.text) {
        Some(scheme) => {
            let arguments = app
                .arguments
                .iter()
                .map(|typ| lower_type(typ, scope))
                .collect::<Result<Vec<_>>>()?;
            scheme.instantiate(app.span, &arguments)
        }
        None => Err(
            Diagnostic::error(format!("unbound proposition {}", app.name.text), app.span)
                .with_note(format!("no proposition {} is defined", app.name.text)),
        ),
    }
}

fn lower_type_true(_: &surface::ast::True, _: &TypeScope) -> Result<kernel::Type> {
    let argument_type = Box::new(kernel::Type::False);
    let result_type = Box::new(kernel::Type::False);
    Ok(kernel::Type::Lambda {
        argument_type,
        result_type,
    })
}

fn lower_type_false(_: &surface::ast::False, _: &TypeScope) -> Result<kernel::Type> {
    Ok(kernel::Type::False)
}

fn lower_type_atom(atom: &surface::ast::Atom, scope: &TypeScope) -> Result<kernel::Type> {
    let name = atom.name.text.clone();
    let found = scope.parameters.iter().any(|ident| ident.text == name);

    if found {
        Ok(kernel::Type::Atom { name })
    } else {
        match scope.aliases.get(&atom.name.text) {
            Some(scheme) => scheme.instantiate(atom.span, &[]),
            None => Err(
                Diagnostic::error(format!("unbound proposition {}", name), atom.span)
                    .with_note(format!("try adding {} as a type parameter", name)),
            ),
        }
    }
}

pub fn lower_term(term: &surface::ast::Term, scope: &TypeScope) -> Result<kernel::Term> {
    match term {
        surface::ast::Term::Var(var) => lower_term_var(var, scope),
        surface::ast::Term::Fun(fun) => lower_term_fun(fun, scope),
        surface::ast::Term::App(app) => lower_term_app(app, scope),
        surface::ast::Term::Pair(pair) => lower_term_pair(pair, scope),
        surface::ast::Term::Fst(fst) => lower_term_fst(fst, scope),
        surface::ast::Term::Snd(snd) => lower_term_snd(snd, scope),
        surface::ast::Term::Inl(inl) => lower_term_inl(inl, scope),
        surface::ast::Term::Inr(inr) => lower_term_inr(inr, scope),
        surface::ast::Term::Case(case) => lower_term_case(case, scope),
        surface::ast::Term::Absurd(absurd) => lower_term_absurd(absurd, scope),
        surface::ast::Term::TrustMe(trustme) => lower_term_trustme(trustme, scope),
    }
}

fn lower_term_var(var: &surface::ast::Var, scope: &TypeScope) -> Result<kernel::Term> {
    let name = var.name.text.clone();

    let mut type_arguments = Vec::new();
    for tp in &var.type_arguments {
        type_arguments.push(lower_type(tp, scope)?);
    }

    Ok(kernel::Term::Var {
        span: var.span,
        name,
        type_arguments,
    })
}

fn lower_term_fun(fun: &surface::ast::Fun, scope: &TypeScope) -> Result<kernel::Term> {
    let argument = fun.argument.text.clone();
    let argument_type = lower_type(&fun.argument_type, scope)?;
    let body = Box::new(lower_term(&fun.body, scope)?);
    Ok(kernel::Term::Lambda {
        span: fun.span,
        argument,
        argument_type,
        body,
    })
}

fn lower_term_app(app: &surface::ast::App, scope: &TypeScope) -> Result<kernel::Term> {
    let function = Box::new(lower_term(&app.function, scope)?);
    let argument = Box::new(lower_term(&app.argument, scope)?);
    Ok(kernel::Term::Application {
        span: app.span,
        function,
        argument,
    })
}

fn lower_term_pair(pair: &surface::ast::Pair, scope: &TypeScope) -> Result<kernel::Term> {
    let left = Box::new(lower_term(&pair.left, scope)?);
    let right = Box::new(lower_term(&pair.right, scope)?);
    Ok(kernel::Term::Pair {
        span: pair.span,
        left,
        right,
    })
}

fn lower_term_fst(fst: &surface::ast::Fst, scope: &TypeScope) -> Result<kernel::Term> {
    let pair = Box::new(lower_term(&fst.pair, scope)?);
    Ok(kernel::Term::Fst {
        span: fst.span,
        pair,
    })
}

fn lower_term_snd(snd: &surface::ast::Snd, scope: &TypeScope) -> Result<kernel::Term> {
    let pair = Box::new(lower_term(&snd.pair, scope)?);
    Ok(kernel::Term::Snd {
        span: snd.span,
        pair,
    })
}

fn lower_term_inl(inl: &surface::ast::Inl, scope: &TypeScope) -> Result<kernel::Term> {
    let right_type = lower_type(&inl.right_type, scope)?;
    let left = Box::new(lower_term(&inl.left, scope)?);
    Ok(kernel::Term::Inl {
        span: inl.span,
        right_type,
        left,
    })
}

fn lower_term_inr(inr: &surface::ast::Inr, scope: &TypeScope) -> Result<kernel::Term> {
    let left_type = lower_type(&inr.left_type, scope)?;
    let right = Box::new(lower_term(&inr.right, scope)?);
    Ok(kernel::Term::Inr {
        span: inr.span,
        left_type,
        right,
    })
}

fn lower_term_case(case: &surface::ast::Case, scope: &TypeScope) -> Result<kernel::Term> {
    let either = Box::new(lower_term(&case.either, scope)?);
    let left_name = case.left_name.text.clone();
    let left_body = Box::new(lower_term(&case.left_body, scope)?);
    let right_name = case.right_name.text.clone();
    let right_body = Box::new(lower_term(&case.right_body, scope)?);
    Ok(kernel::Term::Case {
        span: case.span,
        either,
        left_name,
        left_body,
        right_name,
        right_body,
    })
}

fn lower_term_absurd(absurd: &surface::ast::Absurd, scope: &TypeScope) -> Result<kernel::Term> {
    let goal_type = lower_type(&absurd.goal_type, scope)?;
    let body = Box::new(lower_term(&absurd.body, scope)?);
    Ok(kernel::Term::Absurd {
        span: absurd.span,
        goal_type,
        body,
    })
}

fn lower_term_trustme(trustme: &surface::ast::TrustMe, scope: &TypeScope) -> Result<kernel::Term> {
    let goal_type = lower_type(&trustme.goal_type, scope)?;
    Ok(kernel::Term::TrustMe {
        span: trustme.span,
        goal_type,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diagnostics::Diagnostic;
    use crate::surface::ast::Item;

    // Lower every item in `source` in order, building the alias table as the driver does. Returns
    // the first error, or else the lowered type and body of the last theorem.
    fn lower_module(source: &str) -> Result<(kernel::Type, kernel::Term)> {
        let module = surface::parse(source).expect("should parse");
        let mut aliases = HashMap::new();
        let mut last = None;

        for item in &module.items {
            match item {
                Item::Axiom(axiom) => {
                    let scope = TypeScope {
                        parameters: &axiom.parameters,
                        aliases: &aliases,
                    };
                    lower_type_parameters(&axiom.parameters)?;
                    lower_type(&axiom.typ, &scope)?;
                }
                Item::Theorem(theorem) => {
                    let scope = TypeScope {
                        parameters: &theorem.parameters,
                        aliases: &aliases,
                    };
                    lower_type_parameters(&theorem.parameters)?;
                    let typ = lower_type(&theorem.typ, &scope)?;
                    let body = lower_term(&theorem.body, &scope)?;
                    last = Some((typ, body));
                }
                Item::Proposition(proposition) => {
                    let scope = TypeScope {
                        parameters: &proposition.parameters,
                        aliases: &aliases,
                    };
                    let parameters = lower_type_parameters(&proposition.parameters)?;
                    let typ = lower_type(&proposition.typ, &scope)?;
                    let scheme = kernel::Scheme::new(parameters, typ);
                    aliases.insert(proposition.name.text.clone(), scheme);
                }
            }
        }

        Ok(last.expect("source should contain a theorem"))
    }

    // Lower the type of `theorem t A B C : <typ> := x.` after the definitions in `defs`.
    fn lower_type_str(defs: &str, typ: &str) -> kernel::Type {
        let source = format!("{defs}\ntheorem t A B C : {typ} := x.");
        match lower_module(&source) {
            Ok((typ, _)) => typ,
            Err(diag) => panic!("{typ} failed to lower: {}", diag.message),
        }
    }

    fn assert_same_type(defs: &str, left: &str, right: &str) {
        assert_eq!(
            lower_type_str(defs, left),
            lower_type_str(defs, right),
            "`{left}` and `{right}` should lower to the same type"
        );
    }

    // The error from lowering `source`, and the source text under its primary label.
    fn lower_error(source: &str) -> (String, String) {
        let diag: Diagnostic = match lower_module(source) {
            Ok(_) => panic!("expected `{source}` to fail to lower"),
            Err(diag) => diag,
        };
        let span = diag.labels[0].span;
        (diag.message, source[span.start..span.end].to_string())
    }

    fn unbound(name: &str) -> (String, String) {
        (format!("unbound proposition {name}"), name.to_string())
    }

    const KNIGHTS_AND_KNAVES: &str = r#"
        proposition Knight A := A.
        proposition Knave A := not A.
        proposition Statement A S := (Knight A -> S) and (Knave A -> not S).
    "#;

    #[test]
    fn test_unbound_atom_in_signature() {
        assert_eq!(lower_error("theorem t A : B := x."), unbound("B"));
        assert_eq!(lower_error("theorem t : A -> A := x."), unbound("A"));
        assert_eq!(lower_error("axiom a A : A or B."), unbound("B"));
        assert_eq!(lower_error("proposition P A := A and B."), unbound("B"));
    }

    #[test]
    fn test_unbound_atom_in_body_annotations() {
        let bodies = [
            "fun (x : B) => x",
            "inl [B] x",
            "inr [B] x",
            "absurd [B] x",
            "trustme [B]",
            "f [B]",
            "f [A] [A -> B]",
        ];
        for body in bodies {
            let source = format!("theorem t A : A := {body}.");
            assert_eq!(lower_error(&source), unbound("B"), "in `{body}`");
        }
    }

    #[test]
    fn test_parameters_are_in_scope_in_body_annotations() {
        let source = "theorem t A B : A := fun (x : A and B) => absurd [A] (f [B] (inl [A] x)).";
        assert!(lower_module(source).is_ok());
    }

    #[test]
    fn test_duplicate_parameter() {
        let source = "theorem t A B A : A := x.";
        let diag = lower_module(source).map(|_| ()).unwrap_err();
        assert_eq!(diag.message, "duplicate parameter A");
        // The primary label is on the second `A`, the secondary on the first.
        assert_eq!(diag.labels[0].span.start, source.find("A : ").unwrap());
        assert_eq!(diag.labels[1].span.start, source.find("A B").unwrap());
    }

    #[test]
    fn test_equiv_desugars() {
        assert_same_type("", "A <-> B", "(A -> B) and (B -> A)");
    }

    #[test]
    fn test_alias_expansion() {
        let defs = KNIGHTS_AND_KNAVES;
        assert_same_type(defs, "Knight A", "A");
        assert_same_type(defs, "Knave A", "not A");
        assert_same_type(defs, "Knave (A and B)", "not (A and B)");
        assert_same_type(defs, "not Knave A", "not not A");
        assert_same_type(defs, "Knave A -> Knight A", "not A -> A");
    }

    #[test]
    fn test_nested_alias_expansion() {
        assert_same_type(
            KNIGHTS_AND_KNAVES,
            "Statement A (Knave B)",
            "(A -> not B) and (not A -> not not B)",
        );
    }

    #[test]
    fn test_alias_substitution_is_simultaneous() {
        // The caller's arguments are the alias's own parameter names, swapped.
        let defs = "proposition Flip A B := B and A.";
        assert_same_type(defs, "Flip B A", "A and B");
        assert_same_type(defs, "Flip A A", "A and A");
    }

    #[test]
    fn test_nullary_alias() {
        let defs = "proposition Top := False -> False.";
        assert_same_type(defs, "Top", "True");
        assert_same_type(defs, "Top and A", "True and A");
    }

    #[test]
    fn test_alias_in_body_annotations() {
        let source = format!("{KNIGHTS_AND_KNAVES}\ntheorem t A : A := fun (x : Knave A) => x.");
        let (_, body) = lower_module(&source).unwrap();
        match body {
            kernel::Term::Lambda { argument_type, .. } => {
                assert_eq!(argument_type, lower_type_str("", "not A"))
            }
            _ => panic!("expected a lambda"),
        }

        // And in type arguments.
        let source = format!("{KNIGHTS_AND_KNAVES}\ntheorem t A : A := f [Knave A].");
        let (_, body) = lower_module(&source).unwrap();
        match body {
            kernel::Term::Var { type_arguments, .. } => {
                assert_eq!(type_arguments, vec![lower_type_str("", "not A")])
            }
            _ => panic!("expected a variable"),
        }
    }

    #[test]
    fn test_parameter_shadows_alias() {
        let source = format!("{KNIGHTS_AND_KNAVES}\ntheorem t Knave : Knave := x.");
        let (typ, _) = lower_module(&source).unwrap();
        assert_eq!(
            typ,
            kernel::Type::Atom {
                name: "Knave".to_string()
            }
        );
    }

    #[test]
    fn test_alias_arity() {
        let too_many = format!("{KNIGHTS_AND_KNAVES}\ntheorem t A B : Knave A B := x.");
        assert_eq!(
            lower_error(&too_many),
            (
                "expected 1 type argument but got 2".to_string(),
                "Knave A B".to_string()
            )
        );

        let bare = format!("{KNIGHTS_AND_KNAVES}\ntheorem t A : Knave -> A := x.");
        assert_eq!(
            lower_error(&bare),
            (
                "expected 1 type argument but got 0".to_string(),
                "Knave".to_string()
            )
        );

        let nullary_applied = "proposition Top := True.\ntheorem t A : Top A := x.";
        assert_eq!(
            lower_error(nullary_applied),
            (
                "expected 0 type arguments but got 1".to_string(),
                "Top A".to_string()
            )
        );
    }

    #[test]
    fn test_applying_a_parameter() {
        assert_eq!(
            lower_error("theorem t A B : A B := x."),
            (
                "A is a parameter and takes no arguments".to_string(),
                "A B".to_string()
            )
        );
    }

    #[test]
    fn test_unbound_applied_name() {
        assert_eq!(
            lower_error("theorem t A : F A := x."),
            ("unbound proposition F".to_string(), "F A".to_string())
        );
    }

    #[test]
    fn test_alias_used_before_definition() {
        let source = "theorem t A : Knave A := x.\nproposition Knave A := not A.";
        assert_eq!(
            lower_error(source),
            (
                "unbound proposition Knave".to_string(),
                "Knave A".to_string()
            )
        );
    }

    #[test]
    fn test_alias_cannot_refer_to_itself() {
        assert_eq!(
            lower_error("proposition K A := K A."),
            ("unbound proposition K".to_string(), "K A".to_string())
        );
        assert_eq!(lower_error("proposition K := not K."), unbound("K"));
    }
}
