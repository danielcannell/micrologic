use crate::diagnostics::{Diagnostic, Result};
use crate::kernel;
use crate::surface;
use std::collections::HashMap;

pub fn lower_type_parameters(parameters: &[surface::ast::Ident]) -> Result<Vec<String>> {
    let mut seen = HashMap::new();
    let mut params = Vec::new();

    for param in parameters {
        // If the seen set already contained the parameter
        if let Some(prev_span) = seen.insert(&param.text, param.span) {
            return Err(Diagnostic::error(
                format!("duplicate proposition {}", param.text),
                param.span,
            )
            .with_label(prev_span, format!("previous declaration of {}", param.text)));
        }

        params.push(param.text.clone());
    }

    Ok(params)
}

pub fn lower_type(typ: &surface::ast::Type, scope: &[surface::ast::Ident]) -> Result<kernel::Type> {
    match typ {
        surface::ast::Type::Lambda(lambda) => lower_type_lambda(lambda, scope),
        surface::ast::Type::Or(or) => lower_type_or(or, scope),
        surface::ast::Type::And(and) => lower_type_and(and, scope),
        surface::ast::Type::Not(not) => lower_type_not(not, scope),
        surface::ast::Type::True(t) => lower_type_true(t, scope),
        surface::ast::Type::False(f) => lower_type_false(f, scope),
        surface::ast::Type::Atom(atom) => lower_type_atom(atom, scope),
    }
}

fn lower_type_lambda(
    lambda: &surface::ast::Lambda,
    scope: &[surface::ast::Ident],
) -> Result<kernel::Type> {
    let argument_type = Box::new(lower_type(&lambda.argument_type, scope)?);
    let result_type = Box::new(lower_type(&lambda.result_type, scope)?);
    Ok(kernel::Type::Lambda {
        argument_type,
        result_type,
    })
}

fn lower_type_or(or: &surface::ast::Or, scope: &[surface::ast::Ident]) -> Result<kernel::Type> {
    let left_type = Box::new(lower_type(&or.left, scope)?);
    let right_type = Box::new(lower_type(&or.right, scope)?);
    Ok(kernel::Type::Either {
        left_type,
        right_type,
    })
}

fn lower_type_and(and: &surface::ast::And, scope: &[surface::ast::Ident]) -> Result<kernel::Type> {
    let left_type = Box::new(lower_type(&and.left, scope)?);
    let right_type = Box::new(lower_type(&and.right, scope)?);
    Ok(kernel::Type::Pair {
        left_type,
        right_type,
    })
}

fn lower_type_not(not: &surface::ast::Not, scope: &[surface::ast::Ident]) -> Result<kernel::Type> {
    let argument_type = Box::new(lower_type(&not.operand, scope)?);
    let result_type = Box::new(kernel::Type::False);
    Ok(kernel::Type::Lambda {
        argument_type,
        result_type,
    })
}

fn lower_type_true(_: &surface::ast::True, _: &[surface::ast::Ident]) -> Result<kernel::Type> {
    let argument_type = Box::new(kernel::Type::False);
    let result_type = Box::new(kernel::Type::False);
    Ok(kernel::Type::Lambda {
        argument_type,
        result_type,
    })
}

fn lower_type_false(_: &surface::ast::False, _: &[surface::ast::Ident]) -> Result<kernel::Type> {
    Ok(kernel::Type::False)
}

fn lower_type_atom(
    atom: &surface::ast::Atom,
    scope: &[surface::ast::Ident],
) -> Result<kernel::Type> {
    let name = atom.name.text.clone();

    let mut found = false;
    for ident in scope {
        if ident.text == name {
            found = true;
            break;
        }
    }

    if !found {
        let in_scope: Vec<&str> = scope.iter().map(|ident| ident.text.as_str()).collect();
        return Err(
            Diagnostic::error(format!("unbound proposition {}", name), atom.span)
                .with_note(format!("propositions in scope: {}", in_scope.join(", "))),
        );
    }

    Ok(kernel::Type::Atom { name })
}

pub fn lower_term(
    term: &surface::ast::Term,
    scope: &[surface::ast::Ident],
) -> Result<kernel::Term> {
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

fn lower_term_var(var: &surface::ast::Var, scope: &[surface::ast::Ident]) -> Result<kernel::Term> {
    let name = var.name.text.clone();

    let mut type_arguments = Vec::new();
    for tp in &var.type_arguments {
        type_arguments.push(lower_type(tp, scope)?);
    }

    Ok(kernel::Term::Var {
        name,
        type_arguments,
    })
}

fn lower_term_fun(fun: &surface::ast::Fun, scope: &[surface::ast::Ident]) -> Result<kernel::Term> {
    let argument = fun.argument.text.clone();
    let argument_type = lower_type(&fun.argument_type, scope)?;
    let body = Box::new(lower_term(&fun.body, scope)?);
    Ok(kernel::Term::Lambda {
        argument,
        argument_type,
        body,
    })
}

fn lower_term_app(app: &surface::ast::App, scope: &[surface::ast::Ident]) -> Result<kernel::Term> {
    let function = Box::new(lower_term(&app.function, scope)?);
    let argument = Box::new(lower_term(&app.argument, scope)?);
    Ok(kernel::Term::Application { function, argument })
}

fn lower_term_pair(
    pair: &surface::ast::Pair,
    scope: &[surface::ast::Ident],
) -> Result<kernel::Term> {
    let left = Box::new(lower_term(&pair.left, scope)?);
    let right = Box::new(lower_term(&pair.right, scope)?);
    Ok(kernel::Term::Pair { left, right })
}

fn lower_term_fst(fst: &surface::ast::Fst, scope: &[surface::ast::Ident]) -> Result<kernel::Term> {
    let pair = Box::new(lower_term(&fst.pair, scope)?);
    Ok(kernel::Term::Fst { pair })
}

fn lower_term_snd(snd: &surface::ast::Snd, scope: &[surface::ast::Ident]) -> Result<kernel::Term> {
    let pair = Box::new(lower_term(&snd.pair, scope)?);
    Ok(kernel::Term::Snd { pair })
}

fn lower_term_inl(inl: &surface::ast::Inl, scope: &[surface::ast::Ident]) -> Result<kernel::Term> {
    let right_type = lower_type(&inl.right_type, scope)?;
    let left = Box::new(lower_term(&inl.left, scope)?);
    Ok(kernel::Term::Inl { right_type, left })
}

fn lower_term_inr(inr: &surface::ast::Inr, scope: &[surface::ast::Ident]) -> Result<kernel::Term> {
    let left_type = lower_type(&inr.left_type, scope)?;
    let right = Box::new(lower_term(&inr.right, scope)?);
    Ok(kernel::Term::Inr { left_type, right })
}

fn lower_term_case(
    case: &surface::ast::Case,
    scope: &[surface::ast::Ident],
) -> Result<kernel::Term> {
    let either = Box::new(lower_term(&case.either, scope)?);
    let left_name = case.left_name.text.clone();
    let left_body = Box::new(lower_term(&case.left_body, scope)?);
    let right_name = case.right_name.text.clone();
    let right_body = Box::new(lower_term(&case.right_body, scope)?);
    Ok(kernel::Term::Case {
        either,
        left_name,
        left_body,
        right_name,
        right_body,
    })
}

fn lower_term_absurd(
    absurd: &surface::ast::Absurd,
    scope: &[surface::ast::Ident],
) -> Result<kernel::Term> {
    let goal_type = lower_type(&absurd.goal_type, scope)?;
    let body = Box::new(lower_term(&absurd.body, scope)?);
    Ok(kernel::Term::Absurd { goal_type, body })
}

fn lower_term_trustme(
    trustme: &surface::ast::TrustMe,
    scope: &[surface::ast::Ident],
) -> Result<kernel::Term> {
    let goal_type = lower_type(&trustme.goal_type, scope)?;
    Ok(kernel::Term::TrustMe { goal_type })
}
