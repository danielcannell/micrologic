pub mod surface;
pub mod diagnostics;
pub mod kernel;

use std::path::PathBuf;

use clap::Parser;

fn lower_type(typ: &surface::ast::Type) -> kernel::Type {
    match typ {
        surface::ast::Type::Lambda(lambda) => { lower_type_lambda(lambda) }
        surface::ast::Type::Or(or) => { lower_type_or(or) }
        surface::ast::Type::And(and) => { lower_type_and(and) }
        surface::ast::Type::Not(not) => { lower_type_not(not) }
        surface::ast::Type::True(t) => { lower_type_true(t) }
        surface::ast::Type::False(f) => { lower_type_false(f) }
        surface::ast::Type::Atom(atom) => { lower_type_atom(atom) }
    }
}

fn lower_type_lambda(lambda: &surface::ast::Lambda) -> kernel::Type {
    let argument_type = Box::new(lower_type(&lambda.argument_type));
    let result_type = Box::new(lower_type(&lambda.result_type));
    kernel::Type::Lambda { argument_type, result_type }
}

fn lower_type_or(or: &surface::ast::Or) -> kernel::Type {
    let left_type = Box::new(lower_type(&or.left));
    let right_type = Box::new(lower_type(&or.right));
    kernel::Type::Either { left_type, right_type }
}

fn lower_type_and(and: &surface::ast::And) -> kernel::Type {
    let left_type = Box::new(lower_type(&and.left));
    let right_type = Box::new(lower_type(&and.right));
    kernel::Type::Pair { left_type, right_type }
}

fn lower_type_not(not: &surface::ast::Not) -> kernel::Type {
    let argument_type = Box::new(lower_type(&not.operand));
    let result_type = Box::new(kernel::Type::False);
    kernel::Type::Lambda { argument_type, result_type }
}

fn lower_type_true(_: &surface::ast::True) -> kernel::Type {
    let argument_type = Box::new(kernel::Type::False);
    let result_type = Box::new(kernel::Type::False);
    kernel::Type::Lambda { argument_type, result_type }
}

fn lower_type_false(_: &surface::ast::False) -> kernel::Type {
    kernel::Type::False
}

fn lower_type_atom(atom: &surface::ast::Atom) -> kernel::Type {
    let name = atom.name.text.clone();
    kernel::Type::Atom { name }
}

fn lower_term(term: &surface::ast::Term) -> kernel::Term {
    match term {
        surface::ast::Term::Var(var) => { lower_term_var(var) }
        surface::ast::Term::Fun(fun) => { lower_term_fun(fun) }
        surface::ast::Term::App(app) => { lower_term_app(app) }
        surface::ast::Term::Pair(pair) => { lower_term_pair(pair) }
        surface::ast::Term::Fst(fst) => { lower_term_fst(fst) }
        surface::ast::Term::Snd(snd) => { lower_term_snd(snd) }
        surface::ast::Term::Inl(inl) => { lower_term_inl(inl) }
        surface::ast::Term::Inr(inr) => { lower_term_inr(inr) }
        surface::ast::Term::Case(case) => { lower_term_case(case) }
        surface::ast::Term::Absurd(absurd) => { lower_term_absurd(absurd) }
        surface::ast::Term::TrustMe(trustme) => { lower_term_trustme(trustme) }
    }
}

fn lower_term_var(var: &surface::ast::Var) -> kernel::Term {
    let name = var.name.text.clone();
    kernel::Term::Var { name }
}

fn lower_term_fun(fun: &surface::ast::Fun) -> kernel::Term {
    let argument = fun.argument.text.clone();
    let argument_type = lower_type(&fun.argument_type);
    let body = Box::new(lower_term(&fun.body));
    kernel::Term::Lambda { argument, argument_type, body }
}

fn lower_term_app(app: &surface::ast::App) -> kernel::Term {
    let function = Box::new(lower_term(&app.function));
    let argument = Box::new(lower_term(&app.argument));
    kernel::Term::Application { function, argument }
}

fn lower_term_pair(pair: &surface::ast::Pair) -> kernel::Term {
    let left = Box::new(lower_term(&pair.left));
    let right = Box::new(lower_term(&pair.right));
    kernel::Term::Pair { left, right }
}

fn lower_term_fst(fst: &surface::ast::Fst) -> kernel::Term {
    let pair = Box::new(lower_term(&fst.pair));
    kernel::Term::Fst { pair }
}

fn lower_term_snd(snd: &surface::ast::Snd) -> kernel::Term {
    let pair = Box::new(lower_term(&snd.pair));
    kernel::Term::Snd { pair }
}

fn lower_term_inl(inl: &surface::ast::Inl) -> kernel::Term {
    let right_type = lower_type(&inl.right_type);
    let left = Box::new(lower_term(&inl.left));
    kernel::Term::Inl { right_type, left }
}

fn lower_term_inr(inr: &surface::ast::Inr) -> kernel::Term {
    let left_type = lower_type(&inr.left_type);
    let right = Box::new(lower_term(&inr.right));
    kernel::Term::Inr { left_type, right }
}

fn lower_term_case(case: &surface::ast::Case) -> kernel::Term {
    let either = Box::new(lower_term(&case.either));
    let left_name = case.left_name.text.clone();
    let left_body = Box::new(lower_term(&case.left_body));
    let right_name = case.right_name.text.clone();
    let right_body = Box::new(lower_term(&case.right_body));
    kernel::Term::Case { either, left_name, left_body, right_name, right_body }
}

fn lower_term_absurd(absurd: &surface::ast::Absurd) -> kernel::Term {
    let goal_type = lower_type(&absurd.goal_type);
    let body = Box::new(lower_term(&absurd.body));
    kernel::Term::Absurd { goal_type, body }
}

fn lower_term_trustme(trustme: &surface::ast::TrustMe) -> kernel::Term {
    let goal_type = lower_type(&trustme.goal_type);
    kernel::Term::TrustMe { goal_type }
}

#[derive(Parser)]
struct Args {
    /// Source file to check
    source_file: PathBuf,
}

fn main() {
    let args = Args::parse();

    let source = std::fs::read_to_string(&args.source_file).expect("Could not read source file");

    let module = match surface::parse(&source) {
        Ok(module) => module,
        Err(diag) => { diag.emit(&source); std::process::exit(1); }
    };

    let mut ctx = kernel::Context::new();

    for item in &module.items {
        match item {
            surface::ast::Item::Axiom(axiom) => {
                let typ = lower_type(&axiom.typ);
                println!("axiom {} : {}", axiom.name.text, typ);
                ctx = ctx.bind(axiom.name.text.clone(), typ);
            }
            surface::ast::Item::Theorem(theorem) => {
                let typ = lower_type(&theorem.typ);
                let body = lower_term(&theorem.body);
                match kernel::check(&ctx, &body, typ.clone()) {
                    Ok(()) => {
                        println!("ok {} : {}", theorem.name.text, typ);
                    }
                    Err(err) => {
                        println!("err {} : {}", theorem.name.text, err);
                    }
                }
                ctx = ctx.bind(theorem.name.text.clone(), typ);
            }
        }
    }
}
