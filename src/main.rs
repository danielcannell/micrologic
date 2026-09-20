// Not yet consumed by `main`; the lowering pass will use it.
#[allow(dead_code)]
pub mod surface;
pub mod diagnostics;

use std::fmt::Display;
use std::path::PathBuf;
use std::rc::Rc;

use clap::Parser;

#[derive(Debug, Clone, Eq, PartialEq)]
#[allow(unused)]
enum Type {
    // `A`
    //
    // Corresponds to a proposition
    Atom {
        name: String,
    },

    // `A -> B`
    //
    // Corresponds to implication
    Lambda {
        argument_type: Box<Type>,
        result_type: Box<Type>,
    },

    // `Pair A B`
    //
    // Corresponds to conjunction
    Pair {
        left_type: Box<Type>,
        right_type: Box<Type>,
    },

    // `Either A B`
    //
    // Corresponds to disjunction
    Either {
        left_type: Box<Type>,
        right_type: Box<Type>,
    },

    // `False`
    //
    // Corresponds to false. True is represented as `False -> False`
    False,
}

impl Type {
    fn fmt_at_prec(&self, f: &mut std::fmt::Formatter<'_>, prec: u8) -> std::fmt::Result {
        let this_prec = match self {
            Type::Atom { .. } => 2,
            Type::Lambda { .. } => 1,
            Type::Pair { .. } => 1,
            Type::Either { .. } => 1,
            Type::False => 2,
        };

        if this_prec < prec {
            write!(f, "(")?;
        }

        match self {
            Type::Atom { name } => write!(f, "{}", name)?,

            Type::Lambda {
                argument_type,
                result_type,
            } => {
                argument_type.fmt_at_prec(f, this_prec + 1)?;
                write!(f, " -> ")?;
                result_type.fmt_at_prec(f, this_prec)?;
            }

            Type::Pair {
                left_type,
                right_type,
            } => {
                write!(f, "Pair ")?;
                left_type.fmt_at_prec(f, this_prec + 1)?;
                write!(f, " ")?;
                right_type.fmt_at_prec(f, this_prec + 1)?;
            }

            Type::Either {
                left_type,
                right_type,
            } => {
                write!(f, "Either ")?;
                left_type.fmt_at_prec(f, this_prec + 1)?;
                write!(f, " ")?;
                right_type.fmt_at_prec(f, this_prec + 1)?;
            }

            Type::False => write!(f, "false")?,
        }

        if this_prec < prec {
            write!(f, ")")?;
        }

        Ok(())
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_at_prec(f, 0)
    }
}

#[derive(Debug, Clone)]
#[allow(unused)]
enum Term {
    /// `name`
    ///
    /// Corresponds to a hypothesis or previously proved theorem
    Var { name: String },

    /// `fun (x: A) = t`
    ///
    /// Corresponds to implication introduction
    Lambda {
        argument: String,
        argument_type: Type,
        body: Box<Term>,
    },

    /// `t u`
    ///
    /// Corresponds to implication elimination (modus ponens)
    Application {
        function: Box<Term>,
        argument: Box<Term>,
    },

    /// `(t, u)`
    ///
    /// Corresponds to conjunction introduction
    Pair { left: Box<Term>, right: Box<Term> },

    /// `fst t`
    ///
    /// Corresponds to left conjunction elimination
    Fst { pair: Box<Term> },

    /// `snd t`
    ///
    /// Corresponds to right conjunction elimination
    Snd { pair: Box<Term> },

    /// `inl [R] t`
    ///
    /// Corresponds to left disjunction introduction. The right type is annotated to avoid the need
    /// for bidirectional inference for now.
    Inl { right_type: Type, left: Box<Term> },

    /// `inr [L] t`
    ///
    /// Corresponds to right disjunction introduction. The left type is annotated to avoid the need
    /// for bidirectional inference for now.
    Inr { left_type: Type, right: Box<Term> },

    /// `case t of | inl x => u | inr y => v`
    ///
    /// Corresponds to disjunction elimination
    Case {
        either: Box<Term>,
        left_name: String,
        left_body: Box<Term>,
        right_name: String,
        right_body: Box<Term>,
    },

    /// `absurd [C] t`
    ///
    /// Corresponds to false elimination. The goal type is annotated to avoid the need for
    /// bidirectional inference for now.
    Absurd { goal_type: Type, body: Box<Term> },
}

#[derive(Debug, Clone)]
enum ContextInner {
    Empty,
    Binding {
        name: String,
        typ: Type,
        parent: Rc<ContextInner>,
    },
}

impl ContextInner {
    fn bind(self: Rc<Self>, name: String, typ: Type) -> Rc<Self> {
        Rc::new(ContextInner::Binding {
            name,
            typ,
            parent: self,
        })
    }

    fn lookup(&self, n: &str) -> Option<Type> {
        match self {
            ContextInner::Empty => None,
            ContextInner::Binding { name, typ, parent } => {
                if name == n {
                    Some(typ.clone())
                } else {
                    parent.lookup(n)
                }
            }
        }
    }
}

#[derive(Debug, Clone)]
struct Context(Rc<ContextInner>);

impl Context {
    fn new() -> Self {
        Context(Rc::new(ContextInner::Empty))
    }

    fn bind(&self, name: String, typ: Type) -> Self {
        Context(self.0.clone().bind(name, typ))
    }

    fn lookup(&self, name: &str) -> Option<Type> {
        self.0.lookup(name)
    }
}

fn infer(ctx: &Context, term: &Term) -> Result<Type, String> {
    match term {
        Term::Var { name } => ctx
            .lookup(name)
            .ok_or_else(|| format!("Unknown variable {}", name)),

        Term::Lambda {
            argument,
            argument_type,
            body,
        } => {
            let result_type_inferred =
                infer(&ctx.bind(argument.clone(), argument_type.clone()), body)?;
            Ok(Type::Lambda {
                argument_type: Box::new(argument_type.clone()),
                result_type: Box::new(result_type_inferred),
            })
        }

        Term::Application { function, argument } => {
            let function_type_inferred = infer(ctx, function)?;
            let argument_type_inferred = infer(ctx, argument)?;

            if let Type::Lambda {
                argument_type,
                result_type,
            } = function_type_inferred
            {
                if argument_type_inferred == *argument_type {
                    Ok(*result_type)
                } else {
                    Err(format!(
                        "Incorrect argument type in application: expected {}, but got {}",
                        argument_type, argument_type_inferred
                    ))
                }
            } else {
                Err(format!(
                    "Incorrect function type in application: expected function, but got {}",
                    function_type_inferred
                ))
            }
        }

        Term::Pair {
            left: lhs,
            right: rhs,
        } => Ok(Type::Pair {
            left_type: Box::new(infer(ctx, lhs)?),
            right_type: Box::new(infer(ctx, rhs)?),
        }),

        Term::Fst { pair } => match infer(ctx, pair)? {
            Type::Pair { left_type, .. } => Ok(*left_type),
            other => Err(format!(
                "Incorrect type in fst: expected Pair but got {}",
                other
            )),
        },

        Term::Snd { pair } => match infer(ctx, pair)? {
            Type::Pair { right_type, .. } => Ok(*right_type),
            other => Err(format!(
                "Incorrect type in snd: expected Pair but got {}",
                other
            )),
        },

        Term::Inl { right_type, left } => {
            let left_type_inferred = infer(ctx, left)?;
            Ok(Type::Either {
                left_type: Box::new(left_type_inferred),
                right_type: Box::new(right_type.clone()),
            })
        }

        Term::Inr { left_type, right } => {
            let right_type_inferred = infer(ctx, right)?;
            Ok(Type::Either {
                left_type: Box::new(left_type.clone()),
                right_type: Box::new(right_type_inferred),
            })
        }

        Term::Case {
            either,
            left_name,
            left_body,
            right_name,
            right_body,
        } => {
            let either_type = infer(ctx, either)?;
            let (left_type, right_type) = match either_type {
                Type::Either {
                    left_type,
                    right_type,
                } => (left_type, right_type),
                other => {
                    return Err(format!(
                        "Incorrect type in case value: expected Either, but got {}",
                        other
                    ));
                }
            };

            let left_body_type_inferred =
                infer(&ctx.bind(left_name.clone(), *left_type), left_body)?;

            let right_body_type_inferred =
                infer(&ctx.bind(right_name.clone(), *right_type), right_body)?;

            if left_body_type_inferred == right_body_type_inferred {
                Ok(left_body_type_inferred)
            } else {
                Err(format!(
                    "Mismatched branch types in case: left branch has type {}, but right branch has type {}",
                    left_body_type_inferred, right_body_type_inferred
                ))
            }
        }

        Term::Absurd { goal_type, body } => {
            let body_type = infer(ctx, body)?;
            match body_type {
                Type::False => Ok(goal_type.clone()),
                other => Err(format!(
                    "Incorrect type in absurd: expected False, but got {}",
                    other
                )),
            }
        }
    }
}

fn check(ctx: &Context, term: &Term, term_type: Type) -> Result<(), String> {
    let term_type_inferred = infer(ctx, term)?;
    if term_type_inferred != term_type {
        return Err(format!(
            "Incorrect type: expected {} but got {}",
            term_type, term_type_inferred
        ));
    }
    Ok(())
}

fn lower_type(typ: &surface::ast::Type) -> Type {
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

fn lower_type_lambda(lambda: &surface::ast::Lambda) -> Type {
    let argument_type = Box::new(lower_type(&lambda.argument_type));
    let result_type = Box::new(lower_type(&lambda.result_type));
    Type::Lambda { argument_type, result_type }
}

fn lower_type_or(or: &surface::ast::Or) -> Type {
    let left_type = Box::new(lower_type(&or.left));
    let right_type = Box::new(lower_type(&or.right));
    Type::Either { left_type, right_type }
}

fn lower_type_and(and: &surface::ast::And) -> Type {
    let left_type = Box::new(lower_type(&and.left));
    let right_type = Box::new(lower_type(&and.right));
    Type::Pair { left_type, right_type }
}

fn lower_type_not(not: &surface::ast::Not) -> Type {
    let argument_type = Box::new(lower_type(&not.operand));
    let result_type = Box::new(Type::False);
    Type::Lambda { argument_type, result_type }
}

fn lower_type_true(_: &surface::ast::True) -> Type {
    let argument_type = Box::new(Type::False);
    let result_type = Box::new(Type::False);
    Type::Lambda { argument_type, result_type }
}

fn lower_type_false(_: &surface::ast::False) -> Type {
    Type::False
}

fn lower_type_atom(atom: &surface::ast::Atom) -> Type {
    let name = atom.name.text.clone();
    Type::Atom { name }
}

fn lower_term(term: &surface::ast::Term) -> Term {
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
    }
}

fn lower_term_var(var: &surface::ast::Var) -> Term {
    let name = var.name.text.clone();
    Term::Var { name }
}

fn lower_term_fun(fun: &surface::ast::Fun) -> Term {
    let argument = fun.argument.text.clone();
    let argument_type = lower_type(&fun.argument_type);
    let body = Box::new(lower_term(&fun.body));
    Term::Lambda { argument, argument_type, body }
}

fn lower_term_app(app: &surface::ast::App) -> Term {
    let function = Box::new(lower_term(&app.function));
    let argument = Box::new(lower_term(&app.argument));
    Term::Application { function, argument }
}

fn lower_term_pair(pair: &surface::ast::Pair) -> Term {
    let left = Box::new(lower_term(&pair.left));
    let right = Box::new(lower_term(&pair.right));
    Term::Pair { left, right }
}

fn lower_term_fst(fst: &surface::ast::Fst) -> Term {
    let pair = Box::new(lower_term(&fst.pair));
    Term::Fst { pair }
}

fn lower_term_snd(snd: &surface::ast::Snd) -> Term {
    let pair = Box::new(lower_term(&snd.pair));
    Term::Snd { pair }
}

fn lower_term_inl(inl: &surface::ast::Inl) -> Term {
    let right_type = lower_type(&inl.right_type);
    let left = Box::new(lower_term(&inl.left));
    Term::Inl { right_type, left }
}

fn lower_term_inr(inr: &surface::ast::Inr) -> Term {
    let left_type = lower_type(&inr.left_type);
    let right = Box::new(lower_term(&inr.right));
    Term::Inr { left_type, right }
}

fn lower_term_case(case: &surface::ast::Case) -> Term {
    let either = Box::new(lower_term(&case.either));
    let left_name = case.left_name.text.clone();
    let left_body = Box::new(lower_term(&case.left_body));
    let right_name = case.right_name.text.clone();
    let right_body = Box::new(lower_term(&case.right_body));
    Term::Case { either, left_name, left_body, right_name, right_body }
}

fn lower_term_absurd(absurd: &surface::ast::Absurd) -> Term {
    let goal_type = lower_type(&absurd.goal_type);
    let body = Box::new(lower_term(&absurd.body));
    Term::Absurd { goal_type, body }
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

    let mut ctx = Context::new();

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
                match check(&ctx, &body, typ.clone()) {
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
