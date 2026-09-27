use std::collections::{HashMap, HashSet};
use std::fmt::Display;
use std::rc::Rc;

use crate::diagnostics::{Diagnostic, Result, Span};

#[derive(Debug, Clone, Eq, PartialEq)]
#[allow(unused)]
pub enum Type {
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
    fn substitute(&self, arguments: &HashMap<&str, &Type>) -> Type {
        match self {
            Type::Atom { name } => match arguments.get(name.as_str()) {
                Some(&typ) => typ.clone(),
                None => Type::Atom { name: name.clone() },
            },
            Type::Lambda {
                argument_type,
                result_type,
            } => Type::Lambda {
                argument_type: Box::new(argument_type.substitute(arguments)),
                result_type: Box::new(result_type.substitute(arguments)),
            },
            Type::Pair {
                left_type,
                right_type,
            } => Type::Pair {
                left_type: Box::new(left_type.substitute(arguments)),
                right_type: Box::new(right_type.substitute(arguments)),
            },
            Type::Either {
                left_type,
                right_type,
            } => Type::Either {
                left_type: Box::new(left_type.substitute(arguments)),
                right_type: Box::new(right_type.substitute(arguments)),
            },
            Type::False => Type::False,
        }
    }

    fn free_atoms(&self, out: &mut HashSet<String>) {
        match self {
            Type::Atom { name } => {
                out.insert(name.clone());
            }
            Type::Lambda {
                argument_type,
                result_type,
            } => {
                argument_type.free_atoms(out);
                result_type.free_atoms(out);
            }
            Type::Pair {
                left_type,
                right_type,
            } => {
                left_type.free_atoms(out);
                right_type.free_atoms(out);
            }
            Type::Either {
                left_type,
                right_type,
            } => {
                left_type.free_atoms(out);
                right_type.free_atoms(out);
            }
            Type::False => {}
        }
    }

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
pub struct Scheme {
    // Bound parameter names.
    params: Vec<String>,

    // Type, where atoms refer to names bound in `params`.
    typ: Type,
}

impl Scheme {
    pub fn new(params: Vec<String>, typ: Type) -> Self {
        // Get the set of type parameters
        let params_set: HashSet<String> = params.iter().cloned().collect();

        // Check that we had no duplicates in the list -- the lowering should guarantee this
        if params_set.len() != params.len() {
            panic!("should never have duplicate type parameters in scheme");
        }

        // Get the set of free atoms in the type
        let mut free_atoms_set = HashSet::new();
        typ.free_atoms(&mut free_atoms_set);

        // All free atoms in the type must be bound in the scheme -- the lowering should guarantee
        // this
        if !free_atoms_set.is_subset(&params_set) {
            panic!("should never have unbound atoms in scheme type");
        }

        Self { params, typ }
    }

    fn new_monomorphic(typ: Type) -> Self {
        Self {
            params: Vec::new(),
            typ,
        }
    }

    pub fn instantiate(&self, at: Span, type_arguments: &[Type]) -> Result<Type> {
        // Check the correct number of type arguments have been provided.
        if type_arguments.len() != self.params.len() {
            return Err(Diagnostic::error(
                format!(
                    "expected {} type argument{} but got {}",
                    self.params.len(),
                    if self.params.len() != 1 { "s" } else { "" },
                    type_arguments.len()
                ),
                at,
            ));
        }

        // Substitute the type parameters with the provided types
        let type_arguments: HashMap<&str, &Type> = self
            .params
            .iter()
            .map(|name| name.as_str())
            .zip(type_arguments.iter())
            .collect();
        let substituted_type = self.typ.substitute(&type_arguments);

        Ok(substituted_type)
    }
}

#[derive(Debug, Clone)]
#[allow(unused)]
pub enum Term {
    /// `name [A] [B]`
    ///
    /// Corresponds to a hypothesis or previously proved theorem. Any type parameters are explicitly
    /// annotated to avoid the need for bidirectional type checking for now.
    Var {
        span: Span,
        name: String,
        type_arguments: Vec<Type>,
    },

    /// `fun (x: A) = t`
    ///
    /// Corresponds to implication introduction
    Lambda {
        span: Span,
        argument: String,
        argument_type: Type,
        body: Box<Term>,
    },

    /// `t u`
    ///
    /// Corresponds to implication elimination (modus ponens)
    Application {
        span: Span,
        function: Box<Term>,
        argument: Box<Term>,
    },

    /// `(t, u)`
    ///
    /// Corresponds to conjunction introduction
    Pair {
        span: Span,
        left: Box<Term>,
        right: Box<Term>,
    },

    /// `fst t`
    ///
    /// Corresponds to left conjunction elimination
    Fst { span: Span, pair: Box<Term> },

    /// `snd t`
    ///
    /// Corresponds to right conjunction elimination
    Snd { span: Span, pair: Box<Term> },

    /// `inl [R] t`
    ///
    /// Corresponds to left disjunction introduction. The right type is annotated to avoid the need
    /// for bidirectional inference for now.
    Inl {
        span: Span,
        right_type: Type,
        left: Box<Term>,
    },

    /// `inr [L] t`
    ///
    /// Corresponds to right disjunction introduction. The left type is annotated to avoid the need
    /// for bidirectional inference for now.
    Inr {
        span: Span,
        left_type: Type,
        right: Box<Term>,
    },

    /// `case t of | inl x => u | inr y => v`
    ///
    /// Corresponds to disjunction elimination
    Case {
        span: Span,
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
    Absurd {
        span: Span,
        goal_type: Type,
        body: Box<Term>,
    },

    /// `trustme [A]`
    ///
    /// Corresponds to the assumption that A is true. Used as a placeholder.
    TrustMe { span: Span, goal_type: Type },
}

impl Term {
    fn span(&self) -> Span {
        match self {
            Term::Var { span, .. } => *span,
            Term::Lambda { span, .. } => *span,
            Term::Application { span, .. } => *span,
            Term::Pair { span, .. } => *span,
            Term::Fst { span, .. } => *span,
            Term::Snd { span, .. } => *span,
            Term::Inl { span, .. } => *span,
            Term::Inr { span, .. } => *span,
            Term::Case { span, .. } => *span,
            Term::Absurd { span, .. } => *span,
            Term::TrustMe { span, .. } => *span,
        }
    }
}

/// Whether a proof is complete or relies on a `trustme`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Trust {
    /// Fully checked.
    Proved,
    /// Depends on at least one `trustme`.
    Admitted,
}

impl Trust {
    fn admit(&mut self, other: Trust) {
        if other == Trust::Admitted {
            *self = Trust::Admitted;
        }
    }
}

#[derive(Debug, Clone)]
enum ContextInner {
    Empty,
    Binding {
        name: String,
        scheme: Scheme,
        trust: Trust,
        parent: Rc<ContextInner>,
    },
}

impl ContextInner {
    fn bind(self: Rc<Self>, name: String, scheme: Scheme, trust: Trust) -> Rc<Self> {
        Rc::new(ContextInner::Binding {
            name,
            scheme,
            trust,
            parent: self,
        })
    }

    fn lookup(&self, n: &str) -> Option<(&Scheme, Trust)> {
        match self {
            ContextInner::Empty => None,
            ContextInner::Binding {
                name,
                scheme,
                trust,
                parent,
            } => {
                if name == n {
                    Some((scheme, *trust))
                } else {
                    parent.lookup(n)
                }
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct Context(Rc<ContextInner>);

impl Context {
    pub fn new() -> Self {
        Context(Rc::new(ContextInner::Empty))
    }

    pub fn bind(&self, name: String, scheme: Scheme) -> Self {
        self.bind_with_trust(name, scheme, Trust::Proved)
    }

    pub fn bind_with_trust(&self, name: String, scheme: Scheme, trust: Trust) -> Self {
        Context(self.0.clone().bind(name, scheme, trust))
    }

    pub fn lookup(&self, name: &str) -> Option<(&Scheme, Trust)> {
        self.0.lookup(name)
    }
}

impl Default for Context {
    fn default() -> Self {
        Self::new()
    }
}

fn infer(ctx: &Context, term: &Term, trust: &mut Trust) -> Result<Type> {
    match term {
        Term::Var {
            span,
            name,
            type_arguments,
        } => {
            let (scheme, binding_trust) = ctx
                .lookup(name)
                .ok_or_else(|| Diagnostic::error(format!("Unknown variable {}", name), *span))?;

            // Referring to an admitted theorem taints this proof too.
            trust.admit(binding_trust);

            // Substitute type arguments for type parameters
            scheme.instantiate(*span, type_arguments)
        }

        Term::Lambda {
            span: _,
            argument,
            argument_type,
            body,
        } => {
            let result_type_inferred = infer(
                &ctx.bind(
                    argument.clone(),
                    Scheme::new_monomorphic(argument_type.clone()),
                ),
                body,
                trust,
            )?;
            Ok(Type::Lambda {
                argument_type: Box::new(argument_type.clone()),
                result_type: Box::new(result_type_inferred),
            })
        }

        Term::Application {
            span: _,
            function,
            argument,
        } => {
            let function_type_inferred = infer(ctx, function, trust)?;
            let argument_type_inferred = infer(ctx, argument, trust)?;

            if let Type::Lambda {
                argument_type,
                result_type,
            } = function_type_inferred
            {
                if argument_type_inferred == *argument_type {
                    Ok(*result_type)
                } else {
                    Err(Diagnostic::error(
                        format!(
                            "Incorrect argument type in application: expected {}, but got {}",
                            argument_type, argument_type_inferred
                        ),
                        argument.span(),
                    ))
                }
            } else {
                Err(Diagnostic::error(
                    format!(
                        "Incorrect function type in application: expected function, but got {}",
                        function_type_inferred
                    ),
                    function.span(),
                ))
            }
        }

        Term::Pair {
            span: _,
            left: lhs,
            right: rhs,
        } => Ok(Type::Pair {
            left_type: Box::new(infer(ctx, lhs, trust)?),
            right_type: Box::new(infer(ctx, rhs, trust)?),
        }),

        Term::Fst { span: _, pair } => match infer(ctx, pair, trust)? {
            Type::Pair { left_type, .. } => Ok(*left_type),
            other => Err(Diagnostic::error(
                format!("Incorrect type in fst: expected Pair but got {}", other),
                pair.span(),
            )),
        },

        Term::Snd { span: _, pair } => match infer(ctx, pair, trust)? {
            Type::Pair { right_type, .. } => Ok(*right_type),
            other => Err(Diagnostic::error(
                format!("Incorrect type in snd: expected Pair but got {}", other),
                pair.span(),
            )),
        },

        Term::Inl {
            span: _,
            right_type,
            left,
        } => {
            let left_type_inferred = infer(ctx, left, trust)?;
            Ok(Type::Either {
                left_type: Box::new(left_type_inferred),
                right_type: Box::new(right_type.clone()),
            })
        }

        Term::Inr {
            span: _,
            left_type,
            right,
        } => {
            let right_type_inferred = infer(ctx, right, trust)?;
            Ok(Type::Either {
                left_type: Box::new(left_type.clone()),
                right_type: Box::new(right_type_inferred),
            })
        }

        Term::Case {
            span,
            either,
            left_name,
            left_body,
            right_name,
            right_body,
        } => {
            let either_type = infer(ctx, either, trust)?;
            let (left_type, right_type) = match either_type {
                Type::Either {
                    left_type,
                    right_type,
                } => (left_type, right_type),
                other => {
                    return Err(Diagnostic::error(
                        format!(
                            "Incorrect type in case value: expected Either, but got {}",
                            other
                        ),
                        either.span(),
                    ));
                }
            };

            let left_body_type_inferred = infer(
                &ctx.bind(left_name.clone(), Scheme::new_monomorphic(*left_type)),
                left_body,
                trust,
            )?;

            let right_body_type_inferred = infer(
                &ctx.bind(right_name.clone(), Scheme::new_monomorphic(*right_type)),
                right_body,
                trust,
            )?;

            if left_body_type_inferred == right_body_type_inferred {
                Ok(left_body_type_inferred)
            } else {
                Err(Diagnostic::error(
                    format!(
                        "Mismatched branch types in case: left branch has type {}, but right branch has type {}",
                        left_body_type_inferred, right_body_type_inferred
                    ),
                    *span,
                ))
            }
        }

        Term::Absurd {
            span: _,
            goal_type,
            body,
        } => {
            let body_type = infer(ctx, body, trust)?;
            match body_type {
                Type::False => Ok(goal_type.clone()),
                other => Err(Diagnostic::error(
                    format!(
                        "Incorrect type in absurd: expected False, but got {}",
                        other
                    ),
                    body.span(),
                )),
            }
        }

        Term::TrustMe { span: _, goal_type } => {
            // Infer the requested type, but taint the proof.
            *trust = Trust::Admitted;
            Ok(goal_type.clone())
        }
    }
}

pub fn check(ctx: &Context, term: &Term, scheme: &Scheme) -> Result<Trust> {
    let mut trust = Trust::Proved;
    let term_type_inferred = infer(ctx, term, &mut trust)?;
    if term_type_inferred != scheme.typ {
        return Err(Diagnostic::error(
            format!(
                "Incorrect type: expected {} but got {}",
                scheme.typ, term_type_inferred
            ),
            term.span(),
        ));
    }
    Ok(trust)
}

#[cfg(test)]
mod tests {
    use super::*;

    // Kernel terms are built directly here, so spans don't matter.
    const NO_SPAN: Span = Span { start: 0, end: 0 };

    fn atom(name: &str) -> Type {
        Type::Atom {
            name: name.to_string(),
        }
    }

    fn arrow(argument_type: Type, result_type: Type) -> Type {
        Type::Lambda {
            argument_type: Box::new(argument_type),
            result_type: Box::new(result_type),
        }
    }

    fn and(left_type: Type, right_type: Type) -> Type {
        Type::Pair {
            left_type: Box::new(left_type),
            right_type: Box::new(right_type),
        }
    }

    fn scheme(params: &[&str], typ: Type) -> Scheme {
        Scheme::new(params.iter().map(|p| p.to_string()).collect(), typ)
    }

    fn var(name: &str, type_arguments: Vec<Type>) -> Term {
        Term::Var {
            span: NO_SPAN,
            name: name.to_string(),
            type_arguments,
        }
    }

    fn lam(argument: &str, argument_type: Type, body: Term) -> Term {
        Term::Lambda {
            span: NO_SPAN,
            argument: argument.to_string(),
            argument_type,
            body: Box::new(body),
        }
    }

    fn app(function: Term, argument: Term) -> Term {
        Term::Application {
            span: NO_SPAN,
            function: Box::new(function),
            argument: Box::new(argument),
        }
    }

    fn fst(pair: Term) -> Term {
        Term::Fst {
            span: NO_SPAN,
            pair: Box::new(pair),
        }
    }

    fn trustme(goal_type: Type) -> Term {
        Term::TrustMe {
            span: NO_SPAN,
            goal_type,
        }
    }

    // `swap A B : A and B -> B and A`
    fn swap_scheme() -> Scheme {
        scheme(
            &["A", "B"],
            arrow(and(atom("A"), atom("B")), and(atom("B"), atom("A"))),
        )
    }

    // `id A : A -> A`
    fn id_scheme() -> Scheme {
        scheme(&["A"], arrow(atom("A"), atom("A")))
    }

    fn error_message(result: Result<Trust>) -> String {
        match result {
            Ok(trust) => panic!("expected an error, got {:?}", trust),
            Err(diag) => diag.message,
        }
    }

    #[test]
    fn test_instantiate_is_simultaneous() {
        // Substituting A := B then B := A one at a time would give `A and A -> A and A`.
        let instantiated = swap_scheme()
            .instantiate(NO_SPAN, &[atom("B"), atom("A")])
            .unwrap();
        assert_eq!(
            instantiated,
            arrow(and(atom("B"), atom("A")), and(atom("A"), atom("B")))
        );
    }

    #[test]
    fn test_instantiate_with_compound_type() {
        let a_to_a = arrow(atom("A"), atom("A"));
        let instantiated = id_scheme().instantiate(NO_SPAN, &[a_to_a.clone()]).unwrap();
        assert_eq!(instantiated, arrow(a_to_a.clone(), a_to_a));
    }

    #[test]
    fn test_instantiate_monomorphic() {
        let typ = arrow(Type::False, Type::False);
        let instantiated = scheme(&[], typ.clone()).instantiate(NO_SPAN, &[]).unwrap();
        assert_eq!(instantiated, typ);
    }

    #[test]
    fn test_instantiate_rejects_wrong_arity() {
        let too_few = id_scheme().instantiate(NO_SPAN, &[]).unwrap_err();
        assert_eq!(too_few.message, "expected 1 type argument but got 0");

        let too_many = id_scheme()
            .instantiate(NO_SPAN, &[atom("A"), atom("B")])
            .unwrap_err();
        assert_eq!(too_many.message, "expected 1 type argument but got 2");

        let for_mono = scheme(&[], Type::False)
            .instantiate(NO_SPAN, &[atom("A")])
            .unwrap_err();
        assert_eq!(for_mono.message, "expected 0 type arguments but got 1");
    }

    #[test]
    #[should_panic(expected = "unbound atoms")]
    fn test_scheme_rejects_free_atom() {
        // `ax A : B` would let `B` leak into the context, where a later theorem generalising over
        // its own `B` could capture it.
        scheme(&["A"], arrow(atom("A"), atom("B")));
    }

    #[test]
    #[should_panic(expected = "duplicate")]
    fn test_scheme_rejects_duplicate_parameters() {
        scheme(&["A", "A"], atom("A"));
    }

    #[test]
    fn test_polymorphic_theorem_used_at_swapped_arguments() {
        // theorem t A B : B and A -> A and B := swap [B] [A]
        let ctx = Context::new().bind("swap".to_string(), swap_scheme());
        let goal = scheme(
            &["A", "B"],
            arrow(and(atom("B"), atom("A")), and(atom("A"), atom("B"))),
        );
        let body = var("swap", vec![atom("B"), atom("A")]);
        assert_eq!(check(&ctx, &body, &goal).unwrap(), Trust::Proved);
    }

    #[test]
    fn test_polymorphic_theorem_used_at_compound_type() {
        // theorem t A : (A -> A) -> (A -> A) := id [A -> A]
        let ctx = Context::new().bind("id".to_string(), id_scheme());
        let a_to_a = arrow(atom("A"), atom("A"));
        let goal = scheme(&["A"], arrow(a_to_a.clone(), a_to_a.clone()));
        let body = var("id", vec![a_to_a]);
        assert_eq!(check(&ctx, &body, &goal).unwrap(), Trust::Proved);
    }

    #[test]
    fn test_polymorphic_theorem_used_without_type_arguments() {
        let ctx = Context::new().bind("id".to_string(), id_scheme());
        let goal = scheme(&["A"], arrow(atom("A"), atom("A")));
        let body = var("id", vec![]);
        assert_eq!(
            error_message(check(&ctx, &body, &goal)),
            "expected 1 type argument but got 0"
        );
    }

    #[test]
    fn test_local_variable_with_type_arguments() {
        // fun (x : A) => x [A]
        let goal = scheme(&["A"], arrow(atom("A"), atom("A")));
        let body = lam("x", atom("A"), var("x", vec![atom("A")]));
        assert_eq!(
            error_message(check(&Context::new(), &body, &goal)),
            "expected 0 type arguments but got 1"
        );
    }

    #[test]
    fn test_local_binder_shadows_polymorphic_theorem() {
        // fun (id : A) => id  -- the local `id` is monomorphic, so takes no type arguments.
        let ctx = Context::new().bind("id".to_string(), id_scheme());
        let goal = scheme(&["A"], arrow(atom("A"), atom("A")));
        let body = lam("id", atom("A"), var("id", vec![]));
        assert_eq!(check(&ctx, &body, &goal).unwrap(), Trust::Proved);
    }

    #[test]
    fn test_parameters_are_rigid() {
        // theorem bad A B : A -> B := fun (x : A) => x
        let goal = scheme(&["A", "B"], arrow(atom("A"), atom("B")));
        let body = lam("x", atom("A"), var("x", vec![]));
        assert!(check(&Context::new(), &body, &goal).is_err());
    }

    #[test]
    fn test_instantiation_cannot_prove_false() {
        // With `id A : A -> A`, instantiating at False gives `False -> False`, never `False`.
        let ctx = Context::new().bind("id".to_string(), id_scheme());
        let goal = scheme(&[], Type::False);
        let body = var("id", vec![Type::False]);
        assert!(check(&ctx, &body, &goal).is_err());
    }

    #[test]
    fn test_rejects_ill_typed_eliminations() {
        let goal = scheme(&["A"], arrow(atom("A"), atom("A")));

        // fun (x : A) => fst x
        let body = lam("x", atom("A"), fst(var("x", vec![])));
        assert!(check(&Context::new(), &body, &goal).is_err());

        // fun (x : A) => x x
        let body = lam("x", atom("A"), app(var("x", vec![]), var("x", vec![])));
        assert!(check(&Context::new(), &body, &goal).is_err());

        // fun (x : A) => absurd [A] x
        let body = lam(
            "x",
            atom("A"),
            Term::Absurd {
                span: NO_SPAN,
                goal_type: atom("A"),
                body: Box::new(var("x", vec![])),
            },
        );
        assert!(check(&Context::new(), &body, &goal).is_err());
    }

    #[test]
    fn test_unknown_variable() {
        let goal = scheme(&[], Type::False);
        assert_eq!(
            error_message(check(&Context::new(), &var("nope", vec![]), &goal)),
            "Unknown variable nope"
        );
    }

    #[test]
    fn test_trustme_is_admitted() {
        let goal = scheme(&[], Type::False);
        assert_eq!(
            check(&Context::new(), &trustme(Type::False), &goal).unwrap(),
            Trust::Admitted
        );
    }

    #[test]
    fn test_admitted_theorem_taints_users() {
        let goal = scheme(&["A"], arrow(atom("A"), atom("A")));
        let body = var("id", vec![atom("A")]);

        let proved = Context::new().bind_with_trust("id".to_string(), id_scheme(), Trust::Proved);
        assert_eq!(check(&proved, &body, &goal).unwrap(), Trust::Proved);

        let admitted =
            Context::new().bind_with_trust("id".to_string(), id_scheme(), Trust::Admitted);
        assert_eq!(check(&admitted, &body, &goal).unwrap(), Trust::Admitted);
    }
}
