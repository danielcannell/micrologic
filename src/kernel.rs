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

    /// Print in surface syntax, recovering the sugar that lowering removed, so that messages
    /// show `not A` rather than `A -> False`. Aliases can't be recovered: they are fully expanded.
    ///
    /// Precedence levels match the parser: `<->` (0) < `->` (1) < `or` (2) < `and` (3) < `not`
    /// (4) < atoms (5). The binary operators are right-associative.
    fn fmt_at_prec(&self, f: &mut std::fmt::Formatter<'_>, prec: u8) -> std::fmt::Result {
        let this_prec = match self {
            _ if self.as_true() => 5,
            _ if self.as_equiv().is_some() => 0,
            _ if self.as_not().is_some() => 4,
            Type::Atom { .. } | Type::False => 5,
            Type::Lambda { .. } => 1,
            Type::Either { .. } => 2,
            Type::Pair { .. } => 3,
        };

        if this_prec < prec {
            write!(f, "(")?;
        }

        if self.as_true() {
            write!(f, "True")?;
        } else if let Some((left, right)) = self.as_equiv() {
            left.fmt_at_prec(f, this_prec + 1)?;
            write!(f, " <-> ")?;
            right.fmt_at_prec(f, this_prec)?;
        } else if let Some(operand) = self.as_not() {
            write!(f, "not ")?;
            operand.fmt_at_prec(f, this_prec)?;
        } else {
            match self {
                Type::Atom { name } => write!(f, "{}", name)?,
                Type::False => write!(f, "False")?,
                Type::Lambda {
                    argument_type: left,
                    result_type: right,
                }
                | Type::Either {
                    left_type: left,
                    right_type: right,
                }
                | Type::Pair {
                    left_type: left,
                    right_type: right,
                } => {
                    let operator = match self {
                        Type::Lambda { .. } => "->",
                        Type::Either { .. } => "or",
                        _ => "and",
                    };
                    left.fmt_at_prec(f, this_prec + 1)?;
                    write!(f, " {operator} ")?;
                    right.fmt_at_prec(f, this_prec)?;
                }
            }
        }

        if this_prec < prec {
            write!(f, ")")?;
        }

        Ok(())
    }

    /// `False -> False`, which lowering produces for `True`.
    fn as_true(&self) -> bool {
        matches!(
            self,
            Type::Lambda { argument_type, result_type }
                if **argument_type == Type::False && **result_type == Type::False
        )
    }

    /// `A -> False`, which lowering produces for `not A`.
    fn as_not(&self) -> Option<&Type> {
        match self {
            Type::Lambda {
                argument_type,
                result_type,
            } if **result_type == Type::False => Some(argument_type),
            _ => None,
        }
    }

    /// `(A -> B) and (B -> A)`, which lowering produces for `A <-> B`.
    fn as_equiv(&self) -> Option<(&Type, &Type)> {
        let Type::Pair {
            left_type,
            right_type,
        } = self
        else {
            return None;
        };
        match (&**left_type, &**right_type) {
            (
                Type::Lambda {
                    argument_type: a,
                    result_type: b,
                },
                Type::Lambda {
                    argument_type: b2,
                    result_type: a2,
                },
            ) if a == a2 && b == b2 => Some((a, b)),
            _ => None,
        }
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

    /// The names of the parameters, in declaration order.
    pub fn params(&self) -> &[String] {
        &self.params
    }

    /// Substitute `type_arguments` for the parameters, simultaneously.
    pub fn instantiate(&self, type_arguments: &[Type]) -> std::result::Result<Type, ArityMismatch> {
        if type_arguments.len() != self.params.len() {
            return Err(ArityMismatch {
                expected: self.params.len(),
                found: type_arguments.len(),
            });
        }

        let type_arguments: HashMap<&str, &Type> = self
            .params
            .iter()
            .map(|name| name.as_str())
            .zip(type_arguments.iter())
            .collect();
        Ok(self.typ.substitute(&type_arguments))
    }
}

/// A scheme was instantiated with the wrong number of arguments. Callers turn this into a
/// diagnostic, since only they know what was being instantiated.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ArityMismatch {
    pub expected: usize,
    pub found: usize,
}

/// `count(1, "argument")` is "1 argument", `count(0, "argument")` is "no arguments".
pub fn count(n: usize, noun: &str) -> String {
    match n {
        0 => format!("no {noun}s"),
        1 => format!("1 {noun}"),
        _ => format!("{n} {noun}s"),
    }
}

/// `["A", "B"]` becomes "`A`, `B`".
pub fn quoted_list(names: &[String]) -> String {
    let quoted: Vec<String> = names.iter().map(|name| format!("`{name}`")).collect();
    quoted.join(", ")
}

/// "was" or "were", to agree with `count(n, ..)`.
pub fn was_were(n: usize) -> &'static str {
    if n == 1 { "was" } else { "were" }
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
    pub fn span(&self) -> Span {
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
            let (scheme, binding_trust) = ctx.lookup(name).ok_or_else(|| {
                Diagnostic::error(format!("cannot find `{name}` in this scope"), *span)
                    .with_primary_label("not a hypothesis, theorem or axiom")
            })?;

            // Referring to an admitted theorem taints this proof too.
            trust.admit(binding_trust);

            // Substitute type arguments for type parameters
            scheme
                .instantiate(type_arguments)
                .map_err(|mismatch| type_arity_error(name, scheme, mismatch, *span))
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
                            "mismatched argument: expected `{argument_type}`, found `{argument_type_inferred}`"
                        ),
                        argument.span(),
                    )
                    .with_primary_label(format!("this has type `{argument_type_inferred}`"))
                    .with_label(
                        function.span(),
                        format!(
                            "this has type `{}`",
                            Type::Lambda {
                                argument_type,
                                result_type
                            }
                        ),
                    ))
                }
            } else {
                Err(Diagnostic::error(
                    format!("cannot apply a proof of `{function_type_inferred}` to an argument"),
                    function.span(),
                )
                .with_primary_label(format!(
                    "this has type `{function_type_inferred}`, which is not an implication"
                ))
                .with_label(argument.span(), "argument supplied here"))
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
            other => Err(
                Diagnostic::error("`fst` expects a proof of a conjunction", pair.span())
                    .with_primary_label(format!("this has type `{other}`")),
            ),
        },

        Term::Snd { span: _, pair } => match infer(ctx, pair, trust)? {
            Type::Pair { right_type, .. } => Ok(*right_type),
            other => Err(
                Diagnostic::error("`snd` expects a proof of a conjunction", pair.span())
                    .with_primary_label(format!("this has type `{other}`")),
            ),
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
            span: _,
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
                        "`case` expects a proof of a disjunction",
                        either.span(),
                    )
                    .with_primary_label(format!("this has type `{other}`")));
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
                Err(
                    Diagnostic::error("`case` branches have different types", right_body.span())
                        .with_primary_label(format!(
                            "this branch has type `{right_body_type_inferred}`"
                        ))
                        .with_label(
                            left_body.span(),
                            format!("but this branch has type `{left_body_type_inferred}`"),
                        ),
                )
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
                other => Err(
                    Diagnostic::error("`absurd` expects a proof of `False`", body.span())
                        .with_primary_label(format!("this has type `{other}`")),
                ),
            }
        }

        Term::TrustMe { span: _, goal_type } => {
            // Infer the requested type, but taint the proof.
            *trust = Trust::Admitted;
            Ok(goal_type.clone())
        }
    }
}

/// A `Var` was given the wrong number of type arguments. Public so the tactic elaborator can word
/// the same mistake the same way.
pub fn type_arity_error(
    name: &str,
    scheme: &Scheme,
    mismatch: ArityMismatch,
    at: Span,
) -> Diagnostic {
    let ArityMismatch { expected, found } = mismatch;
    let diag = if expected == 0 {
        Diagnostic::error(format!("`{name}` takes no type arguments"), at)
            .with_primary_label(format!("{} supplied", count(found, "type argument")))
    } else {
        Diagnostic::error(
            format!(
                "`{name}` takes {} but {found} {} supplied",
                count(expected, "type argument"),
                was_were(found)
            ),
            at,
        )
        .with_primary_label(format!("expected {}", count(expected, "type argument")))
    };

    if expected == 0 {
        diag
    } else {
        let placeholders: Vec<String> = scheme.params().iter().map(|p| format!("[{p}]")).collect();
        diag.with_note(format!(
            "`{name}` has type parameters {}; supply one type for each: `{name} {}`",
            quoted_list(scheme.params()),
            placeholders.join(" ")
        ))
    }
}

/// Check that `term` proves `scheme`, whose statement is written at `statement`.
///
/// Returns whether the proof is complete or relies on a `trustme`.
pub fn check(ctx: &Context, term: &Term, scheme: &Scheme, statement: Span) -> Result<Trust> {
    let mut trust = Trust::Proved;
    let why = Expectation {
        span: statement,
        reason: "expected because of this statement",
    };
    check_against(ctx, term, &scheme.typ, why, &mut trust)?;
    Ok(trust)
}

/// Where an expected type came from, shown as a secondary label on a mismatch: usually the theorem's
/// statement, but inside `absurd [C] t` the expected `False` comes from the `absurd`.
#[derive(Debug, Clone, Copy)]
struct Expectation {
    span: Span,
    reason: &'static str,
}

/// Check `term` against an `expected` type.
///
/// This is equivalent to inferring the type and comparing it with `expected`, but pushes the
/// expected type into lambdas, pairs, injections, `case` branches and `absurd` so that a mismatch
/// is reported at the innermost sub-term that is wrong, rather than at the whole proof. `why` says
/// where the expected type came from.
fn check_against(
    ctx: &Context,
    term: &Term,
    expected: &Type,
    why: Expectation,
    trust: &mut Trust,
) -> Result<()> {
    match (term, expected) {
        (
            Term::Lambda {
                span,
                argument,
                argument_type,
                body,
            },
            Type::Lambda {
                argument_type: expected_argument_type,
                result_type: expected_result_type,
            },
        ) => {
            if argument_type != &**expected_argument_type {
                return Err(Diagnostic::error(
                    format!("hypothesis `{argument}` has the wrong type"),
                    *span,
                )
                .with_primary_label(format!(
                    "`{argument}` is declared as `{argument_type}`, but `{expected_argument_type}` is expected"
                ))
                .with_label(why.span, why.reason));
            }
            let ctx = ctx.bind(
                argument.clone(),
                Scheme::new_monomorphic(argument_type.clone()),
            );
            check_against(&ctx, body, expected_result_type, why, trust)
        }

        (
            Term::Pair { left, right, .. },
            Type::Pair {
                left_type,
                right_type,
            },
        ) => {
            check_against(ctx, left, left_type, why, trust)?;
            check_against(ctx, right, right_type, why, trust)
        }

        (
            Term::Inl {
                span,
                right_type,
                left,
            },
            Type::Either {
                left_type: expected_left_type,
                right_type: expected_right_type,
            },
        ) => {
            if right_type != &**expected_right_type {
                return Err(wrong_injection_annotation(
                    "inl",
                    "right",
                    right_type,
                    expected_right_type,
                    *span,
                    why,
                ));
            }
            check_against(ctx, left, expected_left_type, why, trust)
        }

        (
            Term::Inr {
                span,
                left_type,
                right,
            },
            Type::Either {
                left_type: expected_left_type,
                right_type: expected_right_type,
            },
        ) => {
            if left_type != &**expected_left_type {
                return Err(wrong_injection_annotation(
                    "inr",
                    "left",
                    left_type,
                    expected_left_type,
                    *span,
                    why,
                ));
            }
            check_against(ctx, right, expected_right_type, why, trust)
        }

        (
            Term::Case {
                either,
                left_name,
                left_body,
                right_name,
                right_body,
                ..
            },
            _,
        ) => {
            let (left_type, right_type) = match infer(ctx, either, trust)? {
                Type::Either {
                    left_type,
                    right_type,
                } => (left_type, right_type),
                other => {
                    return Err(Diagnostic::error(
                        "`case` expects a proof of a disjunction",
                        either.span(),
                    )
                    .with_primary_label(format!("this has type `{other}`")));
                }
            };
            let left_ctx = ctx.bind(left_name.clone(), Scheme::new_monomorphic(*left_type));
            check_against(&left_ctx, left_body, expected, why, trust)?;
            let right_ctx = ctx.bind(right_name.clone(), Scheme::new_monomorphic(*right_type));
            check_against(&right_ctx, right_body, expected, why, trust)
        }

        (
            Term::Absurd {
                span,
                goal_type,
                body,
            },
            _,
        ) => {
            // The annotation must be the expected type, exactly as inferring `absurd [C] t` (which
            // gives `C`) and comparing would require.
            if goal_type != expected {
                return Err(
                    Diagnostic::error("`absurd` is annotated with the wrong type", *span)
                        .with_primary_label(format!(
                            "annotated as `{goal_type}`, but `{expected}` is expected"
                        ))
                        .with_label(why.span, why.reason),
                );
            }
            let why = Expectation {
                span: *span,
                reason: "this needs a proof of `False`",
            };
            check_against(ctx, body, &Type::False, why, trust)
        }

        _ => {
            let inferred = infer(ctx, term, trust)?;
            if inferred == *expected {
                Ok(())
            } else {
                Err(Diagnostic::error(
                    format!("mismatched types: expected `{expected}`, found `{inferred}`"),
                    term.span(),
                )
                .with_primary_label(format!("this has type `{inferred}`"))
                .with_label(why.span, why.reason))
            }
        }
    }
}

/// `inl [R] t` (or `inr [L] t`) checked against `A or B` where the annotation isn't the expected
/// side: `injection` is `"inl"` or `"inr"`, and `side` is the side its annotation gives.
fn wrong_injection_annotation(
    injection: &str,
    side: &str,
    annotation: &Type,
    expected: &Type,
    span: Span,
    why: Expectation,
) -> Diagnostic {
    Diagnostic::error(
        format!("`{injection}` is annotated with the wrong {side} side"),
        span,
    )
    .with_primary_label(format!(
        "the {side} side is annotated as `{annotation}`, but `{expected}` is expected"
    ))
    .with_label(why.span, why.reason)
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

    fn or(left_type: Type, right_type: Type) -> Type {
        Type::Either {
            left_type: Box::new(left_type),
            right_type: Box::new(right_type),
        }
    }

    fn not(typ: Type) -> Type {
        arrow(typ, Type::False)
    }

    #[test]
    fn test_display_uses_surface_syntax() {
        let (a, b, c) = (atom("A"), atom("B"), atom("C"));
        let cases = [
            (Type::False, "False"),
            (arrow(Type::False, Type::False), "True"),
            (not(a.clone()), "not A"),
            (not(not(a.clone())), "not not A"),
            (not(and(a.clone(), b.clone())), "not (A and B)"),
            (and(not(a.clone()), b.clone()), "not A and B"),
            (arrow(a.clone(), arrow(b.clone(), c.clone())), "A -> B -> C"),
            (
                arrow(arrow(a.clone(), b.clone()), c.clone()),
                "(A -> B) -> C",
            ),
            (or(and(a.clone(), b.clone()), c.clone()), "A and B or C"),
            (and(or(a.clone(), b.clone()), c.clone()), "(A or B) and C"),
            (and(a.clone(), and(b.clone(), c.clone())), "A and B and C"),
            (and(and(a.clone(), b.clone()), c.clone()), "(A and B) and C"),
            (
                and(arrow(a.clone(), b.clone()), arrow(b.clone(), a.clone())),
                "A <-> B",
            ),
            (
                arrow(
                    and(arrow(a.clone(), b.clone()), arrow(b.clone(), a.clone())),
                    c.clone(),
                ),
                "(A <-> B) -> C",
            ),
            // Not an equivalence: the two implications don't mirror each other.
            (
                and(arrow(a.clone(), b.clone()), arrow(a.clone(), b.clone())),
                "(A -> B) and (A -> B)",
            ),
        ];
        for (typ, expected) in cases {
            assert_eq!(typ.to_string(), expected);
        }
    }

    #[test]
    fn test_instantiate_is_simultaneous() {
        // Substituting A := B then B := A one at a time would give `A and A -> A and A`.
        let instantiated = swap_scheme().instantiate(&[atom("B"), atom("A")]).unwrap();
        assert_eq!(
            instantiated,
            arrow(and(atom("B"), atom("A")), and(atom("A"), atom("B")))
        );
    }

    #[test]
    fn test_instantiate_with_compound_type() {
        let a_to_a = arrow(atom("A"), atom("A"));
        let instantiated = id_scheme()
            .instantiate(std::slice::from_ref(&a_to_a))
            .unwrap();
        assert_eq!(instantiated, arrow(a_to_a.clone(), a_to_a));
    }

    #[test]
    fn test_instantiate_monomorphic() {
        let typ = arrow(Type::False, Type::False);
        let instantiated = scheme(&[], typ.clone()).instantiate(&[]).unwrap();
        assert_eq!(instantiated, typ);
    }

    #[test]
    fn test_instantiate_rejects_wrong_arity() {
        let too_few = id_scheme().instantiate(&[]).unwrap_err();
        assert_eq!(
            too_few,
            ArityMismatch {
                expected: 1,
                found: 0
            }
        );

        let too_many = id_scheme()
            .instantiate(&[atom("A"), atom("B")])
            .unwrap_err();
        assert_eq!(
            too_many,
            ArityMismatch {
                expected: 1,
                found: 2
            }
        );

        let for_mono = scheme(&[], Type::False)
            .instantiate(&[atom("A")])
            .unwrap_err();
        assert_eq!(
            for_mono,
            ArityMismatch {
                expected: 0,
                found: 1
            }
        );
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
        assert_eq!(check(&ctx, &body, &goal, NO_SPAN).unwrap(), Trust::Proved);
    }

    #[test]
    fn test_polymorphic_theorem_used_at_compound_type() {
        // theorem t A : (A -> A) -> (A -> A) := id [A -> A]
        let ctx = Context::new().bind("id".to_string(), id_scheme());
        let a_to_a = arrow(atom("A"), atom("A"));
        let goal = scheme(&["A"], arrow(a_to_a.clone(), a_to_a.clone()));
        let body = var("id", vec![a_to_a]);
        assert_eq!(check(&ctx, &body, &goal, NO_SPAN).unwrap(), Trust::Proved);
    }

    #[test]
    fn test_polymorphic_theorem_used_without_type_arguments() {
        let ctx = Context::new().bind("id".to_string(), id_scheme());
        let goal = scheme(&["A"], arrow(atom("A"), atom("A")));
        let body = var("id", vec![]);
        assert_eq!(
            error_message(check(&ctx, &body, &goal, NO_SPAN)),
            "`id` takes 1 type argument but 0 were supplied"
        );
    }

    #[test]
    fn test_local_variable_with_type_arguments() {
        // fun (x : A) => x [A]
        let goal = scheme(&["A"], arrow(atom("A"), atom("A")));
        let body = lam("x", atom("A"), var("x", vec![atom("A")]));
        assert_eq!(
            error_message(check(&Context::new(), &body, &goal, NO_SPAN)),
            "`x` takes no type arguments"
        );
    }

    #[test]
    fn test_local_binder_shadows_polymorphic_theorem() {
        // fun (id : A) => id  -- the local `id` is monomorphic, so takes no type arguments.
        let ctx = Context::new().bind("id".to_string(), id_scheme());
        let goal = scheme(&["A"], arrow(atom("A"), atom("A")));
        let body = lam("id", atom("A"), var("id", vec![]));
        assert_eq!(check(&ctx, &body, &goal, NO_SPAN).unwrap(), Trust::Proved);
    }

    #[test]
    fn test_parameters_are_rigid() {
        // theorem bad A B : A -> B := fun (x : A) => x
        let goal = scheme(&["A", "B"], arrow(atom("A"), atom("B")));
        let body = lam("x", atom("A"), var("x", vec![]));
        assert!(check(&Context::new(), &body, &goal, NO_SPAN).is_err());
    }

    #[test]
    fn test_instantiation_cannot_prove_false() {
        // With `id A : A -> A`, instantiating at False gives `False -> False`, never `False`.
        let ctx = Context::new().bind("id".to_string(), id_scheme());
        let goal = scheme(&[], Type::False);
        let body = var("id", vec![Type::False]);
        assert!(check(&ctx, &body, &goal, NO_SPAN).is_err());
    }

    #[test]
    fn test_rejects_ill_typed_eliminations() {
        let goal = scheme(&["A"], arrow(atom("A"), atom("A")));

        // fun (x : A) => fst x
        let body = lam("x", atom("A"), fst(var("x", vec![])));
        assert!(check(&Context::new(), &body, &goal, NO_SPAN).is_err());

        // fun (x : A) => x x
        let body = lam("x", atom("A"), app(var("x", vec![]), var("x", vec![])));
        assert!(check(&Context::new(), &body, &goal, NO_SPAN).is_err());

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
        assert!(check(&Context::new(), &body, &goal, NO_SPAN).is_err());
    }

    #[test]
    fn test_unknown_variable() {
        let goal = scheme(&[], Type::False);
        assert_eq!(
            error_message(check(&Context::new(), &var("nope", vec![]), &goal, NO_SPAN)),
            "cannot find `nope` in this scope"
        );
    }

    #[test]
    fn test_trustme_is_admitted() {
        let goal = scheme(&[], Type::False);
        assert_eq!(
            check(&Context::new(), &trustme(Type::False), &goal, NO_SPAN).unwrap(),
            Trust::Admitted
        );
    }

    #[test]
    fn test_admitted_theorem_taints_users() {
        let goal = scheme(&["A"], arrow(atom("A"), atom("A")));
        let body = var("id", vec![atom("A")]);

        let proved = Context::new().bind_with_trust("id".to_string(), id_scheme(), Trust::Proved);
        assert_eq!(
            check(&proved, &body, &goal, NO_SPAN).unwrap(),
            Trust::Proved
        );

        let admitted =
            Context::new().bind_with_trust("id".to_string(), id_scheme(), Trust::Admitted);
        assert_eq!(
            check(&admitted, &body, &goal, NO_SPAN).unwrap(),
            Trust::Admitted
        );
    }

    fn inl(right_type: Type, left: Term) -> Term {
        Term::Inl {
            span: NO_SPAN,
            right_type,
            left: Box::new(left),
        }
    }

    fn inr(left_type: Type, right: Term) -> Term {
        Term::Inr {
            span: NO_SPAN,
            left_type,
            right: Box::new(right),
        }
    }

    #[test]
    fn test_injections_are_checked_against_the_expected_disjunction() {
        // theorem t A B : A -> A or B := fun (a : A) => inl [B] a
        let goal = scheme(&["A", "B"], arrow(atom("A"), or(atom("A"), atom("B"))));
        let body = lam("a", atom("A"), inl(atom("B"), var("a", vec![])));
        assert_eq!(
            check(&Context::new(), &body, &goal, NO_SPAN).unwrap(),
            Trust::Proved
        );

        // theorem t A B : B -> A or (A -> B) := fun (b : B) => inr [A] (fun (a : A) => b)
        let goal = scheme(
            &["A", "B"],
            arrow(atom("B"), or(atom("A"), arrow(atom("A"), atom("B")))),
        );
        let body = lam(
            "b",
            atom("B"),
            inr(atom("A"), lam("a", atom("A"), var("b", vec![]))),
        );
        assert_eq!(
            check(&Context::new(), &body, &goal, NO_SPAN).unwrap(),
            Trust::Proved
        );
    }

    #[test]
    fn test_injection_mismatch_is_reported_inside() {
        // theorem bad A : A or not A := inr [A] (fun (a : A) => a)
        // The expected type is pushed through `inr` and the lambda, so the mistake is found at
        // `a`, which should prove `False`.
        let goal = scheme(&["A"], or(atom("A"), not(atom("A"))));
        let body = inr(atom("A"), lam("a", atom("A"), var("a", vec![])));
        assert_eq!(
            error_message(check(&Context::new(), &body, &goal, NO_SPAN)),
            "mismatched types: expected `False`, found `A`"
        );

        // theorem bad A B : B -> A or B := fun (b : B) => inl [B] b
        let goal = scheme(&["A", "B"], arrow(atom("B"), or(atom("A"), atom("B"))));
        let body = lam("b", atom("B"), inl(atom("B"), var("b", vec![])));
        assert_eq!(
            error_message(check(&Context::new(), &body, &goal, NO_SPAN)),
            "mismatched types: expected `A`, found `B`"
        );
    }

    #[test]
    fn test_injection_with_wrong_annotation() {
        // theorem bad A B : A -> A or B := fun (a : A) => inl [A] a
        let goal = scheme(&["A", "B"], arrow(atom("A"), or(atom("A"), atom("B"))));
        let body = lam("a", atom("A"), inl(atom("A"), var("a", vec![])));
        assert_eq!(
            error_message(check(&Context::new(), &body, &goal, NO_SPAN)),
            "`inl` is annotated with the wrong right side"
        );

        // theorem bad A B : B -> A or B := fun (b : B) => inr [B] b
        let goal = scheme(&["A", "B"], arrow(atom("B"), or(atom("A"), atom("B"))));
        let body = lam("b", atom("B"), inr(atom("B"), var("b", vec![])));
        assert_eq!(
            error_message(check(&Context::new(), &body, &goal, NO_SPAN)),
            "`inr` is annotated with the wrong left side"
        );
    }

    fn absurd(goal_type: Type, body: Term) -> Term {
        Term::Absurd {
            span: NO_SPAN,
            goal_type,
            body: Box::new(body),
        }
    }

    #[test]
    fn test_absurd_annotation_must_match_the_expected_type() {
        // theorem bad A B : False -> A := fun (f : False) => absurd [B] f
        // Inferring `absurd [B] f` gives `B`, so checking against `A` must fail too: `check_against`
        // accepts exactly the terms that infer-then-compare does.
        let goal = scheme(&["A", "B"], arrow(Type::False, atom("A")));
        let body = lam("f", Type::False, absurd(atom("B"), var("f", vec![])));
        assert_eq!(
            error_message(check(&Context::new(), &body, &goal, NO_SPAN)),
            "`absurd` is annotated with the wrong type"
        );

        // With the right annotation it's accepted.
        let body = lam("f", Type::False, absurd(atom("A"), var("f", vec![])));
        assert_eq!(
            check(&Context::new(), &body, &goal, NO_SPAN).unwrap(),
            Trust::Proved
        );
    }

    #[test]
    fn test_absurd_body_is_checked_against_false() {
        // theorem bad A B : A -> B := fun (a : A) => absurd [B] a
        let goal = scheme(&["A", "B"], arrow(atom("A"), atom("B")));
        let body = lam("a", atom("A"), absurd(atom("B"), var("a", vec![])));
        assert_eq!(
            error_message(check(&Context::new(), &body, &goal, NO_SPAN)),
            "mismatched types: expected `False`, found `A`"
        );

        // `False` is pushed into the body, so a lambda there is checked against `False` too.
        // theorem bad A : A := absurd [A] (fun (f : False) => f)
        let goal = scheme(&["A"], atom("A"));
        let body = absurd(atom("A"), lam("f", Type::False, var("f", vec![])));
        assert_eq!(
            error_message(check(&Context::new(), &body, &goal, NO_SPAN)),
            "mismatched types: expected `False`, found `True`"
        );
    }

    #[test]
    fn test_absurd_without_an_expected_type() {
        // In a function position there's no expected type, so `absurd` is inferred and the old
        // message is used. theorem bad A B : A -> B := fun (a : A) => (absurd [A -> B] a) a
        let goal = scheme(&["A", "B"], arrow(atom("A"), atom("B")));
        let body = lam(
            "a",
            atom("A"),
            app(
                absurd(arrow(atom("A"), atom("B")), var("a", vec![])),
                var("a", vec![]),
            ),
        );
        assert_eq!(
            error_message(check(&Context::new(), &body, &goal, NO_SPAN)),
            "`absurd` expects a proof of `False`"
        );
    }
}
