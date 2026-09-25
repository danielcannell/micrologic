use std::collections::{HashMap, HashSet};
use std::fmt::Display;
use std::rc::Rc;

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
}

#[derive(Debug, Clone)]
#[allow(unused)]
pub enum Term {
    /// `name [A] [B]`
    ///
    /// Corresponds to a hypothesis or previously proved theorem. Any type parameters are explicitly
    /// annotated to avoid the need for bidirectional type checking for now.
    Var {
        name: String,
        type_arguments: Vec<Type>,
    },

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

    /// `trustme [A]`
    ///
    /// Corresponds to the assumption that A is true. Used as a placeholder.
    TrustMe { goal_type: Type },
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

fn infer(ctx: &Context, term: &Term, trust: &mut Trust) -> Result<Type, String> {
    match term {
        Term::Var {
            name,
            type_arguments,
        } => {
            let (scheme, binding_trust) = ctx
                .lookup(name)
                .ok_or_else(|| format!("Unknown variable {}", name))?;

            // Referring to an admitted theorem taints this proof too.
            trust.admit(binding_trust);

            // Check the correct number of type arguments have been provided.
            if type_arguments.len() != scheme.params.len() {
                return Err("Incorrect number of type parameters".to_string());
            }

            // Substitute the type parameters with the provided types
            let type_arguments: HashMap<&str, &Type> = scheme
                .params
                .iter()
                .map(|name| name.as_str())
                .zip(type_arguments.iter())
                .collect();
            let substituted_type = scheme.typ.substitute(&type_arguments);

            Ok(substituted_type)
        }

        Term::Lambda {
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

        Term::Application { function, argument } => {
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
            left_type: Box::new(infer(ctx, lhs, trust)?),
            right_type: Box::new(infer(ctx, rhs, trust)?),
        }),

        Term::Fst { pair } => match infer(ctx, pair, trust)? {
            Type::Pair { left_type, .. } => Ok(*left_type),
            other => Err(format!(
                "Incorrect type in fst: expected Pair but got {}",
                other
            )),
        },

        Term::Snd { pair } => match infer(ctx, pair, trust)? {
            Type::Pair { right_type, .. } => Ok(*right_type),
            other => Err(format!(
                "Incorrect type in snd: expected Pair but got {}",
                other
            )),
        },

        Term::Inl { right_type, left } => {
            let left_type_inferred = infer(ctx, left, trust)?;
            Ok(Type::Either {
                left_type: Box::new(left_type_inferred),
                right_type: Box::new(right_type.clone()),
            })
        }

        Term::Inr { left_type, right } => {
            let right_type_inferred = infer(ctx, right, trust)?;
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
            let either_type = infer(ctx, either, trust)?;
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
                Err(format!(
                    "Mismatched branch types in case: left branch has type {}, but right branch has type {}",
                    left_body_type_inferred, right_body_type_inferred
                ))
            }
        }

        Term::Absurd { goal_type, body } => {
            let body_type = infer(ctx, body, trust)?;
            match body_type {
                Type::False => Ok(goal_type.clone()),
                other => Err(format!(
                    "Incorrect type in absurd: expected False, but got {}",
                    other
                )),
            }
        }

        Term::TrustMe { goal_type } => {
            // Infer the requested type, but taint the proof.
            *trust = Trust::Admitted;
            Ok(goal_type.clone())
        }
    }
}

pub fn check(ctx: &Context, term: &Term, scheme: &Scheme) -> Result<Trust, String> {
    let mut trust = Trust::Proved;
    let term_type_inferred = infer(ctx, term, &mut trust)?;
    if term_type_inferred != scheme.typ {
        return Err(format!(
            "Incorrect type: expected {} but got {}",
            scheme.typ, term_type_inferred
        ));
    }
    Ok(trust)
}
