use std::fmt::Display;
use std::rc::Rc;

#[derive(Debug, Clone, Eq, PartialEq)]
#[allow(unused)]
enum Type {
    Atom {
        name: String,
    },

    Lambda {
        argument_type: Box<Type>,
        result_type: Box<Type>,
    },

    Pair {
        left_type: Box<Type>,
        right_type: Box<Type>,
    },

    Either {
        left_type: Box<Type>,
        right_type: Box<Type>,
    },

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

    /// `case t of | inl x => u | inr y => v end`
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

fn main() {
    let a = Type::Atom {
        name: "A".to_string(),
    };
    let b = Type::Atom {
        name: "B".to_string(),
    };
    let a_imp_b = Type::Lambda {
        argument_type: Box::new(a.clone()),
        result_type: Box::new(b.clone()),
    };
    let a_and_a_imp_b = Type::Pair {
        left_type: Box::new(a.clone()),
        right_type: Box::new(a_imp_b.clone()),
    };
    let a_and_a_imp_b_imp_b = Type::Lambda {
        argument_type: Box::new(a_and_a_imp_b.clone()),
        result_type: Box::new(b.clone()),
    };
    let h = Term::Var {
        name: "h".to_string(),
    };
    let snd_h = Term::Snd {
        pair: Box::new(h.clone()),
    };
    let fst_h = Term::Fst {
        pair: Box::new(h.clone()),
    };
    let snd_h_fst_h = Term::Application {
        function: Box::new(snd_h),
        argument: Box::new(fst_h),
    };
    let mp = Term::Lambda {
        argument: "h".to_string(),
        argument_type: a_and_a_imp_b.clone(),
        body: Box::new(snd_h_fst_h.clone()),
    };

    let ctx = Context::new();
    check(&ctx, &mp, a_and_a_imp_b_imp_b.clone()).unwrap();
}
