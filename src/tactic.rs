use crate::diagnostics::{Diagnostic, Result, Span};
use crate::kernel;
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone)]
pub struct Script {
    pub span: Span,
    pub tactics: Vec<Tactic>,
}

#[derive(Debug, Clone)]
pub enum Tactic {
    Intro { span: Span, name: String },
    Exact { span: Span, term: kernel::Term },
    Split { span: Span },
    Left { span: Span },
    Right { span: Span },
    Assumption { span: Span },
    Admit { span: Span },
}

impl Tactic {
    fn span(&self) -> Span {
        match self {
            Tactic::Intro { span, .. } => *span,
            Tactic::Exact { span, .. } => *span,
            Tactic::Split { span, .. } => *span,
            Tactic::Left { span, .. } => *span,
            Tactic::Right { span, .. } => *span,
            Tactic::Assumption { span, .. } => *span,
            Tactic::Admit { span, .. } => *span,
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
struct GoalId(u64);

#[derive(Debug, Clone)]
struct Local {
    name: String,
    typ: kernel::Type,
}

/// An open goal: prove `target` using the hypotheses in `locals`.
///
/// Invariant: `locals` are exactly the binders in scope at this goal's hole in the partial term,
/// oldest first. This is what lets a term filling the hole (from `exact` or `assumption`) refer to
/// the locals by name, so every tactic that adds a local must also wrap the new hole in a binder
/// for it, as `intro` does with a `fun`.
#[derive(Debug, Clone)]
struct Goal {
    id: GoalId,
    locals: Vec<Local>,
    target: kernel::Type,
}

impl Goal {
    /// The locals that can still be referred to by name, oldest first. A local is hidden when a
    /// later local has the same name.
    fn visible_locals(&self) -> Vec<&Local> {
        let mut seen = HashSet::new();
        let mut visible: Vec<&Local> = self
            .locals
            .iter()
            .rev()
            .filter(|local| seen.insert(&local.name))
            .collect();
        visible.reverse();
        visible
    }
}

/// Shows the goal the way Coq and Lean do: one hypothesis per line, then the target.
///
/// ```text
/// a : A
/// b : B
/// ⊢ B and A
/// ```
///
/// Hidden (shadowed) hypotheses are left out, since they can't be referred to.
impl std::fmt::Display for Goal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for local in self.visible_locals() {
            writeln!(f, "{} : {}", local.name, local.typ)?;
        }
        write!(f, "⊢ {}", self.target)
    }
}

/// A note showing the goal a tactic was working on.
fn goal_note(goal: &Goal) -> String {
    format!("the goal is\n{goal}")
}

/// A tactic was used on a goal of the wrong shape, e.g. `split` on `A or B`.
fn wrong_goal_shape(tactic: &str, form: &str, goal: &Goal, span: Span) -> Diagnostic {
    Diagnostic::error(
        format!("`{tactic}` needs a goal of the form `{form}`"),
        span,
    )
    .with_primary_label(format!("the goal here is `{}`", goal.target))
    .with_note(goal_note(goal))
}

/// A mirror of the kernel's term, where sub-terms may be replaced with a 'hole'.
///
/// This allows elaboration to build up a term from the top down, leaving holes for parts that
/// haven't been built yet.
#[derive(Debug, Clone)]
enum Partial {
    Hole {
        goal_id: GoalId,
    },
    Term {
        term: kernel::Term,
    },
    Lambda {
        span: Span,
        argument: String,
        argument_type: kernel::Type,
        body: Box<Partial>,
    },
    Pair {
        span: Span,
        left: Box<Partial>,
        right: Box<Partial>,
    },
    Inl {
        span: Span,
        right_type: kernel::Type,
        left: Box<Partial>,
    },
    Inr {
        span: Span,
        left_type: kernel::Type,
        right: Box<Partial>,
    },
}

impl Partial {
    fn fill(self, solutions: &mut HashMap<GoalId, Partial>) -> kernel::Term {
        match self {
            Partial::Hole { goal_id } => solutions
                .remove(&goal_id)
                .expect("all goals should be solved before calling fill")
                .fill(solutions),
            Partial::Term { term } => term,
            Partial::Lambda {
                span,
                argument,
                argument_type,
                body,
            } => kernel::Term::Lambda {
                span,
                argument,
                argument_type,
                body: Box::new(body.fill(solutions)),
            },
            Partial::Pair { span, left, right } => kernel::Term::Pair {
                span,
                left: Box::new(left.fill(solutions)),
                right: Box::new(right.fill(solutions)),
            },
            Partial::Inl {
                span,
                right_type,
                left,
            } => kernel::Term::Inl {
                span,
                right_type,
                left: Box::new(left.fill(solutions)),
            },
            Partial::Inr {
                span,
                left_type,
                right,
            } => kernel::Term::Inr {
                span,
                left_type,
                right: Box::new(right.fill(solutions)),
            },
        }
    }
}

#[derive(Debug, Clone)]
struct ProofState {
    goals: Vec<Goal>,
    solutions: HashMap<GoalId, Partial>,
    next_goal_id: u64,
}

impl ProofState {
    /// Push a goal onto the stack of goals
    fn push_goal(&mut self, locals: Vec<Local>, target: kernel::Type) -> GoalId {
        let id = GoalId(self.next_goal_id);
        self.next_goal_id += 1;
        let goal = Goal { id, locals, target };
        self.goals.push(goal);
        id
    }

    /// Pop the most recently added goal
    fn pop_goal(&mut self) -> Option<Goal> {
        self.goals.pop()
    }

    fn add_solution(&mut self, goal_id: GoalId, solution: Partial) {
        let ok = self.solutions.insert(goal_id, solution).is_none();
        assert!(
            ok,
            "should not be able to create two solutions for one goal"
        );
    }
}

/// Turn a tactics script into an ordinary kernel term.
///
/// This works backwards from the target type, building up a kernel term of that type sub-term by
/// sub-term. The script is a list of tactics, and each tactic fills in further sub-terms.
pub fn elaborate(
    _ctx: &kernel::Context,
    script: &Script,
    target: &kernel::Type,
) -> Result<kernel::Term> {
    let mut proof_state = ProofState {
        goals: Vec::new(),
        solutions: HashMap::new(),
        next_goal_id: 0,
    };

    let root_goal_id = proof_state.push_goal(Vec::new(), target.clone());

    for tactic in &script.tactics {
        let goal = match proof_state.pop_goal() {
            Some(goal) => goal,
            None => {
                return Err(Diagnostic::error("no goals left", tactic.span())
                    .with_primary_label("there is nothing left to prove here")
                    .with_note("try removing the tactic"));
            }
        };

        match tactic {
            Tactic::Intro { span, name } => {
                if let kernel::Type::Lambda {
                    argument_type,
                    result_type,
                } = goal.target
                {
                    let mut new_locals = goal.locals;
                    new_locals.push(Local {
                        name: name.clone(),
                        typ: (*argument_type).clone(),
                    });

                    let new_goal_id = proof_state.push_goal(new_locals, *result_type);

                    let solution = Partial::Lambda {
                        span: *span,
                        argument: name.clone(),
                        argument_type: *argument_type,
                        body: Box::new(Partial::Hole {
                            goal_id: new_goal_id,
                        }),
                    };

                    proof_state.add_solution(goal.id, solution);
                } else {
                    return Err(wrong_goal_shape("intro", "A -> B", &goal, *span));
                }
            }
            Tactic::Exact { span: _, term } => {
                let solution = Partial::Term { term: term.clone() };
                proof_state.add_solution(goal.id, solution);
            }
            Tactic::Split { span } => {
                if let kernel::Type::Pair {
                    left_type,
                    right_type,
                } = goal.target
                {
                    // Push the right goal first, so that we work on the left goal before the right
                    // goal
                    let new_goal_id_right = proof_state.push_goal(goal.locals.clone(), *right_type);
                    let new_goal_id_left = proof_state.push_goal(goal.locals.clone(), *left_type);

                    let solution = Partial::Pair {
                        span: *span,
                        left: Box::new(Partial::Hole {
                            goal_id: new_goal_id_left,
                        }),
                        right: Box::new(Partial::Hole {
                            goal_id: new_goal_id_right,
                        }),
                    };

                    proof_state.add_solution(goal.id, solution);
                } else {
                    return Err(wrong_goal_shape("split", "A and B", &goal, *span));
                }
            }
            Tactic::Left { span } => {
                if let kernel::Type::Either {
                    left_type,
                    right_type,
                } = goal.target
                {
                    let new_goal_id = proof_state.push_goal(goal.locals.clone(), *left_type);

                    let solution = Partial::Inl {
                        span: *span,
                        right_type: *right_type,
                        left: Box::new(Partial::Hole {
                            goal_id: new_goal_id,
                        }),
                    };

                    proof_state.add_solution(goal.id, solution);
                } else {
                    return Err(wrong_goal_shape("left", "A or B", &goal, *span));
                }
            }
            Tactic::Right { span } => {
                if let kernel::Type::Either {
                    left_type,
                    right_type,
                } = goal.target
                {
                    let new_goal_id = proof_state.push_goal(goal.locals.clone(), *right_type);

                    let solution = Partial::Inr {
                        span: *span,
                        left_type: *left_type,
                        right: Box::new(Partial::Hole {
                            goal_id: new_goal_id,
                        }),
                    };

                    proof_state.add_solution(goal.id, solution);
                } else {
                    return Err(wrong_goal_shape("right", "A or B", &goal, *span));
                }
            }
            Tactic::Assumption { span } => {
                let visible = goal.visible_locals();
                let Some(local) = visible.iter().rev().find(|local| local.typ == goal.target)
                else {
                    let mut diag = Diagnostic::error("no hypothesis matches the goal", *span)
                        .with_primary_label(format!("no hypothesis has type `{}`", goal.target));

                    // Every local of the right type is hidden, so the fix is to rename.
                    if let Some(hidden) = goal.locals.iter().find(|local| local.typ == goal.target)
                    {
                        diag = diag.with_note(format!(
                            "`{name}` has type `{typ}`, but it is hidden by a later hypothesis \
                             also named `{name}`; use a different name in one of the `intro`s",
                            name = hidden.name,
                            typ = hidden.typ,
                        ));
                    }

                    return Err(diag.with_note(goal_note(&goal)));
                };

                let solution = Partial::Term {
                    term: kernel::Term::Var {
                        span: *span,
                        name: local.name.clone(),
                        type_arguments: Vec::new(),
                    },
                };
                proof_state.add_solution(goal.id, solution);
            }
            Tactic::Admit { span } => {
                let solution = Partial::Term {
                    term: kernel::Term::TrustMe {
                        span: *span,
                        goal_type: goal.target,
                    },
                };
                proof_state.add_solution(goal.id, solution);
            }
        }
    }

    if !proof_state.goals.is_empty() {
        let n = proof_state.goals.len();
        // Point at the last tactic rather than the whole (possibly many-line) script.
        let span = script.tactics.last().map_or(script.span, Tactic::span);
        let mut diag = Diagnostic::error(kernel::count(n, "unsolved goal"), span)
            .with_primary_label("the proof is incomplete after this tactic");

        // List the goals in the order the next tactics would work on them: the stack's top first.
        for (i, goal) in proof_state.goals.iter().rev().enumerate() {
            diag = diag.with_note(if n == 1 {
                goal_note(goal)
            } else {
                format!("goal {} of {n} is\n{goal}", i + 1)
            });
        }

        return Err(diag);
    }

    Ok(Partial::Hole {
        goal_id: root_goal_id,
    }
    .fill(&mut proof_state.solutions))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lower::{self, TypeScope};
    use crate::surface;

    // Render a kernel term as a compact s-expression, like `surface`'s test printer. Types are
    // printed in brackets with `Display`.
    fn show_term(term: &kernel::Term) -> String {
        use kernel::Term;
        match term {
            Term::Var {
                name,
                type_arguments,
                ..
            } => {
                if type_arguments.is_empty() {
                    name.clone()
                } else {
                    let arguments: Vec<String> =
                        type_arguments.iter().map(|t| format!("[{t}]")).collect();
                    format!("({name} {})", arguments.join(" "))
                }
            }
            Term::Lambda {
                argument,
                argument_type,
                body,
                ..
            } => format!("(fun {argument} [{argument_type}] {})", show_term(body)),
            Term::Application {
                function, argument, ..
            } => format!("(app {} {})", show_term(function), show_term(argument)),
            Term::Pair { left, right, .. } => {
                format!("(pair {} {})", show_term(left), show_term(right))
            }
            Term::Fst { pair, .. } => format!("(fst {})", show_term(pair)),
            Term::Snd { pair, .. } => format!("(snd {})", show_term(pair)),
            Term::Inl {
                right_type, left, ..
            } => format!("(inl [{right_type}] {})", show_term(left)),
            Term::Inr {
                left_type, right, ..
            } => format!("(inr [{left_type}] {})", show_term(right)),
            Term::Case {
                either,
                left_name,
                left_body,
                right_name,
                right_body,
                ..
            } => format!(
                "(case {} {left_name} {} {right_name} {})",
                show_term(either),
                show_term(left_body),
                show_term(right_body)
            ),
            Term::Absurd {
                goal_type, body, ..
            } => format!("(absurd [{goal_type}] {})", show_term(body)),
            Term::TrustMe { goal_type, .. } => format!("(trustme [{goal_type}])"),
        }
    }

    // Parse, lower and elaborate the single theorem in `source`. The term is not checked by the
    // kernel, so these tests see exactly what the elaborator built.
    fn elaborate_source(source: &str) -> kernel::Term {
        let module = surface::parse(source).expect("should parse");
        let [surface::ast::Item::Theorem(theorem)] = &module.items[..] else {
            panic!("expected a single theorem:\n{source}");
        };
        let surface::ast::Body::Script(script) = &theorem.body else {
            panic!("expected a tactic script:\n{source}");
        };
        let aliases = HashMap::new();
        let scope = TypeScope {
            parameters: &theorem.parameters,
            aliases: &aliases,
            defining: None,
        };
        let target = lower::lower_type(&theorem.typ, &scope).expect("type should lower");
        let script = lower::lower_script(script, &scope).expect("script should lower");
        match elaborate(&kernel::Context::new(), &script, &target) {
            Ok(term) => term,
            Err(diag) => panic!("failed to elaborate: {}\n{source}", diag.message),
        }
    }

    fn elaborate_str(source: &str) -> String {
        show_term(&elaborate_source(source))
    }

    #[test]
    fn test_intro_and_exact() {
        assert_eq!(
            elaborate_str("theorem t A : A -> A := by intro h; exact h."),
            "(fun h [A] h)"
        );
        // `exact` takes any term, used as is.
        assert_eq!(
            elaborate_str("theorem t A B : (A -> B) -> A -> B := by intro f; intro a; exact f a."),
            "(fun f [A -> B] (fun a [A] (app f a)))"
        );
    }

    #[test]
    fn test_intro_on_desugared_types() {
        // `not A` is `A -> False` and `True` is `False -> False` by the time tactics run.
        assert_eq!(
            elaborate_str("theorem t A : A -> not not A := by intro a; intro na; exact na a."),
            "(fun a [A] (fun na [not A] (app na a)))"
        );
        assert_eq!(
            elaborate_str("theorem t : True := by intro f; exact f."),
            "(fun f [False] f)"
        );
    }

    #[test]
    fn test_split_fills_left_then_right() {
        assert_eq!(
            elaborate_str(
                "theorem t A B : A -> B -> B and A := by intro a; intro b; split; exact b; exact a."
            ),
            "(fun a [A] (fun b [B] (pair b a)))"
        );
        // New goals go before the goals that were already open, so the inner `split`'s goals are
        // solved before the outer `split`'s right goal.
        assert_eq!(
            elaborate_str(
                "theorem t A B C : A -> B -> C -> (A and B) and C := by \
                 intro a; intro b; intro c; split; split; exact a; exact b; exact c."
            ),
            "(fun a [A] (fun b [B] (fun c [C] (pair (pair a b) c))))"
        );
    }

    #[test]
    fn test_split_on_equivalence() {
        // `A <-> B` is a pair of implications.
        assert_eq!(
            elaborate_str("theorem t A : A <-> A := by split; intro x; exact x; intro y; exact y."),
            "(pair (fun x [A] x) (fun y [A] y))"
        );
    }

    #[test]
    fn test_left_and_right() {
        // The annotation is the *other* side of the disjunction.
        assert_eq!(
            elaborate_str("theorem t A B : A -> A or B := by intro a; left; exact a."),
            "(fun a [A] (inl [B] a))"
        );
        assert_eq!(
            elaborate_str("theorem t A B : A -> B or A := by intro a; right; exact a."),
            "(fun a [A] (inr [B] a))"
        );
    }

    #[test]
    fn test_assumption() {
        assert_eq!(
            elaborate_str("theorem t A B : A -> B -> A := by intro a; intro b; assumption."),
            "(fun a [A] (fun b [B] a))"
        );
        // With several matches, the most recent is used.
        assert_eq!(
            elaborate_str("theorem t A : A -> A -> A := by intro x; intro y; assumption."),
            "(fun x [A] (fun y [A] y))"
        );
        // A shadowed hypothesis of the wrong type doesn't get in the way.
        assert_eq!(
            elaborate_str("theorem t A B : B -> A -> A := by intro h; intro h; assumption."),
            "(fun h [B] (fun h [A] h))"
        );
    }

    #[test]
    fn test_admit() {
        assert_eq!(
            elaborate_str("theorem t A B : A -> B := by intro a; admit."),
            "(fun a [A] (trustme [B]))"
        );
    }

    #[test]
    fn test_generated_terms_take_the_tactic_span() {
        let source =
            "theorem t A B : A -> B -> B and A := by intro a; intro b; split; exact b; exact a.";
        let text = |span: Span| &source[span.start..span.end];

        let kernel::Term::Lambda { span, body, .. } = elaborate_source(source) else {
            panic!("expected a lambda");
        };
        assert_eq!(text(span), "intro a");
        let kernel::Term::Lambda { span, body, .. } = *body else {
            panic!("expected a lambda");
        };
        assert_eq!(text(span), "intro b");
        let kernel::Term::Pair { span, left, .. } = *body else {
            panic!("expected a pair");
        };
        assert_eq!(text(span), "split");
        // A term from `exact` keeps its own spans.
        let kernel::Term::Var { span, .. } = *left else {
            panic!("expected a variable");
        };
        assert_eq!(text(span), "b");
    }

    // Check a module that should be rejected, returning the diagnostic.
    fn reject(source: &str) -> Diagnostic {
        match crate::process_module(source) {
            Ok(summary) => panic!("should reject, but got {summary:?}:\n{source}"),
            Err(diag) => diag,
        }
    }

    // The source text under the primary label, and the label's message.
    fn primary_label(source: &str, diag: &Diagnostic) -> (String, String) {
        let label = &diag.labels[0];
        (
            source[label.span.start..label.span.end].to_string(),
            label.message.clone().unwrap_or_default(),
        )
    }

    #[test]
    fn test_wrong_goal_shape() {
        let cases = [
            (
                "theorem t A : A := by intro x.",
                "`intro` needs a goal of the form `A -> B`",
                "intro x",
                "the goal here is `A`",
            ),
            (
                "theorem t A B : A or B := by split.",
                "`split` needs a goal of the form `A and B`",
                "split",
                "the goal here is `A or B`",
            ),
            (
                "theorem t A B : A and B := by left.",
                "`left` needs a goal of the form `A or B`",
                "left",
                "the goal here is `A and B`",
            ),
            (
                "theorem t A B : A -> B := by right.",
                "`right` needs a goal of the form `A or B`",
                "right",
                "the goal here is `A -> B`",
            ),
        ];
        for (source, message, text, label) in cases {
            let diag = reject(source);
            assert_eq!(diag.message, message, "in:\n{source}");
            assert_eq!(
                primary_label(source, &diag),
                (text.to_string(), label.to_string()),
                "in:\n{source}"
            );
        }
    }

    #[test]
    fn test_goal_note_shows_hypotheses() {
        let diag = reject("theorem t A B : A -> B -> A or B := by intro a; intro b; split.");
        assert_eq!(diag.notes, vec!["the goal is\na : A\nb : B\n⊢ A or B"]);
    }

    #[test]
    fn test_goal_note_hides_shadowed_hypotheses() {
        let diag = reject("theorem t A B : A -> B -> A or B := by intro h; intro h; split.");
        assert_eq!(diag.notes, vec!["the goal is\nh : B\n⊢ A or B"]);
    }

    #[test]
    fn test_assumption_without_a_match() {
        let source = "theorem t A B : A -> B := by intro a; assumption.";
        let diag = reject(source);
        assert_eq!(diag.message, "no hypothesis matches the goal");
        assert_eq!(
            primary_label(source, &diag),
            (
                "assumption".to_string(),
                "no hypothesis has type `B`".to_string()
            )
        );
        assert_eq!(diag.notes, vec!["the goal is\na : A\n⊢ B"]);
    }

    #[test]
    fn test_assumption_ignores_shadowed_hypotheses() {
        // The first `h : A` can't be named any more, so `assumption` must not use it: `Var "h"`
        // would refer to the second `h : B`.
        let diag = reject("theorem t A B : A -> B -> A := by intro h; intro h; assumption.");
        assert_eq!(diag.message, "no hypothesis matches the goal");
        assert_eq!(
            diag.notes,
            vec![
                "`h` has type `A`, but it is hidden by a later hypothesis also named `h`; use a \
                 different name in one of the `intro`s",
                "the goal is\nh : B\n⊢ A",
            ]
        );
    }

    #[test]
    fn test_unsolved_goals() {
        let source = "theorem t A B : A -> B and A := by intro a; split.";
        let diag = reject(source);
        assert_eq!(diag.message, "2 unsolved goals");
        assert_eq!(
            primary_label(source, &diag),
            (
                "split".to_string(),
                "the proof is incomplete after this tactic".to_string()
            )
        );
        // In the order the next tactics would work on them.
        assert_eq!(
            diag.notes,
            vec!["goal 1 of 2 is\na : A\n⊢ B", "goal 2 of 2 is\na : A\n⊢ A"]
        );

        let diag = reject("theorem t A B : A -> B and A := by intro a; split; admit.");
        assert_eq!(diag.message, "1 unsolved goal");
        assert_eq!(diag.notes, vec!["the goal is\na : A\n⊢ A"]);
    }

    #[test]
    fn test_no_goals_left() {
        let source = "theorem t A : A -> A := by intro x; exact x; split.";
        let diag = reject(source);
        assert_eq!(diag.message, "no goals left");
        assert_eq!(
            primary_label(source, &diag),
            (
                "split".to_string(),
                "there is nothing left to prove here".to_string()
            )
        );
    }
}
