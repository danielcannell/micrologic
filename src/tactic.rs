use crate::diagnostics::{Diagnostic, Result, Span};
use crate::kernel;
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone)]
pub struct Script {
    pub span: Span,
    pub tactics: Vec<Tactic>,
}

/// A name written in a script, such as the hypothesis in `intro h`, with where it was written.
#[derive(Debug, Clone)]
pub struct Name {
    pub text: String,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum Tactic {
    Focus {
        span: Span,
        script: Script,
    },
    Intro {
        span: Span,
        name: Name,
    },
    Exact {
        span: Span,
        term: kernel::Term,
    },
    Split {
        span: Span,
    },
    Left {
        span: Span,
    },
    Right {
        span: Span,
    },
    Assumption {
        span: Span,
    },
    Admit {
        span: Span,
    },
    ExFalso {
        span: Span,
    },
    Destruct {
        span: Span,
        hypothesis: Name,
        left: Name,
        right: Name,
    },
    Cases {
        span: Span,
        hypothesis: Name,
        left: Name,
        right: Name,
    },
    Have {
        span: Span,
        hypothesis: Name,
        typ: kernel::Type,
    },
    Apply {
        span: Span,
        term: kernel::Term,
    },
}

impl Tactic {
    fn span(&self) -> Span {
        match self {
            Tactic::Focus { span, .. } => *span,
            Tactic::Intro { span, .. } => *span,
            Tactic::Exact { span, .. } => *span,
            Tactic::Split { span, .. } => *span,
            Tactic::Left { span, .. } => *span,
            Tactic::Right { span, .. } => *span,
            Tactic::Assumption { span, .. } => *span,
            Tactic::Admit { span, .. } => *span,
            Tactic::ExFalso { span, .. } => *span,
            Tactic::Destruct { span, .. } => *span,
            Tactic::Cases { span, .. } => *span,
            Tactic::Have { span, .. } => *span,
            Tactic::Apply { span, .. } => *span,
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
    /// The locals that can still be referred to by name, newest first. A local is hidden when a
    /// later local has the same name.
    fn iter_visible_locals(&self) -> impl Iterator<Item = &Local> {
        let mut seen = HashSet::new();
        self.locals
            .iter()
            .rev()
            .filter(move |local| seen.insert(&local.name))
    }

    fn lookup_local_by_type(&self, typ: &kernel::Type) -> Option<&Local> {
        self.iter_visible_locals().find(|local| &local.typ == typ)
    }

    fn lookup_local_by_name(&self, name: &str) -> Option<&Local> {
        self.iter_visible_locals().find(|local| local.name == name)
    }

    /// The locals that can't be referred to by name, because a later local has the same name,
    /// newest first.
    fn iter_hidden_locals(&self) -> impl Iterator<Item = &Local> {
        let mut seen = HashSet::new();
        self.locals
            .iter()
            .rev()
            .filter(move |local| !seen.insert(&local.name))
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
        // Oldest first, as they were introduced.
        let mut locals: Vec<&Local> = self.iter_visible_locals().collect();
        locals.reverse();

        for local in locals {
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

/// A tactic named a hypothesis that isn't in the goal.
fn unknown_hypothesis(ctx: &kernel::Context, tactic: &str, name: &Name, goal: &Goal) -> Diagnostic {
    let mut diag = Diagnostic::error(format!("cannot find hypothesis `{}`", name.text), name.span)
        .with_primary_label("not a hypothesis");

    // Tactics like `destruct` only take hypotheses for now, not theorems or axioms.
    if ctx.lookup(&name.text).is_some() {
        diag = diag.with_note(format!(
            "`{}` is a theorem or axiom, but `{tactic}` only works on hypotheses",
            name.text
        ));
    }

    diag.with_note(goal_note(goal))
}

/// A tactic was used on a hypothesis of the wrong shape, e.g. `destruct` on `h : A or B`. The
/// caller adds the goal note, after any notes of its own.
fn wrong_hypothesis_shape(tactic: &str, form: &str, name: &Name, typ: &kernel::Type) -> Diagnostic {
    Diagnostic::error(
        format!("`{tactic}` needs a hypothesis of the form `{form}`"),
        name.span,
    )
    .with_primary_label(format!("`{}` has type `{typ}`", name.text))
}

/// A note for when the hypothesis a tactic needed exists, but is hidden by a later one with the
/// same name.
fn hidden_note(hidden: &Local) -> String {
    format!(
        "an earlier `{name}` has type `{typ}`, but a later hypothesis with the same name hides it; \
         give one of them a different name",
        name = hidden.name,
        typ = hidden.typ,
    )
}

/// A tactic's term (in `exact` or `apply`) mentions a name that isn't in scope at this goal.
fn unknown_name(name: &str, span: Span, goal: &Goal, proof_state: &ProofState) -> Diagnostic {
    let mut diag = Diagnostic::error(format!("cannot find `{name}` in this scope"), span)
        .with_primary_label("not a hypothesis, theorem or axiom");

    // Most likely a hypothesis that only exists in a later goal, e.g. the `h` of `have h : T`
    // used in its own proof.
    if proof_state
        .open_goals()
        .any(|other| other.lookup_local_by_name(name).is_some())
    {
        diag = diag.with_note(format!(
            "`{name}` is a hypothesis of a later goal, but not of this one; for example, the \
             hypothesis of a `have` can't be used in its own proof"
        ));
    }

    diag.with_note(goal_note(goal))
}

/// The names a term refers to that aren't bound inside it, with where each is used, in order.
fn free_names(term: &kernel::Term) -> Vec<(&str, Span)> {
    fn walk<'a>(term: &'a kernel::Term, bound: &mut Vec<&'a str>, free: &mut Vec<(&'a str, Span)>) {
        use kernel::Term;
        match term {
            Term::Var { span, name, .. } => {
                if !bound.contains(&name.as_str()) {
                    free.push((name, *span));
                }
            }
            Term::Lambda { argument, body, .. } => {
                bound.push(argument);
                walk(body, bound, free);
                bound.pop();
            }
            Term::Application {
                function, argument, ..
            } => {
                walk(function, bound, free);
                walk(argument, bound, free);
            }
            Term::Pair { left, right, .. } => {
                walk(left, bound, free);
                walk(right, bound, free);
            }
            Term::Fst { pair, .. } | Term::Snd { pair, .. } => walk(pair, bound, free),
            Term::Inl { left, .. } => walk(left, bound, free),
            Term::Inr { right, .. } => walk(right, bound, free),
            Term::Case {
                either,
                left_name,
                left_body,
                right_name,
                right_body,
                ..
            } => {
                walk(either, bound, free);
                bound.push(left_name);
                walk(left_body, bound, free);
                bound.pop();
                bound.push(right_name);
                walk(right_body, bound, free);
                bound.pop();
            }
            Term::Absurd { body, .. } => walk(body, bound, free),
            Term::TrustMe { .. } => {}
        }
    }

    let mut free = Vec::new();
    walk(term, &mut Vec::new(), &mut free);
    free
}

/// A reference to a hypothesis.
fn var(span: Span, name: &str) -> kernel::Term {
    kernel::Term::Var {
        span,
        name: name.to_string(),
        type_arguments: Vec::new(),
    }
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
    Absurd {
        span: Span,
        goal_type: kernel::Type,
        body: Box<Partial>,
    },
    Application {
        span: Span,
        function: Box<Partial>,
        argument: Box<Partial>,
    },
    Case {
        span: Span,
        either: kernel::Term,
        left_name: String,
        left_body: Box<Partial>,
        right_name: String,
        right_body: Box<Partial>,
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
            Partial::Absurd {
                span,
                goal_type,
                body,
            } => kernel::Term::Absurd {
                span,
                goal_type,
                body: Box::new(body.fill(solutions)),
            },
            Partial::Application {
                span,
                function,
                argument,
            } => kernel::Term::Application {
                span,
                function: Box::new(function.fill(solutions)),
                argument: Box::new(argument.fill(solutions)),
            },
            Partial::Case {
                span,
                either,
                left_name,
                left_body,
                right_name,
                right_body,
            } => kernel::Term::Case {
                span,
                either: Box::new(either),
                left_name,
                left_body: Box::new(left_body.fill(solutions)),
                right_name,
                right_body: Box::new(right_body.fill(solutions)),
            },
        }
    }
}

#[derive(Debug, Clone)]
struct ProofState {
    goals: Vec<Vec<Goal>>,
    solutions: HashMap<GoalId, Partial>,
    next_goal_id: u64,
}

impl ProofState {
    fn new() -> Self {
        Self {
            goals: Vec::new(),
            solutions: HashMap::new(),
            next_goal_id: 0,
        }
    }

    fn new_goal(&mut self, locals: Vec<Local>, target: kernel::Type) -> Goal {
        let id = GoalId(self.next_goal_id);
        self.next_goal_id += 1;
        Goal { id, locals, target }
    }

    /// Push a goal onto the stack of goals
    fn push_new_goal(&mut self, locals: Vec<Local>, target: kernel::Type) -> GoalId {
        let goal = self.new_goal(locals, target);
        let id = goal.id;
        self.push_goal(goal);
        id
    }

    fn push_goal(&mut self, goal: Goal) {
        self.goals
            .last_mut()
            .expect("should always be at least one level of goals")
            .push(goal);
    }

    /// Pop the most recently added goal
    fn pop_goal(&mut self) -> Option<Goal> {
        self.goals
            .last_mut()
            .expect("should always be at least one level of goals")
            .pop()
    }

    /// Every open goal, in all blocks.
    fn open_goals(&self) -> impl Iterator<Item = &Goal> {
        self.goals.iter().flatten()
    }

    fn push_focus(&mut self, goal: Goal) {
        self.goals.push(vec![goal]);
    }

    /// Whether the tactics being run are inside a `{ ... }` block, rather than at the top level of
    /// the script.
    fn in_block(&self) -> bool {
        self.goals.len() > 1
    }

    /// Leave the current block (or the whole script), which must have no goals left. `script` is
    /// the block's (or the whole) script.
    fn pop_focus(&mut self, script: &Script) -> Result<()> {
        let in_block = self.in_block();
        let what = if in_block { "block" } else { "proof" };

        // Point at the last tactic rather than the whole (possibly many-line) script. An empty
        // script's span is its `by` or `{`.
        let (span, label) = match script.tactics.last() {
            Some(tactic) => (
                tactic.span(),
                format!("the {what} is incomplete after this tactic"),
            ),
            None => (script.span, format!("the {what} has no tactics yet")),
        };
        let goals = self
            .goals
            .pop()
            .expect("should always be at least one level of goals");

        if !goals.is_empty() {
            let n = goals.len();

            let mut diag = Diagnostic::error(kernel::count(n, "unsolved goal"), span)
                .with_primary_label(label);

            // List the goals in the order the next tactics would work on them: the stack's top first.
            for (i, goal) in goals.iter().rev().enumerate() {
                diag = diag.with_note(if n == 1 {
                    goal_note(goal)
                } else {
                    format!("goal {} of {n} is\n{goal}", i + 1)
                });
            }
            if in_block {
                diag = diag.with_note("a `{ ... }` block must prove its goal before the `}`");
            }

            return Err(diag);
        }

        Ok(())
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
    ctx: &kernel::Context,
    script: &Script,
    target: &kernel::Type,
) -> Result<kernel::Term> {
    let mut proof_state = ProofState::new();
    let goal = proof_state.new_goal(Vec::new(), target.clone());
    let goal_id = goal.id;
    elaborate_focus(ctx, script, goal, &mut proof_state)?;
    let partial = Partial::Hole { goal_id };
    Ok(partial.fill(&mut proof_state.solutions))
}

fn elaborate_focus(
    ctx: &kernel::Context,
    script: &Script,
    goal: Goal,
    proof_state: &mut ProofState,
) -> Result<()> {
    proof_state.push_focus(goal);

    for tactic in &script.tactics {
        let goal = match proof_state.pop_goal() {
            Some(goal) => goal,
            None => {
                let diag = Diagnostic::error("no goals left", tactic.span())
                    .with_primary_label("there is nothing left to prove here");
                return Err(if proof_state.in_block() {
                    diag.with_note(
                        "a `{ ... }` block works on a single goal, which is already proved; \
                         close the block with `}` before working on the next goal",
                    )
                } else {
                    diag.with_note("try removing the tactic")
                });
            }
        };

        match tactic {
            Tactic::Focus { span: _, script } => {
                elaborate_focus(ctx, script, goal, proof_state)?;
            }
            Tactic::Intro { span, name } => {
                if let kernel::Type::Lambda {
                    argument_type,
                    result_type,
                } = goal.target
                {
                    let mut new_locals = goal.locals;
                    new_locals.push(Local {
                        name: name.text.clone(),
                        typ: (*argument_type).clone(),
                    });

                    let new_goal_id = proof_state.push_new_goal(new_locals, *result_type);

                    let solution = Partial::Lambda {
                        span: *span,
                        argument: name.text.clone(),
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
                // The kernel checks the term, but a name that isn't in scope is reported here,
                // where the goal is known and can be shown.
                for (name, name_span) in free_names(term) {
                    if goal.lookup_local_by_name(name).is_none() && ctx.lookup(name).is_none() {
                        return Err(unknown_name(name, name_span, &goal, proof_state));
                    }
                }

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
                    let new_goal_id_right =
                        proof_state.push_new_goal(goal.locals.clone(), *right_type);
                    let new_goal_id_left =
                        proof_state.push_new_goal(goal.locals.clone(), *left_type);

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
                    let new_goal_id = proof_state.push_new_goal(goal.locals.clone(), *left_type);

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
                    let new_goal_id = proof_state.push_new_goal(goal.locals.clone(), *right_type);

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
                let Some(local) = goal.lookup_local_by_type(&goal.target) else {
                    let mut diag = Diagnostic::error("no hypothesis matches the goal", *span)
                        .with_primary_label(format!("no hypothesis has type `{}`", goal.target));

                    // Every local of the right type is hidden, so the fix is to rename.
                    if let Some(hidden) = goal
                        .iter_hidden_locals()
                        .find(|local| local.typ == goal.target)
                    {
                        diag = diag.with_note(hidden_note(hidden));
                    }

                    return Err(diag.with_note(goal_note(&goal)));
                };

                let solution = Partial::Term {
                    term: var(*span, &local.name),
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
            Tactic::ExFalso { span } => {
                let new_goal_id =
                    proof_state.push_new_goal(goal.locals.clone(), kernel::Type::False);

                let solution = Partial::Absurd {
                    span: *span,
                    goal_type: goal.target,
                    body: Box::new(Partial::Hole {
                        goal_id: new_goal_id,
                    }),
                };
                proof_state.add_solution(goal.id, solution);
            }
            Tactic::Destruct {
                span,
                hypothesis,
                left,
                right,
            } => {
                let Some(local) = goal.lookup_local_by_name(&hypothesis.text) else {
                    return Err(unknown_hypothesis(ctx, "destruct", hypothesis, &goal));
                };
                let kernel::Type::Pair {
                    left_type,
                    right_type,
                } = &local.typ
                else {
                    let mut diag =
                        wrong_hypothesis_shape("destruct", "A and B", hypothesis, &local.typ);

                    // An earlier local with the same name might be the pair that was meant.
                    if let Some(hidden) = goal.iter_hidden_locals().find(|hidden| {
                        hidden.name == local.name && matches!(hidden.typ, kernel::Type::Pair { .. })
                    }) {
                        diag = diag.with_note(hidden_note(hidden));
                    }

                    return Err(diag.with_note(goal_note(&goal)));
                };
                let left_type = (**left_type).clone();
                let right_type = (**right_type).clone();

                let mut new_locals = goal.locals.clone();
                new_locals.push(Local {
                    name: left.text.clone(),
                    typ: left_type.clone(),
                });
                new_locals.push(Local {
                    name: right.text.clone(),
                    typ: right_type.clone(),
                });
                let new_goal_id = proof_state.push_new_goal(new_locals, goal.target.clone());

                // The kernel has no `let`, so bind the parts with a redex:
                //
                //     (fun (x : A) => fun (y : B) => ?) (fst h) (snd h)
                //
                // `fst h` and `snd h` are outside the lambdas, so they still refer to the pair even
                // if `x` or `y` is also named `h`.
                let lambdas = Partial::Lambda {
                    span: *span,
                    argument: left.text.clone(),
                    argument_type: left_type,
                    body: Box::new(Partial::Lambda {
                        span: *span,
                        argument: right.text.clone(),
                        argument_type: right_type,
                        body: Box::new(Partial::Hole {
                            goal_id: new_goal_id,
                        }),
                    }),
                };
                let fst = kernel::Term::Fst {
                    span: *span,
                    pair: Box::new(var(hypothesis.span, &hypothesis.text)),
                };
                let snd = kernel::Term::Snd {
                    span: *span,
                    pair: Box::new(var(hypothesis.span, &hypothesis.text)),
                };
                let solution = Partial::Application {
                    span: *span,
                    function: Box::new(Partial::Application {
                        span: *span,
                        function: Box::new(lambdas),
                        argument: Box::new(Partial::Term { term: fst }),
                    }),
                    argument: Box::new(Partial::Term { term: snd }),
                };

                proof_state.add_solution(goal.id, solution);
            }
            Tactic::Cases {
                span,
                hypothesis,
                left,
                right,
            } => {
                let Some(local) = goal.lookup_local_by_name(&hypothesis.text) else {
                    return Err(unknown_hypothesis(ctx, "cases", hypothesis, &goal));
                };
                let kernel::Type::Either {
                    left_type,
                    right_type,
                } = &local.typ
                else {
                    let mut diag =
                        wrong_hypothesis_shape("cases", "A or B", hypothesis, &local.typ);

                    // An earlier local with the same name might be the either that was meant.
                    if let Some(hidden) = goal.iter_hidden_locals().find(|hidden| {
                        hidden.name == local.name
                            && matches!(hidden.typ, kernel::Type::Either { .. })
                    }) {
                        diag = diag.with_note(hidden_note(hidden));
                    }

                    return Err(diag.with_note(goal_note(&goal)));
                };
                let left_type = (**left_type).clone();
                let right_type = (**right_type).clone();

                let mut right_locals = goal.locals.clone();
                right_locals.push(Local {
                    name: right.text.clone(),
                    typ: right_type.clone(),
                });
                let right_goal_id = proof_state.push_new_goal(right_locals, goal.target.clone());

                let mut left_locals = goal.locals.clone();
                left_locals.push(Local {
                    name: left.text.clone(),
                    typ: left_type.clone(),
                });
                let left_goal_id = proof_state.push_new_goal(left_locals, goal.target.clone());

                let solution = Partial::Case {
                    span: *span,
                    either: var(hypothesis.span, &hypothesis.text),
                    left_name: left.text.clone(),
                    left_body: Box::new(Partial::Hole {
                        goal_id: left_goal_id,
                    }),
                    right_name: right.text.clone(),
                    right_body: Box::new(Partial::Hole {
                        goal_id: right_goal_id,
                    }),
                };

                proof_state.add_solution(goal.id, solution);
            }
            Tactic::Have {
                span,
                hypothesis,
                typ,
            } => {
                // Transform `have h : T` to `(fun (h : T) => ?1) ?2` where:
                //     ?1 is goal.locals, h : T ⊢ goal.target
                //     ?2 is goal.locals ⊢ T

                let mut new_locals = goal.locals.clone();
                new_locals.push(Local {
                    name: hypothesis.text.clone(),
                    typ: typ.clone(),
                });
                let new_goal_id = proof_state.push_new_goal(new_locals, goal.target.clone());

                let h_goal_id = proof_state.push_new_goal(goal.locals.clone(), typ.clone());

                let solution = Partial::Application {
                    span: *span,
                    function: Box::new(Partial::Lambda {
                        span: *span,
                        argument: hypothesis.text.clone(),
                        argument_type: typ.clone(),
                        body: Box::new(Partial::Hole {
                            goal_id: new_goal_id,
                        }),
                    }),
                    argument: Box::new(Partial::Hole { goal_id: h_goal_id }),
                };

                proof_state.add_solution(goal.id, solution);
            }
            Tactic::Apply { span, term } => {
                // Only a name for now: its type comes from the goal or the context. Any other
                // term would need type inference.
                let kernel::Term::Var {
                    span: name_span,
                    name,
                    type_arguments,
                } = term
                else {
                    return Err(Diagnostic::error(
                        "`apply` needs a hypothesis or theorem name",
                        term.span(),
                    )
                    .with_primary_label("not a name")
                    .with_note(
                        "to apply a more complex term, give it a name first: \
                         `have h : T; { exact <term> }; apply h`",
                    ));
                };

                // Locals first, as in the kernel.
                let function_type = if let Some(local) = goal.lookup_local_by_name(name) {
                    if !type_arguments.is_empty() {
                        return Err(Diagnostic::error(
                            format!("`{name}` takes no type arguments"),
                            *name_span,
                        )
                        .with_primary_label(format!(
                            "{} supplied",
                            kernel::count(type_arguments.len(), "type argument")
                        ))
                        .with_note(format!(
                            "`{name}` is a hypothesis; only theorems and axioms take type arguments"
                        ))
                        .with_note(goal_note(&goal)));
                    }
                    local.typ.clone()
                } else if let Some((scheme, _)) = ctx.lookup(name) {
                    scheme.instantiate(type_arguments).map_err(|mismatch| {
                        kernel::type_arity_error(name, scheme, mismatch, *name_span)
                            .with_note(goal_note(&goal))
                    })?
                } else {
                    return Err(unknown_name(name, *name_span, &goal, proof_state));
                };

                // `f : P1 -> ... -> Pn -> C` proves the goal `C` from proofs of `P1` ... `Pn`. Take
                // the smallest `n` that works, so that `f : A -> B -> C` on the goal `B -> C`
                // leaves just `A`.
                let mut premises = Vec::new();
                let mut conclusion = &function_type;
                while *conclusion != goal.target {
                    let kernel::Type::Lambda {
                        argument_type,
                        result_type,
                    } = conclusion
                    else {
                        return Err(Diagnostic::error(
                            format!("`apply` can't use `{name}` to prove `{}`", goal.target),
                            *name_span,
                        )
                        .with_primary_label(format!("`{name}` has type `{function_type}`"))
                        .with_note(format!(
                            "`apply {name}` needs `{name}` to have type `{target}`, or \
                             `P -> {target}`, `P -> Q -> {target}` and so on",
                            target = goal.target
                        ))
                        .with_note(goal_note(&goal)));
                    };
                    premises.push((**argument_type).clone());
                    conclusion = result_type;
                }

                // Push the premises last first, so the first premise is the next goal.
                let mut premise_goal_ids: Vec<GoalId> = premises
                    .into_iter()
                    .rev()
                    .map(|premise| proof_state.push_new_goal(goal.locals.clone(), premise))
                    .collect();
                premise_goal_ids.reverse();

                // `f ?1 ... ?n`
                let solution = premise_goal_ids.into_iter().fold(
                    Partial::Term { term: term.clone() },
                    |function, goal_id| Partial::Application {
                        span: *span,
                        function: Box::new(function),
                        argument: Box::new(Partial::Hole { goal_id }),
                    },
                );

                proof_state.add_solution(goal.id, solution);
            }
        }
    }

    proof_state.pop_focus(script)
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
                "an earlier `h` has type `A`, but a later hypothesis with the same name hides it; \
                 give one of them a different name",
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

    #[test]
    fn test_exfalso() {
        assert_eq!(
            elaborate_str(
                "theorem t A B : A -> not A -> B := by intro a; intro na; exfalso; exact na a."
            ),
            "(fun a [A] (fun na [not A] (absurd [B] (app na a))))"
        );
    }

    #[test]
    fn test_destruct() {
        // A redex binds the two parts: `(fun (a : A) => fun (b : B) => ?) (fst h) (snd h)`.
        assert_eq!(
            elaborate_str(
                "theorem t A B : A and B -> B := by intro h; destruct h as a b; exact b."
            ),
            "(fun h [A and B] (app (app (fun a [A] (fun b [B] b)) (fst h)) (snd h)))"
        );
        // The parts can reuse the pair's name: `fst h` and `snd h` are outside the lambdas, so they
        // still refer to the pair.
        assert_eq!(
            elaborate_str(
                "theorem t A B : A and B -> A := by intro h; destruct h as h b; exact h."
            ),
            "(fun h [A and B] (app (app (fun h [A] (fun b [B] h)) (fst h)) (snd h)))"
        );
    }

    #[test]
    fn test_destruct_uses_the_visible_hypothesis() {
        // The newer `h` is the pair; the older one is hidden.
        assert_eq!(
            elaborate_str(
                "theorem t A B C : C -> A and B -> A := by intro h; intro h; destruct h as a b; exact a."
            ),
            "(fun h [C] (fun h [A and B] (app (app (fun a [A] (fun b [B] a)) (fst h)) (snd h))))"
        );
    }

    #[test]
    fn test_destruct_terms_are_accepted_by_the_kernel() {
        // The elaborator's tests above don't run the kernel; check the redexes really type-check,
        // including the name-reusing ones.
        let summary = crate::process_module(
            r#"
            theorem t1 A B : A and B -> B and A := by
                intro h; destruct h as a b; split; { exact b }; { exact a }.
            theorem t2 A B : A and B -> A := by intro h; destruct h as h b; exact h.
            theorem t3 A B : A and B -> B := by intro h; destruct h as a h; exact h.
            theorem t4 A B C : (A and B) and C -> B := by
                intro h; destruct h as ab c; destruct ab as a b; exact b.
            "#,
        )
        .unwrap_or_else(|diag| panic!("should accept, but got `{}`", diag.message));
        assert_eq!((summary.proved, summary.admitted), (4, 0));
    }

    #[test]
    fn test_focus_builds_the_same_term() {
        // Blocks only group tactics; the term is the same as without them.
        let without = elaborate_str(
            "theorem t A B C : A -> B -> C -> (A and B) and C := by \
             intro a; intro b; intro c; split; split; exact a; exact b; exact c.",
        );
        let with = elaborate_str(
            "theorem t A B C : A -> B -> C -> (A and B) and C := by \
             intro a; intro b; intro c; split; { split; { exact a }; { exact b } }; { exact c }.",
        );
        assert_eq!(with, without);
    }

    #[test]
    fn test_destruct_errors() {
        let source = "theorem t A : A -> A := by intro h; destruct x as a b; exact h.";
        let diag = reject(source);
        assert_eq!(diag.message, "cannot find hypothesis `x`");
        assert_eq!(
            primary_label(source, &diag),
            ("x".to_string(), "not a hypothesis".to_string())
        );
        assert_eq!(diag.notes, vec!["the goal is\nh : A\n⊢ A"]);

        // A theorem or axiom isn't a hypothesis.
        let diag =
            reject("axiom p A B : A and B.\ntheorem t A B : A := by destruct p as a b; exact a.");
        assert_eq!(diag.message, "cannot find hypothesis `p`");
        assert_eq!(
            diag.notes,
            vec![
                "`p` is a theorem or axiom, but `destruct` only works on hypotheses",
                "the goal is\n⊢ A",
            ]
        );

        let source = "theorem t A B : A or B -> A := by intro h; destruct h as a b; exact a.";
        let diag = reject(source);
        assert_eq!(
            diag.message,
            "`destruct` needs a hypothesis of the form `A and B`"
        );
        assert_eq!(
            primary_label(source, &diag),
            ("h".to_string(), "`h` has type `A or B`".to_string())
        );
        assert_eq!(diag.notes, vec!["the goal is\nh : A or B\n⊢ A"]);

        // The pair that was meant is hidden by a later hypothesis with the same name.
        let diag = reject(
            "theorem t A B C : A and B -> C -> A := by intro h; intro h; destruct h as a b; exact a.",
        );
        assert_eq!(
            diag.notes,
            vec![
                "an earlier `h` has type `A and B`, but a later hypothesis with the same name hides it; \
                 give one of them a different name",
                "the goal is\nh : C\n⊢ A",
            ]
        );
    }

    #[test]
    fn test_unsolved_goals_in_a_block() {
        let source = "theorem t A B : A -> B -> (A and B) and A := by intro a; intro b; split; { split; exact a }; { exact a }.";
        let diag = reject(source);
        assert_eq!(diag.message, "1 unsolved goal");
        assert_eq!(
            primary_label(source, &diag),
            (
                "exact a".to_string(),
                "the block is incomplete after this tactic".to_string()
            )
        );
        assert_eq!(diag.labels[0].span.start, source.find("exact a").unwrap());
        assert_eq!(
            diag.notes,
            vec![
                "the goal is\na : A\nb : B\n⊢ B",
                "a `{ ... }` block must prove its goal before the `}`",
            ]
        );
    }

    #[test]
    fn test_no_goals_left_in_a_block() {
        let source = "theorem t A B : A -> B -> B and A := by intro a; intro b; split; { exact b; exact a }.";
        let diag = reject(source);
        assert_eq!(diag.message, "no goals left");
        assert_eq!(diag.labels[0].span.start, source.rfind("exact a").unwrap());
        assert_eq!(
            diag.notes,
            vec![
                "a `{ ... }` block works on a single goal, which is already proved; close the \
                 block with `}` before working on the next goal"
            ]
        );

        // A block with no goal to work on.
        let diag = reject("theorem t A : A -> A := by intro a; exact a; { exact a }.");
        assert_eq!(diag.message, "no goals left");
        assert_eq!(diag.notes, vec!["try removing the tactic"]);
    }

    #[test]
    fn test_cases() {
        assert_eq!(
            elaborate_str(
                "theorem t A B : A or B -> B or A := by \
                 intro h; cases h as a b; { right; exact a }; { left; exact b }."
            ),
            "(fun h [A or B] (case h a (inr [B] a) b (inl [A] b)))"
        );
        // Without blocks, the left branch's goal comes first.
        assert_eq!(
            elaborate_str(
                "theorem t A B : A or B -> B or A := by \
                 intro h; cases h as a b; right; exact a; left; exact b."
            ),
            "(fun h [A or B] (case h a (inr [B] a) b (inl [A] b)))"
        );
    }

    #[test]
    fn test_cases_uses_the_visible_hypothesis() {
        assert_eq!(
            elaborate_str(
                "theorem t A B C : C -> A or B -> B or A := by \
                 intro h; intro h; cases h as a b; { right; exact a }; { left; exact b }."
            ),
            "(fun h [C] (fun h [A or B] (case h a (inr [B] a) b (inl [A] b))))"
        );
    }

    #[test]
    fn test_have() {
        // `have h : T` is `(fun (h : T) => <rest>) <proof of T>`, and the proof of `T` comes
        // first.
        assert_eq!(
            elaborate_str(
                "theorem t A B : A -> A and A := by intro a; have h : A; exact a; split; exact h; exact h."
            ),
            "(fun a [A] (app (fun h [A] (pair h h)) a))"
        );
    }

    #[test]
    fn test_new_tactics_are_accepted_by_the_kernel() {
        // The elaborator's tests above don't run the kernel; check these terms really type-check.
        let summary = crate::process_module(
            r#"
            theorem or_comm A B : A or B -> B or A := by
                intro h; cases h as a b; { right; exact a }; { left; exact b }.
            theorem reuse A B : A or B -> B or A := by
                intro h; cases h as h h; { right; exact h }; { left; exact h }.
            theorem have_twice A : A -> A and A := by
                intro a; have h : A; { exact a }; have k : A; { exact h }; split; exact h; exact k.
            theorem have_then_cases A B : (A or B) and (A -> B) -> B := by
                intro p; destruct p as ab f; have g : B -> B; { intro b; exact b };
                cases ab as a b; { exact f a }; { exact g b }.
            "#,
        )
        .unwrap_or_else(|diag| panic!("should accept, but got `{}`", diag.message));
        assert_eq!((summary.proved, summary.admitted), (4, 0));
    }

    #[test]
    fn test_have_does_not_leak_into_its_own_proof() {
        // The proof of `T` doesn't have `h` in scope, either in the goal...
        let diag = reject("theorem t A : A := by have h : A; { split }; { exact h }.");
        assert_eq!(diag.notes, vec!["the goal is\n⊢ A"]);

        // ...or in the term: the kernel can't find `h` there.
        let source = "theorem t A : A := by have h : A; { exact h }; { exact h }.";
        let diag = reject(source);
        assert_eq!(diag.message, "cannot find `h` in this scope");
        assert_eq!(
            diag.notes,
            vec![
                "`h` is a hypothesis of a later goal, but not of this one; for example, the \
                 hypothesis of a `have` can't be used in its own proof",
                "the goal is\n⊢ A",
            ]
        );
        assert_eq!(
            diag.labels[0].span.start,
            source.find("exact h").unwrap() + "exact ".len()
        );
    }

    #[test]
    fn test_cases_errors() {
        let source = "theorem t A : A -> A := by intro h; cases x as a b; exact h.";
        let diag = reject(source);
        assert_eq!(diag.message, "cannot find hypothesis `x`");
        assert_eq!(
            primary_label(source, &diag),
            ("x".to_string(), "not a hypothesis".to_string())
        );

        let diag =
            reject("axiom em A : A or not A.\ntheorem t A : A := by cases em as a b; admit.");
        assert_eq!(
            diag.notes,
            vec![
                "`em` is a theorem or axiom, but `cases` only works on hypotheses",
                "the goal is\n⊢ A",
            ]
        );

        let source = "theorem t A B : A and B -> A := by intro h; cases h as a b; exact a.";
        let diag = reject(source);
        assert_eq!(
            diag.message,
            "`cases` needs a hypothesis of the form `A or B`"
        );
        assert_eq!(
            primary_label(source, &diag),
            ("h".to_string(), "`h` has type `A and B`".to_string())
        );

        let diag = reject(
            "theorem t A B C : A or B -> C -> A := by intro h; intro h; cases h as a b; exact a.",
        );
        assert_eq!(
            diag.notes,
            vec![
                "an earlier `h` has type `A or B`, but a later hypothesis with the same name hides it; \
                 give one of them a different name",
                "the goal is\nh : C\n⊢ A",
            ]
        );
    }

    #[test]
    fn test_cases_with_unsolved_branch() {
        let source =
            "theorem t A B : A or B -> B or A := by intro h; cases h as a b; right; exact a.";
        let diag = reject(source);
        assert_eq!(diag.message, "1 unsolved goal");
        assert_eq!(diag.notes, vec!["the goal is\nh : A or B\nb : B\n⊢ B or A"]);
    }

    #[test]
    fn test_exact_with_unknown_name() {
        let source = "theorem t A : A -> A := by intro a; exact b.";
        let diag = reject(source);
        assert_eq!(diag.message, "cannot find `b` in this scope");
        assert_eq!(
            primary_label(source, &diag),
            (
                "b".to_string(),
                "not a hypothesis, theorem or axiom".to_string()
            )
        );
        // No "later goal" note: `b` isn't a hypothesis anywhere.
        assert_eq!(diag.notes, vec!["the goal is\na : A\n⊢ A"]);
    }

    #[test]
    fn test_exact_names_bound_inside_the_term_are_fine() {
        // `x`, `l` and `r` are bound by the term itself, and `id` is a theorem.
        let summary = crate::process_module(
            r#"
            theorem id A : A -> A := fun (x : A) => x.
            theorem t A B : A or B -> B or A := by
                exact fun (x : A or B) => case x of | inl l => inr [B] (id [A] l) | inr r => inl [A] r.
            "#,
        )
        .unwrap_or_else(|diag| panic!("should accept, but got `{}`", diag.message));
        assert_eq!((summary.proved, summary.admitted), (2, 0));
    }

    #[test]
    fn test_empty_script_shows_the_goal() {
        let source = "theorem t A B : A and B -> B and A := by .";
        let diag = reject(source);
        assert_eq!(diag.message, "1 unsolved goal");
        assert_eq!(
            primary_label(source, &diag),
            ("by".to_string(), "the proof has no tactics yet".to_string())
        );
        assert_eq!(diag.notes, vec!["the goal is\n⊢ A and B -> B and A"]);
    }

    #[test]
    fn test_empty_block_shows_its_goal() {
        let source =
            "theorem t A B : A -> B -> B and A := by intro a; intro b; split; { }; { exact a }.";
        let diag = reject(source);
        assert_eq!(diag.message, "1 unsolved goal");
        assert_eq!(
            primary_label(source, &diag),
            ("{".to_string(), "the block has no tactics yet".to_string())
        );
        assert_eq!(
            diag.notes,
            vec![
                "the goal is\na : A\nb : B\n⊢ B",
                "a `{ ... }` block must prove its goal before the `}`",
            ]
        );
    }

    #[test]
    fn test_apply() {
        // One premise becomes one goal.
        assert_eq!(
            elaborate_str(
                "theorem t A B : (A -> B) -> A -> B := by intro f; intro a; apply f; exact a."
            ),
            "(fun f [A -> B] (fun a [A] (app f a)))"
        );
        // Several premises become goals in order, first premise first.
        assert_eq!(
            elaborate_str(
                "theorem t A B C : (A -> B -> C) -> A -> B -> C := by \
                 intro f; intro a; intro b; apply f; exact a; exact b."
            ),
            "(fun f [A -> B -> C] (fun a [A] (fun b [B] (app (app f a) b))))"
        );
        // A hypothesis that already proves the goal leaves no goals, like `exact`.
        assert_eq!(
            elaborate_str("theorem t A : A -> A := by intro a; apply a."),
            "(fun a [A] a)"
        );
    }

    #[test]
    fn test_apply_uses_as_few_premises_as_possible() {
        // On the goal `B -> C`, `f : A -> B -> C` needs only `A`.
        assert_eq!(
            elaborate_str(
                "theorem t A B C : (A -> B -> C) -> A -> B -> C := by \
                 intro f; intro a; apply f; exact a."
            ),
            "(fun f [A -> B -> C] (fun a [A] (app f a)))"
        );
    }

    #[test]
    fn test_apply_negation() {
        // `not B` is `B -> False`, so applying it to the goal `False` leaves `B`.
        assert_eq!(
            elaborate_str(
                "theorem t A B : (A -> B) -> not B -> not A := by \
                 intro f; intro nb; intro a; apply nb; apply f; exact a."
            ),
            "(fun f [A -> B] (fun nb [not B] (fun a [A] (app nb (app f a)))))"
        );
    }

    #[test]
    fn test_apply_uses_the_visible_hypothesis() {
        // The later `f` hides the earlier one.
        assert_eq!(
            elaborate_str(
                "theorem t A B : (B -> A) -> (A -> B) -> A -> B := by \
                 intro f; intro f; intro a; apply f; exact a."
            ),
            "(fun f [B -> A] (fun f [A -> B] (fun a [A] (app f a))))"
        );
    }

    #[test]
    fn test_apply_theorems_and_axioms() {
        // Theorems and axioms need their type arguments; the terms must pass the kernel too.
        let summary = crate::process_module(
            r#"
            theorem id A : A -> A := fun (x : A) => x.
            axiom mp A B : A -> (A -> B) -> B.
            theorem use_id B : B -> B := by apply id [B].
            theorem use_mp A B : A -> (A -> B) -> B := by
                intro a; intro f; apply mp [A] [B]; { exact a }; { exact f }.
            theorem compound A B : (A -> B) -> A -> B := by
                intro f; intro a; apply id [A -> B]; { exact f }; { exact a }.
            "#,
        )
        .unwrap_or_else(|diag| panic!("should accept, but got `{}`", diag.message));
        assert_eq!((summary.proved, summary.admitted), (4, 0));
    }

    #[test]
    fn test_apply_leaves_premises_as_goals() {
        let source = "theorem t A B C : (A -> B -> C) -> C := by intro f; apply f.";
        let diag = reject(source);
        assert_eq!(diag.message, "2 unsolved goals");
        assert_eq!(
            diag.notes,
            vec![
                "goal 1 of 2 is\nf : A -> B -> C\n⊢ A",
                "goal 2 of 2 is\nf : A -> B -> C\n⊢ B",
            ]
        );
    }

    #[test]
    fn test_apply_errors() {
        // The conclusion doesn't match the goal.
        let source = "theorem t A B : (A -> B) -> A -> A := by intro f; intro a; apply f; exact a.";
        let diag = reject(source);
        assert_eq!(diag.message, "`apply` can't use `f` to prove `A`");
        assert_eq!(
            primary_label(source, &diag),
            ("f".to_string(), "`f` has type `A -> B`".to_string())
        );
        assert_eq!(
            diag.notes,
            vec![
                "`apply f` needs `f` to have type `A`, or `P -> A`, `P -> Q -> A` and so on",
                "the goal is\nf : A -> B\na : A\n⊢ A",
            ]
        );

        // Not a name.
        let source = "theorem t A : A -> A := by intro a; apply (fun (x : A) => x) a.";
        let diag = reject(source);
        assert_eq!(diag.message, "`apply` needs a hypothesis or theorem name");
        assert_eq!(
            primary_label(source, &diag),
            ("(fun (x : A) => x) a".to_string(), "not a name".to_string())
        );

        // An unknown name.
        let source = "theorem t A : A -> A := by intro a; apply g.";
        let diag = reject(source);
        assert_eq!(diag.message, "cannot find `g` in this scope");
        assert_eq!(
            primary_label(source, &diag),
            (
                "g".to_string(),
                "not a hypothesis, theorem or axiom".to_string()
            )
        );

        // Type arguments on a hypothesis.
        let source = "theorem t A : A -> A := by intro a; apply a [A].";
        let diag = reject(source);
        assert_eq!(diag.message, "`a` takes no type arguments");
        assert_eq!(
            diag.notes,
            vec![
                "`a` is a hypothesis; only theorems and axioms take type arguments",
                "the goal is\na : A\n⊢ A",
            ]
        );

        // Missing type arguments on a theorem: worded as in the kernel.
        let diag = reject(
            "theorem id A : A -> A := fun (x : A) => x.\ntheorem t B : B -> B := by apply id.",
        );
        assert_eq!(
            diag.message,
            "`id` takes 1 type argument but 0 were supplied"
        );
        assert_eq!(
            diag.notes,
            vec![
                "`id` has type parameters `A`; supply one type for each: `id [A]`",
                "the goal is\n⊢ B -> B",
            ]
        );
    }
}
