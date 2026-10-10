use crate::diagnostics::{Diagnostic, Result, Span};
use crate::kernel;
use std::collections::{HashMap, VecDeque};

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

#[derive(Debug, Clone)]
struct Goal {
    id: GoalId,
    locals: Vec<Local>,
    target: kernel::Type,
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
            Partial::Hole { goal_id } => solutions.remove(&goal_id).expect("all goals should be solved before calling fill").fill(solutions),
            Partial::Term { term } => term,
            Partial::Lambda { span, argument, argument_type, body} => kernel::Term::Lambda {
                span,
                argument,
                argument_type,
                body: Box::new(body.fill(solutions))
            },
            Partial::Pair { span, left, right } => kernel::Term::Pair {
                span,
                left: Box::new(left.fill(solutions)),
                right: Box::new(right.fill(solutions))
            },
            Partial::Inl { span, right_type, left } => kernel::Term::Inl {
                span,
                right_type,
                left: Box::new(left.fill(solutions)),
            },
            Partial::Inr { span, left_type, right } => kernel::Term::Inr {
                span,
                left_type,
                right: Box::new(right.fill(solutions)),
            },
        }
    }
}

#[derive(Debug, Clone)]
struct ProofState {
    goals: VecDeque<Goal>,
    solutions: HashMap<GoalId, Partial>,
    next_goal_id: u64,
}

impl ProofState {
    fn add_goal(&mut self, locals: Vec<Local>, target: kernel::Type) -> GoalId {
        let id = GoalId(self.next_goal_id);
        self.next_goal_id += 1;
        let goal = Goal { id, locals, target };
        self.goals.push_back(goal);
        id
    }

    fn pop_goal(&mut self) -> Option<Goal> {
        self.goals.pop_front()
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
    let mut proof_state = ProofState {
        goals: VecDeque::new(),
        solutions: HashMap::new(),
        next_goal_id: 0,
    };

    let root_goal_id = proof_state.add_goal(Vec::new(), target.clone());

    for tactic in &script.tactics {
        let goal = match proof_state.pop_goal() {
            Some(goal) => goal,
            None => {
                return Err(Diagnostic::error("no goals left", tactic.span())
                    .with_primary_label("no goals left")
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

                    let new_goal_id = proof_state.add_goal(new_locals, *result_type);

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
                    return Err(Diagnostic::error(
                        "`intro` needs a goal of the form `A -> B`",
                        *span,
                    ));
                }
            }
            Tactic::Exact { span, term } => {
                let solution = Partial::Term { term: term.clone() };
                proof_state.add_solution(goal.id, solution);
            }
            Tactic::Split { span } => {
                if let kernel::Type::Pair { left_type, right_type } = goal.target {
                    let new_goal_id_left = proof_state.add_goal(goal.locals.clone(), *left_type);
                    let new_goal_id_right = proof_state.add_goal(goal.locals, *right_type);

                    let solution = Partial::Pair {
                        span: *span,
                        left: Box::new(Partial::Hole { goal_id: new_goal_id_left }),
                        right: Box::new(Partial::Hole { goal_id: new_goal_id_right }),
                    };

                    proof_state.add_solution(goal.id, solution);
                } else {
                    return Err(Diagnostic::error(
                        "`split` needs a goal of the form `A and B`",
                        *span,
                    ))
                }
            }
            Tactic::Left { span } => {
                if let kernel::Type::Either { left_type, right_type } = goal.target {
                    let new_goal_id = proof_state.add_goal(goal.locals.clone(), *left_type);

                    let solution = Partial::Inl {
                        span: *span,
                        right_type: *right_type,
                        left: Box::new(Partial::Hole { goal_id: new_goal_id }),
                    };

                    proof_state.add_solution(goal.id, solution);
                } else {
                    return Err(Diagnostic::error(
                        "`left` needs a term of type `A` or `B`",
                        *span,
                    ))
                }
            }
            Tactic::Right { span } => {
                if let kernel::Type::Either { left_type, right_type } = goal.target {
                    let new_goal_id = proof_state.add_goal(goal.locals.clone(), *right_type);

                    let solution = Partial::Inr {
                        span: *span,
                        left_type: *left_type,
                        right: Box::new(Partial::Hole { goal_id: new_goal_id }),
                    };

                    proof_state.add_solution(goal.id, solution);
                } else {
                    return Err(Diagnostic::error(
                        "`right` needs a term of type `A` or `B`",
                        *span,
                    ))
                }
            }
            Tactic::Assumption { span } => {
                todo!()
            }
            Tactic::Admit { span } => {
                let solution = Partial::Term { term: kernel::Term::TrustMe { span: *span, goal_type: goal.target } };
                proof_state.add_solution(goal.id, solution);
            }
        }
    }

    if !proof_state.goals.is_empty() {
        return Err(Diagnostic::error("unresolved goals", script.span))
    }

    Ok(Partial::Hole { goal_id: root_goal_id }.fill(&mut proof_state.solutions))
}
