//! An alternative solver.

use ir::*;
use std::collections::{HashMap, HashSet};
use std::usize;

pub struct WfsSolver {
    program: Arc<ProgramEnvironment>,
    table: HashMap<CanonicalGoal, TableEntry>,
    stack: Vec<StackEntry>,
}

struct StackEntry {
    goal: CanonicalGoal,
    pos_link: usize,
    neg_link: usize,
}

struct TableEntry {
    answers: HashSet<CanonicalGoal>,
    positives: Vec<WaitingGoal>,
    negatives: Vec<WaitingGoal>,
    completely_evaluated: bool,
}

struct WaitingGoal {
    subgoal: CanonicalGoal,
    clause: CanonicalGoal,
}

type CanonicalGoal = Canonical<InEnvironment<Goal>>;

impl WfsSolver {
    pub fn new(program: &Arc<ProgramEnvironment>, goal: Goal) {
        let program = program.clone();

        // Initial program has no free variables, so it is canonical
        // by definition, and it starts from an empty environment.
        let canonical_goal = Canonical {
            value: InEnvironment::empty(goal),
            binders: vec![],
        };

        let mut table = HashMap::new();
        table.insert(
            canonical_goal.clone(),
            TableEntry {
                answers: HashSet::new(),
                positives: vec![],
                negatives: vec![],
                completely_evaluated: false,
            });

        let stack = vec![
            StackEntry {
                goal: canonical_goal,
                pos_link: 0,
                neg_link: usize::MAX,
            }
        ];

        let mut wfs = WfsSolver { program, table, stack };

        let mut pos_min = 1;
        let mut neg_min = usize::MAX;
        wfs.subgoal(&canonical_goal, &mut pos_min, &mut neg_min);
    }

    fn subgoal(&mut self,
               goal: &CanonicalGoal,
               pos_min: &mut usize,
               neg_min: &mut usize) {
        for resolvent in resolvents {
            self.new_clause(resolvent, goal, pos_min, neg_min)
        }
        self.complete(goal, pos_min, neg_min)
    }

    /// Create obligations for the given goal in the given environment. This may
    /// ultimately create any number of obligations.
    pub fn push_goal(&mut self, environment: &Arc<Environment>, goal: Goal) {
        debug!("push_goal({:?}, {:?})", goal, environment);
        match goal {
            Goal::Quantified(QuantifierKind::ForAll, subgoal) => {
                let mut new_environment = environment.clone();
                let parameters: Vec<_> =
                    subgoal.binders
                           .iter()
                           .map(|pk| {
                               new_environment = new_environment.new_universe();
                               match *pk {
                                   ParameterKind::Lifetime(()) => {
                                       let lt = Lifetime::ForAll(new_environment.universe);
                                       ParameterKind::Lifetime(lt)
                                   }
                                   ParameterKind::Ty(()) =>
                                       ParameterKind::Ty(Ty::Apply(ApplicationTy {
                                           name: TypeName::ForAll(new_environment.universe),
                                           parameters: vec![]
                                       })),
                               }
                           })
                           .collect();
                let subgoal = subgoal.value.subst(&parameters);
                self.push_goal(&new_environment, subgoal);
            }
            Goal::Quantified(QuantifierKind::Exists, subgoal) => {
                let subgoal = self.instantiate_in(environment.universe,
                                                  subgoal.binders.iter().cloned(),
                                                  &subgoal.value);
                self.push_goal(environment, *subgoal);
            }
            Goal::Implies(wc, subgoal) => {
                let new_environment = &environment.add_clauses(wc);
                self.push_goal(new_environment, *subgoal);
            }
            Goal::And(subgoal1, subgoal2) => {
                self.push_goal(environment, *subgoal1);
                self.push_goal(environment, *subgoal2);
            }
            Goal::Not(subgoal) => {
                let in_env = InEnvironment::new(environment, *subgoal);
                self.obligations.push(Obligation::Refute(in_env));
            }
            Goal::Leaf(wc) => {
                self.obligations.push(Obligation::Prove(InEnvironment::new(environment, wc)));
            }
        }
    }
}
