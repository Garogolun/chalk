//! An alternative solver based around the well-formed semantics. This
//! algorithm is very closed based on the description found in the
//! following paper, which I will refer to in the comments as EWFS:
//!
//!     Efficient Top-Down Computation of Queries Under the Well-formed Semantics
//!     (Chen, Swift, and Warren; Journal of Logic Programming '95)
//!
//! However, to understand that paper, I would recommend first
//! starting with the following paper, which I will refer to in the
//! comments as NFTD:
//!
//!     A New Formulation of Tabled resolution With Delay
//!     (Swift; EPIA '99)
//!
//! Another useful paper that gives a kind of high-level overview of
//! concepts at play is the following, which I will refer to as XSB:
//!
//!     XSB: Extending Prolog with Tabled Logic Programming
//!     (Swift and Warren; Theory and Practice of Logic Programming '10)
//!
//! Glossary of other terms:
//!
//! - WAM: Warren abstract machine, an efficient way to evaluate Prolog programs.
//!   See <http://wambook.sourceforge.net/>.
//! - HH: Hereditary harrop predicates. What Chalk deals in.
//!   Popularized by Lambda Prolog.

use ir::*;
use std::collections::{HashMap, HashSet};
use std::usize;

pub struct WfsSolver {
    program: Arc<ProgramEnvironment>,
}

/// The **FOREST** of evaluation tracks all the in-progress work.
/// Conceptually, it corresponds to the forest F described in NFTD,
/// however, we structure it more like the "table" described in EWFS.
/// In particular, we never materialize the forest and subgraphs
/// *directly*, instead keeping two bits of information:
///
/// - There is **table** for each tree with root node `A :- A` in the forest.
///   This table is indexed by the (canonical) root node A. It contains
///   the answers found so far, as well as links to nodes from other trees in the
///   forest that are still waiting for answeres.
/// - There is a **stack** of nodes `A :- G` from the forest. Roughly
///   speaking, this stack stores nodes in the forest which have not
///   yet been completely evaluated.
///   - Calling this is stack can be a bit misleading: although the
///     activity of the system is focused on the top of the stack, we
///     also will wind up doing things like producing a new answer
///     that feeds into a goal higher-up the stack. For example, we might
///     have a stack like the following (where the stack grows down):
///
///         foo(X) :- bar(X), baz(X).
///         bar(X) :- ...
///
///     Here, we see that `foo(X)` is waiting on a result from `bar(X)`. Let's
///     say we just found an answer, `bar(1)`. In that case, we would feed that answer
///     to `foo`, causing us to push a new stack entry:
///
///         foo(X) :- bar(X), baz(X).
///         bar(X) :- ...
///         foo(X) :- baz(1).
///
///     `bar(X)` and the node on top of it in the stack are not really
///     related. (Indeed, coping with this is actually the source of
///     some complexity in the machine itself.)
struct Forest {
    tables: Tables,
    stack: Stack,
}

/// See `Forest`.
struct Tables {
    /// Maps from a canonical goal to the index of its table.
    table_indices: HashMap<CanonicalGoal, TableIndex>,

    /// Table: as described above, stores the key information for each
    /// tree in the forest.
    tables: Vec<Table>,
}

/// See `Forest`.
struct Stack {
    /// Stack: as described above, stores the in-progress goals.
    stack: Vec<StackEntry>,
}

struct TableIndex {
    value: usize
}

struct StackIndex {
    value: usize
}

struct StackEntry {
    /// The goal G from the stack entry `A :- G` represented here.
    goal: InEnvironment<Goal>,

    /// XXX
    pos_link: usize,

    /// XXX
    neg_link: usize,
}

struct Table {
    /// The canonical goal that started us on this mess.
    canonical_goal: CanonicalGoal,

    /// Inference table for all stack entries related to this goal.
    infer: InferenceTable,

    /// Stores the answers that we have found thus far. These are
    /// expressed as canonical substitutions for the inference
    /// variables found in our initial goal.
    answers: HashSet<CanonicalSubst>,

    /// Stack entries waiting to hear about POSITIVE results from this
    /// table. This occurs when you have something like `foo(X) :-
    /// bar(X)`.
    positives: Vec<WaitingGoal>,

    /// Stack entries waiting to hear about NEGATIVE results from this
    /// table. This occurs when you have something like `foo(X) :- not
    /// bar(X)`.
    negatives: Vec<WaitingGoal>,

    /// True if this table has been COMPLETELY EVALUATED, meaning that
    /// we have found all the answers that there are to find (and put
    /// them in the `answers` set).
    completely_evaluated: bool,
}

/// When we start processing, we have a HH goal, which may include
/// more complex operations than what we are hoping for. We "simplify"
/// these goals into more atomic goals.
struct SimplifiedGoals {
    /// Something that we have to prove to be true. These are always
    /// leaf goals.
    positive: Vec<InEnvironment<LeafGoal>>,

    /// Something that we have to **refute** (prove to be false).
    /// Note that these are HH goals, not leaf goals.
    negative: Vec<InEnvironment<Goal>>,
}

struct WaitingGoal {
    table_index: TableIndex,
    stack_index: StackIndex,
}

type CanonicalGoal = Canonical<InEnvironment<Goal>>;
type CanonicalSubst = Canonical<ConstrainedSubst>>;

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

    /// In EWFS, this is SLG_SUBGOAL. We have expanded it slightly to
    /// account for the fact that we have richer sets of goals in
    /// HH predicates.
    fn subgoal(&mut self,
               table: TableIndex,
               initial_environment: &Arc<Environment>,
               initial_goal: Goal,
               pos_min: &mut usize,
               neg_min: &mut usize) {
        let simplified_goals = self.simplify_goal(initial_environment, initial_goal);

        assert!(simplified_goals.negative.is_empty(),
                "negative goals not implemented yet");

        for positive_goal in simplify_goal.positive {
            for resolvent in resolvents {
                self.new_clause(resolvent, goal, pos_min, neg_min)
            }
            self.complete(goal, pos_min, neg_min)
        }
    }

    fn simplify_goal(&mut self,
                     initial_environment: &Arc<Environment>,
                     initial_goal: Goal)
                     -> Vec<SimplifiedGoals>
    {
        // A stack of higher-level goals to process.
        let mut goals = vec![(initial_environment.clone(), initial_goal)];

        // An accumulated list of leaf goals.
        let mut simplified_goals = SimplifiedGoals {
            positive: vec![],
            negative: vec![],
        };

        while let Some((environment, goal)) = goals.pop() {
            match goal {
                Goal::Quantified(QuantifierKind::ForAll, subgoal) => {
                    let mut new_environment = environment;
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
                    goals.push((new_environment, subgoal));
                }
                Goal::Quantified(QuantifierKind::Exists, subgoal) => {
                    let subgoal = self.instantiate_in(environment.universe,
                                                      subgoal.binders.iter().cloned(),
                                                      &subgoal.value);
                    goals.push((environment, *subgoal))
                }
                Goal::Implies(wc, subgoal) => {
                    let new_environment = &environment.add_clauses(wc);
                    goals.push((new_environment, *subgoal));
                }
                Goal::And(subgoal1, subgoal2) => {
                    goals.push((environment, *subgoal1));
                    goals.push((environment, *subgoal2));
                }
                Goal::Not(subgoal) => {
                    simplified_goals.negative.push(InEnvironment::new(&environment, *subgoal));
                }
                Goal::Leaf(wc) => {
                    simplified_goals.positive.push(InEnvironment::new(&environment, wc));
                }
            }
        }

        simplified_goals
    }

    fn clauses(&mut self,
               environment: &Arc<Environment>,
               goal: &LeafGoal)
               -> Vec<ProgramClause>
    {
        
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
