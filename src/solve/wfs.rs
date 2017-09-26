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
use std::ops::{Index, IndexMut};
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
    positive: Vec<InEnvironment<DomainGoal>>,

    /// Something that we have to **refute** (prove to be false).
    /// Note that these are HH goals, not leaf goals.
    negative: Vec<InEnvironment<Goal>>,
}

/// The paper describes these as `A :- D | G`.
struct ExClause {
    /// The goal of the table `A`.
    table_goal: DomainGoal,

    /// Delayed literals: things that we depend on negatively,
    /// but which have not yet been fully evaluated.
    delayed_literals: Vec<Goal>,

    /// Literals: domain goals that must be proven to be true.
    literals: Vec<DomainGoal>,

    /// Goals: HH goals that must be proven to be true. These are
    /// basically just literals that have not yet been simplified into
    /// domain goals.
    subgoals: Vec<Goal>,
}

struct WaitingGoal {
    table_index: TableIndex,
    stack_index: StackIndex,
}

struct Minimums {
    positive: usize,
    negative: usize,
}

type CanonicalGoal = Canonical<InEnvironment<Goal>>;
type CanonicalSubst = Canonical<ConstrainedSubst>>;
type CanonicalExClause = Canonical<InEnvironment<ExClause>>;

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

        let mut minimums = Minimums { positive: 1, negative: usize::MAX };
        wfs.subgoal_hh(&canonical_goal, &mut minimums)
    }

    /// This is the HH-extension of SLG_SUBGOAL from EWFS. We have
    /// expanded it slightly to account for the fact that we have
    /// richer sets of goals in HH predicates.
    fn subgoal_hh(&mut self,
                  table: TableIndex,
                  initial_environment: &Arc<Environment>,
                  initial_goal: Goal,
                  minimums: &mut Minimums) {
        let simplified_goals = self.simplify_hh_goal(initial_environment, initial_goal)?;

        assert!(simplified_goals.negative.is_empty(),
                "negative goals not implemented yet");

        for InEnvironment { environment, goal } in simplify_goal.positive {
            self.subgoal_leaf(table, environment, goal, minimums);
        }
    }

    /// In EWFS, this is SLG_SUBGOAL.
    fn subgoal_domain(&mut self,
                      table: TableIndex,
                      environment: &Arc<Environment>,
                      goal: DomainGoal,
                      minimums: &mut Minimums) {
        let clauses = self.clauses(&environment, &goal);
        for clause in clauses {
            do catch {
                self.new_clause(table, environment, goal, clause, minimums)?;
            }
        }
    }

    /// Simplifies an HH goal into a series of positive domain goals
    /// and negative HH goals. This operation may fail if the HH goal
    /// includes unifications that cannot be completed.
    fn simplify_hh_goal(&mut self,
                        table_index: TableIndex,
                        initial_environment: &Arc<Environment>,
                        initial_goal: Goal)
                        -> Result<SimplifiedGoals>
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
                Goal::Leaf(LeafGoal::EqGoal(eq_goal)) => {
                    goals.extend(self.unify(table_index, environment, eq_goal)?);
                }
                Goal::Leaf(LeafGoal::DomainGoal(domain_goal)) => {
                    simplified_goals.positive.push(InEnvironment::new(&environment, wc));
                }
            }
        }

        simplified_goals
    }

    fn unify(&mut self,
             table_index: TableIndex,
             environment: &Arc<Environment>,
             eq_goal: &EqGoal)
             -> Result<Vec<(Arc<Environment>, Goal)>>
    {
        self.tables[table_index].unify(environment, &eq_goal.a, &eq_goal.b)
    }

    fn clauses(&mut self,
               environment: &Arc<Environment>,
               goal: &DomainGoal)
               -> Vec<ProgramClause>
    {
        let environment_clauses =
            environment.clauses
                       .iter()
                       .filter(|domain_goal| domain_goal.could_match(goal))
                       .map(|domain_goal| domain_goal.clone().into_program_clause());

        let program_clauses =
            self.program.program_clauses.iter()
                                        .filter(|clause| clause.could_match(goal));

        environment_clauses.chain(program_clauses).collect()
    }

    fn new_clause(&mut self,
                  table_index: TableIndex,
                  environment: &Arc<Environment>,
                  goal: DomainGoal,
                  clause: ProgramClause,
                  minimums: &mut Minimums)
                  -> Result<()>
    {
        // First, compute the SLG resolvent of goal + clause. This
        // operation may fail, in which case the new-clause fails.
        let goals = self.slg_resolve(table_index, environment, goal, clause)?;

        // Now we begin with SLG_NEWCLAUSE proper. What the text calls
        // G is basically the list of clauses in `goals`.
        if goals.is_empty() {
            self.slg_answer()
        } else {
            
        }
    }

    fn slg_resolvent(&mut self,
                     goal: &CanonicalExClause,
                     clause: &Binders<ProgramClauseImplication>)
                     -> Result<CanonicalExClause>
    {
        // From EWFS:
        //
        // Let G be an X-clause A :- D | L1,...Ln, where N > 0, and Li be selected atom.
        //
        // Let C be an X-clause with no delayed literals. Let
        //
        //     C' = A' :- L'1...L'n
        //
        // be a variant of C such that G and C' have no variables in
        // common.
        //
        // Let Li and A' be unified with MGU S.
        //
        // Then:
        //
        //     S(A :- D | L1...Li-1, L1'...Lm', Li+1...Ln)
        //
        // is the SLG resolvent of G with C.

        // Relating the above description to our situation:
        //
        // - `goal` G, except with binders for any existential variables.
        //   - Also, we always select the first literal in `ex_clause.literals`, so `i` is 0.
        // - `clause` is C, except with binders for any existential variables.

        let mut infer = InferenceTable::new();

        // Goal here is now G.
        let InEnvironment { environment, goal } = infer.instantiate(&goal.binders, &goal.value);

        // Clause here is now C' in the description above. Note that G
        // and C' have no variables in common.
        let clause = infer.instantiate_in(environment.universe, &clause.binders, &clause.value);

        // The selected literal for us will always be Ln. See if we
        // can unify that with C'.
        assert!(goal.literals.len() > 0, "goal has no selected literals");
        let selected_literal = goal.literals.pop();
        let UnificationResult { goals, constraints, cannot_prove } =
            infer.unify(environment, &goal.literals[0], clause.implication)?;
        assert!(constraints.is_empty(), "Not yet implemented: region constraints");
        assert!(!cannot_prove, "Not yet implemented: cannot_prove");

        goal.literals.
        subgoals.extend(clause.conditions.into_iter().map(|g| InEnvironment::new(environment, g)));

        // Return the union of L1'...Lm' with those extra conditions. We are assuming
        // in this routine that the selected literal Li was the only literal.
        Ok(subgoals)
    }
}

impl Index<TableIndex> for Tables {
    type Output = Table;

    fn index(&self, index: TableIndex) -> &Table {
        &self.tables[index.value]
    }
}

impl IndexMut<TableIndex> for Tables {
    fn index_mut(&mut self, index: TableIndex) -> &mut Table {
        &mut self.tables[index.value]
    }
}

impl Table {
    /// Unify `a` and `b`. If this succeeds, it returns a series of
    /// sub-goals that must then be processed as a result.
    fn unify<T>(&mut self,
                environment: &Arc<Environment>,
                a: &T,
                b: &T)
                -> Result<Vec<(Arc<Environment>, Goal)>>
        where T: ?Sized + Zip + Debug
    {
        let table = &mut self.tables[table_index];
        let UnificationResult { goals, constraints, cannot_prove } =
            table.infer.unify(environment, a)?;

        assert!(constraints.is_empty(), "Not yet implemented: region constraints");
        assert!(!cannot_prove, "Not yet implemented: cannot_prove");

        Ok(goals.into_iter().map(|goal| (environment.clone(), goal)).collect())
    }

    /// Instantiate `value`, replacing all the bound variables with
    /// free inference variables.
    fn instantiate_binders<T>(&mut self, value: &Binders<T>) -> T::Result
        where T: Fold
    {
        self.infer.instantiate(&value.binders, &value.value)
    }
}
