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

/// The paper describes these as `A :- D | G`.
struct ExClause {
    /// The goal of the table `A`.
    table_goal: InEnvironment<Goal>,

    /// Delayed literals: things that we depend on negatively,
    /// but which have not yet been fully evaluated.
    delayed_literals: Vec<InEnvironment<Goal>>,

    /// Literals: domain goals that must be proven to be true.
    subgoals: Vec<InEnvironment<DomainGoal>>,
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
type CanonicalDomainGoal = Canonical<InEnvironment<DomainGoal>>;
type CanonicalSubst = Canonical<ConstrainedSubst>>;
type CanonicalExClause = Canonical<ExClause>;

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
    fn subgoal(&mut self,
               table: TableIndex,
               canonical_goal: &CanonicalGoal,
               minimums: &mut Minimums) {
        // We are tweaking the paper definition just a bit. In the
        // paper, the first step is to find the SLG resolvent of `A :-
        // A` with some clause. In this implementation, we first
        // "lower" the HH goal to a domain goal, and hence we have
        // something like `A :- L0...Ln`, where `L0...Ln` are domain
        // goals (literals). Then we find the resolvent with the first
        // of *those*.  In the case where the HH goal *is* a domain
        // goal, this should be identical.
        let ex_clause = self.hh_goal_to_ex_clause(canonical_goal);
        let clauses = self.clauses(canonical_goal);

        for clause in &clauses {
            if let Ok(slg_resolvent) = self.slg_resolvent(&ex_clause, clause) {
                self.new_clause(table, slg_resolvent, minimums)?;
            }
        }

        self.complete(table, minimums);
    }

    /// Simplifies an HH goal into a series of positive domain goals
    /// and negative HH goals. This operation may fail if the HH goal
    /// includes unifications that cannot be completed.
    fn simplify_hh_goal(&mut self, goal: &CanonicalGoal) -> Result<CanonicalExClause> {
        let mut infer = InferenceTable::new();

        let initial_env_goal = infer.instantiate(&goal.binders, &goal.value);

        // The final result we will accumulate into.
        let mut ex_clause = ExClause {
            table_goal: initial_env_goal.clone(),

            delayed_literals: vec![],

            subgoals: vec![]
        };

        // A stack of higher-level goals to process.
        let mut pending_goals = vec![initial_env_goal];

        while let Some(InEnvironment { environment, value: goal }) = pending_goals.pop() {
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
                    pending_goals.push(InEnvironment::new(&new_environment, subgoal));
                }
                Goal::Quantified(QuantifierKind::Exists, subgoal) => {
                    let subgoal = self.instantiate_in(environment.universe,
                                                      subgoal.binders.iter().cloned(),
                                                      &subgoal.value);
                    pending_goals.push(InEnvironment::new(&environment, *subgoal))
                }
                Goal::Implies(wc, subgoal) => {
                    let new_environment = &environment.add_clauses(wc);
                    pending_goals.push(InEnvironment::new(&new_environment, *subgoal));
                }
                Goal::And(subgoal1, subgoal2) => {
                    pending_goals.push(InEnvironment::new(&environment, *subgoal1));
                    pending_goals.push(InEnvironment::new(&environment, *subgoal2));
                }
                Goal::Not(subgoal) => {
                    panic!("not yet implemented -- negative goals")
                }
                Goal::Leaf(LeafGoal::EqGoal(eq_goal)) => {
                    let UnificationResult { goals, constraints, cannot_prove } =
                        infer.unify(environment, &eq_goal.a, &eq_goal.b)?;

                    assert!(constraints.is_empty(), "Not yet implemented: region constraints");
                    assert!(!cannot_prove, "Not yet implemented: cannot_prove");

                    pending_goals.extend(goals);
                }
                Goal::Leaf(LeafGoal::DomainGoal(domain_goal)) => {
                    ex_clause.subgoals.push(InEnvironment::new(&environment, domain_goal));
                }
            }
        }

        infer.canonicalize(&ex_clause)
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
               goal: &CanonicalDomainGoal)
               -> Vec<ProgramClause>
    {
        let &InEnvironment { ref environment, value: ref goal } = &goal.value;

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
                  table: TableIndex,
                  ex_clause: &CanonicalExClause, // Contains both A and G together.
                  minimums: &mut Minimums)
                  -> Result<()>
    {
        // Now we begin with SLG_NEWCLAUSE proper. What the text calls
        // G is basically the list of clauses in `goals`.
        if ex_clause.subgoals.is_empty() {
            self.slg_answer(table, ex_clause, minimums)
        } else {
            // Here is where we *would* distinguish between positive/negative literals,
            // but I'm not worrying about negative cases yet.
            self.slg_positive(table, ex_clause, minimums)
        }
    }

    fn slg_positive(&mut self,
                    table: TableIndex,
                    ex_clause: &CanonicalExClause,
                    minimums: &mut Minimums)
    {
        let mut infer = InferenceTable::new();

        let mut ex_clause = infer.instantiate(&ex_clause.binders, &ex_clause.value);

        let selected_subgoal = ex_clause.subgoals.pop().unwrap();
        let canonical_subgoal = infer.canonicalize(&selected_subgoal);
        if /* canonical subgoal is not in table T */ {
            // ...
            let minimums = &mut Minimums::new();
            self.subgoal(new_table_index, &canonical_subgoal, minimums);
            // ...
            return;
        }

        // Canonical subgoal IS in the table T.
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
        let goal = infer.instantiate(&goal.binders, &goal.value);

        // The selected literal for us will always be Ln. See if we
        // can unify that with C'.
        assert!(goal.subgoals.len() > 0, "goal has no selected literals");
        let InEnvironment { environment, value: selected_literal } = goal.subgoals.pop();

        // Clause here is now C' in the description above. Note that G
        // and C' have no variables in common.
        let clause = infer.instantiate_in(environment.universe, &clause.binders, &clause.value);

        // Unify the selected literal Li with C'.
        let UnificationResult { goals, constraints, cannot_prove } =
            infer.unify(environment, &selected_literal, clause.implication)?;

        // One (minor) complication: unification for us sometimes yields further domain goals.
        assert!(constraints.is_empty(), "Not yet implemented: region constraints");
        assert!(!cannot_prove, "Not yet implemented: cannot_prove");
        goal.subgoals.extend(goals);

        // Return the union of L1'...Lm' with those extra conditions. We are assuming
        // in this routine that the selected literal Li was the only literal.
        Ok(infer.canonicalize(&goal))
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
    }

    /// Instantiate `value`, replacing all the bound variables with
    /// free inference variables.
    fn instantiate_binders<T>(&mut self, value: &Binders<T>) -> T::Result
        where T: Fold
    {
        self.infer.instantiate(&value.binders, &value.value)
    }
}
