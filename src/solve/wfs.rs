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

use cast::Caster;
use errors::*;
use ir::*;
use ir::could_match::CouldMatch;
use solve::infer::{InferenceTable, UnificationResult};
use std::collections::{HashMap, HashSet};
use std::cmp::min;
use std::ops::{Index, IndexMut};
use std::sync::Arc;

pub fn solve(program: &Arc<ProgramEnvironment>, goal: Goal) {
    // Forest::solve(program, goal)
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
    program: Arc<ProgramEnvironment>,
    dfn: DepthFirstNumber,
    tables: Tables,
    stack: Stack,
}

/// See `Forest`.
#[derive(Default)]
struct Tables {
    /// Maps from a canonical goal to the index of its table.
    table_indices: HashMap<CanonicalDomainGoal, TableIndex>,

    /// Table: as described above, stores the key information for each
    /// tree in the forest.
    tables: Vec<Table>,
}

/// See `Forest`.
#[derive(Default)]
struct Stack {
    /// Stack: as described above, stores the in-progress goals.
    stack: Vec<StackEntry>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
struct TableIndex {
    value: usize
}

copy_fold!(TableIndex);

/// The StackIndex identifies the position of a table's goal in the
/// stack of goals that are actively being processed. Note that once a
/// table is completely evaluated, it may be popped from the stack,
/// and hence no longer have a stack index.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
struct StackIndex {
    value: usize
}

copy_fold!(StackIndex);

/// The `DepthFirstNumber` (DFN) is a sequential number assigned to
/// each goal when it is first encountered. The naming (taken from
/// EWFS) refers to the idea that this number tracks the index of when
/// we encounter the goal during a depth-first traversal of the proof
/// tree.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct DepthFirstNumber {
    value: u64
}

copy_fold!(DepthFirstNumber);

struct StackEntry {
    /// The goal G from the stack entry `A :- G` represented here.
    table: TableIndex,

    /// The DFN of this computation.
    dfn: DepthFirstNumber,

    /// Tracks the dependencies of this stack entry on things beneath
    /// it in the stack. This field is updated "periodically",
    /// e.g. when a direct subgoal completes. Otherwise, the minimums
    /// for the active computation are tracked in a local variable
    /// that is threaded around.
    link: Minimums,
}

struct Table {
    /// Stores the answers that we have found thus far. These are
    /// expressed as canonical substitutions for the inference
    /// variables found in our initial goal.
    answers: HashSet<CanonicalExClauseAnswer>,

    /// Stack entries waiting to hear about POSITIVE results from this
    /// table. This occurs when you have something like `foo(X) :-
    /// bar(X)`.
    positives: Vec<CanonicalPendingExClause>,

    /// Stack entries waiting to hear about NEGATIVE results from this
    /// table. This occurs when you have something like `foo(X) :- not
    /// bar(X)`.
    negatives: Vec<CanonicalExClause>,

    /// True if this table has been COMPLETELY EVALUATED, meaning that
    /// we have found all the answers that there are to find (and put
    /// them in the `answers` set).
    completely_evaluated: bool,
}

#[derive(Clone, Debug)]
struct PendingExClause {
    goal_depth: StackIndex,
    table_goal: InEnvironment<DomainGoal>,
    selected_literal: InEnvironment<DomainGoal>,
    delayed_literals: Vec<InEnvironment<DomainGoal>>,
    subgoals: Vec<InEnvironment<DomainGoal>>,
}

struct_fold!(PendingExClause {
    goal_depth,
    table_goal,
    selected_literal,
    delayed_literals,
    subgoals
});

/// The paper describes these as `A :- D | G`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct ExClause {
    /// The goal of the table `A`.
    table_goal: InEnvironment<DomainGoal>,

    /// Delayed literals: things that we depend on negatively,
    /// but which have not yet been fully evaluated.
    delayed_literals: Vec<InEnvironment<DomainGoal>>,

    /// Literals: domain goals that must be proven to be true.
    subgoals: Vec<InEnvironment<DomainGoal>>,
}

struct_fold!(ExClause { table_goal, delayed_literals, subgoals });

/// When we actually find an answer to an X-clause,
/// this is it.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct ExClauseAnswer {
    table_goal: InEnvironment<DomainGoal>,
    delayed_literals: Vec<InEnvironment<DomainGoal>>,
}

struct_fold!(ExClauseAnswer { table_goal, delayed_literals });

/// The `Minimums` structure is used to track the dependencies between
/// some item E on the evaluation stack. In particular, tracks cases
/// cases where the success of E depends (or may depend) on items
/// deeper in the stack than E (i.e., with lower DFNs).
///
/// `positive` tracks the lowest index on the stack to which we had a
/// POSITIVE dependency (e.g. `foo(X) :- bar(X)`) -- meaning that in
/// order for E to succeed, the dependency must succeed. It is
/// initialized with the index of the predicate on the stack. So
/// imagine we have a stack like this:
///
/// ```
/// 0 foo(X)   <-- bottom of stack
/// 1 bar(X)
/// 2 baz(X)   <-- top of stack
/// ```
///
/// In this case, `positive` would be initially 0, 1, and 2 for `foo`,
/// `bar`, and `baz` respectively. This reflects the fact that the
/// answers for `foo(X)` depend on the answers for `foo(X)`. =)
///
/// Now imagine that we had a clause `baz(X) :- foo(X)`, inducing a
/// cycle. In this case, we would update `positive` for `baz(X)` to be
/// 0, reflecting the fact that its answers depend on the answers for
/// `foo(X)`. Similarly, the minimum for `bar` would (eventually) be
/// updated, since it too transitively depends on `foo`. `foo` is
/// unaffected.
///
/// `negative` tracks the lowest index on the stack to which we had a
/// NEGATIVE dependency (e.g., `foo(X) :- not { bar(X) }`) -- meaning
/// that for E to succeed, the dependency must fail. This is initially
/// `usize::MAX`, reflecting the fact that the answers for `foo(X)` do
/// not depend on `not(foo(X))`. When negative cycles are encountered,
/// however, this value must be updated.
#[derive(Copy, Clone)]
struct Minimums {
    positive: DepthFirstNumber,
    negative: DepthFirstNumber,
}

struct SimplifiedGoals {
    positive: Vec<InEnvironment<DomainGoal>>,
    negative: Vec<InEnvironment<DomainGoal>>,
}

enum Sign {
    Positive,
    Negative,
}

type CanonicalGoal = Canonical<InEnvironment<Goal>>;
type CanonicalDomainGoal = Canonical<InEnvironment<DomainGoal>>;
type CanonicalSubst = Canonical<ConstrainedSubst>;
type CanonicalExClause = Canonical<ExClause>;
type CanonicalExClauseAnswer = Canonical<ExClauseAnswer>;
type CanonicalPendingExClause = Canonical<PendingExClause>;

impl Forest {
    fn solve_root_domain_goal(program: &Arc<ProgramEnvironment>, goal: DomainGoal)
                              -> HashSet<CanonicalExClauseAnswer> {
        let program = program.clone();

        let mut forest = Forest {
            dfn: DepthFirstNumber::MIN,
            program: program.clone(),
            tables: Tables::default(),
            stack: Stack::default(),
        };

        // Initial program has no free variables, so it is canonical
        // by definition, and it starts from an empty environment.
        let canonical_goal = Canonical {
            value: InEnvironment::empty(goal),
            binders: vec![],
        };

        let root_table_depth = forest.push_new_table(&canonical_goal);
        let root_table = forest.stack[root_table_depth].table;
        let mut minimums = forest.stack[root_table_depth].link;
        let _ = forest.subgoal(root_table_depth, &canonical_goal, &mut minimums);

        forest.tables[root_table].answers.clone()
    }

    /// Pushes a new goal onto the stack, creating a table entry in the process.
    fn push_new_table(&mut self, goal: &CanonicalDomainGoal) -> StackIndex {
        let table = self.tables.insert(goal);
        let dfn = self.dfn.next();
        self.stack.push(table, dfn)
    }

    /// This is SLG_SUBGOAL from EWFS.
    fn subgoal(&mut self,
               goal_depth: StackIndex,
               canonical_goal: &CanonicalDomainGoal,
               minimums: &mut Minimums)
               -> Result<()>
    {
        let clauses = self.clauses(canonical_goal);

        for clause in clauses {
            if let Ok(resolvent) = Self::resolvent_clause(canonical_goal, &clause.implication) {
                // FIXME: we are ignoring fallback here. Have to think about that.
                let _ = self.new_clause(goal_depth, &resolvent, minimums);
            }
        }

        self.complete(goal_depth, minimums);

        Ok(())
    }

    fn clauses(&mut self,
               goal: &CanonicalDomainGoal)
               -> Vec<ProgramClause>
    {
        let &InEnvironment { ref environment, goal: ref goal } = &goal.value;

        let environment_clauses =
            environment.clauses
                       .iter()
                       .filter(|&domain_goal| domain_goal.could_match(goal))
                       .map(|domain_goal| domain_goal.clone().into_program_clause());

        let program_clauses =
            self.program.program_clauses.iter()
                                        .filter(|clause| clause.could_match(goal))
                                        .cloned();

        environment_clauses.chain(program_clauses).collect()
    }

    fn new_clause(&mut self,
                  goal_depth: StackIndex,
                  ex_clause: &CanonicalExClause, // Contains both A and G together.
                  minimums: &mut Minimums)
                  -> Result<()>
    {
        // Now we begin with SLG_NEWCLAUSE proper. What the text calls
        // G is basically the list of clauses in `goals`.
        if ex_clause.value.subgoals.is_empty() {
            self.answer(goal_depth, ex_clause, minimums);
            Ok(())
        } else {
            // Here is where we *would* distinguish between positive/negative literals,
            // but I'm not worrying about negative cases yet.
            self.positive(goal_depth, ex_clause, minimums)
        }
    }

    fn positive(&mut self,
                goal_depth: StackIndex,
                ex_clause: &CanonicalExClause,
                minimums: &mut Minimums)
                -> Result<()>
    {
        let mut infer = InferenceTable::new();

        let mut ex_clause = infer.instantiate_canonical(&ex_clause);

        let selected_literal = ex_clause.subgoals.pop().unwrap();

        // First, check if we have an existing table for this selected literal.
        let canonical_literal = infer.canonicalize(&selected_literal).quantified;
        let index = match self.tables.index_of(&canonical_literal) {
            Some(i) => i,
            None => {
                // If not, that's the easy case. Start a new table.
                let subgoal_depth = self.push_new_table(&canonical_literal);
                let mut subgoal_minimums = self.stack.top().link;
                self.subgoal(subgoal_depth, &canonical_literal, &mut subgoal_minimums);
                self.update_solution(goal_depth,
                                     subgoal_depth,
                                     Sign::Positive,
                                     minimums,
                                     &mut subgoal_minimums);
                return Ok(());
            }
        };

        // Otherwise, we have encountered a cycle. This is a bit
        // tricky. We will start by registering ourselves to receive
        // any new answers that will come later.
        let pending_ex_clause = {
            let Canonical {
                binders,
                value: (table_goal, selected_literal, delayed_literals, subgoals)
            } = infer.canonicalize(&(
                &ex_clause.table_goal,
                &selected_literal,
                &ex_clause.delayed_literals,
                &ex_clause.subgoals
            )).quantified;

            Canonical {
                binders,
                value: PendingExClause {
                    goal_depth, table_goal, selected_literal, delayed_literals, subgoals
                }
            }
        };
        self.tables[index].positives.push(pending_ex_clause);

        // Next, we will process the answers that have already been
        // found one by one.
        let mut new_ex_clauses = {
            self.tables[index]
                .answers
                .iter()
                .flat_map(|answer| {
                    Self::incorporate_cached_answer(&mut infer,
                                                    &ex_clause,
                                                    &selected_literal,
                                                    answer)
                })
                .collect()
        };

        for ex_clause in new_ex_clauses {
            let _ = self.new_clause(goal_depth, &ex_clause, minimums);
        }

        Ok(())
    }

    fn incorporate_cached_answer(infer: &mut InferenceTable,
                                 ex_clause: &ExClause,
                                 selected_literal: &InEnvironment<DomainGoal>,
                                 answer: &CanonicalExClauseAnswer)
                                 -> Result<CanonicalExClause>
    {
        if answer.value.delayed_literals.is_empty() {
            Self::resolvent_answer(infer,
                                   ex_clause,
                                   selected_literal,
                                   answer)
        } else {
            unimplemented!("delayed literals")
        }
    }

    fn answer(&mut self,
              goal_depth: StackIndex,
              ex_clause: &CanonicalExClause, // Contains both A and G together.
              minimums: &mut Minimums)
    {
        // Produce the canonical form of the answer.
        let canonical_answer = {
            let Canonical {
                binders,
                value: ExClause {
                    table_goal,
                    delayed_literals,
                    subgoals,
                },
            } = ex_clause.clone();

            // Subtle: to produce the canonical answer, it is safe to extract
            // the canonicalized bits from `ex_clause` and just drop `subgoals`;
            // it cannot disturb the canonical ordering of variables because it is
            // just an empty vector, and hence does not contain any variables.
            assert!(subgoals.is_empty(), "...else not an answer");

            Canonical {
                binders: ex_clause.binders.clone(),
                value: ExClauseAnswer {
                    table_goal,
                    delayed_literals,
                },
            }
        };

        // If we've already seen this answer, we're done.
        let goal_table = self.stack[goal_depth].table;
        if self.tables[goal_table].answers.contains(&canonical_answer) {
            return;
        }

        // Otherwise, the answer is new, so insert it into our answer
        // set, and then find the people that are waiting and deliver
        // it to them.
        self.tables[goal_table].answers.insert(canonical_answer.clone());
        if ex_clause.value.delayed_literals.is_empty() {
            // Clear out all the people waiting for negative results; we
            // have an answer now, so they have failed.
            self.tables[goal_table].negatives = vec![];

            // Produce a list of people waiting for *positive* results.
            let mut list: Vec<_> =
                self.tables[goal_table]
                .positives
                .iter()
                .filter_map(|p| Self::resolvent_pending(p, &canonical_answer).ok())
                .collect();

            // Process each of them in turn.
            for (pending_table, pending_ex_clause) in list {
                let _ = self.new_clause(pending_table, &pending_ex_clause, minimums);
            }
        } else {
            unimplemented!("delayed literals")
        }
    }

    /// Updates `minimums` to account for the dependencies of a
    /// subgoal. Invoked when:
    ///
    /// - in the midst of solving `table`,
    /// - `subgoal_table` was the selected literal,
    /// - we invoked `subgoal()` and it returned,
    /// - with `subgoal_minimums` as its "result".
    fn update_solution(&mut self,
                       goal_depth: StackIndex,
                       subgoal_depth: StackIndex,
                       sign: Sign,
                       minimums: &mut Minimums,
                       subgoal_minimums: &Minimums)
    {
        let subgoal_table = self.stack[subgoal_depth].table;
        if !self.tables[subgoal_table].completely_evaluated {
            self.update_lookup(goal_depth, subgoal_depth, sign, minimums, subgoal_minimums);
        } else {
            self.stack[goal_depth].link.take_minimums(subgoal_minimums);
            minimums.take_minimums(subgoal_minimums);
        }
    }

    /// Like `update_solution`, but invoked when `subgoal_table`
    /// is known to be incomplete.
    fn update_lookup(&mut self,
                     goal_depth: StackIndex,
                     subgoal_depth: StackIndex,
                     sign: Sign,
                     minimums: &mut Minimums,
                     subgoal_minimums: &Minimums)
    {
        match sign {
            Sign::Positive => {
                self.stack[goal_depth].link.take_minimums(subgoal_minimums);
                minimums.take_minimums(subgoal_minimums);
            }

            Sign::Negative => {
                // If `goal` depends on `not(subgoal)`, then for goal
                // to succeed, `subgoal` must be completely
                // evaluated. Therefore, `goal` depends (negatively)
                // on the minimum link of `subgoal` as a whole -- it
                // doesn't matter whether it's pos or neg.
                let subgoal_min = self.stack[subgoal_depth].link.minimum_of_pos_and_neg();
                self.stack[goal_depth].link.take_negative_minimum(subgoal_min);
                minimums.take_negative_minimum(subgoal_min);
            }
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    // SLG RESOLVENTS
    //
    // The "SLG Resolvent" is used to combine a *goal* G with some
    // clause or answer *C*.  It unifies the goal's selected literal
    // with the clause and then inserts the clause's conditions into
    // the goal's list of things to prove, basically. Although this is
    // one operation in EWFS, we have specialized variants for merging
    // a program clause and an answer (though they share some code in
    // common).
    //
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

    /// Applies the SLG resolvent algorithm to incorporate a new
    /// answer and apply it to a previously blocked ex-clause.
    fn resolvent_pending(pending_ex_clause: &CanonicalPendingExClause,
                         answer: &CanonicalExClauseAnswer)
                         -> Result<(StackIndex, CanonicalExClause)>
    {
        let mut infer = InferenceTable::new();

        let PendingExClause {
            goal_depth,
            table_goal,
            selected_literal,
            delayed_literals,
            subgoals,
        } = infer.instantiate_canonical(pending_ex_clause);

        let ex_clause = ExClause {
            table_goal,
            delayed_literals,
            subgoals,
        };

        let resolvent = Self::resolvent_answer(&mut infer, &ex_clause, &selected_literal, answer)?;
        Ok((goal_depth, resolvent))
    }

    /// Applies the SLG resolvent algorithm to incorporate an answer
    /// produced by the selected literal into the main X-clause,
    /// producing a new X-clause that must be solved.
    ///
    /// # Parameters
    ///
    /// - `ex_clause` is the X-clause we are trying to prove,
    ///   with the selected literal removed from its list of subgoals
    /// - `selected_literal` is the selected literal that was removed
    /// - `answer` is some answer to `selected_literal` that has been found
    fn resolvent_answer(infer: &mut InferenceTable,
                        ex_clause: &ExClause,
                        selected_literal: &InEnvironment<DomainGoal>,
                        answer: &CanonicalExClauseAnswer)
                        -> Result<CanonicalExClause>
    {
        // Relating the above describes to our parameters:
        //
        // - the goal G is `ex_clause` is, with `selected_literal` being
        //   the selected literal Li, already removed from the list.
        // - the clause C is `answer.` (i.e., the answer has no conditions).

        let snapshot = infer.snapshot();

        let result = do catch {
            // C' is now `answer`. No variables in commmon with G.
            let answer = infer.instantiate_canonical(&answer);

            assert!(answer.delayed_literals.is_empty(),
                    "slg resolvent invoked with delayed literals");

            // Perform the SLG resolvent unification.
            Ok(Self::resolvent_unify(infer,
                                     ex_clause.clone(),
                                     selected_literal,
                                     &answer.table_goal,
                                     vec![])?)
        };

        infer.rollback_to(snapshot);

        result
    }

    /// Applies the SLG resolvent algorithm to incorporate a program
    /// clause into the main X-clause, producing a new X-clause that
    /// must be solved.
    ///
    /// # Parameters
    ///
    /// - `goal` is the goal G that we are trying to solve
    /// - `clause` is the program clause that may be useful to that end
    fn resolvent_clause(goal: &CanonicalDomainGoal,
                        clause: &Binders<ProgramClauseImplication>)
                        -> Result<CanonicalExClause>
    {
        // Relating the above description to our situation:
        //
        // - `goal` G, except with binders for any existential variables.
        //   - Also, we always select the first literal in `ex_clause.literals`, so `i` is 0.
        // - `clause` is C, except with binders for any existential variables.

        let mut infer = InferenceTable::new();

        // Goal here is now G.
        let goal = ExClause {
            table_goal: infer.instantiate_canonical(&goal),
            delayed_literals: vec![],
            subgoals: vec![],
        };

        // The selected literal for us will always be Ln. See if we
        // can unify that with C'.
        let selected_literal = goal.subgoals.pop().expect("goal has no selected literals");
        let environment = &selected_literal.environment;

        // C' in the description above is `consequence :- conditions`.
        //
        // Note that G and C' have no variables in common.
        let ProgramClauseImplication { consequence, conditions } =
            infer.instantiate_binders_in(environment.universe, clause);
        let consequence = InEnvironment::new(&environment, consequence);

        Self::resolvent_unify(&mut infer,
                              goal,
                              &selected_literal,
                              &consequence,
                              conditions)
    }

    /// Given the goal G (`goal`) with selected literal Li
    /// (`selected_literal`), the goal environment `environment`, and
    /// the clause C' (`consequence :- conditions`), applies the SLG
    /// resolvent algorithm to yield a new `ExClause`.
    fn resolvent_unify(infer: &mut InferenceTable,
                       goal: ExClause,
                       selected_literal: &InEnvironment<DomainGoal>,
                       consequence: &InEnvironment<DomainGoal>,
                       conditions: Vec<Goal>)
                       -> Result<CanonicalExClause>
    {
        let environment = &selected_literal.environment;

        // Unify the selected literal Li with C'.
        let UnificationResult { goals, constraints, cannot_prove } =
            infer.unify(&selected_literal.environment, selected_literal, consequence)?;

        // Add the `conditions` into the result. One complication is
        // that these are HH-clauses, so we have to simplify into
        // literals first.
        for condition in conditions {
            let SimplifiedGoals { positive, negative } =
                Self::simplify_hh_goal(infer, environment, condition)?;
            assert!(negative.is_empty(), "not thinking about negative clauses yet");
            goal.subgoals.extend(positive);
        }

        // One (minor) complication: unification for us sometimes yields further domain goals.
        assert!(constraints.is_empty(), "Not yet implemented: region constraints");
        assert!(!cannot_prove, "Not yet implemented: cannot_prove");
        goal.subgoals.extend(goals.into_iter().casted());

        // Return the union of L1'...Lm' with those extra conditions. We are assuming
        // in this routine that the selected literal Li was the only literal.
        Ok(infer.canonicalize(&goal).quantified)
    }


    /// Simplifies an HH goal into a series of positive domain goals
    /// and negative HH goals. This operation may fail if the HH goal
    /// includes unifications that cannot be completed.
    fn simplify_hh_goal(infer: &mut InferenceTable,
                        initial_environment: &Arc<Environment>,
                        initial_goal: Goal)
                        -> Result<SimplifiedGoals> {
        // The final result we will accumulate into.
        let mut simplified_goals = SimplifiedGoals {
            negative: vec![],
            positive: vec![]
        };

        // A stack of higher-level goals to process.
        let mut pending_goals = vec![InEnvironment::new(initial_environment, initial_goal)];

        while let Some(InEnvironment { environment, goal }) = pending_goals.pop() {
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
                    let subgoal = infer.instantiate_in(environment.universe,
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
                        infer.unify(&environment, &eq_goal.a, &eq_goal.b)?;

                    assert!(constraints.is_empty(), "Not yet implemented: region constraints");
                    assert!(!cannot_prove, "Not yet implemented: cannot_prove");

                    simplified_goals.positive.extend(goals);
                }
                Goal::Leaf(LeafGoal::DomainGoal(domain_goal)) => {
                    simplified_goals.positive.push(InEnvironment::new(&environment, domain_goal));
                }
            }
        }

        Ok(simplified_goals)
    }
}

impl Stack {
    fn len(&self) -> usize {
        self.stack.len()
    }

    fn push(&mut self, table: TableIndex, dfn: DepthFirstNumber) -> StackIndex {
        let len = self.len();
        self.stack.push(StackEntry {
            table,
            dfn,
            link: Minimums {
                positive: dfn,
                negative: DepthFirstNumber::MAX,
            }
        });
        StackIndex { value: len }
    }

    fn top(&self) -> &StackEntry {
        self.stack.last().unwrap()
    }
}

impl Index<StackIndex> for Stack {
    type Output = StackEntry;

    fn index(&self, index: StackIndex) -> &StackEntry {
        &self.stack[index.value]
    }
}

impl IndexMut<StackIndex> for Stack {
    fn index_mut(&mut self, index: StackIndex) -> &mut StackEntry {
        &mut self.stack[index.value]
    }
}

impl Tables {
    fn insert(&mut self, goal: &CanonicalDomainGoal) -> TableIndex {
        let index = TableIndex { value: self.tables.len() };
        self.tables.push(Table {
            answers: HashSet::new(),
            positives: vec![],
            negatives: vec![],
            completely_evaluated: false,
        });
        self.table_indices.insert(goal.clone(), index);
        index
    }

    fn index_of(&self, literal: &CanonicalDomainGoal) -> Option<TableIndex> {
        self.table_indices.get(literal).cloned()
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

impl Minimums {
    /// Update our fields to be the minimum of our current value
    /// and the values from other.
    fn take_minimums(&mut self, other: &Minimums) {
        self.positive = min(self.positive, other.positive);
        self.negative = min(self.negative, other.negative);
    }

    fn take_negative_minimum(&mut self, other: DepthFirstNumber) {
        self.negative = min(self.negative, other);
    }

    fn minimum_of_pos_and_neg(&self) -> DepthFirstNumber {
        min(self.positive, self.negative)
    }
}

impl DepthFirstNumber {
    const MIN: DepthFirstNumber = DepthFirstNumber { value: 0 };
    const MAX: DepthFirstNumber = DepthFirstNumber { value: ::std::u64::MAX };

    fn next(&mut self) -> DepthFirstNumber {
        let value = self.value;
        self.value += 1;
        DepthFirstNumber { value }
    }
}

