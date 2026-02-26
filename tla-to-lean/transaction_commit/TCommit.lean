import Mathlib.Data.Fintype.Basic

-- The four states of resource managers
inductive RMState where
  | working
  | prepared
  | committed
  | aborted

-- The set of participating resource managers
variable {RM : Type} [Fintype RM] [DecidableEq RM]

-- The overall state shape of the Transaction Commit system
local notation "TCState" => RM → RMState

-- The specific initial state of the Transaction Commit system
def tcInit : TCState := fun _ => RMState.working

-- The Transaction Commit system can commit if all resource managers are
-- either in the prepare state or committed state.
def canCommit (state : TCState) : Prop :=
  ∀ rm : RM, state rm = RMState.prepared ∨ state rm = RMState.committed

-- The Transaction Commit system hasn't committed when none of the resource
-- managers are in the committed state
def notCommitted (state : TCState) : Prop :=
  ∀ rm : RM, state rm ≠ RMState.committed

-- Step transition "prepare"
def do_prepare (rm : RM) (old_state new_state : TCState) : Prop :=
  old_state rm = RMState.working
  ∧ new_state = Function.update old_state rm RMState.prepared

-- Step transition "decide"
def do_decide (rm : RM) (old_state new_state : TCState) : Prop :=
    old_state rm = RMState.prepared
    ∧ canCommit old_state
    ∧ new_state = Function.update old_state rm RMState.committed
  ∨ (old_state rm = RMState.prepared ∨ old_state rm = RMState.working)
    ∧ notCommitted old_state
    ∧ new_state = Function.update old_state rm RMState.aborted

-- A step can either be "prepare" or "decide"
def step (rm : RM) (old_state new_state : TCState) : Prop :=
  do_prepare rm old_state new_state
  ∨ do_decide rm old_state new_state

-- The valid next steps. The Transaction Commit system can transition to
-- the next state if there exists at least one resource manager that can
-- take a step (any step)
def tcNext (old_state new_state : TCState) : Prop :=
  ∃ rm : RM, step rm old_state new_state

-- Definition of when a Transaction Commit state is consistent.
-- This is the state invariant that we will want to always hold.
def tcConsistent (state : TCState) : Prop :=
  ¬ ∃ rm' rm'' : RM, state rm' = RMState.aborted ∧ state rm'' = RMState.committed


-- Helper lemma for the base case
omit [Fintype RM] [DecidableEq RM] in
lemma tcConsistent_init : tcConsistent (tcInit : TCState) := by
  unfold tcConsistent tcInit
  simp

-- Helper lemma for the inductive case
omit [Fintype RM] in
lemma tcConsistent_step (old_state new_state : TCState) :
  tcConsistent old_state → tcNext old_state new_state → tcConsistent new_state := by
    -- Unfold all definitions to expose the raw logical structure
  simp only [tcConsistent, tcNext, step, do_prepare, do_decide, canCommit, notCommitted]
  -- Transform ¬∃ into ∀...→ form (easier to work with)
  push_neg
  -- Introduce: h_con is the old consistency, rm is the RM that stepped,
  -- r1/r2 are the two RMs we must show aren't in conflict, h_abt says r1 is aborted
  intro h_con ⟨rm, h_step⟩ r1 r2 h_abt
  -- Case split on which action was taken
  rcases h_step with ⟨_, rfl⟩ | (⟨_, hcan, rfl⟩ | ⟨_, hnot, rfl⟩)
  -- Case 1: prepare (rm: working → prepared)
  · simp only [Function.update_apply] at h_abt ⊢
    split_ifs at h_abt with h_r1
    -- pos case (prepared = aborted) auto-closed
    split_ifs with h_r2
    · simp  -- r2 = rm, so prepared ≠ committed
    · exact h_con r1 r2 h_abt  -- both unchanged, use old consistency
  -- Case 2: decide-commit (rm: prepared → committed, canCommit holds)
  · simp only [Function.update_apply] at h_abt ⊢
    split_ifs at h_abt with h_r1
    -- pos case (committed = aborted) auto-closed
    -- r1 ≠ rm, so old_state r1 = aborted. But canCommit says all are prepared/committed.
    split_ifs with h_r2
    · rcases hcan r1 with h | h <;> simp_all
    · rcases hcan r1 with h | h <;> simp_all
  -- Case 3: decide-abort (rm → aborted, notCommitted holds)
  · simp only [Function.update_apply] at ⊢
    split_ifs with h_r2
    · simp  -- r2 = rm, so aborted ≠ committed
    · exact hnot r2  -- r2 unchanged, notCommitted says old r2 ≠ committed


inductive Reachable : (TCState) → Prop where
  | init : Reachable tcInit
  | step {s s'} : Reachable s → tcNext s s' → Reachable s'


-- Asserts that TCTypeOK and TCConsistent are invariants of the protocol
omit [Fintype RM] in
theorem tcSpec (s : TCState) : Reachable s → tcConsistent s := by
  intro h
  induction h with
  | init => exact tcConsistent_init
  | step h_reach h_next ih => exact tcConsistent_step _ _ ih h_next
