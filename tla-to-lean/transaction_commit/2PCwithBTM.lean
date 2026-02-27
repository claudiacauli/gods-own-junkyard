import Mathlib.Data.Fintype.Basic

/-!
# Two-Phase Commit with Backup Transaction Manager (BTM)

A Lean formalization of the 2PCwithBTM TLA+ specification.
This models Two-Phase Commit with:
- A backup transaction manager (BTM) that takes over if the primary TM crashes
- RM failure (controlled by RMMAYFAIL parameter)
- TM failure (controlled by TMMAYFAIL parameter)
- Explicit program counters (PlusCal style) rather than message passing
-/

variable {RM : Type} [Fintype RM] [DecidableEq RM]

-- The five states of resource managers (TLA+ line 180)
-- Extends the usual 4 states with "failed"
inductive BTMRMState where
  | working
  | prepared
  | committed
  | aborted
  | failed
  deriving DecidableEq

-- The four states of the transaction manager (TLA+ line 181)
inductive BTMTMState where
  | init
  | commit
  | abort
  | hidden
  deriving DecidableEq

-- Program counter labels for RM processes (TLA+ line 79-80)
inductive RMLabel where
  | RS
  | Done
  deriving DecidableEq

-- Program counter labels for the TM process (TLA+ lines 102-133)
inductive TMLabel where
  | TS
  | TC
  | F1
  | TA
  | F2
  | Done
  deriving DecidableEq

-- Program counter labels for the BTM process (TLA+ lines 137-153)
inductive BTMLabel where
  | BTS
  | BTC
  | BTA
  | Done
  deriving DecidableEq

-- The overall state of the 2PC with BTM system
structure BTMState (RM : Type) where
  rmState : RM → BTMRMState
  tmState : BTMTMState
  rmPC    : RM → RMLabel
  tmPC    : TMLabel
  btmPC   : BTMLabel

-- canCommit: all RMs prepared, or some RM already committed (TLA+ line 66-67)
def btmCanCommit (s : BTMState RM) : Prop :=
  (∀ rm : RM, s.rmState rm = BTMRMState.prepared)
  ∨ (∃ rm : RM, s.rmState rm = BTMRMState.committed)

-- canAbort: some RM aborted or failed, and no RM committed (TLA+ line 68-69)
def btmCanAbort (s : BTMState RM) : Prop :=
  (∃ rm : RM, s.rmState rm = BTMRMState.aborted ∨ s.rmState rm = BTMRMState.failed)
  ∧ (∀ rm : RM, s.rmState rm ≠ BTMRMState.committed)

-- The initial state (TLA+ lines 76-81)
def btmInit : BTMState RM where
  rmState := fun _ => BTMRMState.working
  tmState := BTMTMState.init
  rmPC    := fun _ => RMLabel.RS
  tmPC    := TMLabel.TS
  btmPC   := BTMLabel.BTS

-------------------------------------------------------------------------------
-- RM actions (TLA+ lines 83-100)
-- RS action, THEN branch: rmState[self] ∈ {working, prepared}, stays at RS
-------------------------------------------------------------------------------

-- RM prepares: working → prepared (TLA+ line 85-86)
def rmPrepare (rm : RM) (s s' : BTMState RM) : Prop :=
  s.rmPC rm = RMLabel.RS
  ∧ s.rmState rm = BTMRMState.working
  ∧ s'.rmState = Function.update s.rmState rm BTMRMState.prepared
  ∧ s'.rmPC = s.rmPC
  ∧ s'.tmState = s.tmState
  ∧ s'.tmPC = s.tmPC
  ∧ s'.btmPC = s.btmPC

-- RM decides to commit: tmState = commit → committed (TLA+ line 87-88)
def rmDecideCommit (rm : RM) (s s' : BTMState RM) : Prop :=
  s.rmPC rm = RMLabel.RS
  ∧ (s.rmState rm = BTMRMState.working ∨ s.rmState rm = BTMRMState.prepared)
  ∧ s.tmState = BTMTMState.commit
  ∧ s'.rmState = Function.update s.rmState rm BTMRMState.committed
  ∧ s'.rmPC = s.rmPC
  ∧ s'.tmState = s.tmState
  ∧ s'.tmPC = s.tmPC
  ∧ s'.btmPC = s.btmPC

-- RM decides to abort: working or tmState = abort → aborted (TLA+ line 89-90)
def rmDecideAbort (rm : RM) (s s' : BTMState RM) : Prop :=
  s.rmPC rm = RMLabel.RS
  ∧ (s.rmState rm = BTMRMState.working ∨ s.rmState rm = BTMRMState.prepared)
  ∧ (s.rmState rm = BTMRMState.working ∨ s.tmState = BTMTMState.abort)
  ∧ s'.rmState = Function.update s.rmState rm BTMRMState.aborted
  ∧ s'.rmPC = s.rmPC
  ∧ s'.tmState = s.tmState
  ∧ s'.tmPC = s.tmPC
  ∧ s'.btmPC = s.btmPC

-- RM fails (TLA+ lines 91-94): IF/THEN/ELSE modeled as disjunction
def rmFail (RMMAYFAIL : Bool) (rm : RM) (s s' : BTMState RM) : Prop :=
  s.rmPC rm = RMLabel.RS
  ∧ (s.rmState rm = BTMRMState.working ∨ s.rmState rm = BTMRMState.prepared)
  ∧ ((RMMAYFAIL = true ∧ (∀ r : RM, s.rmState r ≠ BTMRMState.failed)
      ∧ s'.rmState = Function.update s.rmState rm BTMRMState.failed)
    ∨ (¬(RMMAYFAIL = true ∧ ∀ r : RM, s.rmState r ≠ BTMRMState.failed)
      ∧ s'.rmState = s.rmState))
  ∧ s'.rmPC = s.rmPC
  ∧ s'.tmState = s.tmState
  ∧ s'.tmPC = s.tmPC
  ∧ s'.btmPC = s.btmPC

-- RM exits while loop: rmState ∉ {working, prepared} → Done (TLA+ line 96-97)
def rmDone (rm : RM) (s s' : BTMState RM) : Prop :=
  s.rmPC rm = RMLabel.RS
  ∧ s.rmState rm ≠ BTMRMState.working
  ∧ s.rmState rm ≠ BTMRMState.prepared
  ∧ s'.rmPC = Function.update s.rmPC rm RMLabel.Done
  ∧ s'.rmState = s.rmState
  ∧ s'.tmState = s.tmState
  ∧ s'.tmPC = s.tmPC
  ∧ s'.btmPC = s.btmPC

-------------------------------------------------------------------------------
-- TM actions (TLA+ lines 102-135)
-------------------------------------------------------------------------------

-- TM chooses to commit path: canCommit → move to TC (TLA+ lines 102-104)
def tsCommit (s s' : BTMState RM) : Prop :=
  s.tmPC = TMLabel.TS
  ∧ btmCanCommit s
  ∧ s'.tmPC = TMLabel.TC
  ∧ s'.rmState = s.rmState
  ∧ s'.tmState = s.tmState
  ∧ s'.rmPC = s.rmPC
  ∧ s'.btmPC = s.btmPC

-- TM chooses to abort path: canAbort → move to TA (TLA+ lines 105-106)
def tsAbort (s s' : BTMState RM) : Prop :=
  s.tmPC = TMLabel.TS
  ∧ btmCanAbort s
  ∧ s'.tmPC = TMLabel.TA
  ∧ s'.rmState = s.rmState
  ∧ s'.tmState = s.tmState
  ∧ s'.rmPC = s.rmPC
  ∧ s'.btmPC = s.btmPC

-- TM sets tmState to commit (TLA+ lines 109-112)
def tmTC (s s' : BTMState RM) : Prop :=
  s.tmPC = TMLabel.TC
  ∧ s'.tmState = BTMTMState.commit
  ∧ s'.tmPC = TMLabel.F1
  ∧ s'.rmState = s.rmState
  ∧ s'.rmPC = s.rmPC
  ∧ s'.btmPC = s.btmPC

-- TM may fail after commit (TLA+ lines 114-120)
def tmF1 (TMMAYFAIL : Bool) (s s' : BTMState RM) : Prop :=
  s.tmPC = TMLabel.F1
  ∧ ((TMMAYFAIL = true ∧ s'.tmState = BTMTMState.hidden)
    ∨ (TMMAYFAIL = false ∧ s'.tmState = s.tmState))
  ∧ s'.tmPC = TMLabel.Done
  ∧ s'.rmState = s.rmState
  ∧ s'.rmPC = s.rmPC
  ∧ s'.btmPC = s.btmPC

-- TM sets tmState to abort (TLA+ lines 122-125)
def tmTA (s s' : BTMState RM) : Prop :=
  s.tmPC = TMLabel.TA
  ∧ s'.tmState = BTMTMState.abort
  ∧ s'.tmPC = TMLabel.F2
  ∧ s'.rmState = s.rmState
  ∧ s'.rmPC = s.rmPC
  ∧ s'.btmPC = s.btmPC

-- TM may fail after abort (TLA+ lines 127-133)
def tmF2 (TMMAYFAIL : Bool) (s s' : BTMState RM) : Prop :=
  s.tmPC = TMLabel.F2
  ∧ ((TMMAYFAIL = true ∧ s'.tmState = BTMTMState.hidden)
    ∨ (TMMAYFAIL = false ∧ s'.tmState = s.tmState))
  ∧ s'.tmPC = TMLabel.Done
  ∧ s'.rmState = s.rmState
  ∧ s'.rmPC = s.rmPC
  ∧ s'.btmPC = s.btmPC

-------------------------------------------------------------------------------
-- BTM (Backup Transaction Manager) actions (TLA+ lines 137-154)
-------------------------------------------------------------------------------

-- BTM chooses commit path: canCommit ∧ tmState = hidden → BTC (TLA+ lines 138-139)
def btsCommit (s s' : BTMState RM) : Prop :=
  s.btmPC = BTMLabel.BTS
  ∧ btmCanCommit s
  ∧ s.tmState = BTMTMState.hidden
  ∧ s'.btmPC = BTMLabel.BTC
  ∧ s'.rmState = s.rmState
  ∧ s'.tmState = s.tmState
  ∧ s'.rmPC = s.rmPC
  ∧ s'.tmPC = s.tmPC

-- BTM chooses abort path: canAbort ∧ tmState = hidden → BTA (TLA+ lines 140-141)
def btsAbort (s s' : BTMState RM) : Prop :=
  s.btmPC = BTMLabel.BTS
  ∧ btmCanAbort s
  ∧ s.tmState = BTMTMState.hidden
  ∧ s'.btmPC = BTMLabel.BTA
  ∧ s'.rmState = s.rmState
  ∧ s'.tmState = s.tmState
  ∧ s'.rmPC = s.rmPC
  ∧ s'.tmPC = s.tmPC

-- BTM commits: tmState → commit (TLA+ lines 144-147)
def btmBTC (s s' : BTMState RM) : Prop :=
  s.btmPC = BTMLabel.BTC
  ∧ s'.tmState = BTMTMState.commit
  ∧ s'.btmPC = BTMLabel.Done
  ∧ s'.rmState = s.rmState
  ∧ s'.rmPC = s.rmPC
  ∧ s'.tmPC = s.tmPC

-- BTM aborts: tmState → abort (TLA+ lines 149-152)
def btmBTA (s s' : BTMState RM) : Prop :=
  s.btmPC = BTMLabel.BTA
  ∧ s'.tmState = BTMTMState.abort
  ∧ s'.btmPC = BTMLabel.Done
  ∧ s'.rmState = s.rmState
  ∧ s'.rmPC = s.rmPC
  ∧ s'.tmPC = s.tmPC

-------------------------------------------------------------------------------
-- Terminating, Next, Reachable (TLA+ lines 157-164)
-------------------------------------------------------------------------------

-- Stuttering when all processes are done (TLA+ lines 157-158)
def btmTerminating (s s' : BTMState RM) : Prop :=
  (∀ rm : RM, s.rmPC rm = RMLabel.Done)
  ∧ s.tmPC = TMLabel.Done
  ∧ s.btmPC = BTMLabel.Done
  ∧ s' = s

-- The next-state relation (TLA+ lines 160-162)
def btmNext (RMMAYFAIL TMMAYFAIL : Bool) (s s' : BTMState RM) : Prop :=
  -- TManager
  tsCommit s s' ∨ tsAbort s s' ∨ tmTC s s'
  ∨ tmF1 TMMAYFAIL s s' ∨ tmTA s s' ∨ tmF2 TMMAYFAIL s s'
  -- BTManager
  ∨ btsCommit s s' ∨ btsAbort s s' ∨ btmBTC s s' ∨ btmBTA s s'
  -- RManagers
  ∨ (∃ rm : RM, rmPrepare rm s s' ∨ rmDecideCommit rm s s'
    ∨ rmDecideAbort rm s s' ∨ rmFail RMMAYFAIL rm s s' ∨ rmDone rm s s')
  -- Terminating
  ∨ btmTerminating s s'

-- Reachable states
inductive BTMReachable (RMMAYFAIL TMMAYFAIL : Bool) : BTMState RM → Prop where
  | init : BTMReachable RMMAYFAIL TMMAYFAIL btmInit
  | step {s s'} : BTMReachable RMMAYFAIL TMMAYFAIL s
    → btmNext RMMAYFAIL TMMAYFAIL s s' → BTMReachable RMMAYFAIL TMMAYFAIL s'

-------------------------------------------------------------------------------
-- Safety properties (TLA+ lines 173-193)
-------------------------------------------------------------------------------

-- Consistency: no RM aborted while another committed (TLA+ lines 183-189)
def btmConsistent (s : BTMState RM) : Prop :=
  ¬ ∃ rm1 rm2 : RM, s.rmState rm1 = BTMRMState.aborted ∧ s.rmState rm2 = BTMRMState.committed

-------------------------------------------------------------------------------
-- Strengthened inductive invariant
--
-- Consistency alone is not inductive. We strengthen it with auxiliary facts
-- about tmState and program counter coherence.
-------------------------------------------------------------------------------

def btmInvariant (s : BTMState RM) : Prop :=
  -- 1. Consistency
  btmConsistent s
  -- 2. tmState = commit → no RM aborted
  ∧ (s.tmState = BTMTMState.commit → ∀ rm : RM, s.rmState rm ≠ BTMRMState.aborted)
  -- 3. tmState = abort → no RM committed
  ∧ (s.tmState = BTMTMState.abort → ∀ rm : RM, s.rmState rm ≠ BTMRMState.committed)
  -- 4. RM committed → tmState ∈ {commit, hidden}
  ∧ (∀ rm : RM, s.rmState rm = BTMRMState.committed
      → s.tmState = BTMTMState.commit ∨ s.tmState = BTMTMState.hidden)
  -- 5. tmState = init → no RM committed
  ∧ (s.tmState = BTMTMState.init → ∀ rm : RM, s.rmState rm ≠ BTMRMState.committed)
  -- 6. tmState = hidden → tmPC = Done (TM must have finished to become hidden)
  ∧ (s.tmState = BTMTMState.hidden → s.tmPC = TMLabel.Done)
  -- 7. tmPC = F1 → tmState = commit (TC already executed)
  ∧ (s.tmPC = TMLabel.F1 → s.tmState = BTMTMState.commit)
  -- 8. tmPC = F2 → tmState = abort (TA already executed)
  ∧ (s.tmPC = TMLabel.F2 → s.tmState = BTMTMState.abort)
  -- 9a. tmPC = TC → no RM aborted
  ∧ (s.tmPC = TMLabel.TC → ∀ rm : RM, s.rmState rm ≠ BTMRMState.aborted)
  -- 9b. tmPC = TC → no RM working
  ∧ (s.tmPC = TMLabel.TC → ∀ rm : RM, s.rmState rm ≠ BTMRMState.working)
  -- 10. tmPC = TA → canAbort s (TS guard verified)
  ∧ (s.tmPC = TMLabel.TA → btmCanAbort s)
  -- 11. btmPC = BTC → tmState = hidden (BTS guard verified; BTC hasn't run yet)
  ∧ (s.btmPC = BTMLabel.BTC → s.tmState = BTMTMState.hidden)
  -- 12. btmPC = BTA → tmState = hidden (BTS guard verified; BTA hasn't run yet)
  ∧ (s.btmPC = BTMLabel.BTA → s.tmState = BTMTMState.hidden)
  -- 13a. btmPC = BTC → no RM aborted
  ∧ (s.btmPC = BTMLabel.BTC → ∀ rm : RM, s.rmState rm ≠ BTMRMState.aborted)
  -- 13b. btmPC = BTC → no RM working
  ∧ (s.btmPC = BTMLabel.BTC → ∀ rm : RM, s.rmState rm ≠ BTMRMState.working)
  -- 14. btmPC = BTA → canAbort s
  ∧ (s.btmPC = BTMLabel.BTA → btmCanAbort s)
  -- 15. tmState = commit → tmPC ∈ {F1, Done}
  ∧ (s.tmState = BTMTMState.commit → s.tmPC = TMLabel.F1 ∨ s.tmPC = TMLabel.Done)
  -- 16. tmState = abort → tmPC ∈ {F2, Done}
  ∧ (s.tmState = BTMTMState.abort → s.tmPC = TMLabel.F2 ∨ s.tmPC = TMLabel.Done)
  -- 17. tmState = commit → no RM working (canCommit was verified, RMs don't revert)
  ∧ (s.tmState = BTMTMState.commit → ∀ rm : RM, s.rmState rm ≠ BTMRMState.working)
  -- 18. some RM committed → no RM working (committed implies commit/hidden path was taken)
  ∧ ((∃ rm : RM, s.rmState rm = BTMRMState.committed) →
      ∀ rm : RM, s.rmState rm ≠ BTMRMState.working)

-------------------------------------------------------------------------------
-- Reusable proof helpers
-------------------------------------------------------------------------------

/-- Discharge a goal whose hypothesis contradicts a rewrite target. -/
macro "absurd_hyp" h:ident : tactic =>
  `(tactic| (intro h_contra; rw [show _ = _ from $h] at h_contra; simp at h_contra))

/-- Lift `∀ r, f r ≠ target` through `Function.update` when `newVal ≠ target`. -/
lemma ne_update_of_ne {α : Type} [DecidableEq α] {f : α → BTMRMState} {a : α}
    {newVal target : BTMRMState}
    (h_new : newVal ≠ target) (h_old : ∀ r, f r ≠ target) :
    ∀ r, Function.update f a newVal r ≠ target := by
  intro r; simp only [Function.update_apply]; split_ifs with h
  · exact h_new
  · exact h_old r

/-- Lift consistency through `Function.update` when `newVal` is neither aborted nor committed. -/
lemma btmConsistent_update {α : Type} [DecidableEq α] {f : α → BTMRMState} {a : α}
    {newVal : BTMRMState}
    (h_cons : ¬∃ r1 r2, f r1 = BTMRMState.aborted ∧ f r2 = BTMRMState.committed)
    (h_na : newVal ≠ BTMRMState.aborted)
    (h_nc : newVal ≠ BTMRMState.committed) :
    ¬∃ r1 r2, Function.update f a newVal r1 = BTMRMState.aborted
            ∧ Function.update f a newVal r2 = BTMRMState.committed := by
  rintro ⟨r1, r2, hr1, hr2⟩
  simp only [Function.update_apply] at hr1 hr2
  split_ifs at hr1 with heq1 <;> split_ifs at hr2 with heq2 <;>
    first | exact absurd hr1 h_na | exact absurd hr2 h_nc
          | exact absurd ⟨r1, r2, hr1, hr2⟩ h_cons

-------------------------------------------------------------------------------
-- Proof skeleton: base case, per-action lemmas, inductive step, main theorem
-------------------------------------------------------------------------------

-- Base case: the initial state satisfies the invariant
omit [Fintype RM] [DecidableEq RM] in
lemma btmInvariant_init : btmInvariant (btmInit : BTMState RM) := by
  simp only [btmInvariant, btmConsistent, btmInit]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp

-- Terminating preserves the invariant (trivial: state unchanged)
omit [Fintype RM] [DecidableEq RM] in
lemma btmInvariant_terminating (s s' : BTMState RM) :
    btmInvariant s → btmTerminating s s' → btmInvariant s' := by
  intro h_inv ⟨_, _, _, h_eq⟩; rw [h_eq]; exact h_inv

-- tsCommit preserves the invariant (only tmPC changes: TS → TC)
omit [Fintype RM] [DecidableEq RM] in
lemma btmInvariant_tsCommit (s s' : BTMState RM) :
    btmInvariant s → tsCommit s s' → btmInvariant s' := by
  intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
    ⟨h_ts, h_cc, h_tmPC, h_rm, h_tm, h_rmPC, h_btmPC⟩
  unfold btmInvariant btmConsistent btmCanCommit btmCanAbort at *
  rw [h_rm, h_tm, h_btmPC]
  refine ⟨h1, h2, h3, h4, h5, ?_, ?_, ?_, ?_, ?_, ?_, h12, h13, h14, h15, h16, ?_, ?_, ⟨h19, h20⟩⟩
  -- 6. hidden → tmPC' = Done
  · intro h; rw [h_tmPC]; exact absurd (h6 h) (by rw [h_ts]; simp)
  -- 7. tmPC' = F1 → commit
  · absurd_hyp h_tmPC
  -- 8. tmPC' = F2 → abort
  · absurd_hyp h_tmPC
  -- 9a. tmPC' = TC → no RM aborted
  · intro _ rm h_abt
    rcases h_cc with h_all | ⟨r, h_comm⟩
    · exact absurd h_abt (by rw [h_all rm]; simp)
    · exact absurd ⟨rm, r, h_abt, h_comm⟩ h1
  -- 9b. tmPC' = TC → no RM working
  · intro _ rm h_wk
    rcases h_cc with h_all | ⟨r, h_comm⟩
    · exact absurd h_wk (by rw [h_all rm]; simp)
    · exact h20 ⟨r, h_comm⟩ rm h_wk
  -- 10. tmPC' = TA → canAbort
  · absurd_hyp h_tmPC
  -- 17. commit → tmPC' ∈ {F1, Done}
  · intro h; rcases h17 h with h' | h' <;> simp_all
  -- 18. abort → tmPC' ∈ {F2, Done}
  · intro h; rcases h18 h with h' | h' <;> simp_all

-- tsAbort preserves the invariant (only tmPC changes: TS → TA)
omit [Fintype RM] [DecidableEq RM] in
lemma btmInvariant_tsAbort (s s' : BTMState RM) :
    btmInvariant s → tsAbort s s' → btmInvariant s' := by
  intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
    ⟨h_ts, h_ca, h_tmPC, h_rm, h_tm, h_rmPC, h_btmPC⟩
  unfold btmInvariant btmConsistent btmCanAbort at *
  rw [h_rm, h_tm, h_btmPC]
  refine ⟨h1, h2, h3, h4, h5, ?_, ?_, ?_, ?_, ?_, ?_, h12, h13, h14, h15, h16, ?_, ?_, ⟨h19, h20⟩⟩
  · intro h; rw [h_tmPC]; exact absurd (h6 h) (by rw [h_ts]; simp)
  · absurd_hyp h_tmPC
  · absurd_hyp h_tmPC
  · absurd_hyp h_tmPC
  · absurd_hyp h_tmPC
  · intro _; exact h_ca
  -- 17. commit → tmPC' ∈ {F1, Done}
  · intro h; rcases h17 h with h' | h' <;> simp_all
  -- 18. abort → tmPC' ∈ {F2, Done}
  · intro h; rcases h18 h with h' | h' <;> simp_all

-- tmTC preserves the invariant (tmState → commit, tmPC: TC → F1)
omit [Fintype RM] [DecidableEq RM] in
lemma btmInvariant_tmTC (s s' : BTMState RM) :
    btmInvariant s → tmTC s s' → btmInvariant s' := by
  intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
    ⟨h_tc, h_tmState, h_tmPC, h_rm, h_rmPC, h_btmPC⟩
  unfold btmInvariant btmConsistent btmCanAbort at *
  rw [h_rm, h_btmPC]
  have h_na := h9 h_tc   -- no RM aborted
  have h_nw := h10 h_tc  -- no RM working
  refine ⟨h1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h14, h15, h16, ?_, ?_, ⟨?_, h20⟩⟩
  -- 2. tmState' = commit → no RM aborted
  · intro _; exact h_na
  -- 3. tmState' = abort → no RM committed
  · absurd_hyp h_tmState
  -- 4. RM committed → tmState' ∈ {commit, hidden}
  · intro _ _; left; exact h_tmState
  -- 5. tmState' = init → no RM committed
  · absurd_hyp h_tmState
  -- 6. tmState' = hidden → tmPC' = Done
  · absurd_hyp h_tmState
  -- 7. tmPC' = F1 → tmState' = commit
  · intro _; exact h_tmState
  -- 8. tmPC' = F2 → abort
  · absurd_hyp h_tmPC
  -- 9a. tmPC' = TC → no aborted
  · absurd_hyp h_tmPC
  -- 9b. tmPC' = TC → no working
  · absurd_hyp h_tmPC
  -- 10. tmPC' = TA → canAbort
  · absurd_hyp h_tmPC
  -- 11. btmPC = BTC → tmState' = hidden
  · intro h; exact absurd (h6 (h12 h)) (by rw [h_tc]; simp)
  -- 12. btmPC = BTA → tmState' = hidden
  · intro h; exact absurd (h6 (h13 h)) (by rw [h_tc]; simp)
  -- 17. commit → tmPC' ∈ {F1, Done}
  · intro _; left; exact h_tmPC
  -- 18. abort → tmPC' ∈ {F2, Done}
  · absurd_hyp h_tmState
  -- 19. commit → no RM working
  · intro _; exact h_nw

-- tmF1 preserves the invariant (tmState may → hidden, tmPC: F1 → Done)
omit [Fintype RM] [DecidableEq RM] in
lemma btmInvariant_tmF1 (TMMAYFAIL : Bool) (s s' : BTMState RM) :
    btmInvariant s → tmF1 TMMAYFAIL s s' → btmInvariant s' := by
  intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
    ⟨h_f1, h_tmS, h_tmPC, h_rm, h_rmPC, h_btmPC⟩
  have h_commit := h7 h_f1 -- tmState = commit
  unfold btmInvariant btmConsistent btmCanAbort at *
  rw [h_rm, h_btmPC]
  rcases h_tmS with ⟨_, h_hidden⟩ | ⟨_, h_same⟩
  -- Case: TMMAYFAIL = true, tmState' = hidden
  · refine ⟨h1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h14, h15, h16, ?_, ?_, ⟨?_, ?_⟩⟩
    · absurd_hyp h_hidden
    · absurd_hyp h_hidden
    · intro rm hr; right; exact h_hidden
    · absurd_hyp h_hidden
    · intro _; exact h_tmPC
    · absurd_hyp h_tmPC
    · absurd_hyp h_tmPC
    · absurd_hyp h_tmPC
    · absurd_hyp h_tmPC
    · absurd_hyp h_tmPC
    · intro h; exact h_hidden
    · intro h; exact h_hidden
    · absurd_hyp h_hidden
    · absurd_hyp h_hidden
    -- 19. hidden ≠ commit, vacuous
    · absurd_hyp h_hidden
    -- 20. some committed → no working
    · exact h20
  -- Case: TMMAYFAIL = false, tmState' = s.tmState
  · rw [h_same]
    refine ⟨h1, h2, h3, h4, h5, ?_, ?_, ?_, ?_, ?_, ?_, h12, h13, h14, h15, h16, ?_, ?_, ⟨h19, h20⟩⟩
    · intro h; exact absurd (h6 h) (by rw [h_f1]; simp)
    · absurd_hyp h_tmPC
    · absurd_hyp h_tmPC
    · absurd_hyp h_tmPC
    · absurd_hyp h_tmPC
    · absurd_hyp h_tmPC
    · intro _; right; exact h_tmPC
    · absurd_hyp h_commit

-- tmTA preserves the invariant (tmState → abort, tmPC: TA → F2)
omit [Fintype RM] [DecidableEq RM] in
lemma btmInvariant_tmTA (s s' : BTMState RM) :
    btmInvariant s → tmTA s s' → btmInvariant s' := by
  intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
    ⟨h_ta, h_tmState, h_tmPC, h_rm, h_rmPC, h_btmPC⟩
  have h_ca := h11 h_ta
  unfold btmInvariant btmConsistent btmCanAbort at *
  rw [h_rm, h_btmPC]
  refine ⟨h1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h14, h15, h16, ?_, ?_, ⟨?_, ?_⟩⟩
  -- 2. tmState' = commit → no RM aborted
  · absurd_hyp h_tmState
  -- 3. tmState' = abort → no RM committed
  · intro _; exact h_ca.2
  -- 4. RM committed → tmState' ∈ {commit, hidden}
  · intro rm hr; exact absurd hr (h_ca.2 rm)
  -- 5. tmState' = init → no RM committed
  · absurd_hyp h_tmState
  -- 6. tmState' = hidden → tmPC' = Done
  · absurd_hyp h_tmState
  -- 7. tmPC' = F1 → tmState' = commit
  · absurd_hyp h_tmPC
  -- 8. tmPC' = F2 → tmState' = abort
  · intro _; exact h_tmState
  -- 9a. tmPC' = TC → no aborted
  · absurd_hyp h_tmPC
  -- 9b. tmPC' = TC → no working
  · absurd_hyp h_tmPC
  -- 10. tmPC' = TA → canAbort
  · absurd_hyp h_tmPC
  -- 11. btmPC = BTC → tmState' = hidden
  · intro h; exact absurd (h6 (h12 h)) (by rw [h_ta]; simp)
  -- 12. btmPC = BTA → tmState' = hidden
  · intro h; exact absurd (h6 (h13 h)) (by rw [h_ta]; simp)
  -- 17. commit → tmPC' ∈ {F1, Done}
  · absurd_hyp h_tmState
  -- 18. abort → tmPC' ∈ {F2, Done}
  · intro _; left; exact h_tmPC
  -- 19. abort ≠ commit, vacuous
  · absurd_hyp h_tmState
  -- 20. some committed → no working (no committed exists by h_ca.2)
  · intro ⟨r, hr⟩; exact absurd hr (h_ca.2 r)

-- tmF2 preserves the invariant (tmState may → hidden, tmPC: F2 → Done)
omit [Fintype RM] [DecidableEq RM] in
lemma btmInvariant_tmF2 (TMMAYFAIL : Bool) (s s' : BTMState RM) :
    btmInvariant s → tmF2 TMMAYFAIL s s' → btmInvariant s' := by
  intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
    ⟨h_f2, h_tmS, h_tmPC, h_rm, h_rmPC, h_btmPC⟩
  have h_abort := h8 h_f2
  unfold btmInvariant btmConsistent btmCanAbort at *
  rw [h_rm, h_btmPC]
  rcases h_tmS with ⟨_, h_hidden⟩ | ⟨_, h_same⟩
  -- Case: TMMAYFAIL = true, tmState' = hidden
  · refine ⟨h1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h14, h15, h16, ?_, ?_, ⟨?_, ?_⟩⟩
    · absurd_hyp h_hidden
    · absurd_hyp h_hidden
    · intro rm hr; rcases h4 rm hr with h | h
      · left; rw [h] at h_abort; simp at h_abort
      · right; exact h_hidden
    · absurd_hyp h_hidden
    · intro _; exact h_tmPC
    · absurd_hyp h_tmPC
    · absurd_hyp h_tmPC
    · absurd_hyp h_tmPC
    · absurd_hyp h_tmPC
    · absurd_hyp h_tmPC
    · intro h; exact h_hidden
    · intro h; exact h_hidden
    · absurd_hyp h_hidden
    · absurd_hyp h_hidden
    -- 19. hidden ≠ commit, vacuous
    · absurd_hyp h_hidden
    -- 20. some committed → no working
    · exact h20
  -- Case: TMMAYFAIL = false, tmState' = s.tmState
  · rw [h_same]
    refine ⟨h1, h2, h3, h4, h5, ?_, ?_, ?_, ?_, ?_, ?_, h12, h13, h14, h15, h16, ?_, ?_, ⟨h19, h20⟩⟩
    · intro h; exact absurd (h6 h) (by rw [h_f2]; simp)
    · absurd_hyp h_tmPC
    · absurd_hyp h_tmPC
    · absurd_hyp h_tmPC
    · absurd_hyp h_tmPC
    · absurd_hyp h_tmPC
    · absurd_hyp h_abort
    · intro _; right; exact h_tmPC

-- btsCommit preserves the invariant (only btmPC changes: BTS → BTC)
omit [Fintype RM] [DecidableEq RM] in
lemma btmInvariant_btsCommit (s s' : BTMState RM) :
    btmInvariant s → btsCommit s s' → btmInvariant s' := by
  intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
    ⟨h_bts, h_cc, h_hidden, h_btmPC, h_rm, h_tm, h_rmPC, h_tmPC⟩
  unfold btmInvariant btmConsistent btmCanCommit btmCanAbort at *
  rw [h_rm, h_tm, h_tmPC]
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ?_, ?_, ?_, ?_, ?_, h17, h18, ⟨h19, h20⟩⟩
  -- 11. btmPC' = BTC → tmState = hidden
  · intro _; exact h_hidden
  -- 12. btmPC' = BTA → tmState = hidden
  · absurd_hyp h_btmPC
  -- 13a. btmPC' = BTC → no aborted
  · intro _ rm h_abt
    rcases h_cc with h_all | ⟨r, h_comm⟩
    · exact absurd h_abt (by rw [h_all rm]; simp)
    · exact absurd ⟨rm, r, h_abt, h_comm⟩ h1
  -- 13b. btmPC' = BTC → no working
  · intro _ rm h_wk
    rcases h_cc with h_all | ⟨r, h_comm⟩
    · exact absurd h_wk (by rw [h_all rm]; simp)
    · exact h20 ⟨r, h_comm⟩ rm h_wk
  -- 14. btmPC' = BTA → canAbort
  · absurd_hyp h_btmPC

-- btsAbort preserves the invariant (only btmPC changes: BTS → BTA)
omit [Fintype RM] [DecidableEq RM] in
lemma btmInvariant_btsAbort (s s' : BTMState RM) :
    btmInvariant s → btsAbort s s' → btmInvariant s' := by
  intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
    ⟨h_bts, h_ca, h_hidden, h_btmPC, h_rm, h_tm, h_rmPC, h_tmPC⟩
  unfold btmInvariant btmConsistent btmCanAbort at *
  rw [h_rm, h_tm, h_tmPC]
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ?_, ?_, ?_, ?_, ?_, h17, h18, ⟨h19, h20⟩⟩
  -- 11. btmPC' = BTC → tmState = hidden
  · absurd_hyp h_btmPC
  -- 12. btmPC' = BTA → tmState = hidden
  · intro _; exact h_hidden
  -- 13a. btmPC' = BTC → no aborted
  · absurd_hyp h_btmPC
  -- 13b. btmPC' = BTC → no working
  · absurd_hyp h_btmPC
  -- 14. btmPC' = BTA → canAbort
  · intro _; exact h_ca

-- btmBTC preserves the invariant (tmState → commit from hidden, btmPC: BTC → Done)
omit [Fintype RM] [DecidableEq RM] in
lemma btmInvariant_btmBTC (s s' : BTMState RM) :
    btmInvariant s → btmBTC s s' → btmInvariant s' := by
  intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
    ⟨h_btc, h_tmState, h_btmPC, h_rm, h_rmPC, h_tmPC⟩
  have h_was_hidden := h12 h_btc
  have h_na := h14 h_btc   -- no aborted
  have h_nw := h15 h_btc   -- no working
  unfold btmInvariant btmConsistent btmCanAbort at *
  rw [h_rm, h_tmPC]
  refine ⟨h1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h9, h10, h11, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩⟩
  -- 2. tmState' = commit → no RM aborted
  · intro _; exact h_na
  -- 3. tmState' = abort → no RM committed
  · absurd_hyp h_tmState
  -- 4. RM committed → tmState' ∈ {commit, hidden}
  · intro _ _; left; exact h_tmState
  -- 5. tmState' = init → no RM committed
  · absurd_hyp h_tmState
  -- 6. tmState' = hidden → tmPC' = Done
  · absurd_hyp h_tmState
  -- 7. tmPC = F1 → tmState' = commit
  · intro h; exact absurd h (by rw [h6 h_was_hidden]; simp)
  -- 8. tmPC = F2 → tmState' = abort
  · intro h; exact absurd h (by rw [h6 h_was_hidden]; simp)
  -- 11-16. btmPC' = Done, so all impossible
  · absurd_hyp h_btmPC
  · absurd_hyp h_btmPC
  · absurd_hyp h_btmPC
  · absurd_hyp h_btmPC
  · absurd_hyp h_btmPC
  -- 17. commit → tmPC ∈ {F1, Done}
  · intro _; right; exact h6 h_was_hidden
  -- 18. abort → tmPC ∈ {F2, Done}
  · absurd_hyp h_tmState
  -- 19. commit → no RM working
  · intro _; exact h_nw
  -- 20. some committed → no working
  · exact h20

-- btmBTA preserves the invariant (tmState → abort from hidden, btmPC: BTA → Done)
omit [Fintype RM] [DecidableEq RM] in
lemma btmInvariant_btmBTA (s s' : BTMState RM) :
    btmInvariant s → btmBTA s s' → btmInvariant s' := by
  intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
    ⟨h_bta, h_tmState, h_btmPC, h_rm, h_rmPC, h_tmPC⟩
  have h_was_hidden := h13 h_bta
  have h_ca := h16 h_bta
  unfold btmInvariant btmConsistent btmCanAbort at *
  rw [h_rm, h_tmPC]
  refine ⟨h1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h9, h10, h11, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩⟩
  -- 2. tmState' = commit → no RM aborted
  · absurd_hyp h_tmState
  -- 3. tmState' = abort → no RM committed
  · intro _; exact h_ca.2
  -- 4. RM committed → tmState' ∈ {commit, hidden}
  · intro rm hr; exact absurd hr (h_ca.2 rm)
  -- 5. tmState' = init → no RM committed
  · absurd_hyp h_tmState
  -- 6. tmState' = hidden → tmPC' = Done
  · absurd_hyp h_tmState
  -- 7. tmPC = F1 → tmState' = commit
  · intro h; exact absurd h (by rw [h6 h_was_hidden]; simp)
  -- 8. tmPC = F2 → tmState' = abort
  · intro h; exact absurd h (by rw [h6 h_was_hidden]; simp)
  -- 11-16. btmPC' = Done, so all impossible
  · absurd_hyp h_btmPC
  · absurd_hyp h_btmPC
  · absurd_hyp h_btmPC
  · absurd_hyp h_btmPC
  · absurd_hyp h_btmPC
  -- 17. commit → tmPC ∈ {F1, Done}
  · absurd_hyp h_tmState
  -- 18. abort → tmPC ∈ {F2, Done}
  · intro _; right; exact h6 h_was_hidden
  -- 19. abort ≠ commit, vacuous
  · absurd_hyp h_tmState
  -- 20. some committed → no working (no committed by h_ca.2)
  · intro ⟨r, hr⟩; exact absurd hr (h_ca.2 r)

-- rmPrepare preserves the invariant (rmState: working → prepared)
omit [Fintype RM] in
lemma btmInvariant_rmPrepare (rm : RM) (s s' : BTMState RM) :
    btmInvariant s → rmPrepare rm s s' → btmInvariant s' := by
  intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
    ⟨_, h_working, h_rm, h_rmPC, h_tm, h_tmPC, h_btmPC⟩
  unfold btmInvariant btmConsistent btmCanAbort at *
  rw [h_tm, h_tmPC, h_btmPC]
  refine ⟨?_, ?_, ?_, ?_, ?_, h6, h7, h8, ?_, ?_, ?_, h12, h13, ?_, ?_, ?_, h17, h18, ⟨?_, ?_⟩⟩
  -- 1. Consistency: no aborted+committed
  · rw [h_rm]; exact btmConsistent_update h1 (by decide) (by decide)
  -- 2. commit → no aborted
  · intro h; rw [h_rm]; exact ne_update_of_ne (by decide) (h2 h)
  -- 3. abort → no committed
  · intro h; rw [h_rm]; exact ne_update_of_ne (by decide) (h3 h)
  -- 4. committed → tmState ∈ {commit, hidden}
  · intro r h; rw [h_rm] at h; simp only [Function.update_apply] at h
    split_ifs at h; exact h4 r h
  -- 5. init → no committed
  · intro h; rw [h_rm]; exact ne_update_of_ne (by decide) (h5 h)
  -- 9a. tmPC = TC → no aborted
  · intro h; rw [h_rm]; exact ne_update_of_ne (by decide) (h9 h)
  -- 9b. tmPC = TC → no working
  · intro h; rw [h_rm]; exact ne_update_of_ne (by decide) (h10 h)
  -- 10. tmPC = TA → canAbort
  · intro h; rw [h_rm]; rcases h11 h with ⟨⟨r, hr⟩, h_nc⟩
    exact ⟨⟨r, by simp only [Function.update_apply]; split_ifs with heq <;> simp_all⟩,
           ne_update_of_ne (by decide) h_nc⟩
  -- 13a. btmPC = BTC → no aborted
  · intro h; rw [h_rm]; exact ne_update_of_ne (by decide) (h14 h)
  -- 13b. btmPC = BTC → no working
  · intro h; rw [h_rm]; exact ne_update_of_ne (by decide) (h15 h)
  -- 14. btmPC = BTA → canAbort (rmState changed, need to lift)
  · intro h; rw [h_rm]; rcases h16 h with ⟨⟨r, hr⟩, h_nc⟩
    exact ⟨⟨r, by simp only [Function.update_apply]; split_ifs with heq <;> simp_all⟩,
           ne_update_of_ne (by decide) h_nc⟩
  -- 19. commit → no RM working (rmState changed: working → prepared)
  · intro h; rw [h_rm]; exact ne_update_of_ne (by decide) (h19 h)
  -- 20. some committed → no working
  · intro ⟨r, hr⟩
    rw [h_rm] at hr; simp only [Function.update_apply] at hr
    by_cases heq : r = rm
    · subst heq; simp_all
    · simp only [heq, ↓reduceIte] at hr
      have := h20 ⟨r, hr⟩
      intro r'; rw [h_rm]; simp only [Function.update_apply]
      split_ifs with h <;> simp_all

-- rmDecideCommit preserves the invariant (rmState → committed)
omit [Fintype RM] in
lemma btmInvariant_rmDecideCommit (rm : RM) (s s' : BTMState RM) :
    btmInvariant s → rmDecideCommit rm s s' → btmInvariant s' := by
  intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
    ⟨_, _, h_commit, h_rm, h_rmPC, h_tm, h_tmPC, h_btmPC⟩
  unfold btmInvariant btmConsistent btmCanAbort at *
  rw [h_tm, h_tmPC, h_btmPC]
  refine ⟨?_, ?_, ?_, ?_, ?_, h6, h7, h8, ?_, ?_, ?_, h12, h13, ?_, ?_, ?_, h17, h18, ⟨?_, ?_⟩⟩
  -- 1. Consistency: no aborted+committed (tmState=commit → no RM aborted by h2)
  · rintro ⟨r1, r2, hr1, hr2⟩
    rw [h_rm] at hr1; simp only [Function.update_apply] at hr1
    split_ifs at hr1 with heq1; simp_all
  -- 2. commit → no aborted
  · intro h; rw [h_rm]; exact ne_update_of_ne (by decide) (h2 h)
  -- 3. abort → no committed (tmState = commit ≠ abort, contradiction)
  · absurd_hyp h_commit
  -- 4. committed → tmState ∈ {commit, hidden}
  · intro _ _; left; exact h_tm ▸ h_commit
  -- 5. init → no committed (tmState = commit ≠ init, contradiction)
  · absurd_hyp h_commit
  -- 9a. tmPC = TC → no aborted
  · intro h; rw [h_rm]; exact ne_update_of_ne (by decide) (h9 h)
  -- 9b. tmPC = TC → no working
  · intro h; rw [h_rm]; exact ne_update_of_ne (by decide) (h10 h)
  -- 10. tmPC = TA → canAbort (rmState changed, lift)
  · intro h; rw [h_rm]; rcases h11 h with ⟨⟨r, hr⟩, h_nc⟩
    constructor
    · exact ⟨r, by simp only [Function.update_apply]; split_ifs with heq <;> simp_all⟩
    · intro r'; simp only [Function.update_apply]; split_ifs <;> simp_all
  -- 13a. btmPC = BTC → no aborted
  · intro h; rw [h_rm]; exact ne_update_of_ne (by decide) (h14 h)
  -- 13b. btmPC = BTC → no working
  · intro h; rw [h_rm]; exact ne_update_of_ne (by decide) (h15 h)
  -- 14. btmPC = BTA → canAbort
  · intro h; rw [h_rm]; rcases h16 h with ⟨⟨r, hr⟩, h_nc⟩
    constructor
    · exact ⟨r, by simp only [Function.update_apply]; split_ifs with heq <;> simp_all⟩
    · intro r'; simp only [Function.update_apply]; split_ifs <;> simp_all
  -- 19. commit → no RM working (tmState = commit, use h19)
  · intro h; rw [h_rm]; exact ne_update_of_ne (by decide) (h19 h)
  -- 20. some committed → no working (rm is committed, use h19 h_commit)
  · intro _ r; rw [h_rm]; simp only [Function.update_apply]
    split_ifs <;> simp_all [h19 h_commit r]

-- rmDecideAbort preserves the invariant (rmState → aborted)
omit [Fintype RM] in
lemma btmInvariant_rmDecideAbort (rm : RM) (s s' : BTMState RM) :
    btmInvariant s → rmDecideAbort rm s s' → btmInvariant s' := by
  intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
    ⟨_, h_wp, h_guard, h_rm, h_rmPC, h_tm, h_tmPC, h_btmPC⟩
  unfold btmInvariant btmConsistent btmCanAbort at *
  rw [h_tm, h_tmPC, h_btmPC]
  refine ⟨?_, ?_, ?_, ?_, ?_, h6, h7, h8, ?_, ?_, ?_, h12, h13, ?_, ?_, ?_, h17, h18, ⟨?_, ?_⟩⟩
  -- 1. Consistency (rm → aborted; need no committed)
  · rintro ⟨r1, r2, hr1, hr2⟩
    rw [h_rm] at hr2; simp only [Function.update_apply] at hr2
    by_cases heq2 : r2 = rm
    · simp only [heq2, ite_true] at hr2; exact BTMRMState.noConfusion hr2
    · simp only [show ¬(r2 = rm) from heq2, ite_false] at hr2
      rcases h_guard with hw | ha
      · exact h20 ⟨r2, hr2⟩ rm hw
      · exact h3 ha r2 hr2
  -- 2. commit → no aborted (tmState=commit + guard working∨abort → contradiction via h19)
  · intro hc; exfalso
    rcases h_guard with hw | ha
    · exact h19 hc rm hw
    · rw [hc] at ha; simp at ha
  -- 3. abort → no committed
  · intro h; rw [h_rm]; exact ne_update_of_ne (by decide) (h3 h)
  -- 4. committed → tmState ∈ {commit, hidden}
  · intro r hr; rw [h_rm] at hr; simp only [Function.update_apply] at hr
    split_ifs at hr; simp_all [h4 r hr]
  -- 5. init → no committed
  · intro h; rw [h_rm]; exact ne_update_of_ne (by decide) (h5 h)
  -- 9a. TC → no aborted
  · intro htc r; rw [h_rm]; simp only [Function.update_apply]
    split_ifs with heq <;> simp_all
  -- 9b. TC → no working
  · intro h; rw [h_rm]; exact ne_update_of_ne (by decide) (h10 h)
  -- 10. TA → canAbort
  · intro hta; rw [h_rm]
    rcases h11 hta with ⟨⟨r, hr⟩, h_nc⟩
    exact ⟨⟨rm, by simp⟩, ne_update_of_ne (by decide) h_nc⟩
  -- 13a. BTC → no aborted
  · intro hbtc r; rw [h_rm]; simp only [Function.update_apply]
    split_ifs with heq <;> simp_all
  -- 13b. BTC → no working
  · intro h; rw [h_rm]; exact ne_update_of_ne (by decide) (h15 h)
  -- 14. BTA → canAbort
  · intro hbta; rw [h_rm]
    rcases h16 hbta with ⟨⟨r, hr⟩, h_nc⟩
    exact ⟨⟨rm, by simp⟩, ne_update_of_ne (by decide) h_nc⟩
  -- 19. commit → no working
  · intro h; rw [h_rm]; exact ne_update_of_ne (by decide) (h19 h)
  -- 20. some committed → no working
  · intro ⟨r, hr⟩; rw [h_rm] at hr; simp only [Function.update_apply] at hr
    by_cases heq : r = rm
    · subst heq; simp_all
    · simp [heq] at hr
      intro r'; rw [h_rm]; simp only [Function.update_apply]
      split_ifs <;> simp_all [h20 ⟨r, hr⟩]

-- rmFail preserves the invariant (rmState → failed or unchanged)
omit [Fintype RM] in
lemma btmInvariant_rmFail (RMMAYFAIL : Bool) (rm : RM) (s s' : BTMState RM) :
    btmInvariant s → rmFail RMMAYFAIL rm s s' → btmInvariant s' := by
  intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
    ⟨_, h_wp, h_disj, h_rmPC, h_tm, h_tmPC, h_btmPC⟩
  unfold btmInvariant btmConsistent btmCanAbort at *
  rw [h_tm, h_tmPC, h_btmPC]
  rcases h_disj with ⟨_, _, h_rm⟩ | ⟨_, h_rm⟩
  · -- Case: rmState rm → failed
    rw [h_rm]
    refine ⟨?_, ?_, ?_, ?_, ?_, h6, h7, h8, ?_, ?_, ?_, h12, h13, ?_, ?_, ?_, h17, h18, ⟨?_, ?_⟩⟩
    -- 1. Consistency
    · exact btmConsistent_update h1 (by decide) (by decide)
    -- 2. commit → no aborted
    · intro h; exact ne_update_of_ne (by decide) (h2 h)
    -- 3. abort → no committed
    · intro h; exact ne_update_of_ne (by decide) (h3 h)
    -- 4. committed → tmState ∈ {commit, hidden}
    · intro r hr; simp only [Function.update_apply] at hr
      split_ifs at hr; simp_all [h4 r hr]
    -- 5. init → no committed
    · intro h; exact ne_update_of_ne (by decide) (h5 h)
    -- 9a. TC → no aborted
    · intro h; exact ne_update_of_ne (by decide) (h9 h)
    -- 9b. TC → no working
    · intro h; exact ne_update_of_ne (by decide) (h10 h)
    -- 10. TA → canAbort
    · intro h; rcases h11 h with ⟨⟨r, hr⟩, h_nc⟩
      exact ⟨⟨r, by simp only [Function.update_apply]; split_ifs with heq <;> simp_all⟩,
             ne_update_of_ne (by decide) h_nc⟩
    -- 13a. BTC → no aborted
    · intro h; exact ne_update_of_ne (by decide) (h14 h)
    -- 13b. BTC → no working
    · intro h; exact ne_update_of_ne (by decide) (h15 h)
    -- 14. BTA → canAbort
    · intro h; rcases h16 h with ⟨⟨r, hr⟩, h_nc⟩
      exact ⟨⟨r, by simp only [Function.update_apply]; split_ifs with heq <;> simp_all⟩,
             ne_update_of_ne (by decide) h_nc⟩
    -- 19. commit → no working
    · intro h; exact ne_update_of_ne (by decide) (h19 h)
    -- 20. some committed → no working
    · intro ⟨r, hr⟩; simp only [Function.update_apply] at hr
      by_cases heq : r = rm
      · subst heq; simp_all
      · simp [heq] at hr
        intro r'; simp only [Function.update_apply]
        split_ifs <;> simp_all [h20 ⟨r, hr⟩]
  · -- Case: noop (rmState unchanged)
    rw [h_rm]
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
      h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩

-- rmDone preserves the invariant (only rmPC changes)
omit [Fintype RM] in
lemma btmInvariant_rmDone (rm : RM) (s s' : BTMState RM) :
    btmInvariant s → rmDone rm s s' → btmInvariant s' := by
  intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
    ⟨_, _, _, _, h_rm, h_tm, h_tmPC, h_btmPC⟩
  unfold btmInvariant btmConsistent btmCanAbort at *
  rw [h_rm, h_tm, h_tmPC, h_btmPC]
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩

-- Inductive step: any btmNext step preserves the invariant
omit [Fintype RM] in
lemma btmInvariant_step (RMMAYFAIL TMMAYFAIL : Bool) (s s' : BTMState RM) :
    btmInvariant s → btmNext RMMAYFAIL TMMAYFAIL s s' → btmInvariant s' := by
  intro h_inv h_next
  unfold btmNext at h_next
  rcases h_next with h | h | h | h | h | h | h | h | h | h
    | ⟨rm, h | h | h | h | h⟩ | h
  · exact btmInvariant_tsCommit s s' h_inv h
  · exact btmInvariant_tsAbort s s' h_inv h
  · exact btmInvariant_tmTC s s' h_inv h
  · exact btmInvariant_tmF1 TMMAYFAIL s s' h_inv h
  · exact btmInvariant_tmTA s s' h_inv h
  · exact btmInvariant_tmF2 TMMAYFAIL s s' h_inv h
  · exact btmInvariant_btsCommit s s' h_inv h
  · exact btmInvariant_btsAbort s s' h_inv h
  · exact btmInvariant_btmBTC s s' h_inv h
  · exact btmInvariant_btmBTA s s' h_inv h
  · exact btmInvariant_rmPrepare rm s s' h_inv h
  · exact btmInvariant_rmDecideCommit rm s s' h_inv h
  · exact btmInvariant_rmDecideAbort rm s s' h_inv h
  · exact btmInvariant_rmFail RMMAYFAIL rm s s' h_inv h
  · exact btmInvariant_rmDone rm s s' h_inv h
  · exact btmInvariant_terminating s s' h_inv h

-- MAIN THEOREM: Consistency is an invariant of the 2PC with BTM protocol
omit [Fintype RM] in
theorem btmSpec (RMMAYFAIL TMMAYFAIL : Bool) (s : BTMState RM) :
    BTMReachable RMMAYFAIL TMMAYFAIL s → btmConsistent s := by
  intro h
  suffices btmInvariant s from this.1
  induction h with
  | init => exact btmInvariant_init
  | step h_reach h_next ih => exact btmInvariant_step RMMAYFAIL TMMAYFAIL _ _ ih h_next
