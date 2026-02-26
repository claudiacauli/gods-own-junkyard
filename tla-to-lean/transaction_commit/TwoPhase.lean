import TCommit

variable {RM : Type} [Fintype RM] [DecidableEq RM]

-- The set of all possible messages (TLA+ line 43-51)
-- Prepared: sent from an RM to the TM
-- Commit/Abort: broadcast by the TM to all RMs
inductive Message (RM : Type) where
  | prepared (rm : RM)
  | commit
  | abort

-- The three states of the transaction manager (TLA+ line 58)
inductive TMState where
  | init
  | committed
  | aborted

-- The overall state of the Two-Phase Commit system (TLA+ lines 21-26)
-- rmState: state of each resource manager
-- tmState: state of the transaction manager
-- tmPrepared: set of RMs from which the TM has received "Prepared" messages
-- msgs: set of all messages that have been sent
structure TPState (RM : Type) where
  rmState : RM → RMState
  tmState : TMState
  tmPrepared : Set RM
  msgs : Set (Message RM)

-- The initial state (TLA+ lines 62-69)
def tpInit : TPState RM where
  rmState := fun _ => RMState.working
  tmState := TMState.init
  tmPrepared := ∅
  msgs := ∅

-- TM receives a "Prepared" message from resource manager rm (TLA+ lines 75-82)
def tmRcvPrepared (rm : RM) (s s' : TPState RM) : Prop :=
  s.tmState = TMState.init
  ∧ Message.prepared rm ∈ s.msgs
  ∧ s'.tmPrepared = s.tmPrepared ∪ {rm}
  ∧ s'.rmState = s.rmState
  ∧ s'.tmState = s.tmState
  ∧ s'.msgs = s.msgs

-- TM commits the transaction (TLA+ lines 84-93)
-- Enabled iff TM is in init state and every RM has sent "Prepared"
def tmCommit (s s' : TPState RM) : Prop :=
  s.tmState = TMState.init
  ∧ s.tmPrepared = Set.univ
  ∧ s'.tmState = TMState.committed
  ∧ s'.msgs = s.msgs ∪ {Message.commit}
  ∧ s'.rmState = s.rmState
  ∧ s'.tmPrepared = s.tmPrepared

-- TM spontaneously aborts the transaction (TLA+ lines 95-102)
def tmAbort (s s' : TPState RM) : Prop :=
  s.tmState = TMState.init
  ∧ s'.tmState = TMState.aborted
  ∧ s'.msgs = s.msgs ∪ {Message.abort}
  ∧ s'.rmState = s.rmState
  ∧ s'.tmPrepared = s.tmPrepared

-- Resource manager rm prepares (TLA+ lines 104-111)
def rmPrepare (rm : RM) (s s' : TPState RM) : Prop :=
  s.rmState rm = RMState.working
  ∧ s'.rmState = Function.update s.rmState rm RMState.prepared
  ∧ s'.msgs = s.msgs ∪ {Message.prepared rm}
  ∧ s'.tmState = s.tmState
  ∧ s'.tmPrepared = s.tmPrepared

-- Resource manager rm spontaneously decides to abort (TLA+ lines 113-120)
def rmChooseToAbort (rm : RM) (s s' : TPState RM) : Prop :=
  s.rmState rm = RMState.working
  ∧ s'.rmState = Function.update s.rmState rm RMState.aborted
  ∧ s'.tmState = s.tmState
  ∧ s'.tmPrepared = s.tmPrepared
  ∧ s'.msgs = s.msgs

-- Resource manager rm is told by the TM to commit (TLA+ lines 122-128)
def rmRcvCommitMsg (rm : RM) (s s' : TPState RM) : Prop :=
  Message.commit ∈ s.msgs
  ∧ s'.rmState = Function.update s.rmState rm RMState.committed
  ∧ s'.tmState = s.tmState
  ∧ s'.tmPrepared = s.tmPrepared
  ∧ s'.msgs = s.msgs

-- Resource manager rm is told by the TM to abort (TLA+ lines 130-136)
def rmRcvAbortMsg (rm : RM) (s s' : TPState RM) : Prop :=
  Message.abort ∈ s.msgs
  ∧ s'.rmState = Function.update s.rmState rm RMState.aborted
  ∧ s'.tmState = s.tmState
  ∧ s'.tmPrepared = s.tmPrepared
  ∧ s'.msgs = s.msgs

-- The next-state relation (TLA+ lines 138-142)
def tpNext (s s' : TPState RM) : Prop :=
  tmCommit s s' ∨ tmAbort s s'
  ∨ ∃ rm : RM,
      tmRcvPrepared rm s s' ∨ rmPrepare rm s s' ∨ rmChooseToAbort rm s s'
      ∨ rmRcvCommitMsg rm s s' ∨ rmRcvAbortMsg rm s s'

-- Reachable states of the Two-Phase protocol
inductive TPReachable : TPState RM → Prop where
  | init : TPReachable tpInit
  | step {s s'} : TPReachable s → tpNext s s' → TPReachable s'

-- The consistency invariant lifted to TPState:
-- no RM has aborted while another has committed
def tpConsistent (s : TPState RM) : Prop :=
  tcConsistent s.rmState

-- Refinement mapping: a TPState projects to a TCState via .rmState
-- This connects the two specs: TC == INSTANCE TCommit (TLA+ line 163)
def refinement (s : TPState RM) : RM → RMState := s.rmState

-- THEOREM TPSpec => []TPTypeOK (TLA+ line 149)
-- Type correctness is guaranteed by Lean's type system — nothing to prove.

-------------------------------------------------------------------------------
-- Strengthened inductive invariant
-- tpConsistent alone is too weak. We need auxiliary facts about messages:
-- 1) If an RM is working, no Commit message has been sent
--    (equivalently: if Commit ∈ msgs, no RM is working)
-- 2) If Commit ∈ msgs, no RM is aborted
-- 3) If Abort ∈ msgs, no RM is committed
-- We bundle these into a single "strong invariant".
-------------------------------------------------------------------------------

-- The strengthened invariant: consistency + message coherence
def tpInvariant (s : TPState RM) : Prop :=
  tpConsistent s
  ∧ (Message.commit ∈ s.msgs → ∀ rm : RM, s.rmState rm ≠ RMState.aborted)
  ∧ (Message.abort ∈ s.msgs → ∀ rm : RM, s.rmState rm ≠ RMState.committed)
  ∧ (∀ rm : RM, s.rmState rm = RMState.committed → Message.commit ∈ s.msgs)
  ∧ (∀ rm : RM, s.rmState rm = RMState.working → ¬ Message.commit ∈ s.msgs)
  ∧ (s.tmState = TMState.init → Message.commit ∉ s.msgs)
  ∧ (Message.commit ∈ s.msgs → s.tmState = TMState.committed)
  ∧ (Message.abort ∈ s.msgs → s.tmState = TMState.aborted)
  ∧ (∀ rm : RM, rm ∈ s.tmPrepared → Message.prepared rm ∈ s.msgs)
  ∧ (∀ rm : RM, Message.prepared rm ∈ s.msgs → s.rmState rm ≠ RMState.working)
  ∧ (∀ rm : RM, Message.prepared rm ∈ s.msgs → s.rmState rm = RMState.aborted
      → Message.abort ∈ s.msgs)

-------------------------------------------------------------------------------
-- Proof skeleton: one lemma per action, showing each preserves the invariant
-------------------------------------------------------------------------------

-- Base case: the initial state satisfies the invariant
omit [Fintype RM] [DecidableEq RM] in
lemma tpInvariant_init : tpInvariant (tpInit : TPState RM) := by
  simp only [tpInvariant, tpConsistent, tcConsistent, tpInit]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp

-- TMRcvPrepared preserves the invariant (rmState, msgs unchanged)
omit [Fintype RM] [DecidableEq RM] in
lemma tpInvariant_tmRcvPrepared (rm : RM) (s s' : TPState RM) :
    tpInvariant s → tmRcvPrepared rm s s' → tpInvariant s' := by
  intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h_nw, h_am, h_pw⟩
    ⟨h_init, h_prep_msg, h_tmPrep, h_rm, h_tm, h_msgs⟩
  unfold tpInvariant tpConsistent at ⊢
  rw [h_rm, h_tm, h_msgs]
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, ?_, h_am, h_pw⟩
  -- ∀ r, r ∈ s'.tmPrepared → prepared r ∈ s.msgs
  intro r hr; rw [h_tmPrep] at hr
  rcases hr with hr | hr
  · exact h_nw r hr
  · rw [Set.mem_singleton_iff] at hr; subst hr
    exact h_prep_msg

-- If an RM is in tmPrepared and aborted, then abort ∈ msgs.
-- (Needs to be added as an invariant clause.)
omit [Fintype RM] [DecidableEq RM] in
lemma tmPrepared_aborted_means_abort (s : TPState RM)
    (h_inv : tpInvariant s)
    (r : RM)
    (h_mem : r ∈ s.tmPrepared)
    (h_abt : s.rmState r = RMState.aborted) :
    Message.abort ∈ s.msgs := by
  exact h_inv.2.2.2.2.2.2.2.2.2.2 r (h_inv.2.2.2.2.2.2.2.2.1 r h_mem) h_abt

-- If tmPrepared = univ and tmState = init, no RM is aborted.
-- (Requires strengthening the invariant with tmPrepared-related clauses.)
omit [Fintype RM] [DecidableEq RM] in
lemma tmPrepared_univ_no_aborted (s : TPState RM)
    (h_prep : s.tmPrepared = Set.univ)
    (h_init : s.tmState = TMState.init)
    (h_inv : tpInvariant s)
    (r : RM) : s.rmState r ≠ RMState.aborted := by
  have h_na : Message.abort ∉ s.msgs := by
    intro h; exact absurd (h_inv.2.2.2.2.2.2.2.1 h)
      (by simp [h_init])
  have h_mem : r ∈ s.tmPrepared := h_prep ▸ Set.mem_univ r
  intro h_abt
  exact h_na
    (tmPrepared_aborted_means_abort s h_inv r h_mem h_abt)

-- If an RM is in tmPrepared, it is not working.
-- (Needs to be added as an invariant clause.)
omit [Fintype RM] [DecidableEq RM] in
lemma tmPrepared_not_working (s : TPState RM)
    (h_inv : tpInvariant s)
    (r : RM)
    (h_mem : r ∈ s.tmPrepared) :
    s.rmState r ≠ RMState.working := by
  exact h_inv.2.2.2.2.2.2.2.2.2.1 r (h_inv.2.2.2.2.2.2.2.2.1 r h_mem)

-- If tmPrepared = univ and tmState = init, no RM is working.
-- (Requires strengthening the invariant with tmPrepared-related clauses.)
omit [Fintype RM] [DecidableEq RM] in
lemma tmPrepared_univ_no_working (s : TPState RM)
    (h_prep : s.tmPrepared = Set.univ)
    (_h_init : s.tmState = TMState.init)
    (h_inv : tpInvariant s)
    (r : RM) : s.rmState r ≠ RMState.working := by
  have h_mem : r ∈ s.tmPrepared := h_prep ▸ Set.mem_univ r
  exact tmPrepared_not_working s h_inv r h_mem

-- TMCommit preserves the invariant
omit [Fintype RM] [DecidableEq RM] in
lemma tpInvariant_tmCommit (s s' : TPState RM) :
    tpInvariant s → tmCommit s s' → tpInvariant s' := by
  intro ⟨h_con, h_ca, h_ac, h_cm, h_wc, h_ic, h_tc, h_ta, h_tp, h_pnw, h_pam⟩
    ⟨h_init, h_prep, h_committed, h_msgs, h_rm, h_tmPrep⟩
  have h_inv : tpInvariant s :=
    ⟨h_con, h_ca, h_ac, h_cm, h_wc, h_ic, h_tc, h_ta, h_tp, h_pnw, h_pam⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- 1. tpConsistent
  · unfold tpConsistent at *; rw [h_rm]; exact h_con
  -- 2. commit ∈ msgs' → ∀ rm, rmState' rm ≠ aborted
  · intro _ r; rw [h_rm]
    exact tmPrepared_univ_no_aborted s h_prep h_init h_inv r
  -- 3. abort ∈ msgs' → ∀ rm, rmState' rm ≠ committed
  · intro h r; rw [h_rm]; rw [h_msgs] at h
    rcases h with h | h
    · exact h_ac h r
    · simp at h
  -- 4. ∀ rm, rmState' rm = committed → commit ∈ msgs'
  · intro _ _; rw [h_msgs]; right; rfl
  -- 5. ∀ rm, rmState' rm = working → commit ∉ msgs'
  · intro r hr; rw [h_rm] at hr
    exact absurd hr (tmPrepared_univ_no_working s h_prep h_init h_inv r)
  -- 6. tmState' = init → commit ∉ msgs'
  · simp [h_committed]
  -- 7. commit ∈ msgs' → tmState' = committed
  · intro; exact h_committed
  -- 8. abort ∈ msgs' → tmState' = aborted
  · intro h; rw [h_msgs] at h
    rcases h with h | h
    · exact absurd (h_ta h) (by simp [h_init])
    · simp at h
  -- 9. ∀ rm, rm ∈ tmPrepared' → prepared rm ∈ msgs'
  · intro r hr; rw [h_tmPrep] at hr; rw [h_msgs]; left; exact h_tp r hr
  -- 10. ∀ rm, prepared rm ∈ msgs' → rmState' rm ≠ working
  · intro r h; rw [h_rm]; rw [h_msgs] at h
    rcases h with h | h
    · exact h_pnw r h
    · simp at h
  -- 11. ∀ rm, prepared rm ∈ msgs' → rmState' rm = aborted → abort ∈ msgs'
  · intro r h; rw [h_rm]; rw [h_msgs] at h
    rcases h with h | h
    · intro ha; rw [h_msgs]; left; exact h_pam r h ha
    · simp at h

-- TMAbort preserves the invariant
omit [Fintype RM] [DecidableEq RM] in
lemma tpInvariant_tmAbort (s s' : TPState RM) :
    tpInvariant s → tmAbort s s' → tpInvariant s' := by
  intro ⟨h_con, h_ca, h_ac, h_cm, h_wc, h_ic, h_tc, h_ta, h_tp, h_pnw, h_pam⟩
    ⟨h_init, h_aborted, h_msgs, h_rm, h_tmPrep⟩
  refine ⟨by unfold tpConsistent at *; rw [h_rm]; exact h_con,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h r; rw [h_rm]; rw [h_msgs] at h
    rcases h with h | h
    · exact h_ca h r
    · simp at h
  · intro _ r; rw [h_rm]
    intro h_eq
    exact absurd (h_cm r h_eq) (h_ic h_init)
  · intro r hr; rw [h_rm] at hr; rw [h_msgs]; left; exact h_cm r hr
  · intro r hr; rw [h_rm] at hr
    intro h; rw [h_msgs] at h
    rcases h with h | h
    · exact h_wc r hr h
    · simp at h
  · intro h_tm; simp [h_aborted] at h_tm
  · intro h; rw [h_msgs] at h; rcases h with h | h
    · exact absurd h (h_ic h_init)
    · simp at h
  · intro _; exact h_aborted
  -- 9. tmPrepared' → prepared ∈ msgs'
  · intro r hr; rw [h_tmPrep] at hr; rw [h_msgs]; left; exact h_tp r hr
  -- 10. prepared ∈ msgs' → not working
  · intro r h; rw [h_rm]; rw [h_msgs] at h
    rcases h with h | h
    · exact h_pnw r h
    · simp at h
  -- 11. prepared ∈ msgs' → aborted → abort ∈ msgs'
  · intro r h; rw [h_rm]; rw [h_msgs] at h
    rcases h with h | h
    · intro ha; rw [h_msgs]; left; exact h_pam r h ha
    · simp at h

-- RMPrepare preserves the invariant
omit [Fintype RM] in
lemma tpInvariant_rmPrepare (rm : RM) (s s' : TPState RM) :
    tpInvariant s → rmPrepare rm s s' → tpInvariant s' := by
  intro ⟨h_con, h_ca, h_ac, h_cm, h_wc, h_ic, h_tc, h_ta, h_tp, h_pnw, h_pam⟩
    ⟨h_working, h_rm, h_msgs, h_tm, h_tmPrep⟩
  have h_nc : Message.commit ∉ s.msgs := h_wc rm h_working
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold tpConsistent tcConsistent
    rintro ⟨_, r2, _, h2⟩; rw [h_rm] at h2; simp only [Function.update_apply] at h2
    split_ifs at h2
    exact absurd (h_cm r2 h2) h_nc
  · intro h r; rw [h_rm]; simp only [Function.update_apply]; split_ifs
    · simp
    · rw [h_msgs] at h; rcases h with h | h
      · exact h_ca h r
      · simp at h
  · intro h r; rw [h_rm]; simp only [Function.update_apply]; split_ifs
    · simp
    · rw [h_msgs] at h; rcases h with h | h
      · exact h_ac h r
      · simp at h
  · intro r h; rw [h_rm] at h; simp only [Function.update_apply] at h; split_ifs at h
    rw [h_msgs]; left; exact h_cm r h
  · intro r h; rw [h_rm] at h; simp only [Function.update_apply] at h; split_ifs at h
    rw [h_msgs]; intro hc; rcases hc with hc | hc
    · exact h_wc r h hc
    · simp at hc
  · rw [h_tm, h_msgs]; intro h hc; rcases hc with hc | hc
    · exact h_ic h hc
    · simp at hc
  · rw [h_tm]; intro h; rw [h_msgs] at h; rcases h with h | h
    · exact h_tc h
    · simp at h
  · rw [h_tm]; intro h; rw [h_msgs] at h; rcases h with h | h
    · exact h_ta h
    · simp at h
  -- 9. tmPrepared' → prepared ∈ msgs' (tmPrepared unchanged, msgs grew)
  · intro r hr; rw [h_tmPrep] at hr; rw [h_msgs]; left; exact h_tp r hr
  -- 10. prepared r ∈ msgs' → rmState' r ≠ working
  · intro r h; rw [h_rm]; simp only [Function.update_apply]
    rw [h_msgs] at h; rcases h with h | h
    · split_ifs with heq
      · simp
      · exact h_pnw r h
    · rw [Set.mem_singleton_iff] at h
      have : r = rm := Message.prepared.inj h
      subst this; simp
  -- 11. prepared r ∈ msgs' → rmState' r = aborted → abort ∈ msgs'
  · intro r h; rw [h_rm]; simp only [Function.update_apply]
    rw [h_msgs] at h; rcases h with h | h
    · split_ifs with heq
      · simp
      · intro ha; rw [h_msgs]; left; exact h_pam r h ha
    · rw [Set.mem_singleton_iff] at h
      have : r = rm := Message.prepared.inj h
      subst this; simp

-- RMChooseToAbort preserves the invariant
omit [Fintype RM] in
lemma tpInvariant_rmChooseToAbort (rm : RM) (s s' : TPState RM) :
    tpInvariant s → rmChooseToAbort rm s s' → tpInvariant s' := by
  intro ⟨h_con, h_ca, h_ac, h_cm, h_wc, h_ic, h_tc, h_ta, h_tp, h_pnw, h_pam⟩
    ⟨h_working, h_rm, h_tm, h_tmPrep, h_msgs⟩
  have h_nc : Message.commit ∉ s.msgs := h_wc rm h_working
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold tpConsistent tcConsistent
    rintro ⟨_, r2, _, h2⟩; rw [h_rm] at h2; simp only [Function.update_apply] at h2
    split_ifs at h2
    exact absurd (h_cm r2 h2) h_nc
  · intro h; rw [h_msgs] at h; exact absurd h h_nc
  · intro h r; rw [h_msgs] at h; rw [h_rm]; simp only [Function.update_apply]; split_ifs
    · simp
    · exact h_ac h r
  · intro r h; rw [h_rm] at h; simp only [Function.update_apply] at h; split_ifs at h
    rw [h_msgs]; exact h_cm r h
  · intro r h; rw [h_rm] at h; simp only [Function.update_apply] at h; split_ifs at h
    rw [h_msgs]; exact h_wc r h
  · rw [h_tm, h_msgs]; exact h_ic
  · rw [h_tm, h_msgs]; exact h_tc
  · rw [h_tm, h_msgs]; exact h_ta
  -- 9. tmPrepared' → prepared ∈ msgs'
  · intro r hr; rw [h_tmPrep] at hr; rw [h_msgs]; exact h_tp r hr
  -- 10. prepared ∈ msgs' → rmState' ≠ working
  · intro r h; rw [h_msgs] at h; rw [h_rm]; simp only [Function.update_apply]
    split_ifs with heq
    · simp
    · exact h_pnw r h
  -- 11. prepared ∈ msgs' → rmState' = aborted → abort ∈ msgs'
  · intro r h; rw [h_msgs] at h; rw [h_rm]; simp only [Function.update_apply]
    split_ifs with heq
    · subst heq; intro; exact absurd h_working (h_pnw r h)
    · intro ha; rw [h_msgs]; exact h_pam r h ha

-- RMRcvCommitMsg preserves the invariant
omit [Fintype RM] in
lemma tpInvariant_rmRcvCommitMsg (rm : RM) (s s' : TPState RM) :
    tpInvariant s → rmRcvCommitMsg rm s s' → tpInvariant s' := by
  intro ⟨h_con, h_ca, h_ac, h_cm, h_wc, h_ic, h_tc, h_ta, h_tp, h_pnw, h_pam⟩
    ⟨h_commit, h_rm, h_tm, h_tmPrep, h_msgs⟩
  have h_na : Message.abort ∉ s.msgs := by
    intro h; have h1 := h_tc h_commit; have h2 := h_ta h; simp [h1] at h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold tpConsistent tcConsistent
    rintro ⟨r1, _, h1, _⟩; rw [h_rm] at h1; simp only [Function.update_apply] at h1
    split_ifs at h1
    exact absurd h1 (h_ca h_commit r1)
  · intro h r; rw [h_rm]; simp only [Function.update_apply]; split_ifs
    · simp
    · rw [h_msgs] at h; exact h_ca h r
  · intro h; rw [h_msgs] at h; exact absurd h h_na
  · intro _ _; rw [h_msgs]; exact h_commit
  · intro r h; rw [h_rm] at h; simp only [Function.update_apply] at h; split_ifs at h
    rw [h_msgs]; exact h_wc r h
  · rw [h_tm, h_msgs]; exact h_ic
  · rw [h_tm, h_msgs]; exact h_tc
  · rw [h_tm, h_msgs]; exact h_ta
  -- 9. tmPrepared' → prepared ∈ msgs'
  · intro r hr; rw [h_tmPrep] at hr; rw [h_msgs]; exact h_tp r hr
  -- 10. prepared ∈ msgs' → rmState' ≠ working
  · intro r h; rw [h_msgs] at h; rw [h_rm]; simp only [Function.update_apply]
    split_ifs
    · simp
    · exact h_pnw r h
  -- 11. prepared ∈ msgs' → rmState' = aborted → abort ∈ msgs'
  · intro r h; rw [h_msgs] at h; rw [h_rm]; simp only [Function.update_apply]
    split_ifs
    · simp
    · intro ha; rw [h_msgs]; exact h_pam r h ha

-- RMRcvAbortMsg preserves the invariant
omit [Fintype RM] in
lemma tpInvariant_rmRcvAbortMsg (rm : RM) (s s' : TPState RM) :
    tpInvariant s → rmRcvAbortMsg rm s s' → tpInvariant s' := by
  intro ⟨h_con, h_ca, h_ac, h_cm, h_wc, h_ic, h_tc, h_ta, h_tp, h_pnw, h_pam⟩
    ⟨h_abort, h_rm, h_tm, h_tmPrep, h_msgs⟩
  have h_nc : Message.commit ∉ s.msgs := by
    intro h; have h1 := h_tc h; have h2 := h_ta h_abort; simp [h1] at h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold tpConsistent tcConsistent
    rintro ⟨_, r2, _, h2⟩; rw [h_rm] at h2; simp only [Function.update_apply] at h2
    split_ifs at h2
    exact absurd h2 (h_ac h_abort r2)
  · intro h; rw [h_msgs] at h; exact absurd h h_nc
  · intro h r; rw [h_rm]; simp only [Function.update_apply]; split_ifs
    · simp
    · rw [h_msgs] at h; exact h_ac h r
  · intro r h; rw [h_rm] at h; simp only [Function.update_apply] at h; split_ifs at h
    rw [h_msgs]; exact h_cm r h
  · intro r h; rw [h_rm] at h; simp only [Function.update_apply] at h; split_ifs at h
    rw [h_msgs]; exact h_wc r h
  · rw [h_tm, h_msgs]; exact h_ic
  · rw [h_tm, h_msgs]; exact h_tc
  · rw [h_tm, h_msgs]; exact h_ta
  -- 9. tmPrepared' → prepared ∈ msgs'
  · intro r hr; rw [h_tmPrep] at hr; rw [h_msgs]; exact h_tp r hr
  -- 10. prepared ∈ msgs' → rmState' ≠ working
  · intro r h; rw [h_msgs] at h; rw [h_rm]; simp only [Function.update_apply]
    split_ifs
    · simp
    · exact h_pnw r h
  -- 11. prepared ∈ msgs' → rmState' = aborted → abort ∈ msgs'
  · intro r h; rw [h_msgs] at h; rw [h_rm]; simp only [Function.update_apply]
    split_ifs
    · intro; rw [h_msgs]; exact h_abort
    · intro ha; rw [h_msgs]; exact h_pam r h ha

-- Inductive step: any tpNext step preserves the invariant
omit [Fintype RM] in
lemma tpInvariant_step (s s' : TPState RM) :
    tpInvariant s → tpNext s s' → tpInvariant s' := by
  intro h_inv h_next
  unfold tpNext at h_next
  rcases h_next with h | h | ⟨rm, h | h | h | h | h⟩
  · exact tpInvariant_tmCommit s s' h_inv h
  · exact tpInvariant_tmAbort s s' h_inv h
  · exact tpInvariant_tmRcvPrepared rm s s' h_inv h
  · exact tpInvariant_rmPrepare rm s s' h_inv h
  · exact tpInvariant_rmChooseToAbort rm s s' h_inv h
  · exact tpInvariant_rmRcvCommitMsg rm s s' h_inv h
  · exact tpInvariant_rmRcvAbortMsg rm s s' h_inv h

-- THEOREM TPSpec => TC!TCSpec (TLA+ line 165)
-- The Two-Phase Commit protocol implements the Transaction Commit protocol.
omit [Fintype RM] in
theorem tpSpec (s : TPState RM) : TPReachable s → tpConsistent s := by
  intro h
  suffices tpInvariant s from this.1
  induction h with
  | init => exact tpInvariant_init
  | step h_reach h_next ih => exact tpInvariant_step _ _ ih h_next
