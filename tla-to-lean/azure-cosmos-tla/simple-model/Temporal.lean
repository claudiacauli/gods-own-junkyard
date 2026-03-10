/-!
# Temporal Logic Infrastructure

Generic infrastructure for reasoning about temporal properties over infinite
execution traces. Models TLA+'s temporal operators:
- `□P` (always) — `always`
- `◇P` (eventually) — `eventually`
- `P ~> Q` (leads-to) — `leadsTo`
- `WF_v(A)` (weak fairness) — `weakFair`

The key theorem is `leadsTo_by_wf1`: the standard WF1 proof rule from TLA+.
If an action is always enabled when P holds, achieves Q when it fires,
and P is preserved by non-action steps, then P ~> Q under weak fairness.

Design decisions:
- Traces are functions `Nat → S` (infinite sequences of states).
- Temporal operators are predicates on traces, parameterized by a
  starting index (suffix semantics).
- No dependency on Mathlib — only core Lean 4. Uses `Classical.byContradiction`
  for the WF1 proof.
-/

open Classical

/- ================================================================
   Section 1: Traces and Executions
   ================================================================ -/

-- An infinite execution trace: an infinite sequence of states
def Trace (S : Type) := Nat → S

-- A trace satisfies a transition relation at every step
def isExecution (init : S → Prop) (next : S → S → Prop)
    (σ : Trace S) : Prop :=
  init (σ 0) ∧ ∀ n, next (σ n) (σ (n + 1))

/- ================================================================
   Section 2: Temporal Operators
   ================================================================ -/

-- □P from index `from`: P holds at every step ≥ from
def always (P : S → Prop) (σ : Trace S) (from_ : Nat) : Prop :=
  ∀ n, n ≥ from_ → P (σ n)

-- ◇P from index `from`: P holds at some step ≥ from
def eventually (P : S → Prop) (σ : Trace S) (from_ : Nat) : Prop :=
  ∃ n, n ≥ from_ ∧ P (σ n)

-- P ~> Q: whenever P holds, Q eventually holds (at the same or later step)
def leadsTo (P Q : S → Prop) (σ : Trace S) : Prop :=
  ∀ n, P (σ n) → eventually Q σ n

-- □P (globally): P holds at every step
def globally (P : S → Prop) (σ : Trace S) : Prop :=
  always P σ 0

/- ================================================================
   Section 3: Fairness
   ================================================================ -/

-- An action is "enabled" at state s if there exists a successor via that action
def enabled (act : S → S → Prop) (s : S) : Prop :=
  ∃ s', act s s'

-- Weak fairness (WF): if the action is continuously enabled from some point,
-- then it is eventually taken.
def weakFair (act : S → S → Prop) (σ : Trace S) : Prop :=
  ∀ n, (∀ m, m ≥ n → enabled act (σ m)) →
    ∃ m, m ≥ n ∧ act (σ m) (σ (m + 1))

-- A fair execution: satisfies the transition relation and weak fairness
-- for a designated action
def isFairExecution (init : S → Prop) (next : S → S → Prop)
    (fair_act : S → S → Prop) (σ : Trace S) : Prop :=
  isExecution init next σ ∧ weakFair fair_act σ

/- ================================================================
   Section 4: Basic Temporal Lemmas
   ================================================================ -/

theorem always_weaken {P : S → Prop} {σ : Trace S} {i j : Nat}
    (h : always P σ i) (hij : i ≤ j) : always P σ j :=
  fun n hn => h n (Nat.le_trans hij hn)

theorem eventually_weaken {P : S → Prop} {σ : Trace S} {i j : Nat}
    (h : eventually P σ j) (hij : i ≤ j) : eventually P σ i :=
  let ⟨n, hn, hp⟩ := h; ⟨n, Nat.le_trans hij hn, hp⟩

theorem always_imp {P Q : S → Prop} {σ : Trace S} {i : Nat}
    (h : always P σ i) (hpq : ∀ s, P s → Q s) : always Q σ i :=
  fun n hn => hpq _ (h n hn)

theorem eventually_imp {P Q : S → Prop} {σ : Trace S} {i : Nat}
    (h : eventually P σ i) (hpq : ∀ s, P s → Q s) : eventually Q σ i :=
  let ⟨n, hn, hp⟩ := h; ⟨n, hn, hpq _ hp⟩

theorem always_at {P : S → Prop} {σ : Trace S} {n : Nat}
    (h : always P σ n) : P (σ n) :=
  h n (Nat.le_refl n)

theorem eventually_of_now {P : S → Prop} {σ : Trace S} {n : Nat}
    (h : P (σ n)) : eventually P σ n :=
  ⟨n, Nat.le_refl n, h⟩

theorem eventually_bind {P Q : S → Prop} {σ : Trace S} {i : Nat}
    (h : eventually P σ i) (hpq : ∀ n, n ≥ i → P (σ n) → eventually Q σ n) :
    eventually Q σ i :=
  let ⟨n, hn, hp⟩ := h
  let ⟨m, hm, hq⟩ := hpq n hn hp
  ⟨m, Nat.le_trans hn hm, hq⟩

/- ================================================================
   Section 5: The Key Liveness Theorem (WF1)
   ================================================================ -/

-- Helper: ¬(∃ m, m ≥ n ∧ P (σ m)) implies ∀ m ≥ n, ¬P (σ m)
private theorem not_eventually_forall {P : S → Prop} {σ : Trace S} {n : Nat}
    (h : ¬eventually P σ n) : ∀ m, m ≥ n → ¬P (σ m) :=
  fun m hm hp => h ⟨m, hm, hp⟩

-- The main leads-to theorem (WF1 rule from TLA+):
--
-- Proof sketch:
-- Suppose P holds at step n but Q never holds at any step ≥ n.
-- Then by induction, P holds at all steps ≥ n (since non-act steps
-- preserve P, and act steps would give Q — contradiction).
-- P always → act always enabled → weak fairness → act fires → Q holds.
-- Contradiction.
theorem leadsTo_by_wf1
    {P Q : S → Prop}
    {next : S → S → Prop}
    {act : S → S → Prop}
    {σ : Trace S}
    (h_exec : ∀ n, next (σ n) (σ (n + 1)))
    (h_fair : weakFair act σ)
    (h_enabled : ∀ s, P s → enabled act s)
    (h_act_achieves : ∀ s s', P s → act s s' → Q s')
    (h_persist : ∀ s s', P s → next s s' → ¬act s s' → P s' ∨ Q s') :
    leadsTo P Q σ := by
  intro n h_pn
  -- Use classical logic: either eventually Q, or never Q
  exact byContradiction fun h_neg => by
    have h_not := not_eventually_forall h_neg
    -- Show P holds at all steps ≥ n
    have h_p_always : ∀ m, m ≥ n → P (σ m) := by
      intro m hm
      induction m with
      | zero =>
          have h0 : n = 0 := by omega
          rw [← h0]; exact h_pn
      | succ k ih =>
        by_cases hk : k ≥ n
        · have h_pk := ih hk
          have h_step := h_exec k
          by_cases h_act : act (σ k) (σ (k + 1))
          · exact absurd (h_act_achieves _ _ h_pk h_act) (h_not (k + 1) (by omega))
          · cases h_persist _ _ h_pk h_step h_act with
            | inl h_p' => exact h_p'
            | inr h_q' => exact absurd h_q' (h_not (k + 1) (by omega))
        · have : k + 1 = n := by omega
          rw [this]; exact h_pn
    -- P always → act always enabled → fairness → act fires → Q → contradiction
    have h_always_enabled : ∀ m, m ≥ n → enabled act (σ m) :=
      fun m hm => h_enabled _ (h_p_always m hm)
    have ⟨m, hm, h_act⟩ := h_fair n h_always_enabled
    exact h_not (m + 1) (by omega) (h_act_achieves _ _ (h_p_always m hm) h_act)

/- ================================================================
   Section 6: Invariant + Liveness Combination
   ================================================================ -/

-- WF1 with an invariant: same as leadsTo_by_wf1 but all premises
-- are guarded by an invariant Inv that holds at every trace state.
theorem leadsTo_by_wf1_with_inv
    {Inv P Q : S → Prop}
    {next : S → S → Prop}
    {act : S → S → Prop}
    {σ : Trace S}
    (h_exec : ∀ n, next (σ n) (σ (n + 1)))
    (h_fair : weakFair act σ)
    (h_inv : ∀ n, Inv (σ n))
    (h_enabled : ∀ s, Inv s → P s → enabled act s)
    (h_act_achieves : ∀ s s', Inv s → P s → act s s' → Q s')
    (h_persist : ∀ s s', Inv s → P s → next s s' → ¬act s s' → P s' ∨ Q s') :
    leadsTo P Q σ := by
  intro n h_pn
  exact byContradiction fun h_neg => by
    have h_not := not_eventually_forall h_neg
    have h_p_always : ∀ m, m ≥ n → P (σ m) := by
      intro m hm
      induction m with
      | zero =>
          have h0 : n = 0 := by omega
          rw [← h0]; exact h_pn
      | succ k ih =>
        by_cases hk : k ≥ n
        · have h_pk := ih hk
          have h_step := h_exec k
          by_cases h_act : act (σ k) (σ (k + 1))
          · exact absurd (h_act_achieves _ _ (h_inv k) h_pk h_act) (h_not (k + 1) (by omega))
          · cases h_persist _ _ (h_inv k) h_pk h_step h_act with
            | inl h_p' => exact h_p'
            | inr h_q' => exact absurd h_q' (h_not (k + 1) (by omega))
        · have : k + 1 = n := by omega
          rw [this]; exact h_pn
    have h_always_enabled : ∀ m, m ≥ n → enabled act (σ m) :=
      fun m hm => h_enabled _ (h_inv m) (h_p_always m hm)
    have ⟨m, hm, h_act⟩ := h_fair n h_always_enabled
    exact h_not (m + 1) (by omega) (h_act_achieves _ _ (h_inv m) (h_p_always m hm) h_act)
