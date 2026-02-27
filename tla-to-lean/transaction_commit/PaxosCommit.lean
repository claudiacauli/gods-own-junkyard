import TCommit

/-!
# Paxos Commit

Lean formalization of the Paxos Commit algorithm (PaxosCommit.tla).
Paxos Commit replaces the single transaction manager of Two-Phase Commit
with a collection of acceptors running one instance of Paxos consensus
per resource manager.  Each RM's prepare/abort decision is agreed upon
by a majority of acceptors; the leader collects these and announces
Commit (all prepared) or Abort (some aborted).

We specify only safety properties.  Leader selection is not modelled:
any process may act as leader at any time.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


variable {RM : Type} [Fintype RM] [DecidableEq RM]
variable {Acceptor : Type} [Fintype Acceptor] [DecidableEq Acceptor]

-------------------------------------------------------------------------------
-- Auxiliary types
-------------------------------------------------------------------------------

-- Value stored by an acceptor: whether the RM prepared, aborted, or
-- no value has been accepted yet.
inductive AccVal where
  | prepared
  | aborted
  | none
  deriving DecidableEq

-- Value carried by phase 2a / 2b messages (only prepared or aborted).
inductive RMVal where
  | prepared
  | aborted
  deriving DecidableEq

-- Convert acceptor values to RM values (AccVal.none maps to aborted).
def accValToRMVal : AccVal → RMVal
  | .prepared => .prepared
  | .aborted  => .aborted
  | .none     => .aborted

-------------------------------------------------------------------------------
-- Acceptor state  (TLA+ lines 90-93)
-- Each acceptor maintains one such record per RM instance.
--   mbal : highest ballot number in which the acceptor has participated
--   bal  : ballot of the highest-numbered ballot in which it voted
--          (Option.none represents TLA+'s -1, i.e. "has never voted")
--   val  : the value it voted for in that ballot (AccVal.none if never voted)
-------------------------------------------------------------------------------

structure AccState where
  mbal : ℕ
  bal  : Option ℕ
  val  : AccVal

-------------------------------------------------------------------------------
-- Messages  (TLA+ lines 57-76)
-------------------------------------------------------------------------------

inductive PCMessage (RM Acceptor : Type) where
  | phase1a (ins : RM) (bal : ℕ)
  | phase1b (ins : RM) (mbal : ℕ) (bal : Option ℕ) (val : AccVal)
            (acc : Acceptor)
  | phase2a (ins : RM) (bal : ℕ) (val : RMVal)
  | phase2b (ins : RM) (bal : ℕ) (val : RMVal) (acc : Acceptor)
  | commit
  | abort

-------------------------------------------------------------------------------
-- System state  (TLA+ lines 78-83)
-------------------------------------------------------------------------------

structure PCState (RM Acceptor : Type) where
  rmState : RM → RMState
  aState  : RM → Acceptor → AccState
  msgs    : Set (PCMessage RM Acceptor)

-------------------------------------------------------------------------------
-- Initial state  (TLA+ lines 96-101)
-------------------------------------------------------------------------------

def pcInit : PCState RM Acceptor where
  rmState := fun _ => RMState.working
  aState  := fun _ _ => { mbal := 0, bal := Option.none, val := AccVal.none }
  msgs    := ∅

-------------------------------------------------------------------------------
-- RM Actions  (TLA+ lines 114-153)
-------------------------------------------------------------------------------

-- RMPrepare: RM rm prepares by sending a phase 2a message for ballot 0
-- with value "prepared".  (TLA+ lines 114-122)
def pcRMPrepare (rm : RM) (s s' : PCState RM Acceptor) : Prop :=
  s.rmState rm = RMState.working
  ∧ s'.rmState = Function.update s.rmState rm RMState.prepared
  ∧ s'.msgs = s.msgs ∪ {PCMessage.phase2a rm 0 RMVal.prepared}
  ∧ s'.aState = s.aState

-- RMChooseToAbort: RM rm spontaneously aborts, sending a phase 2a for
-- ballot 0 with value "aborted".  (TLA+ lines 124-133)
def pcRMChooseToAbort (rm : RM) (s s' : PCState RM Acceptor) : Prop :=
  s.rmState rm = RMState.working
  ∧ s'.rmState = Function.update s.rmState rm RMState.aborted
  ∧ s'.msgs = s.msgs ∪ {PCMessage.phase2a rm 0 RMVal.aborted}
  ∧ s'.aState = s.aState

-- RMRcvCommitMsg: RM rm receives a Commit message.  (TLA+ lines 135-144)
def pcRMRcvCommitMsg (rm : RM) (s s' : PCState RM Acceptor) : Prop :=
  PCMessage.commit ∈ s.msgs
  ∧ s'.rmState = Function.update s.rmState rm RMState.committed
  ∧ s'.aState = s.aState
  ∧ s'.msgs = s.msgs

-- RMRcvAbortMsg: RM rm receives an Abort message.  (TLA+ lines 146-153)
def pcRMRcvAbortMsg (rm : RM) (s s' : PCState RM Acceptor) : Prop :=
  PCMessage.abort ∈ s.msgs
  ∧ s'.rmState = Function.update s.rmState rm RMState.aborted
  ∧ s'.aState = s.aState
  ∧ s'.msgs = s.msgs

-------------------------------------------------------------------------------
-- Leader Actions  (TLA+ lines 163-225)
-------------------------------------------------------------------------------

-- Phase1a: a leader initiates ballot `bal` (bal > 0) for instance `rm`.
-- (TLA+ lines 163-171)
def pcPhase1a (bal : ℕ) (rm : RM) (s s' : PCState RM Acceptor) : Prop :=
  bal > 0
  ∧ s'.msgs = s.msgs ∪ {PCMessage.phase1a rm bal}
  ∧ s'.rmState = s.rmState
  ∧ s'.aState = s.aState

-- Phase2a: a leader sends a phase 2a message with ballot bal > 0 in
-- instance rm, having received phase 1b messages from a majority.
-- The value is determined by the highest-ballot vote among those
-- phase 1b messages (or "aborted" if no acceptor has voted).
-- (TLA+ lines 173-205)
def pcPhase2a (Majority : Set (Set Acceptor))
    (bal : ℕ) (rm : RM) (s s' : PCState RM Acceptor) : Prop :=
  bal > 0
  -- No phase 2a for this ballot/instance already sent
  ∧ (¬ ∃ v : RMVal, PCMessage.phase2a rm bal v ∈ s.msgs)
  -- There is a majority MS of acceptors that responded with phase1b
  ∧ (∃ MS ∈ Majority,
      -- every acceptor in MS sent a phase1b for this ballot
      (∀ ac ∈ MS, ∃ b : Option ℕ, ∃ v : AccVal,
        PCMessage.phase1b rm bal b v ac ∈ s.msgs)
      -- the value to send is determined by the highest previous ballot
      ∧ ∃ val : RMVal,
          -- If no acceptor in MS has previously voted (all bal = none),
          -- the leader sends "aborted".
          -- Otherwise it sends the value from the highest ballot.
          (  (∀ ac ∈ MS, ∀ b v, PCMessage.phase1b rm bal b v ac ∈ s.msgs
                → b = Option.none)
             ∧ val = RMVal.aborted
           ∨ ∃ maxbal : ℕ,
               -- some acceptor voted in ballot maxbal
               (∃ ac ∈ MS, ∃ v, PCMessage.phase1b rm bal (some maxbal) v ac ∈ s.msgs)
               -- no acceptor voted in a higher ballot
               ∧ (∀ ac ∈ MS, ∀ b' : ℕ, ∀ v,
                    PCMessage.phase1b rm bal (some b') v ac ∈ s.msgs → b' ≤ maxbal)
               -- val matches the vote at maxbal
               ∧ ∃ ac ∈ MS, ∃ v : AccVal,
                    PCMessage.phase1b rm bal (some maxbal) v ac ∈ s.msgs
                    ∧ val = (match v with
                             | AccVal.prepared => RMVal.prepared
                             | AccVal.aborted  => RMVal.aborted
                             | AccVal.none     => RMVal.aborted))
          ∧ s'.msgs = s.msgs ∪ {PCMessage.phase2a rm bal val})
  ∧ s'.rmState = s.rmState
  ∧ s'.aState = s.aState

-- Decide: a leader announces Commit or Abort based on phase 2b messages.
-- Commit: every RM instance has a ballot with a majority of "prepared" votes.
-- Abort: some RM instance has a ballot with a majority of "aborted" votes.
-- (TLA+ lines 207-225)
def pcDecide (Majority : Set (Set Acceptor))
    (s s' : PCState RM Acceptor) : Prop :=
  let decided (rm : RM) (v : RMVal) :=
    ∃ b : ℕ, ∃ MS ∈ Majority,
      ∀ ac ∈ MS, PCMessage.phase2b rm b v ac ∈ s.msgs
  (  (∀ rm : RM, decided rm RMVal.prepared)
     ∧ s'.msgs = s.msgs ∪ {PCMessage.commit}
   ∨ (∃ rm : RM, decided rm RMVal.aborted)
     ∧ s'.msgs = s.msgs ∪ {PCMessage.abort})
  ∧ s'.rmState = s.rmState
  ∧ s'.aState = s.aState

-------------------------------------------------------------------------------
-- Acceptor Actions  (TLA+ lines 230-252)
-------------------------------------------------------------------------------

-- Phase1b: acceptor `acc` responds to a phase 1a message.
-- It updates its mbal and sends back its current bal/val.
-- (TLA+ lines 230-241)
def pcPhase1b (acc : Acceptor) (s s' : PCState RM Acceptor) : Prop :=
  ∃ ins : RM, ∃ bal : ℕ,
    PCMessage.phase1a ins bal ∈ s.msgs
    ∧ (s.aState ins acc).mbal < bal
    ∧ s'.aState = Function.update s.aState ins
        (Function.update (s.aState ins) acc
          { (s.aState ins acc) with mbal := bal })
    ∧ s'.msgs = s.msgs ∪
        {PCMessage.phase1b ins bal
          (s.aState ins acc).bal (s.aState ins acc).val acc}
    ∧ s'.rmState = s.rmState

-- Phase2b: acceptor `acc` accepts a phase 2a message.
-- It updates mbal, bal, and val, and sends a phase 2b message.
-- (TLA+ lines 243-252)
def pcPhase2b (acc : Acceptor) (s s' : PCState RM Acceptor) : Prop :=
  ∃ ins : RM, ∃ bal : ℕ, ∃ val : RMVal,
    PCMessage.phase2a ins bal val ∈ s.msgs
    ∧ (s.aState ins acc).mbal ≤ bal
    ∧ s'.aState = Function.update s.aState ins
        (Function.update (s.aState ins) acc
          { mbal := bal, bal := some bal,
            val := match val with
                   | RMVal.prepared => AccVal.prepared
                   | RMVal.aborted  => AccVal.aborted })
    ∧ s'.msgs = s.msgs ∪ {PCMessage.phase2b ins bal val acc}
    ∧ s'.rmState = s.rmState

-------------------------------------------------------------------------------
-- Next-state relation  (TLA+ lines 254-261)
-------------------------------------------------------------------------------

def pcNext (Majority : Set (Set Acceptor))
    (s s' : PCState RM Acceptor) : Prop :=
  (∃ rm : RM, pcRMPrepare rm s s' ∨ pcRMChooseToAbort rm s s'
              ∨ pcRMRcvCommitMsg rm s s' ∨ pcRMRcvAbortMsg rm s s')
  ∨ (∃ bal : ℕ, ∃ rm : RM, pcPhase1a bal rm s s' ∨ pcPhase2a Majority bal rm s s')
  ∨ pcDecide Majority s s'
  ∨ (∃ acc : Acceptor, pcPhase1b acc s s' ∨ pcPhase2b acc s s')

-------------------------------------------------------------------------------
-- Reachability
-------------------------------------------------------------------------------

inductive PCReachable (Majority : Set (Set Acceptor)) :
    PCState RM Acceptor → Prop where
  | init : PCReachable Majority pcInit
  | step {s s'} : PCReachable Majority s → pcNext Majority s s'
      → PCReachable Majority s'

-------------------------------------------------------------------------------
-- The consistency property: no RM has committed while another has aborted
-------------------------------------------------------------------------------

def pcConsistent (s : PCState RM Acceptor) : Prop :=
  tcConsistent s.rmState

-- Refinement mapping (TLA+ line 278: TC == INSTANCE TCommit)
def pcRefinement (s : PCState RM Acceptor) : RM → RMState := s.rmState

-- THEOREM PCSpec => []PCTypeOK  (TLA+ line 268)
-- Type correctness is guaranteed by Lean's type system.

-------------------------------------------------------------------------------
-- Strengthened inductive invariant
-------------------------------------------------------------------------------

-- A value v is decided for instance rm when a majority of acceptors have
-- sent matching phase2b messages in some ballot.
def decided (Majority : Set (Set Acceptor)) (s : PCState RM Acceptor)
    (rm : RM) (v : RMVal) : Prop :=
  ∃ b : ℕ, ∃ MS ∈ Majority,
    ∀ ac ∈ MS, PCMessage.phase2b rm b v ac ∈ s.msgs

-- phase2b messages only exist for values that were proposed in phase2a
def pcPhase2bSafe (s : PCState RM Acceptor) : Prop :=
  ∀ (rm : RM) (b : ℕ) (v : RMVal) (ac : Acceptor),
    PCMessage.phase2b rm b v ac ∈ s.msgs →
    PCMessage.phase2a rm b v ∈ s.msgs

-- For each RM instance and ballot, at most one value is proposed in phase2a
def pcPhase2aUnique (s : PCState RM Acceptor) : Prop :=
  ∀ (rm : RM) (b : ℕ) (v₁ v₂ : RMVal),
    PCMessage.phase2a rm b v₁ ∈ s.msgs →
    PCMessage.phase2a rm b v₂ ∈ s.msgs →
    v₁ = v₂

-- For each RM instance, at most one value can be decided.
def pcAtMostOneDecision (Majority : Set (Set Acceptor))
    (s : PCState RM Acceptor) : Prop :=
  ∀ (rm : RM) (v₁ v₂ : RMVal),
    decided Majority s rm v₁ → decided Majority s rm v₂ → v₁ = v₂

-- An RM that is still working has not yet sent any phase2a at ballot 0.
def pcWorkingNoPhase2a (s : PCState RM Acceptor) : Prop :=
  ∀ (rm : RM) (v : RMVal),
    s.rmState rm = RMState.working → PCMessage.phase2a rm 0 v ∉ s.msgs

-- Lamport-style safe-at predicate: value v is safe at ballot b for RM rm.
-- There exists a majority Q where:
-- (1) All Q members have promised ballot b (sent phase1b at some ballot ≥ b).
-- (2) Either: no Q member voted at any ballot below b, OR there is a highest
--     ballot c < b where all Q-member votes at c are v and no Q member voted
--     between c+1 and b-1.
-- The promise requirement ensures phase2b preservation (new voter at c has
-- mbal ≤ c < b, so can't be in Q). The "highest ballot" formulation allows
-- the leader to establish safe-at using only phase1b information.
def pcSafeAt (Majority : Set (Set Acceptor)) (s : PCState RM Acceptor)
    (rm : RM) (b : ℕ) (v : RMVal) : Prop :=
  ∃ Q ∈ Majority,
    (∀ ac ∈ Q, ∃ mb : ℕ, mb ≥ b ∧ ∃ bal : Option ℕ, ∃ val : AccVal,
      PCMessage.phase1b rm mb bal val ac ∈ s.msgs)
    ∧ (  (∀ ac ∈ Q, ∀ c : ℕ, c < b →
            ∀ v' : RMVal, PCMessage.phase2b rm c v' ac ∉ s.msgs)
       ∨ ∃ c : ℕ, c < b
         ∧ (∀ ac ∈ Q, ∀ v' : RMVal,
              PCMessage.phase2b rm c v' ac ∈ s.msgs → v' = v)
         ∧ (∃ ac ∈ Q, PCMessage.phase2b rm c v ac ∈ s.msgs)
         ∧ (∀ ac ∈ Q, ∀ d : ℕ, c < d → d < b →
              ∀ v' : RMVal, PCMessage.phase2b rm d v' ac ∉ s.msgs))

-- Every phase2a at ballot > 0 is safe-at.
def pcPhase2aSafe (Majority : Set (Set Acceptor))
    (s : PCState RM Acceptor) : Prop :=
  ∀ (rm : RM) (b : ℕ) (v : RMVal),
    PCMessage.phase2a rm b v ∈ s.msgs → b > 0 →
    pcSafeAt Majority s rm b v

-- A prepared phase2a at ballot > 0 is backed by a prepared phase2b at a
-- strictly lower ballot. This is the key link in the cross-ballot chain
-- that ultimately traces a prepared value down to ballot 0.
def pcPreparedHasLowerEvidence (s : PCState RM Acceptor) : Prop :=
  ∀ (rm : RM) (b : ℕ),
    PCMessage.phase2a rm b RMVal.prepared ∈ s.msgs → b > 0 →
    ∃ c : ℕ, c < b ∧ ∃ ac : Acceptor, PCMessage.phase2b rm c RMVal.prepared ac ∈ s.msgs

-- Phase1b with Some ballot faithfully reflects the acceptor's last vote.
def pcPhase1bSomeFaithful (s : PCState RM Acceptor) : Prop :=
  ∀ (rm : RM) (mbal : ℕ) (c : ℕ) (v : AccVal) (acc : Acceptor),
    PCMessage.phase1b rm mbal (some c) v acc ∈ s.msgs →
      c < mbal
      ∧ v ≠ AccVal.none
      ∧ PCMessage.phase2b rm c (accValToRMVal v) acc ∈ s.msgs
      ∧ (∀ c', c < c' → c' < mbal →
          ∀ v' : RMVal, PCMessage.phase2b rm c' v' acc ∉ s.msgs)

-- Phase1b with None means no prior votes below mbal.
def pcPhase1bNoneFaithful (s : PCState RM Acceptor) : Prop :=
  ∀ (rm : RM) (mbal : ℕ) (acc : Acceptor),
    PCMessage.phase1b rm mbal none AccVal.none acc ∈ s.msgs →
      ∀ c, c < mbal → ∀ v' : RMVal, PCMessage.phase2b rm c v' acc ∉ s.msgs

-- Links acceptor state to messages.
def pcAccStateValid (s : PCState RM Acceptor) : Prop :=
  ∀ (rm : RM) (acc : Acceptor),
    -- bal ≤ mbal
    (∀ c, (s.aState rm acc).bal = some c → c ≤ (s.aState rm acc).mbal)
    -- bal = some c ⇒ phase2b exists and val ≠ none
    ∧ (∀ c, (s.aState rm acc).bal = some c →
        (s.aState rm acc).val ≠ AccVal.none
        ∧ PCMessage.phase2b rm c (accValToRMVal (s.aState rm acc).val) acc ∈ s.msgs)
    -- no vote strictly between bal and mbal
    ∧ (∀ c : ℕ,
        (match (s.aState rm acc).bal with | none => False | some b => b < c) →
        c ≤ (s.aState rm acc).mbal →
        ∀ v : RMVal, PCMessage.phase2b rm c v acc ∉ s.msgs)
    -- bal = none ⇒ no votes at or below mbal
    ∧ ((s.aState rm acc).bal = none →
        ∀ c, c ≤ (s.aState rm acc).mbal →
        ∀ v : RMVal, PCMessage.phase2b rm c v acc ∉ s.msgs)
    -- bal = none ⇒ val = none
    ∧ ((s.aState rm acc).bal = none → (s.aState rm acc).val = AccVal.none)
    -- phase1b sent ⇒ current mbal ≥ mbal in message
    ∧ (∀ mb : ℕ, ∀ b : Option ℕ, ∀ v : AccVal,
        PCMessage.phase1b rm mb b v acc ∈ s.msgs →
        (s.aState rm acc).mbal ≥ mb)
    -- phase2b sent ⇒ ballot ≤ current mbal
    ∧ (∀ c : ℕ, ∀ v : RMVal,
        PCMessage.phase2b rm c v acc ∈ s.msgs →
        c ≤ (s.aState rm acc).mbal)

-- Phase1b messages report AccVal.none iff bal = none.
def pcPhase1bValNone (s : PCState RM Acceptor) : Prop :=
  ∀ (rm : RM) (mbal : ℕ) (b : Option ℕ) (v : AccVal) (acc : Acceptor),
    PCMessage.phase1b rm mbal b v acc ∈ s.msgs →
      (b = none ↔ v = AccVal.none)

-- Commit message implies all RMs have decided prepared (via majority vote).
def pcCommitImpliesAllDecidedPrepared (Majority : Set (Set Acceptor))
    (s : PCState RM Acceptor) : Prop :=
  PCMessage.commit ∈ s.msgs →
    ∀ rm : RM, decided Majority s rm RMVal.prepared

-- Abort message implies some RM has decided aborted (via majority vote).
def pcAbortImpliesDecidedAborted (Majority : Set (Set Acceptor))
    (s : PCState RM Acceptor) : Prop :=
  PCMessage.abort ∈ s.msgs →
    ∃ rm : RM, decided Majority s rm RMVal.aborted

-- The strengthened invariant
def pcInvariant (Majority : Set (Set Acceptor))
    (s : PCState RM Acceptor) : Prop :=
  pcConsistent s                                                              -- [1]
  ∧ (PCMessage.commit ∈ s.msgs → ∀ rm : RM, s.rmState rm ≠ RMState.aborted)  -- [2]
  ∧ (PCMessage.abort ∈ s.msgs → ∀ rm : RM, s.rmState rm ≠ RMState.committed) -- [3]
  ∧ (∀ rm : RM, s.rmState rm = RMState.committed → PCMessage.commit ∈ s.msgs) -- [4]
  ∧ (¬(PCMessage.commit ∈ s.msgs ∧ PCMessage.abort ∈ s.msgs))                 -- [5]
  ∧ pcPhase2bSafe s                                                            -- [6]
  ∧ pcPhase2aUnique s                                                          -- [7]
  ∧ pcWorkingNoPhase2a s                                                       -- [8]
  ∧ (∀ rm : RM, s.rmState rm = RMState.aborted →                              -- [9]
      PCMessage.phase2a rm 0 RMVal.aborted ∈ s.msgs ∨ PCMessage.abort ∈ s.msgs)
  ∧ (PCMessage.abort ∈ s.msgs →                                               -- [10]
      ∃ rm : RM, ∃ b : ℕ, PCMessage.phase2a rm b RMVal.aborted ∈ s.msgs)
  ∧ (PCMessage.commit ∈ s.msgs → ∀ rm : RM, s.rmState rm ≠ RMState.working)  -- [11]
  ∧ pcPhase2aSafe Majority s                                                   -- [12]
  ∧ pcPhase1bSomeFaithful s                                                    -- [13]
  ∧ pcPhase1bNoneFaithful s                                                    -- [14]
  ∧ pcAccStateValid s                                                          -- [15]
  ∧ pcPhase1bValNone s                                                         -- [16]
  ∧ pcCommitImpliesAllDecidedPrepared Majority s                               -- [17]
  ∧ pcAbortImpliesDecidedAborted Majority s                                    -- [18]
  ∧ pcPreparedHasLowerEvidence s                                               -- [19]

-------------------------------------------------------------------------------
-- Base case
-------------------------------------------------------------------------------

lemma pcInvariant_init (Majority : Set (Set Acceptor)) :
    pcInvariant Majority (pcInit : PCState RM Acceptor) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold pcConsistent tcConsistent pcInit; simp
  · intro h; simp [pcInit] at h
  · intro h; simp [pcInit] at h
  · intro rm h; simp [pcInit] at h
  · intro ⟨h, _⟩; simp [pcInit] at h
  · intro rm b v ac h; simp [pcInit] at h
  · intro rm b v₁ v₂ h₁; simp [pcInit] at h₁
  · intro rm v _; simp [pcInit]
  · intro rm h; simp [pcInit] at h
  · intro h; simp [pcInit] at h
  · intro h; simp [pcInit] at h
  · -- pcPhase2aSafe: no phase2a messages in init
    intro rm b v h; simp [pcInit] at h
  · -- pcPhase1bSomeFaithful: no phase1b messages in init
    intro rm mbal c v acc h; simp [pcInit] at h
  · -- pcPhase1bNoneFaithful: no phase1b messages in init
    intro rm mbal acc h; simp [pcInit] at h
  · -- pcAccStateValid: initial state has bal=none, val=none, mbal=0
    intro rm acc
    refine ⟨fun c h => ?_, fun c h => ?_, fun c h => ?_,
      fun h => ?_, fun h => ?_, fun mb b v h1b => ?_, fun c v hv => ?_⟩
    · simp [pcInit] at h
    · simp [pcInit] at h
    · simp [pcInit] at h
    · intro c _ v hv; simp [pcInit] at hv
    · simp [pcInit]
    · simp [pcInit] at h1b
    · simp [pcInit] at hv
  · -- pcPhase1bValNone: no phase1b messages in init
    intro rm mbal b v acc h; simp [pcInit] at h
  · -- pcCommitImpliesAllDecidedPrepared: no commit in init
    intro h; simp [pcInit] at h
  · -- pcAbortImpliesDecidedAborted: no abort in init
    intro h; simp [pcInit] at h
  · -- pcPreparedHasLowerEvidence: no phase2a in init
    intro rm b h; simp [pcInit] at h

-------------------------------------------------------------------------------
-- Action preservation lemmas
--
-- Common pattern for actions that add a single non-commit/abort message M:
--   • pcConsistent: rmState unchanged → same
--   • commit/abort coherence: new msg isn't commit/abort → old hyps apply
--   • ¬(commit ∧ abort): no new commit/abort → old hyp applies
--   • pcPhase2bSafe/Unique/WorkingNoPhase2a: case split old msg vs new msg
-------------------------------------------------------------------------------

-- Helper: the ¬(commit ∧ abort) clause when msgs grows by a non-commit/abort msg
private theorem ne_comm_abort_of_union_irrel
    {s : PCState RM Acceptor} {M : PCMessage RM Acceptor}
    (h_ne : ¬(PCMessage.commit ∈ s.msgs ∧ PCMessage.abort ∈ s.msgs))
    (hc : ¬ M = PCMessage.commit) (ha : ¬ M = PCMessage.abort)
    {s' : PCState RM Acceptor} (h_msgs : s'.msgs = s.msgs ∪ {M}) :
    ¬(PCMessage.commit ∈ s'.msgs ∧ PCMessage.abort ∈ s'.msgs) := by
  intro ⟨hc', ha'⟩; rw [h_msgs] at hc' ha'
  rcases hc' with hc' | hc' <;> rcases ha' with ha' | ha'
  · exact h_ne ⟨hc', ha'⟩
  · exact ha (Set.mem_singleton_iff.mp ha' ▸ rfl)
  · exact hc (Set.mem_singleton_iff.mp hc' ▸ rfl)
  · exact ha (Set.mem_singleton_iff.mp ha' ▸ rfl)

-- Phase1a only adds a phase1a message — all invariant clauses trivially hold.
lemma pcInvariant_phase1a (Majority : Set (Set Acceptor))
    (bal : ℕ) (rm : RM) (s s' : PCState RM Acceptor) :
    pcInvariant Majority s → pcPhase1a bal rm s s' → pcInvariant Majority s' := by
  intro ⟨h_con, h_ca, h_ac, h_cm, h_ne, h_2bs, h_2au, h_wn,
    h_abi, h_ami, h_cnw, h_p2as, h_1bs, h_1bn, h_asv, h_1bvn,
    h_cid, h_aid, h_ple⟩
    ⟨_, h_msgs, h_rm, h_as⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [pcConsistent, h_rm]
  · intro h r; rw [h_rm]; rw [h_msgs] at h; rcases h with h | h
    · exact h_ca h r
    · exact absurd (Set.mem_singleton_iff.mp h) (by intro h; cases h)
  · intro h r; rw [h_rm]; rw [h_msgs] at h; rcases h with h | h
    · exact h_ac h r
    · exact absurd (Set.mem_singleton_iff.mp h) (by intro h; cases h)
  · intro r h; rw [h_rm] at h; rw [h_msgs]; exact Or.inl (h_cm r h)
  · exact ne_comm_abort_of_union_irrel h_ne (by intro h; cases h)
      (by intro h; cases h) h_msgs
  · intro r b v ac h; rw [h_msgs] at h; rcases h with h | h
    · rw [h_msgs]; exact Or.inl (h_2bs r b v ac h)
    · exact absurd (Set.mem_singleton_iff.mp h) (by intro h; cases h)
  · intro r b v₁ v₂ h₁ h₂; rw [h_msgs] at h₁ h₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact h_2au r b v₁ v₂ h₁ h₂
    · exact absurd (Set.mem_singleton_iff.mp h₂) (by intro h; cases h)
    · exact absurd (Set.mem_singleton_iff.mp h₁) (by intro h; cases h)
    · exact absurd (Set.mem_singleton_iff.mp h₁) (by intro h; cases h)
  · intro r v hw h2a; rw [h_rm] at hw; rw [h_msgs] at h2a
    rcases h2a with h | h
    · exact h_wn r v hw h
    · exact absurd (Set.mem_singleton_iff.mp h) (by intro h; cases h)
  · intro r ha; rw [h_rm] at ha; rcases h_abi r ha with h | h
    · exact Or.inl (h_msgs ▸ Set.mem_union_left _ h)
    · exact Or.inr (h_msgs ▸ Set.mem_union_left _ h)
  · intro ha; rw [h_msgs] at ha; rcases ha with ha | ha
    · obtain ⟨r, b, hp⟩ := h_ami ha; exact ⟨r, b, h_msgs ▸ Set.mem_union_left _ hp⟩
    · exact absurd (Set.mem_singleton_iff.mp ha) (by intro h; cases h)
  · intro hc r; rw [h_rm]; rw [h_msgs] at hc; rcases hc with hc | hc
    · exact h_cnw hc r
    · exact absurd (Set.mem_singleton_iff.mp hc) (by intro h; cases h)
  · -- pcPhase2aSafe: no new phase2b msgs, no new phase2a msgs (only phase1a)
    intro r b v h2a hb; rw [h_msgs] at h2a; rcases h2a with h2a | h2a
    · obtain ⟨Q, hQ, hQpromise, hQvotes⟩ := h_p2as r b v h2a hb
      refine ⟨Q, hQ, fun ac hac => ?_, ?_⟩
      · obtain ⟨mb, hmb, bal, val, h1b⟩ := hQpromise ac hac
        exact ⟨mb, hmb, bal, val, h_msgs ▸ Set.mem_union_left _ h1b⟩
      · rcases hQvotes with hno | ⟨c, hcb, hcv, hcwit, hcgap⟩
        · left; intro ac hac c' hcb v' hv'
          rw [h_msgs] at hv'; rcases hv' with hv' | hv'
          · exact hno ac hac c' hcb v' hv'
          · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h)
        · right; exact ⟨c, hcb, fun ac hac v' hv' => by
            rw [h_msgs] at hv'; rcases hv' with hv' | hv'
            · exact hcv ac hac v' hv'
            · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h),
            hcwit.imp fun ac ⟨hac, h⟩ => ⟨hac, h_msgs ▸ Set.mem_union_left _ h⟩,
            fun ac hac d hcd hdb v' hv' => by
            rw [h_msgs] at hv'; rcases hv' with hv' | hv'
            · exact hcgap ac hac d hcd hdb v' hv'
            · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h)⟩
    · exact absurd (Set.mem_singleton_iff.mp h2a) (by intro h; cases h)
  · -- pcPhase1bSomeFaithful: new msg is phase1a, not phase1b
    intro r mb c v ac' h; rw [h_msgs] at h; rcases h with h | h
    · obtain ⟨h1, h2, h3, h4⟩ := h_1bs r mb c v ac' h
      exact ⟨h1, h2, h_msgs ▸ Set.mem_union_left _ h3,
        fun c' hc1 hc2 v' hv' => h4 c' hc1 hc2 v' (by
          rw [h_msgs] at hv'; rcases hv' with hv' | hv'
          · exact hv'
          · exact absurd (Set.mem_singleton_iff.mp hv')
              (by intro h; cases h))⟩
    · exact absurd (Set.mem_singleton_iff.mp h) (by intro h; cases h)
  · -- pcPhase1bNoneFaithful: new msg is phase1a, not phase1b
    intro r mb ac' h; rw [h_msgs] at h; rcases h with h | h
    · intro c hc v' hv'; rw [h_msgs] at hv'; rcases hv' with hv' | hv'
      · exact h_1bn r mb ac' h c hc v' hv'
      · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h)
    · exact absurd (Set.mem_singleton_iff.mp h) (by intro h; cases h)
  · -- pcAccStateValid: aState unchanged, no new phase2b msgs
    intro r ac'; rw [h_as]; obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h_asv r ac'
    refine ⟨h1, fun c hc => ?_, fun c hc1 hc2 v hv => ?_,
      fun hn c hc v hv => ?_, h5, fun mb b v h1b => ?_, fun c v hv => ?_⟩
    · obtain ⟨hne, hm⟩ := h2 c hc; exact ⟨hne, h_msgs ▸ Set.mem_union_left _ hm⟩
    · rw [h_msgs] at hv; rcases hv with hv | hv
      · exact h3 c hc1 hc2 v hv
      · exact absurd (Set.mem_singleton_iff.mp hv) (by intro h; cases h)
    · rw [h_msgs] at hv; rcases hv with hv | hv
      · exact h4 hn c hc v hv
      · exact absurd (Set.mem_singleton_iff.mp hv) (by intro h; cases h)
    · rw [h_msgs] at h1b; rcases h1b with h1b | h1b
      · exact h6 mb b v h1b
      · exact absurd (Set.mem_singleton_iff.mp h1b) (by intro h; cases h)
    · rw [h_msgs] at hv; rcases hv with hv | hv
      · exact h7 c v hv
      · exact absurd (Set.mem_singleton_iff.mp hv) (by intro h; cases h)
  · -- pcPhase1bValNone: new msg is phase1a, not phase1b
    intro r mb b' v ac' h; rw [h_msgs] at h; rcases h with h | h
    · exact h_1bvn r mb b' v ac' h
    · exact absurd (Set.mem_singleton_iff.mp h) (by intro h; cases h)
  · -- pcCommitImpliesAllDecidedPrepared: no new commit msg
    intro hc r; rw [h_msgs] at hc; rcases hc with hc | hc
    · obtain ⟨b, MS, hMS, hv⟩ := h_cid hc r
      exact ⟨b, MS, hMS, fun ac hac => h_msgs ▸ Set.mem_union_left _ (hv ac hac)⟩
    · exact absurd (Set.mem_singleton_iff.mp hc) (by intro h; cases h)
  · -- pcAbortImpliesDecidedAborted: no new abort msg
    intro ha; rw [h_msgs] at ha; rcases ha with ha | ha
    · obtain ⟨r, b, MS, hMS, hv⟩ := h_aid ha
      exact ⟨r, b, MS, hMS, fun ac hac => h_msgs ▸ Set.mem_union_left _ (hv ac hac)⟩
    · exact absurd (Set.mem_singleton_iff.mp ha) (by intro h; cases h)
  · -- pcPreparedHasLowerEvidence: new msg is phase1a, not phase2a
    intro r b h2a hb; rw [h_msgs] at h2a; rcases h2a with h2a | h2a
    · obtain ⟨c, hcb, ac, h2b⟩ := h_ple r b h2a hb
      exact ⟨c, hcb, ac, h_msgs ▸ Set.mem_union_left _ h2b⟩
    · exact absurd (Set.mem_singleton_iff.mp h2a) (by intro h; cases h)

-- Phase1b only adds a phase1b message — preserves all clauses.
lemma pcInvariant_phase1b (Majority : Set (Set Acceptor))
    (acc : Acceptor) (s s' : PCState RM Acceptor) :
    pcInvariant Majority s → pcPhase1b acc s s' → pcInvariant Majority s' := by
  intro ⟨h_con, h_ca, h_ac, h_cm, h_ne, h_2bs, h_2au, h_wn, h_abi, h_ami, h_cnw,
    h_p2as, h_1bs, h_1bn, h_asv, h_1bvn, h_cid, h_aid, h_ple⟩
    ⟨ins, bal, h_1a, h_mbal_lt, h_as, h_msgs, h_rm⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [pcConsistent, h_rm]
  · intro h r; rw [h_rm]; rw [h_msgs] at h; rcases h with h | h
    · exact h_ca h r
    · exact absurd (Set.mem_singleton_iff.mp h) (by intro h; cases h)
  · intro h r; rw [h_rm]; rw [h_msgs] at h; rcases h with h | h
    · exact h_ac h r
    · exact absurd (Set.mem_singleton_iff.mp h) (by intro h; cases h)
  · intro r h; rw [h_rm] at h; rw [h_msgs]; exact Or.inl (h_cm r h)
  · exact ne_comm_abort_of_union_irrel h_ne (by intro h; cases h)
      (by intro h; cases h) h_msgs
  · intro r b v ac' h; rw [h_msgs] at h; rcases h with h | h
    · rw [h_msgs]; exact Or.inl (h_2bs r b v ac' h)
    · exact absurd (Set.mem_singleton_iff.mp h) (by intro h; cases h)
  · intro r b v₁ v₂ h₁ h₂; rw [h_msgs] at h₁ h₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact h_2au r b v₁ v₂ h₁ h₂
    · exact absurd (Set.mem_singleton_iff.mp h₂) (by intro h; cases h)
    · exact absurd (Set.mem_singleton_iff.mp h₁) (by intro h; cases h)
    · exact absurd (Set.mem_singleton_iff.mp h₁) (by intro h; cases h)
  · intro r v hw h2a; rw [h_rm] at hw; rw [h_msgs] at h2a
    rcases h2a with h | h
    · exact h_wn r v hw h
    · exact absurd (Set.mem_singleton_iff.mp h) (by intro h; cases h)
  · intro r ha; rw [h_rm] at ha; rcases h_abi r ha with h | h
    · exact Or.inl (h_msgs ▸ Set.mem_union_left _ h)
    · exact Or.inr (h_msgs ▸ Set.mem_union_left _ h)
  · intro ha; rw [h_msgs] at ha; rcases ha with ha | ha
    · obtain ⟨r, b, hp⟩ := h_ami ha; exact ⟨r, b, h_msgs ▸ Set.mem_union_left _ hp⟩
    · exact absurd (Set.mem_singleton_iff.mp ha) (by intro h; cases h)
  · intro hc r; rw [h_rm]; rw [h_msgs] at hc; rcases hc with hc | hc
    · exact h_cnw hc r
    · exact absurd (Set.mem_singleton_iff.mp hc) (by intro h; cases h)
  · -- pcPhase2aSafe: no new phase2b, no new phase2a (only phase1b added)
    intro r b v h2a hb; rw [h_msgs] at h2a; rcases h2a with h2a | h2a
    · obtain ⟨Q, hQ, hQpromise, hQvotes⟩ := h_p2as r b v h2a hb
      refine ⟨Q, hQ, fun ac' hac => ?_, ?_⟩
      · obtain ⟨mb, hmb, bal, val, h1b⟩ := hQpromise ac' hac
        exact ⟨mb, hmb, bal, val, h_msgs ▸ Set.mem_union_left _ h1b⟩
      · rcases hQvotes with hno | ⟨c, hcb, hcv, hcwit, hcgap⟩
        · left; intro ac' hac c' hcb v' hv'
          rw [h_msgs] at hv'; rcases hv' with hv' | hv'
          · exact hno ac' hac c' hcb v' hv'
          · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h)
        · right; exact ⟨c, hcb, fun ac' hac v' hv' => by
            rw [h_msgs] at hv'; rcases hv' with hv' | hv'
            · exact hcv ac' hac v' hv'
            · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h),
            hcwit.imp fun ac ⟨hac, h⟩ => ⟨hac, h_msgs ▸ Set.mem_union_left _ h⟩,
            fun ac' hac d hcd hdb v' hv' => by
            rw [h_msgs] at hv'; rcases hv' with hv' | hv'
            · exact hcgap ac' hac d hcd hdb v' hv'
            · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h)⟩
    · exact absurd (Set.mem_singleton_iff.mp h2a) (by intro h; cases h)
  · -- pcPhase1bSomeFaithful: new phase1b with bal=some c faithfully reports votes
    intro r mb c v ac' h1b; rw [h_msgs] at h1b; rcases h1b with h1b | h1b
    · -- Old phase1b: use h_1bs, lift phase2b to s'.msgs
      obtain ⟨hlt, hne, h2b, hgap⟩ := h_1bs r mb c v ac' h1b
      refine ⟨hlt, hne, h_msgs ▸ Set.mem_union_left _ h2b, fun c' hcc hcm v' hv' => ?_⟩
      rw [h_msgs] at hv'; rcases hv' with hv' | hv'
      · exact hgap c' hcc hcm v' hv'
      · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h)
    · -- New phase1b: phase1b ins bal (s.aState ins acc).bal (s.aState ins acc).val acc
      -- with (s.aState ins acc).bal = some c
      have heq := PCMessage.phase1b.inj (Set.mem_singleton_iff.mp h1b)
      obtain ⟨h_r, h_mb, h_b, h_v, h_ac⟩ := heq
      -- h_b : some c = (s.aState ins acc).bal
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h_asv ins acc
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- c < bal: from h1 (c ≤ mbal) and h_mbal_lt (mbal < bal)
        have hle := h1 c h_b.symm; omega
      · -- val ≠ AccVal.none: from h2
        rw [h_v]; exact (h2 c h_b.symm).1
      · -- phase2b(ins, c, accValToRMVal val, acc) ∈ s'.msgs
        rw [h_v, h_r, h_ac]; rw [h_msgs]
        exact Set.mem_union_left _ (h2 c h_b.symm).2
      · -- no phase2b between c and bal
        intro c' hcc hcm v' hv'
        rw [h_msgs] at hv'; rcases hv' with hv' | hv'
        · -- Old phase2b: need to show c' not between c and bal
          rw [h_r] at hv'; rw [h_ac] at hv'
          rw [h_mb] at hcm
          -- h7 gives c' ≤ mbal, and h3 gives no votes strictly between bal and mbal
          have hle := h7 c' v' hv'
          -- h3: for c < c' ≤ mbal, no phase2b
          exact h3 c' (by rw [← h_b]; exact hcc) hle v' hv'
        · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h)
  · -- pcPhase1bNoneFaithful: new phase1b with bal=none means no prior votes
    intro r mb ac' h1b; rw [h_msgs] at h1b; rcases h1b with h1b | h1b
    · -- Old phase1b: use h_1bn, msgs only grew by phase1b (not phase2b)
      intro c hc v' hv'; rw [h_msgs] at hv'; rcases hv' with hv' | hv'
      · exact h_1bn r mb ac' h1b c hc v' hv'
      · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h)
    · -- New phase1b: phase1b ins bal none AccVal.none acc
      have heq := PCMessage.phase1b.inj (Set.mem_singleton_iff.mp h1b)
      obtain ⟨h_r, h_mb, h_b, _, h_ac⟩ := heq
      -- (s.aState ins acc).bal = none (from h_b)
      -- pcAccStateValid gives: bal = none → ∀ c ≤ mbal, no phase2b
      -- and h7: phase2b c v ∈ s.msgs → c ≤ mbal
      -- So no phase2b at all for this acceptor/rm in s.msgs
      obtain ⟨_, _, _, h4, _, _, h7⟩ := h_asv ins acc
      intro c hc v' hv'; rw [h_msgs] at hv'; rcases hv' with hv' | hv'
      · -- Old phase2b: use h4 (bal=none → c ≤ mbal → no phase2b)
        rw [h_r] at hv'; rw [h_ac] at hv'
        have hle := h7 c v' hv'
        exact h4 h_b.symm c hle v' hv'
      · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h)
  · -- pcAccStateValid: aState changes for (ins, acc), mbal increases to bal
    intro r ac'
    by_cases hr : r = ins
    · subst hr
      by_cases hac : ac' = acc
      · -- (ins, acc): mbal increases from old_mbal to bal, bal/val unchanged
        subst hac
        rw [h_as, Function.update_self, Function.update_self]
        simp only
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h_asv r ac'
        refine ⟨fun c hc => ?_, fun c hc => ?_, fun c hc1 hc2 v hv => ?_,
          fun hn c hc v hv => ?_, h5, fun mb' b v h1b => ?_, fun c v hv => ?_⟩
        · -- bal ≤ mbal: c ≤ old_mbal < bal
          have := h1 c hc; omega
        · -- bal = some c → val ≠ none ∧ phase2b exists
          obtain ⟨hne, hm⟩ := h2 c hc
          exact ⟨hne, h_msgs ▸ Set.mem_union_left _ hm⟩
        · -- no vote between bal and new mbal=bal
          -- hc1 : (match bal with none => False | some b => b < c), hc2 : c ≤ bal
          rw [h_msgs] at hv; rcases hv with hv | hv
          · -- Old phase2b: c ≤ old_mbal by h7, so use h3 if old_bal < c ≤ old_mbal
            have hle := h7 c v hv
            exact h3 c hc1 hle v hv
          · exact absurd (Set.mem_singleton_iff.mp hv) (by intro h; cases h)
        · -- bal = none → no votes ≤ new mbal=bal
          rw [h_msgs] at hv; rcases hv with hv | hv
          · exact h4 hn c (by have := h7 c v hv; omega) v hv
          · exact absurd (Set.mem_singleton_iff.mp hv) (by intro h; cases h)
        · -- phase1b mbal bound: new mbal = bal
          rw [h_msgs] at h1b; rcases h1b with h1b | h1b
          · have := h6 mb' b v h1b; omega
          · -- New phase1b: phase1b ins bal ... acc, mb' = bal
            have heq := PCMessage.phase1b.inj (Set.mem_singleton_iff.mp h1b)
            omega
        · -- phase2b ballot ≤ mbal: new mbal = bal ≥ old_mbal ≥ c
          rw [h_msgs] at hv; rcases hv with hv | hv
          · have := h7 c v hv; omega
          · exact absurd (Set.mem_singleton_iff.mp hv) (by intro h; cases h)
      · -- (ins, ac' ≠ acc): state unchanged
        rw [h_as, Function.update_self]
        simp only [Function.update_apply, if_neg hac]
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h_asv r ac'
        refine ⟨h1, fun c hc => ?_, fun c hc1 hc2 v hv => ?_,
          fun hn c hc v hv => ?_, h5, fun mb' b v h1b => ?_, fun c v hv => ?_⟩
        · obtain ⟨hne, hm⟩ := h2 c hc
          exact ⟨hne, h_msgs ▸ Set.mem_union_left _ hm⟩
        · rw [h_msgs] at hv; rcases hv with hv | hv
          · exact h3 c hc1 hc2 v hv
          · exact absurd (Set.mem_singleton_iff.mp hv) (by intro h; cases h)
        · rw [h_msgs] at hv; rcases hv with hv | hv
          · exact h4 hn c hc v hv
          · exact absurd (Set.mem_singleton_iff.mp hv) (by intro h; cases h)
        · rw [h_msgs] at h1b; rcases h1b with h1b | h1b
          · exact h6 mb' b v h1b
          · -- New phase1b is for acc, not ac'
            obtain ⟨_, _, _, _, rfl⟩ :=
              PCMessage.phase1b.inj (Set.mem_singleton_iff.mp h1b)
            exact absurd rfl hac
        · rw [h_msgs] at hv; rcases hv with hv | hv
          · exact h7 c v hv
          · exact absurd (Set.mem_singleton_iff.mp hv) (by intro h; cases h)
    · -- r ≠ ins: state unchanged entirely
      rw [h_as]; simp only [Function.update_apply, if_neg hr]
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h_asv r ac'
      refine ⟨h1, fun c hc => ?_, fun c hc1 hc2 v hv => ?_,
        fun hn c hc v hv => ?_, h5, fun mb' b v h1b => ?_, fun c v hv => ?_⟩
      · obtain ⟨hne, hm⟩ := h2 c hc
        exact ⟨hne, h_msgs ▸ Set.mem_union_left _ hm⟩
      · rw [h_msgs] at hv; rcases hv with hv | hv
        · exact h3 c hc1 hc2 v hv
        · exact absurd (Set.mem_singleton_iff.mp hv) (by intro h; cases h)
      · rw [h_msgs] at hv; rcases hv with hv | hv
        · exact h4 hn c hc v hv
        · exact absurd (Set.mem_singleton_iff.mp hv) (by intro h; cases h)
      · rw [h_msgs] at h1b; rcases h1b with h1b | h1b
        · exact h6 mb' b v h1b
        · -- New phase1b is for ins, not r
          obtain ⟨rfl, _, _, _, _⟩ :=
            PCMessage.phase1b.inj (Set.mem_singleton_iff.mp h1b)
          exact absurd rfl hr
      · rw [h_msgs] at hv; rcases hv with hv | hv
        · exact h7 c v hv
        · exact absurd (Set.mem_singleton_iff.mp hv) (by intro h; cases h)
  · -- pcPhase1bValNone: new phase1b reports (s.aState ins acc).bal and .val
    intro r mb b' v ac' h1b; rw [h_msgs] at h1b; rcases h1b with h1b | h1b
    · exact h_1bvn r mb b' v ac' h1b
    · -- New message: phase1b ins bal (s.aState ins acc).bal (s.aState ins acc).val acc
      have heq := PCMessage.phase1b.inj (Set.mem_singleton_iff.mp h1b)
      obtain ⟨h_r, h_mb, h_b, h_v, h_ac⟩ := heq
      obtain ⟨_, h2, _, _, h5, _, _⟩ := h_asv ins acc
      constructor
      · -- b' = none → v = AccVal.none
        intro hbn; rw [h_b] at hbn; rw [h_v]; exact h5 hbn
      · -- v = AccVal.none → b' = none
        intro hv; rw [h_v] at hv; rw [h_b]
        by_contra hb
        obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hb
        exact (h2 c hc).1 hv
  · -- pcCommitImpliesAllDecidedPrepared: no new commit msg
    intro hc r; rw [h_msgs] at hc; rcases hc with hc | hc
    · obtain ⟨b, MS, hMS, hv⟩ := h_cid hc r
      exact ⟨b, MS, hMS, fun ac' hac => h_msgs ▸ Set.mem_union_left _ (hv ac' hac)⟩
    · exact absurd (Set.mem_singleton_iff.mp hc) (by intro h; cases h)
  · -- pcAbortImpliesDecidedAborted: no new abort msg
    intro ha; rw [h_msgs] at ha; rcases ha with ha | ha
    · obtain ⟨r, b, MS, hMS, hv⟩ := h_aid ha
      exact ⟨r, b, MS, hMS, fun ac' hac => h_msgs ▸ Set.mem_union_left _ (hv ac' hac)⟩
    · exact absurd (Set.mem_singleton_iff.mp ha) (by intro h; cases h)
  · -- pcPreparedHasLowerEvidence: new msg is phase1b, not phase2a/phase2b
    intro r b h2a hb; rw [h_msgs] at h2a; rcases h2a with h2a | h2a
    · obtain ⟨c, hcb, ac', h2b⟩ := h_ple r b h2a hb
      exact ⟨c, hcb, ac', h_msgs ▸ Set.mem_union_left _ h2b⟩
    · exact absurd (Set.mem_singleton_iff.mp h2a) (by intro h; cases h)

-- Phase2b adds a phase2b message. Key: pcPhase2bSafe must hold for the new msg.
lemma pcInvariant_phase2b (Majority : Set (Set Acceptor))
    (acc : Acceptor) (s s' : PCState RM Acceptor) :
    pcInvariant Majority s → pcPhase2b acc s s' → pcInvariant Majority s' := by
  intro ⟨h_con, h_ca, h_ac, h_cm, h_ne, h_2bs, h_2au, h_wn,
    h_abi, h_ami, h_cnw, h_p2as, h_1bs, h_1bn, h_asv, h_1bvn,
    h_cid, h_aid, h_ple⟩
    ⟨ins, bal, val, h_2a, h_mbal_le, h_as, h_msgs, h_rm⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [pcConsistent, h_rm]
  · intro h r; rw [h_rm]; rw [h_msgs] at h; rcases h with h | h
    · exact h_ca h r
    · exact absurd (Set.mem_singleton_iff.mp h) (by intro h; cases h)
  · intro h r; rw [h_rm]; rw [h_msgs] at h; rcases h with h | h
    · exact h_ac h r
    · exact absurd (Set.mem_singleton_iff.mp h) (by intro h; cases h)
  · intro r h; rw [h_rm] at h; rw [h_msgs]; exact Or.inl (h_cm r h)
  · exact ne_comm_abort_of_union_irrel h_ne (by intro h; cases h)
      (by intro h; cases h) h_msgs
  · -- pcPhase2bSafe: new phase2b(ins,bal,val,acc) has phase2a(ins,bal,val) ∈ msgs
    intro r b v ac' h; rw [h_msgs] at h; rcases h with h | h
    · rw [h_msgs]; exact Or.inl (h_2bs r b v ac' h)
    · rw [Set.mem_singleton_iff] at h
      obtain ⟨rfl, rfl, rfl, _⟩ := PCMessage.phase2b.inj h
      rw [h_msgs]; exact Or.inl h_2a
  · intro r b v₁ v₂ h₁ h₂; rw [h_msgs] at h₁ h₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact h_2au r b v₁ v₂ h₁ h₂
    · exact absurd (Set.mem_singleton_iff.mp h₂) (by intro h; cases h)
    · exact absurd (Set.mem_singleton_iff.mp h₁) (by intro h; cases h)
    · exact absurd (Set.mem_singleton_iff.mp h₁) (by intro h; cases h)
  · intro r v hw h2a; rw [h_rm] at hw; rw [h_msgs] at h2a
    rcases h2a with h | h
    · exact h_wn r v hw h
    · exact absurd (Set.mem_singleton_iff.mp h) (by intro h; cases h)
  · intro r ha; rw [h_rm] at ha; rcases h_abi r ha with h | h
    · exact Or.inl (h_msgs ▸ Set.mem_union_left _ h)
    · exact Or.inr (h_msgs ▸ Set.mem_union_left _ h)
  · intro ha; rw [h_msgs] at ha; rcases ha with ha | ha
    · obtain ⟨r, b, hp⟩ := h_ami ha; exact ⟨r, b, h_msgs ▸ Set.mem_union_left _ hp⟩
    · exact absurd (Set.mem_singleton_iff.mp ha) (by intro h; cases h)
  · intro hc r; rw [h_rm]; rw [h_msgs] at hc; rcases hc with hc | hc
    · exact h_cnw hc r
    · exact absurd (Set.mem_singleton_iff.mp hc) (by intro h; cases h)
  · -- pcPhase2aSafe: new msg is phase2b(ins,bal,val,acc)
    -- New phase2b is for RM ins at ballot bal. For phase2a of RM r at ballot b:
    -- if r ≠ ins, the new msg is for a different RM → singleton check fails.
    -- if r = ins, Q members promised b, acc has mbal ≤ bal < b → acc ∉ Q.
    intro r b v h2a hb
    rw [h_msgs] at h2a; rcases h2a with h2a | h2a
    · obtain ⟨Q, hQ, hQpromise, hQvotes⟩ := h_p2as r b v h2a hb
      refine ⟨Q, hQ, fun ac' hac => ?_, ?_⟩
      · obtain ⟨mb, hmb, bal', val', h1b⟩ := hQpromise ac' hac
        exact ⟨mb, hmb, bal', val', h_msgs ▸ Set.mem_union_left _ h1b⟩
      · rcases hQvotes with hno | ⟨c, hcb, hcv, hcwit, hcgap⟩
        · left; intro ac' hac c' hc'b v' hv'
          rw [h_msgs] at hv'; rcases hv' with hv' | hv'
          · exact hno ac' hac c' hc'b v' hv'
          · have hinj := PCMessage.phase2b.inj (Set.mem_singleton_iff.mp hv')
            obtain ⟨h1, h2, h3, h4⟩ := hinj
            subst h1; subst h4  -- r = ins, ac' = acc
            obtain ⟨mb, hmb, bal', val', h1b⟩ := hQpromise ac' hac
            have := (h_asv r ac').2.2.2.2.2.1 mb bal' val' h1b
            omega
        · right; exact ⟨c, hcb, fun ac' hac v' hv' => by
            rw [h_msgs] at hv'; rcases hv' with hv' | hv'
            · exact hcv ac' hac v' hv'
            · have hinj := PCMessage.phase2b.inj (Set.mem_singleton_iff.mp hv')
              obtain ⟨h1, _, _, h4⟩ := hinj
              subst h1; subst h4
              obtain ⟨mb, hmb, bal', val', h1b⟩ := hQpromise ac' hac
              have := (h_asv r ac').2.2.2.2.2.1 mb bal' val' h1b
              omega,
            hcwit.imp fun ac ⟨hac, h⟩ => ⟨hac, h_msgs ▸ Set.mem_union_left _ h⟩,
            fun ac' hac d hcd hdb v' hv' => by
            rw [h_msgs] at hv'; rcases hv' with hv' | hv'
            · exact hcgap ac' hac d hcd hdb v' hv'
            · have hinj := PCMessage.phase2b.inj (Set.mem_singleton_iff.mp hv')
              obtain ⟨h1, _, _, h4⟩ := hinj
              subst h1; subst h4
              obtain ⟨mb, hmb, bal', val', h1b⟩ := hQpromise ac' hac
              have := (h_asv r ac').2.2.2.2.2.1 mb bal' val' h1b
              omega⟩
    · exact absurd (Set.mem_singleton_iff.mp h2a) (by intro h; cases h)
  · -- pcPhase1bSomeFaithful: new msg is phase2b, not phase1b
    -- phase2b goes into s'.msgs but phase1b membership queries are about old msgs
    intro r mb c v ac' h1b; rw [h_msgs] at h1b; rcases h1b with h1b | h1b
    · obtain ⟨h1, h2, h3, h4⟩ := h_1bs r mb c v ac' h1b
      exact ⟨h1, h2, h_msgs ▸ Set.mem_union_left _ h3,
        fun c' hc1 hc2 v' hv' => by
          rw [h_msgs] at hv'; rcases hv' with hv' | hv'
          · exact h4 c' hc1 hc2 v' hv'
          · have hinj := PCMessage.phase2b.inj (Set.mem_singleton_iff.mp hv')
            obtain ⟨h1, _, _, h4'⟩ := hinj
            subst h1; subst h4'
            have := (h_asv r ac').2.2.2.2.2.1 mb c v h1b
            omega⟩
    · exact absurd (Set.mem_singleton_iff.mp h1b) (by intro h; cases h)
  · -- pcPhase1bNoneFaithful: new msg is phase2b, not phase1b
    intro r mb ac' h1b; rw [h_msgs] at h1b; rcases h1b with h1b | h1b
    · intro c hc v' hv'; rw [h_msgs] at hv'; rcases hv' with hv' | hv'
      · exact h_1bn r mb ac' h1b c hc v' hv'
      · -- new phase2b(ins, bal, val, acc). Need: this doesn't exist below mbal.
        -- h1b says phase1b(r, mb, none, none, ac') ∈ s.msgs
        -- h_1bn: ∀ c < mb, no phase2b(r, c, *, ac') ∈ s.msgs
        -- The new phase2b is for acc, at ballot bal for rm ins.
        -- If r ≠ ins or ac' ≠ acc or bal ≠ c, this is a different
        -- msg → contradiction with singleton
        have hinj := PCMessage.phase2b.inj (Set.mem_singleton_iff.mp hv')
        obtain ⟨h1, h2, h3, h4⟩ := hinj
        subst h1; subst h2; subst h3; subst h4
        have h_mbal_ge :=
          (h_asv r ac').2.2.2.2.2.1 mb none AccVal.none h1b
        omega
    · exact absurd (Set.mem_singleton_iff.mp h1b) (by intro h; cases h)
  · -- pcAccStateValid: aState changes for (ins, acc), msgs grow by phase2b
    intro r ac'
    by_cases hr : r = ins
    · subst hr
      by_cases hac : ac' = acc
      · -- The interesting case: (ins, acc) state changes
        subst hac
        rw [h_as, Function.update_self, Function.update_self]
        simp only
        obtain ⟨h1, h2, h3, h4, h5, h6_acc, h7_acc⟩ := h_asv r ac'
        refine ⟨fun c hc => ?_, fun c hc => ?_, fun c hc1 hc2 v' hv' => ?_,
          fun hn => ?_, fun hn => ?_, fun mb b' v' h1b => ?_, fun c v' hv' => ?_⟩
        · -- bal ≤ mbal: some bal → bal ≤ bal
          simp at hc; omega
        · -- bal = some c → val ≠ none ∧ phase2b exists
          simp at hc; subst hc
          constructor
          · cases val <;> simp
          · -- phase2b(ins, bal, accValToRMVal (match val ...), acc) ∈ s'.msgs
            -- The new phase2b(ins, bal, val, acc) is exactly this
            rw [h_msgs]
            apply Set.mem_union_right
            rw [Set.mem_singleton_iff]
            congr 1
            cases val <;> simp [accValToRMVal]
        · -- no vote between bal and bal: vacuous since bal < c ≤ bal impossible
          simp at hc1; omega
        · -- bal = none: impossible since bal = some bal
          simp at hn
        · -- bal = none: impossible
          simp at hn
        · -- phase1b mbal bound: mbal = bal, need bal ≥ mb
          rw [h_msgs] at h1b; rcases h1b with h1b | h1b
          · -- Old phase1b: h6_acc gives old mbal ≥ mb, and old mbal ≤ bal
            have := h6_acc mb b' v' h1b
            omega
          · exact absurd (Set.mem_singleton_iff.mp h1b) (by intro h; cases h)
        · -- phase2b ballot ≤ mbal: mbal = bal
          rw [h_msgs] at hv'; rcases hv' with hv' | hv'
          · -- old phase2b: h7_acc gives c ≤ old_mbal ≤ bal
            have := h7_acc c v' hv'; omega
          · -- new phase2b(ins, bal, val, acc): c = bal ≤ bal
            obtain ⟨_, rfl, _, _⟩ :=
              PCMessage.phase2b.inj (Set.mem_singleton_iff.mp hv')
            omega
      · -- ac' ≠ acc: state unchanged for this acceptor
        rw [h_as, Function.update_self]
        simp only [Function.update_apply, if_neg hac]
        obtain ⟨h1, h2, h3, h4, h5, h6_ac, h7_ac⟩ := h_asv r ac'
        refine ⟨h1, fun c hc => ?_, fun c hc1 hc2 v' hv' => ?_,
          fun hn c hc v' hv' => ?_, h5, fun mb b' v' h1b => ?_, fun c v' hv' => ?_⟩
        · obtain ⟨hne, hm⟩ := h2 c hc
          exact ⟨hne, h_msgs ▸ Set.mem_union_left _ hm⟩
        · rw [h_msgs] at hv'; rcases hv' with hv' | hv'
          · exact h3 c hc1 hc2 v' hv'
          · obtain ⟨_, _, _, rfl⟩ :=
              PCMessage.phase2b.inj (Set.mem_singleton_iff.mp hv')
            exact absurd rfl hac
        · rw [h_msgs] at hv'; rcases hv' with hv' | hv'
          · exact h4 hn c hc v' hv'
          · obtain ⟨_, _, _, rfl⟩ :=
              PCMessage.phase2b.inj (Set.mem_singleton_iff.mp hv')
            exact absurd rfl hac
        · rw [h_msgs] at h1b; rcases h1b with h1b | h1b
          · exact h6_ac mb b' v' h1b
          · exact absurd (Set.mem_singleton_iff.mp h1b) (by intro h; cases h)
        · -- phase2b ballot ≤ mbal: state unchanged, new phase2b is for acc ≠ ac'
          rw [h_msgs] at hv'; rcases hv' with hv' | hv'
          · exact h7_ac c v' hv'
          · obtain ⟨_, _, _, rfl⟩ :=
              PCMessage.phase2b.inj (Set.mem_singleton_iff.mp hv')
            exact absurd rfl hac
    · -- r ≠ ins: state unchanged entirely
      rw [h_as]; simp only [Function.update_apply, if_neg hr]
      obtain ⟨h1, h2, h3, h4, h5, h6_r, h7_r⟩ := h_asv r ac'
      refine ⟨h1, fun c hc => ?_, fun c hc1 hc2 v' hv' => ?_,
        fun hn c hc v' hv' => ?_, h5, fun mb b' v' h1b => ?_, fun c v' hv' => ?_⟩
      · obtain ⟨hne, hm⟩ := h2 c hc
        exact ⟨hne, h_msgs ▸ Set.mem_union_left _ hm⟩
      · rw [h_msgs] at hv'; rcases hv' with hv' | hv'
        · exact h3 c hc1 hc2 v' hv'
        · obtain ⟨rfl, _, _, _⟩ :=
            PCMessage.phase2b.inj (Set.mem_singleton_iff.mp hv')
          exact absurd rfl hr
      · rw [h_msgs] at hv'; rcases hv' with hv' | hv'
        · exact h4 hn c hc v' hv'
        · obtain ⟨rfl, _, _, _⟩ :=
            PCMessage.phase2b.inj (Set.mem_singleton_iff.mp hv')
          exact absurd rfl hr
      · rw [h_msgs] at h1b; rcases h1b with h1b | h1b
        · exact h6_r mb b' v' h1b
        · exact absurd (Set.mem_singleton_iff.mp h1b) (by intro h; cases h)
      · -- phase2b ballot ≤ mbal: state unchanged, new phase2b is for ins ≠ r
        rw [h_msgs] at hv'; rcases hv' with hv' | hv'
        · exact h7_r c v' hv'
        · obtain ⟨rfl, _, _, _⟩ :=
            PCMessage.phase2b.inj (Set.mem_singleton_iff.mp hv')
          exact absurd rfl hr
  · -- pcPhase1bValNone: new msg is phase2b, not phase1b
    intro r mb b' v ac' h1b; rw [h_msgs] at h1b; rcases h1b with h1b | h1b
    · exact h_1bvn r mb b' v ac' h1b
    · exact absurd (Set.mem_singleton_iff.mp h1b) (by intro h; cases h)
  · -- pcCommitImpliesAllDecidedPrepared: new msg is phase2b, not commit
    intro hc r; rw [h_msgs] at hc; rcases hc with hc | hc
    · obtain ⟨b, MS, hMS, hv⟩ := h_cid hc r
      exact ⟨b, MS, hMS, fun ac' hac => h_msgs ▸ Set.mem_union_left _ (hv ac' hac)⟩
    · exact absurd (Set.mem_singleton_iff.mp hc) (by intro h; cases h)
  · -- pcAbortImpliesDecidedAborted: new msg is phase2b, not abort
    intro ha; rw [h_msgs] at ha; rcases ha with ha | ha
    · obtain ⟨r, b, MS, hMS, hv⟩ := h_aid ha
      exact ⟨r, b, MS, hMS, fun ac' hac => h_msgs ▸ Set.mem_union_left _ (hv ac' hac)⟩
    · exact absurd (Set.mem_singleton_iff.mp ha) (by intro h; cases h)
  · -- pcPreparedHasLowerEvidence: new msg is phase2b, not phase2a
    intro r b h2a hb; rw [h_msgs] at h2a; rcases h2a with h2a | h2a
    · obtain ⟨c, hcb, ac', h2b⟩ := h_ple r b h2a hb
      exact ⟨c, hcb, ac', h_msgs ▸ Set.mem_union_left _ h2b⟩
    · exact absurd (Set.mem_singleton_iff.mp h2a) (by intro h; cases h)

-- Phase2a adds a phase2a message. Key: pcPhase2aUnique must hold.
-- The action guard ensures no phase2a for (rm, bal) already exists.
lemma pcInvariant_phase2a (Majority : Set (Set Acceptor))
    (bal : ℕ) (rm : RM) (s s' : PCState RM Acceptor) :
    pcInvariant Majority s → pcPhase2a Majority bal rm s s' →
    pcInvariant Majority s' := by
  intro ⟨h_con, h_ca, h_ac, h_cm, h_ne, h_2bs, h_2au, h_wn,
    h_abi, h_ami, h_cnw, h_p2as, h_1bs, h_1bn, h_asv, h_1bvn,
    h_cid, h_aid, h_ple⟩ h_act
  have h_bal : bal > 0 := h_act.1
  have h_no2a : ¬ ∃ v : RMVal, PCMessage.phase2a rm bal v ∈ s.msgs := h_act.2.1
  obtain ⟨MS, hMS, h_ms_1b, val, h_val_choice, h_msgs⟩ := h_act.2.2.1
  have h_rm : s'.rmState = s.rmState := h_act.2.2.2.1
  have h_as : s'.aState = s.aState := h_act.2.2.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [pcConsistent, h_rm]
  · intro h r; rw [h_rm]; rw [h_msgs] at h; rcases h with h | h
    · exact h_ca h r
    · exact absurd (Set.mem_singleton_iff.mp h) (by intro h; cases h)
  · intro h r; rw [h_rm]; rw [h_msgs] at h; rcases h with h | h
    · exact h_ac h r
    · exact absurd (Set.mem_singleton_iff.mp h) (by intro h; cases h)
  · intro r h; rw [h_rm] at h; rw [h_msgs]; exact Or.inl (h_cm r h)
  · exact ne_comm_abort_of_union_irrel h_ne (by intro h; cases h)
      (by intro h; cases h) h_msgs
  · intro r b v' ac h; rw [h_msgs] at h; rcases h with h | h
    · rw [h_msgs]; exact Or.inl (h_2bs r b v' ac h)
    · exact absurd (Set.mem_singleton_iff.mp h) (by intro h; cases h)
  · -- pcPhase2aUnique: the new phase2a(rm, bal, val) is the only one at (rm, bal)
    intro r b v₁ v₂ h₁ h₂; rw [h_msgs] at h₁ h₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact h_2au r b v₁ v₂ h₁ h₂
    · obtain ⟨rfl, rfl, rfl⟩ := PCMessage.phase2a.inj (Set.mem_singleton_iff.mp h₂)
      exfalso; exact h_no2a ⟨v₁, h₁⟩
    · obtain ⟨rfl, rfl, rfl⟩ := PCMessage.phase2a.inj (Set.mem_singleton_iff.mp h₁)
      exfalso; exact h_no2a ⟨v₂, h₂⟩
    · obtain ⟨_, _, rfl⟩ := PCMessage.phase2a.inj (Set.mem_singleton_iff.mp h₁)
      obtain ⟨_, _, rfl⟩ := PCMessage.phase2a.inj (Set.mem_singleton_iff.mp h₂)
      rfl
  · -- pcWorkingNoPhase2a: new phase2a has bal > 0, so no conflict with ballot 0
    intro r v hw h2a; rw [h_rm] at hw; rw [h_msgs] at h2a
    rcases h2a with h | h
    · exact h_wn r v hw h
    · obtain ⟨_, hb, _⟩ := PCMessage.phase2a.inj (Set.mem_singleton_iff.mp h)
      omega  -- bal > 0 but hb says bal = 0
  · intro r ha; rw [h_rm] at ha; rcases h_abi r ha with h | h
    · exact Or.inl (h_msgs ▸ Set.mem_union_left _ h)
    · exact Or.inr (h_msgs ▸ Set.mem_union_left _ h)
  · intro ha; rw [h_msgs] at ha; rcases ha with ha | ha
    · obtain ⟨r, b, hp⟩ := h_ami ha; exact ⟨r, b, h_msgs ▸ Set.mem_union_left _ hp⟩
    · exact absurd (Set.mem_singleton_iff.mp ha) (by intro h; cases h)
  · intro hc r; rw [h_rm]; rw [h_msgs] at hc; rcases hc with hc | hc
    · exact h_cnw hc r
    · exact absurd (Set.mem_singleton_iff.mp hc) (by intro h; cases h)
  · -- pcPhase2aSafe: new phase2a(rm, bal, val) at bal > 0 must be safe
    intro r b v h2a hb
    rw [h_msgs] at h2a; rcases h2a with h2a | h2a
    · -- Old phase2a: transfer safe-at from s to s'
      obtain ⟨Q, hQ, hQpromise, hQvotes⟩ := h_p2as r b v h2a hb
      refine ⟨Q, hQ, fun ac' hac => ?_, ?_⟩
      · obtain ⟨mb, hmb, bal', val', h1b⟩ := hQpromise ac' hac
        exact ⟨mb, hmb, bal', val', h_msgs ▸ Set.mem_union_left _ h1b⟩
      · rcases hQvotes with hno | ⟨c, hcb, hcv, hcwit, hcgap⟩
        · left; intro ac' hac c' hcb v' hv'
          rw [h_msgs] at hv'; rcases hv' with hv' | hv'
          · exact hno ac' hac c' hcb v' hv'
          · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h)
        · right; exact ⟨c, hcb, fun ac' hac v' hv' => by
            rw [h_msgs] at hv'; rcases hv' with hv' | hv'
            · exact hcv ac' hac v' hv'
            · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h),
            hcwit.imp fun ac ⟨hac, h⟩ => ⟨hac, h_msgs ▸ Set.mem_union_left _ h⟩,
            fun ac' hac d hcd hdb v' hv' => by
            rw [h_msgs] at hv'; rcases hv' with hv' | hv'
            · exact hcgap ac' hac d hcd hdb v' hv'
            · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h)⟩
    · -- New phase2a(r, b, v): establish safe-at using MS
      have heq := PCMessage.phase2a.inj (Set.mem_singleton_iff.mp h2a)
      obtain ⟨rfl, rfl, rfl⟩ := heq
      -- Goal: pcSafeAt Majority s' r b v
      -- Use Q = MS. All MS members sent phase1b(r, b, ...)
      rcases h_val_choice with ⟨h_all_none, rfl⟩ |
        ⟨maxbal, h_some_mb, h_mb_bound, ac_max, hac_max,
         v_max, h_1b_max, h_val_eq⟩
      · -- Case 1: all-none, v = aborted
        -- Left disjunct: no MS member voted below b
        refine ⟨MS, hMS, fun ac hac => ?_, ?_⟩
        · obtain ⟨b_ac, v_ac, h1b_ac⟩ := h_ms_1b ac hac
          exact ⟨b, le_refl _, b_ac, v_ac, h_msgs ▸ Set.mem_union_left _ h1b_ac⟩
        · left; intro ac hac c' hc'b v' hv'
          rw [h_msgs] at hv'; rcases hv' with hv' | hv'
          · obtain ⟨b_ac, v_ac, h1b_ac⟩ := h_ms_1b ac hac
            have h_bnone := h_all_none ac hac b_ac v_ac h1b_ac
            have h_vn := (h_1bvn r b b_ac v_ac ac h1b_ac).mp h_bnone
            exact h_1bn r b ac (h_bnone ▸ h_vn ▸ h1b_ac) c' hc'b v' hv'
          · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h)
      · -- Case 2: some maxbal, v = accValToRMVal v_max
        subst h_val_eq
        -- Right disjunct with c = maxbal
        have h_1bs_max := h_1bs r b maxbal v_max ac_max h_1b_max
        have h_maxbal_lt_b : maxbal < b := h_1bs_max.1
        refine ⟨MS, hMS, fun ac hac => ?_, ?_⟩
        · obtain ⟨b_ac, v_ac, h1b_ac⟩ := h_ms_1b ac hac
          exact ⟨b, le_refl _, b_ac, v_ac, h_msgs ▸ Set.mem_union_left _ h1b_ac⟩
        · right; refine ⟨maxbal, h_maxbal_lt_b, ?_, ?_, ?_⟩
          · -- Votes at maxbal from MS members are accValToRMVal v_max
            intro ac hac v' hv'
            rw [h_msgs] at hv'; rcases hv' with hv' | hv'
            · -- By pcPhase2bSafe + pcPhase2aUnique, all votes at maxbal carry same value
              have h_2a_v' := h_2bs r maxbal v' ac hv'
              have h_2b_max := h_1bs_max.2.2.1
              have h_2a_max := h_2bs r maxbal (accValToRMVal v_max) ac_max h_2b_max
              exact h_2au r maxbal v' (accValToRMVal v_max) h_2a_v' h_2a_max
            · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h)
          · -- Witness: ac_max voted at maxbal
            exact ⟨ac_max, hac_max, h_msgs ▸ Set.mem_union_left _ h_1bs_max.2.2.1⟩
          · -- No MS member voted between maxbal+1 and b-1
            intro ac hac d hmd hdb v' hv'
            rw [h_msgs] at hv'; rcases hv' with hv' | hv'
            · obtain ⟨b_ac, v_ac, h1b_ac⟩ := h_ms_1b ac hac
              rcases b_ac with _ | b'
              · -- b_ac = none: no votes below b
                have h_vn := (h_1bvn r b none v_ac ac h1b_ac).mp rfl
                exact h_1bn r b ac (h_vn ▸ h1b_ac) d hdb v' hv'
              · -- b_ac = some b': b' ≤ maxbal < d, so b' < d < b
                have h_b'_bound := h_mb_bound ac hac b' v_ac h1b_ac
                have h_faithful := h_1bs r b b' v_ac ac h1b_ac
                have : b' < d := Nat.lt_of_le_of_lt h_b'_bound hmd
                exact h_faithful.2.2.2 d this hdb v' hv'
            · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h)
  · -- pcPhase1bSomeFaithful: new msg is phase2a, not phase1b/phase2b
    intro r mb c v ac' h1b; rw [h_msgs] at h1b; rcases h1b with h1b | h1b
    · obtain ⟨h1, h2, h3, h4⟩ := h_1bs r mb c v ac' h1b
      exact ⟨h1, h2, h_msgs ▸ Set.mem_union_left _ h3,
        fun c' hc1 hc2 v' hv' => by
          rw [h_msgs] at hv'; rcases hv' with hv' | hv'
          · exact h4 c' hc1 hc2 v' hv'
          · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h)⟩
    · exact absurd (Set.mem_singleton_iff.mp h1b) (by intro h; cases h)
  · -- pcPhase1bNoneFaithful: new msg is phase2a, not phase1b/phase2b
    intro r mb ac' h1b; rw [h_msgs] at h1b; rcases h1b with h1b | h1b
    · intro c hc v' hv'; rw [h_msgs] at hv'; rcases hv' with hv' | hv'
      · exact h_1bn r mb ac' h1b c hc v' hv'
      · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h)
    · exact absurd (Set.mem_singleton_iff.mp h1b) (by intro h; cases h)
  · -- pcAccStateValid: aState unchanged, new msg is phase2a (not phase2b)
    intro r ac'; rw [h_as]
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h_asv r ac'
    refine ⟨h1, fun c hc => ?_, fun c hc1 hc2 v hv => ?_,
      fun hn c hc v hv => ?_, h5, fun mb b v h1b => ?_, fun c v hv => ?_⟩
    · obtain ⟨hne, hm⟩ := h2 c hc
      exact ⟨hne, h_msgs ▸ Set.mem_union_left _ hm⟩
    · rw [h_msgs] at hv; rcases hv with hv | hv
      · exact h3 c hc1 hc2 v hv
      · exact absurd (Set.mem_singleton_iff.mp hv) (by intro h; cases h)
    · rw [h_msgs] at hv; rcases hv with hv | hv
      · exact h4 hn c hc v hv
      · exact absurd (Set.mem_singleton_iff.mp hv) (by intro h; cases h)
    · rw [h_msgs] at h1b; rcases h1b with h1b | h1b
      · exact h6 mb b v h1b
      · exact absurd (Set.mem_singleton_iff.mp h1b) (by intro h; cases h)
    · rw [h_msgs] at hv; rcases hv with hv | hv
      · exact h7 c v hv
      · exact absurd (Set.mem_singleton_iff.mp hv) (by intro h; cases h)
  · -- pcPhase1bValNone: new msg is phase2a, not phase1b
    intro r mb b' v ac' h1b; rw [h_msgs] at h1b; rcases h1b with h1b | h1b
    · exact h_1bvn r mb b' v ac' h1b
    · exact absurd (Set.mem_singleton_iff.mp h1b) (by intro h; cases h)
  · -- pcCommitImpliesAllDecidedPrepared: new msg is phase2a, not commit
    intro hc r; rw [h_msgs] at hc; rcases hc with hc | hc
    · obtain ⟨b, MS', hMS', hv⟩ := h_cid hc r
      exact ⟨b, MS', hMS', fun ac' hac =>
        h_msgs ▸ Set.mem_union_left _ (hv ac' hac)⟩
    · exact absurd (Set.mem_singleton_iff.mp hc) (by intro h; cases h)
  · -- pcAbortImpliesDecidedAborted: new msg is phase2a, not abort
    intro ha; rw [h_msgs] at ha; rcases ha with ha | ha
    · obtain ⟨r, b, MS', hMS', hv⟩ := h_aid ha
      exact ⟨r, b, MS', hMS', fun ac' hac =>
        h_msgs ▸ Set.mem_union_left _ (hv ac' hac)⟩
    · exact absurd (Set.mem_singleton_iff.mp ha) (by intro h; cases h)
  · -- pcPreparedHasLowerEvidence: new msg is phase2a(rm, bal, val)
    intro r b h2a hb; rw [h_msgs] at h2a; rcases h2a with h2a | h2a
    · -- Old phase2a: use h_ple, lift phase2b witness into s'.msgs
      obtain ⟨c, hcb, ac', h2b⟩ := h_ple r b h2a hb
      exact ⟨c, hcb, ac', h_msgs ▸ Set.mem_union_left _ h2b⟩
    · -- New phase2a: phase2a rm bal val = phase2a r b prepared
      obtain ⟨rfl, rfl, rfl⟩ := PCMessage.phase2a.inj (Set.mem_singleton_iff.mp h2a)
      -- val = prepared, bal > 0. The value came from maxbal in the phase1b's.
      rcases h_val_choice with ⟨h_all_none, h_val_eq⟩ |
        ⟨maxbal, h_some_mb, h_mb_bound, ac_max, hac_max, v_max, h_1b_max, h_val_eq⟩
      · -- All-none case: val = aborted, contradicts prepared
        exact absurd h_val_eq (by intro h; cases h)
      · -- Some maxbal: val = accValToRMVal v_max = prepared
        -- By pcPhase1bSomeFaithful: phase2b rm maxbal (accValToRMVal v_max) ac_max ∈ s.msgs
        -- with maxbal < bal
        have h_faithful := h_1bs r b maxbal v_max ac_max h_1b_max
        have h_maxbal_lt : maxbal < b := h_faithful.1
        have h_2b_max := h_faithful.2.2.1
        -- accValToRMVal v_max = prepared since val = accValToRMVal v_max = prepared
        have : accValToRMVal v_max = RMVal.prepared := by
          cases v_max <;> simp [accValToRMVal] at h_val_eq ⊢
        exact ⟨maxbal, h_maxbal_lt, ac_max, h_msgs ▸ Set.mem_union_left _ (this ▸ h_2b_max)⟩

-- RMPrepare: rm transitions working→prepared, sends phase2a(rm, 0, prepared).
lemma pcInvariant_rmPrepare (Majority : Set (Set Acceptor))
    (rm : RM) (s s' : PCState RM Acceptor) :
    pcInvariant Majority s → pcRMPrepare rm s s' → pcInvariant Majority s' := by
  intro ⟨h_con, h_ca, h_ac, h_cm, h_ne, h_2bs, h_2au, h_wn,
    h_abi, h_ami, h_cnw, h_p2as, h_1bs, h_1bn, h_asv, h_1bvn,
    h_cid, h_aid, h_ple⟩
    ⟨h_work, h_rm, h_msgs, h_as⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- pcConsistent
    unfold pcConsistent tcConsistent at *
    rintro ⟨r1, r2, h1, h2⟩; rw [h_rm] at h1 h2
    simp only [Function.update_apply] at h1 h2
    revert h1 h2; split_ifs <;> intro h1 h2
    · exact absurd h1 (by simp)
    · exact absurd h1 (by simp)
    · exact absurd h2 (by simp)
    · exact h_con ⟨r1, r2, h1, h2⟩
  · intro hc r; rw [h_rm]; simp only [Function.update_apply]
    rw [h_msgs] at hc; rcases hc with hc | hc
    · split_ifs with hr
      · intro h; simp at h
      · exact h_ca hc r
    · exact absurd (Set.mem_singleton_iff.mp hc) (by intro h; cases h)
  · intro ha r; rw [h_rm]; simp only [Function.update_apply]
    rw [h_msgs] at ha; rcases ha with ha | ha
    · split_ifs with hr
      · intro h; simp at h
      · exact h_ac ha r
    · exact absurd (Set.mem_singleton_iff.mp ha) (by intro h; cases h)
  · intro r h; rw [h_rm] at h; simp only [Function.update_apply] at h
    revert h; split_ifs <;> intro h
    · simp at h
    · rw [h_msgs]; exact Or.inl (h_cm r h)
  · exact ne_comm_abort_of_union_irrel h_ne (by intro h; cases h)
      (by intro h; cases h) h_msgs
  · intro r b v ac h; rw [h_msgs] at h; rcases h with h | h
    · rw [h_msgs]; exact Or.inl (h_2bs r b v ac h)
    · exact absurd (Set.mem_singleton_iff.mp h) (by intro h; cases h)
  · intro r b v₁ v₂ h₁ h₂; rw [h_msgs] at h₁ h₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact h_2au r b v₁ v₂ h₁ h₂
    · have hj := PCMessage.phase2a.inj (Set.mem_singleton_iff.mp h₂)
      exfalso; exact h_wn rm v₁ h_work (hj.1 ▸ hj.2.1 ▸ h₁)
    · have hj := PCMessage.phase2a.inj (Set.mem_singleton_iff.mp h₁)
      exfalso; exact h_wn rm v₂ h_work (hj.1 ▸ hj.2.1 ▸ h₂)
    · have h1 := PCMessage.phase2a.inj (Set.mem_singleton_iff.mp h₁)
      have h2 := PCMessage.phase2a.inj (Set.mem_singleton_iff.mp h₂)
      exact h1.2.2 ▸ h2.2.2 ▸ rfl
  · intro r v hw h2a; rw [h_rm] at hw; simp only [Function.update_apply] at hw
    revert hw; split_ifs <;> intro hw
    · simp at hw
    · rw [h_msgs] at h2a; rcases h2a with h | h
      · exact h_wn r v hw h
      · have hj := PCMessage.phase2a.inj (Set.mem_singleton_iff.mp h)
        exact absurd hj.1 (by assumption)
  · -- pcAbortedImpliesPhase2a: rm goes working→prepared, not aborted
    intro r ha; rw [h_rm] at ha; simp only [Function.update_apply] at ha
    revert ha; split_ifs <;> intro ha
    · simp at ha  -- prepared ≠ aborted
    · rcases h_abi r ha with h | h
      · exact Or.inl (h_msgs ▸ Set.mem_union_left _ h)
      · exact Or.inr (h_msgs ▸ Set.mem_union_left _ h)
  · -- pcAbortMsgImpliesPhase2a: new msg is phase2a(rm, 0, prepared), not abort
    intro ha; rw [h_msgs] at ha; rcases ha with ha | ha
    · obtain ⟨r, b, hp⟩ := h_ami ha; exact ⟨r, b, h_msgs ▸ Set.mem_union_left _ hp⟩
    · exact absurd (Set.mem_singleton_iff.mp ha) (by intro h; cases h)
  · -- pcCommitNoWorking: rm goes working→prepared, new msg is phase2a (not commit)
    intro hc r; rw [h_rm]; simp only [Function.update_apply]
    rw [h_msgs] at hc; rcases hc with hc | hc
    · split_ifs with hr
      · intro h; simp at h  -- prepared ≠ working
      · exact h_cnw hc r
    · exact absurd (Set.mem_singleton_iff.mp hc) (by intro h; cases h)
  · -- pcPhase2aSafe: new msg is phase2a(rm,0,prepared) at ballot 0, safe vacuously
    intro r b v h2a hb
    rw [h_msgs] at h2a; rcases h2a with h2a | h2a
    · obtain ⟨Q, hQ, hQpromise, hQvotes⟩ := h_p2as r b v h2a hb
      refine ⟨Q, hQ, fun ac' hac => ?_, ?_⟩
      · obtain ⟨mb, hmb, bal, val, h1b⟩ := hQpromise ac' hac
        exact ⟨mb, hmb, bal, val, h_msgs ▸ Set.mem_union_left _ h1b⟩
      · rcases hQvotes with hno | ⟨c, hcb, hcv, hcwit, hcgap⟩
        · left; intro ac' hac c' hcb v' hv'
          rw [h_msgs] at hv'; rcases hv' with hv' | hv'
          · exact hno ac' hac c' hcb v' hv'
          · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h)
        · right; exact ⟨c, hcb, fun ac' hac v' hv' => by
            rw [h_msgs] at hv'; rcases hv' with hv' | hv'
            · exact hcv ac' hac v' hv'
            · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h),
            hcwit.imp fun ac ⟨hac, h⟩ => ⟨hac, h_msgs ▸ Set.mem_union_left _ h⟩,
            fun ac' hac d hcd hdb v' hv' => by
            rw [h_msgs] at hv'; rcases hv' with hv' | hv'
            · exact hcgap ac' hac d hcd hdb v' hv'
            · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h)⟩
    · have hj := PCMessage.phase2a.inj (Set.mem_singleton_iff.mp h2a)
      omega
  · -- pcPhase1bSomeFaithful: new msg is phase2a, not phase1b/phase2b
    intro r mb c v ac' h1b; rw [h_msgs] at h1b; rcases h1b with h1b | h1b
    · obtain ⟨h1, h2, h3, h4⟩ := h_1bs r mb c v ac' h1b
      exact ⟨h1, h2, h_msgs ▸ Set.mem_union_left _ h3,
        fun c' hc1 hc2 v' hv' => by
          rw [h_msgs] at hv'; rcases hv' with hv' | hv'
          · exact h4 c' hc1 hc2 v' hv'
          · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h)⟩
    · exact absurd (Set.mem_singleton_iff.mp h1b) (by intro h; cases h)
  · -- pcPhase1bNoneFaithful: new msg is phase2a, not phase1b/phase2b
    intro r mb ac' h1b; rw [h_msgs] at h1b; rcases h1b with h1b | h1b
    · intro c hc v' hv'; rw [h_msgs] at hv'; rcases hv' with hv' | hv'
      · exact h_1bn r mb ac' h1b c hc v' hv'
      · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h)
    · exact absurd (Set.mem_singleton_iff.mp h1b) (by intro h; cases h)
  · -- pcAccStateValid: aState unchanged, new msg is phase2a (not phase2b)
    intro r ac'; rw [h_as]
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h_asv r ac'
    refine ⟨h1, fun c hc => ?_, fun c hc1 hc2 v hv => ?_,
      fun hn c hc v hv => ?_, h5,
      fun mb b v h1b => ?_, fun c v hv => ?_⟩
    · obtain ⟨hne, hm⟩ := h2 c hc; exact ⟨hne, h_msgs ▸ Set.mem_union_left _ hm⟩
    · rw [h_msgs] at hv; rcases hv with hv | hv
      · exact h3 c hc1 hc2 v hv
      · exact absurd (Set.mem_singleton_iff.mp hv) (by intro h; cases h)
    · rw [h_msgs] at hv; rcases hv with hv | hv
      · exact h4 hn c hc v hv
      · exact absurd (Set.mem_singleton_iff.mp hv) (by intro h; cases h)
    · rw [h_msgs] at h1b; rcases h1b with h1b | h1b
      · exact h6 mb b v h1b
      · exact absurd (Set.mem_singleton_iff.mp h1b) (by intro h; cases h)
    · rw [h_msgs] at hv; rcases hv with hv | hv
      · exact h7 c v hv
      · exact absurd (Set.mem_singleton_iff.mp hv) (by intro h; cases h)
  · -- pcPhase1bValNone: new msg is phase2a, not phase1b
    intro r mb b' v ac' h1b; rw [h_msgs] at h1b; rcases h1b with h1b | h1b
    · exact h_1bvn r mb b' v ac' h1b
    · exact absurd (Set.mem_singleton_iff.mp h1b) (by intro h; cases h)
  · -- pcCommitImpliesAllDecidedPrepared: new msg is phase2a, not commit
    intro hc r; rw [h_msgs] at hc; rcases hc with hc | hc
    · obtain ⟨b, MS, hMS, hv⟩ := h_cid hc r
      exact ⟨b, MS, hMS, fun ac' hac => h_msgs ▸ Set.mem_union_left _ (hv ac' hac)⟩
    · exact absurd (Set.mem_singleton_iff.mp hc) (by intro h; cases h)
  · -- pcAbortImpliesDecidedAborted: new msg is phase2a, not abort
    intro ha; rw [h_msgs] at ha; rcases ha with ha | ha
    · obtain ⟨r, b, MS, hMS, hv⟩ := h_aid ha
      exact ⟨r, b, MS, hMS, fun ac' hac => h_msgs ▸ Set.mem_union_left _ (hv ac' hac)⟩
    · exact absurd (Set.mem_singleton_iff.mp ha) (by intro h; cases h)
  · -- pcPreparedHasLowerEvidence: new msg is phase2a(rm, 0, prepared)
    intro r b h2a hb; rw [h_msgs] at h2a; rcases h2a with h2a | h2a
    · obtain ⟨c, hcb, ac', h2b⟩ := h_ple r b h2a hb
      exact ⟨c, hcb, ac', h_msgs ▸ Set.mem_union_left _ h2b⟩
    · -- New phase2a at ballot 0, but b > 0
      obtain ⟨_, hb0, _⟩ := PCMessage.phase2a.inj (Set.mem_singleton_iff.mp h2a)
      omega

-- RMChooseToAbort: rm transitions working→aborted, sends phase2a(rm, 0, aborted).
lemma pcInvariant_rmChooseToAbort (Majority : Set (Set Acceptor))
    (rm : RM) (s s' : PCState RM Acceptor) :
    pcInvariant Majority s → pcRMChooseToAbort rm s s' →
    pcInvariant Majority s' := by
  intro ⟨h_con, h_ca, h_ac, h_cm, h_ne, h_2bs, h_2au, h_wn,
    h_abi, h_ami, h_cnw, h_p2as, h_1bs, h_1bn, h_asv, h_1bvn,
    h_cid, h_aid, h_ple⟩
    ⟨h_work, h_rm, h_msgs, h_as⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- pcConsistent
    unfold pcConsistent tcConsistent at *
    rintro ⟨r1, r2, h1, h2⟩; rw [h_rm] at h1 h2
    simp only [Function.update_apply] at h1 h2
    revert h1 h2; split_ifs <;> intro h1 h2
    · exact h2  -- h2 : False (aborted ≠ committed after simp)
    · -- r1 = rm (now aborted), r2 ≠ rm, h2 : s.rmState r2 = committed
      exact absurd h_work (h_cnw (h_cm _ h2) rm)
    · exact absurd h2 (by simp)
    · exact h_con ⟨r1, r2, h1, h2⟩
  · -- commit → no aborted: rm becomes aborted, so need commit ∉ old msgs.
    -- This requires the full Paxos argument (commit can't exist while RM is working).
    intro hc r; rw [h_rm]; simp only [Function.update_apply]
    rw [h_msgs] at hc; rcases hc with hc | hc
    · split_ifs with hr
      · exact absurd h_work (h_cnw hc rm)
      · exact h_ca hc r
    · exact absurd (Set.mem_singleton_iff.mp hc) (by intro h; cases h)
  · intro ha r; rw [h_rm]; simp only [Function.update_apply]
    rw [h_msgs] at ha; rcases ha with ha | ha
    · split_ifs with hr
      · intro h; simp at h  -- aborted ≠ committed
      · exact h_ac ha r
    · exact absurd (Set.mem_singleton_iff.mp ha) (by intro h; cases h)
  · intro r h; rw [h_rm] at h; simp only [Function.update_apply] at h
    revert h; split_ifs <;> intro h
    · simp at h  -- aborted ≠ committed
    · rw [h_msgs]; exact Or.inl (h_cm r h)
  · exact ne_comm_abort_of_union_irrel h_ne (by intro h; cases h)
      (by intro h; cases h) h_msgs
  · intro r b v ac h; rw [h_msgs] at h; rcases h with h | h
    · rw [h_msgs]; exact Or.inl (h_2bs r b v ac h)
    · exact absurd (Set.mem_singleton_iff.mp h) (by intro h; cases h)
  · intro r b v₁ v₂ h₁ h₂; rw [h_msgs] at h₁ h₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact h_2au r b v₁ v₂ h₁ h₂
    · have hj := PCMessage.phase2a.inj (Set.mem_singleton_iff.mp h₂)
      exfalso; exact h_wn rm v₁ h_work (hj.1 ▸ hj.2.1 ▸ h₁)
    · have hj := PCMessage.phase2a.inj (Set.mem_singleton_iff.mp h₁)
      exfalso; exact h_wn rm v₂ h_work (hj.1 ▸ hj.2.1 ▸ h₂)
    · have h1 := PCMessage.phase2a.inj (Set.mem_singleton_iff.mp h₁)
      have h2 := PCMessage.phase2a.inj (Set.mem_singleton_iff.mp h₂)
      exact h1.2.2 ▸ h2.2.2 ▸ rfl
  · intro r v hw h2a; rw [h_rm] at hw; simp only [Function.update_apply] at hw
    revert hw; split_ifs <;> intro hw
    · simp at hw  -- aborted ≠ working
    · rw [h_msgs] at h2a; rcases h2a with h | h
      · exact h_wn r v hw h
      · have hj := PCMessage.phase2a.inj (Set.mem_singleton_iff.mp h)
        exact absurd hj.1 (by assumption)
  · -- pcAbortedImpliesPhase2a: rm becomes aborted, phase2a(rm,0,aborted) added
    intro r ha; rw [h_rm] at ha; simp only [Function.update_apply] at ha
    revert ha; split_ifs with hr <;> intro ha
    · -- r = rm: the new phase2a(rm, 0, aborted) is in s'.msgs
      subst hr; exact Or.inl (h_msgs ▸ Set.mem_union_right _
        (Set.mem_singleton_iff.mpr rfl))
    · -- r ≠ rm: old state, use h_abi
      rcases h_abi r ha with h | h
      · exact Or.inl (h_msgs ▸ Set.mem_union_left _ h)
      · exact Or.inr (h_msgs ▸ Set.mem_union_left _ h)
  · -- pcAbortMsgImpliesPhase2a: new msg is phase2a, not abort
    intro ha; rw [h_msgs] at ha; rcases ha with ha | ha
    · obtain ⟨r, b, hp⟩ := h_ami ha; exact ⟨r, b, h_msgs ▸ Set.mem_union_left _ hp⟩
    · exact absurd (Set.mem_singleton_iff.mp ha) (by intro h; cases h)
  · -- pcCommitNoWorking: rm goes working→aborted, new msg is phase2a (not commit)
    -- If commit ∈ s'.msgs then commit ∈ s.msgs, contradicting h_cnw + h_work.
    intro hc r; rw [h_rm]; simp only [Function.update_apply]
    rw [h_msgs] at hc; rcases hc with hc | hc
    · exfalso; exact h_cnw hc rm h_work
    · exact absurd (Set.mem_singleton_iff.mp hc) (by intro h; cases h)
  · -- pcPhase2aSafe: new msg is phase2a(rm,0,aborted) at ballot 0, safe vacuously
    intro r b v h2a hb
    rw [h_msgs] at h2a; rcases h2a with h2a | h2a
    · obtain ⟨Q, hQ, hQpromise, hQvotes⟩ := h_p2as r b v h2a hb
      refine ⟨Q, hQ, fun ac' hac => ?_, ?_⟩
      · obtain ⟨mb, hmb, bal, val, h1b⟩ := hQpromise ac' hac
        exact ⟨mb, hmb, bal, val, h_msgs ▸ Set.mem_union_left _ h1b⟩
      · rcases hQvotes with hno | ⟨c, hcb, hcv, hcwit, hcgap⟩
        · left; intro ac' hac c' hcb v' hv'
          rw [h_msgs] at hv'; rcases hv' with hv' | hv'
          · exact hno ac' hac c' hcb v' hv'
          · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h)
        · right; exact ⟨c, hcb, fun ac' hac v' hv' => by
            rw [h_msgs] at hv'; rcases hv' with hv' | hv'
            · exact hcv ac' hac v' hv'
            · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h),
            hcwit.imp fun ac ⟨hac, h⟩ => ⟨hac, h_msgs ▸ Set.mem_union_left _ h⟩,
            fun ac' hac d hcd hdb v' hv' => by
            rw [h_msgs] at hv'; rcases hv' with hv' | hv'
            · exact hcgap ac' hac d hcd hdb v' hv'
            · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h)⟩
    · have hj := PCMessage.phase2a.inj (Set.mem_singleton_iff.mp h2a)
      omega
  · -- pcPhase1bSomeFaithful: new msg is phase2a, not phase1b/phase2b
    intro r mb c v ac' h1b; rw [h_msgs] at h1b; rcases h1b with h1b | h1b
    · obtain ⟨h1, h2, h3, h4⟩ := h_1bs r mb c v ac' h1b
      exact ⟨h1, h2, h_msgs ▸ Set.mem_union_left _ h3,
        fun c' hc1 hc2 v' hv' => by
          rw [h_msgs] at hv'; rcases hv' with hv' | hv'
          · exact h4 c' hc1 hc2 v' hv'
          · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h)⟩
    · exact absurd (Set.mem_singleton_iff.mp h1b) (by intro h; cases h)
  · -- pcPhase1bNoneFaithful: new msg is phase2a, not phase1b/phase2b
    intro r mb ac' h1b; rw [h_msgs] at h1b; rcases h1b with h1b | h1b
    · intro c hc v' hv'; rw [h_msgs] at hv'; rcases hv' with hv' | hv'
      · exact h_1bn r mb ac' h1b c hc v' hv'
      · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h)
    · exact absurd (Set.mem_singleton_iff.mp h1b) (by intro h; cases h)
  · -- pcAccStateValid: aState unchanged, new msg is phase2a (not phase2b)
    intro r ac'; rw [h_as]
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h_asv r ac'
    refine ⟨h1, fun c hc => ?_, fun c hc1 hc2 v hv => ?_,
      fun hn c hc v hv => ?_, h5,
      fun mb b v h1b => ?_, fun c v hv => ?_⟩
    · obtain ⟨hne, hm⟩ := h2 c hc; exact ⟨hne, h_msgs ▸ Set.mem_union_left _ hm⟩
    · rw [h_msgs] at hv; rcases hv with hv | hv
      · exact h3 c hc1 hc2 v hv
      · exact absurd (Set.mem_singleton_iff.mp hv) (by intro h; cases h)
    · rw [h_msgs] at hv; rcases hv with hv | hv
      · exact h4 hn c hc v hv
      · exact absurd (Set.mem_singleton_iff.mp hv) (by intro h; cases h)
    · rw [h_msgs] at h1b; rcases h1b with h1b | h1b
      · exact h6 mb b v h1b
      · exact absurd (Set.mem_singleton_iff.mp h1b) (by intro h; cases h)
    · rw [h_msgs] at hv; rcases hv with hv | hv
      · exact h7 c v hv
      · exact absurd (Set.mem_singleton_iff.mp hv) (by intro h; cases h)
  · -- pcPhase1bValNone: new msg is phase2a, not phase1b
    intro r mb b' v ac' h1b; rw [h_msgs] at h1b; rcases h1b with h1b | h1b
    · exact h_1bvn r mb b' v ac' h1b
    · exact absurd (Set.mem_singleton_iff.mp h1b) (by intro h; cases h)
  · -- pcCommitImpliesAllDecidedPrepared: new msg is phase2a, not commit
    intro hc r; rw [h_msgs] at hc; rcases hc with hc | hc
    · obtain ⟨b, MS, hMS, hv⟩ := h_cid hc r
      exact ⟨b, MS, hMS, fun ac' hac => h_msgs ▸ Set.mem_union_left _ (hv ac' hac)⟩
    · exact absurd (Set.mem_singleton_iff.mp hc) (by intro h; cases h)
  · -- pcAbortImpliesDecidedAborted: new msg is phase2a, not abort
    intro ha; rw [h_msgs] at ha; rcases ha with ha | ha
    · obtain ⟨r, b, MS, hMS, hv⟩ := h_aid ha
      exact ⟨r, b, MS, hMS, fun ac' hac => h_msgs ▸ Set.mem_union_left _ (hv ac' hac)⟩
    · exact absurd (Set.mem_singleton_iff.mp ha) (by intro h; cases h)
  · -- pcPreparedHasLowerEvidence: new msg is phase2a(rm, 0, aborted)
    intro r b h2a hb; rw [h_msgs] at h2a; rcases h2a with h2a | h2a
    · obtain ⟨c, hcb, ac', h2b⟩ := h_ple r b h2a hb
      exact ⟨c, hcb, ac', h_msgs ▸ Set.mem_union_left _ h2b⟩
    · -- New phase2a at ballot 0, but b > 0
      obtain ⟨_, hb0, _⟩ := PCMessage.phase2a.inj (Set.mem_singleton_iff.mp h2a)
      omega

-- RMRcvCommitMsg: rm receives commit, transitions to committed.
-- msgs unchanged, so Paxos properties trivially hold.
lemma pcInvariant_rmRcvCommitMsg (Majority : Set (Set Acceptor))
    (rm : RM) (s s' : PCState RM Acceptor) :
    pcInvariant Majority s → pcRMRcvCommitMsg rm s s' →
    pcInvariant Majority s' := by
  intro ⟨h_con, h_ca, h_ac, h_cm, h_ne, h_2bs, h_2au, h_wn,
    h_abi, h_ami, h_cnw, h_p2as, h_1bs, h_1bn, h_asv, h_1bvn,
    h_cid, h_aid, h_ple⟩
    ⟨h_commit, h_rm, h_as, h_msgs⟩
  have h_ca' := h_ca h_commit  -- ∀ rm, s.rmState rm ≠ aborted
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- pcConsistent
    unfold pcConsistent tcConsistent at *
    rintro ⟨r1, r2, h1, h2⟩; rw [h_rm] at h1 h2
    simp only [Function.update_apply] at h1 h2
    revert h1 h2; split_ifs <;> intro h1 h2
    · exact absurd h1 (by simp)
    · exact absurd h1 (by simp)
    · exact absurd h1 (h_ca' r1)
    · exact h_con ⟨r1, r2, h1, h2⟩
  · intro hc r; rw [h_msgs] at hc; rw [h_rm]; simp only [Function.update_apply]
    split_ifs with hr
    · intro h; simp at h  -- committed ≠ aborted
    · exact h_ca hc r
  · intro ha r; rw [h_msgs] at ha; rw [h_rm]; simp only [Function.update_apply]
    split_ifs with hr
    · exfalso; exact h_ne ⟨h_commit, ha⟩
    · exact h_ac ha r
  · intro r h; rw [h_rm] at h; simp only [Function.update_apply] at h
    revert h; split_ifs <;> intro h
    · rw [h_msgs]; exact h_commit
    · rw [h_msgs]; exact h_cm r h
  · rw [h_msgs]; exact h_ne
  · intro r b v ac h2b; rw [h_msgs] at h2b ⊢; exact h_2bs r b v ac h2b
  · intro r b v₁ v₂ h₁ h₂; rw [h_msgs] at h₁ h₂; exact h_2au r b v₁ v₂ h₁ h₂
  · intro r v hw; rw [h_rm] at hw; simp only [Function.update_apply] at hw
    revert hw; split_ifs <;> intro hw
    · simp at hw  -- committed ≠ working
    · rw [h_msgs]; exact h_wn r v hw
  · -- pcAbortedImpliesPhase2a: rm becomes committed, not aborted
    intro r ha; rw [h_rm] at ha; simp only [Function.update_apply] at ha
    revert ha; split_ifs <;> intro ha
    · simp at ha  -- committed ≠ aborted
    · rw [h_msgs]; exact h_abi r ha
  · -- pcAbortMsgImpliesPhase2a: msgs unchanged
    intro ha; rw [h_msgs] at ha; rw [h_msgs]; exact h_ami ha
  · -- pcCommitNoWorking: rm→committed, msgs unchanged
    intro hc r; rw [h_msgs] at hc; rw [h_rm]; simp only [Function.update_apply]
    split_ifs with hr
    · intro h; simp at h  -- committed ≠ working
    · exact h_cnw hc r
  · -- pcPhase2aSafe: msgs unchanged, aState unchanged
    intro r b v h2a hb
    have h2a' : PCMessage.phase2a r b v ∈ s.msgs := h_msgs ▸ h2a
    obtain ⟨Q, hQ, hQpromise, hQvotes⟩ := h_p2as r b v h2a' hb
    refine ⟨Q, hQ, fun ac' hac => ?_, ?_⟩
    · obtain ⟨mb, hmb, bal, val, h1b⟩ := hQpromise ac' hac
      exact ⟨mb, hmb, bal, val, h_msgs ▸ h1b⟩
    · rcases hQvotes with hno | ⟨c, hcb, hcv, hcwit, hcgap⟩
      · left; exact fun ac' hac c' hcb v' hv' => hno ac' hac c' hcb v' (h_msgs ▸ hv')
      · right; exact ⟨c, hcb,
          fun ac' hac v' hv' => hcv ac' hac v' (h_msgs ▸ hv'),
          hcwit.imp fun ac ⟨hac, h⟩ => ⟨hac, h_msgs ▸ h⟩,
          fun ac' hac d hcd hdb v' hv' => hcgap ac' hac d hcd hdb v' (h_msgs ▸ hv')⟩
  · -- pcPhase1bSomeFaithful: msgs unchanged
    intro r mb c v ac' h1b; rw [h_msgs] at h1b
    obtain ⟨h1, h2, h3, h4⟩ := h_1bs r mb c v ac' h1b
    exact ⟨h1, h2, h_msgs ▸ h3, fun c' hc1 hc2 v' hv' => h4 c' hc1 hc2 v' (h_msgs ▸ hv')⟩
  · -- pcPhase1bNoneFaithful: msgs unchanged
    intro r mb ac' h1b; rw [h_msgs] at h1b
    intro c hc v' hv'; exact h_1bn r mb ac' h1b c hc v' (h_msgs ▸ hv')
  · -- pcAccStateValid: aState unchanged, msgs unchanged
    intro r ac'; rw [h_as]
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h_asv r ac'
    refine ⟨h1, fun c hc => ?_, fun c hc1 hc2 v hv => ?_,
      fun hn c hc v hv => ?_, h5,
      fun mb b v h1b => ?_, fun c v hv => ?_⟩
    · obtain ⟨hne, hm⟩ := h2 c hc; exact ⟨hne, h_msgs ▸ hm⟩
    · exact h3 c hc1 hc2 v (h_msgs ▸ hv)
    · exact h4 hn c hc v (h_msgs ▸ hv)
    · exact h6 mb b v (h_msgs ▸ h1b)
    · exact h7 c v (h_msgs ▸ hv)
  · -- pcPhase1bValNone: msgs unchanged
    intro r mb b' v ac' h1b; rw [h_msgs] at h1b; exact h_1bvn r mb b' v ac' h1b
  · -- pcCommitImpliesAllDecidedPrepared: msgs unchanged
    intro hc r
    have hc' : PCMessage.commit ∈ s.msgs := h_msgs ▸ hc
    obtain ⟨b, MS, hMS, hv⟩ := h_cid hc' r
    exact ⟨b, MS, hMS, fun ac' hac => h_msgs ▸ hv ac' hac⟩
  · -- pcAbortImpliesDecidedAborted: msgs unchanged
    intro ha
    have ha' : PCMessage.abort ∈ s.msgs := h_msgs ▸ ha
    obtain ⟨r, b, MS, hMS, hv⟩ := h_aid ha'
    exact ⟨r, b, MS, hMS, fun ac' hac => h_msgs ▸ hv ac' hac⟩
  · -- pcPreparedHasLowerEvidence: msgs unchanged
    intro r b h2a hb
    obtain ⟨c, hcb, ac', h2b⟩ := h_ple r b (h_msgs ▸ h2a) hb
    exact ⟨c, hcb, ac', h_msgs ▸ h2b⟩

-- RMRcvAbortMsg: rm receives abort, transitions to aborted.
lemma pcInvariant_rmRcvAbortMsg (Majority : Set (Set Acceptor))
    (rm : RM) (s s' : PCState RM Acceptor) :
    pcInvariant Majority s → pcRMRcvAbortMsg rm s s' →
    pcInvariant Majority s' := by
  intro ⟨h_con, h_ca, h_ac, h_cm, h_ne, h_2bs, h_2au, h_wn,
    h_abi, h_ami, h_cnw, h_p2as, h_1bs, h_1bn, h_asv, h_1bvn,
    h_cid, h_aid, h_ple⟩
    ⟨h_abort, h_rm, h_as, h_msgs⟩
  have h_ac' := h_ac h_abort  -- ∀ rm, s.rmState rm ≠ committed
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold pcConsistent tcConsistent at *
    rintro ⟨r1, r2, h1, h2⟩; rw [h_rm] at h1 h2
    simp only [Function.update_apply] at h1 h2
    revert h1 h2; split_ifs <;> intro h1 h2
    · exact absurd h2 (by simp)
    · exact absurd h2 (h_ac' r2)
    · exact absurd h2 (by simp)
    · exact h_con ⟨r1, r2, h1, h2⟩
  · intro hc r; rw [h_msgs] at hc; rw [h_rm]; simp only [Function.update_apply]
    split_ifs with hr
    · exfalso; exact h_ne ⟨hc, h_abort⟩
    · exact h_ca hc r
  · intro ha r; rw [h_msgs] at ha; rw [h_rm]; simp only [Function.update_apply]
    split_ifs with hr
    · intro h; simp at h  -- aborted ≠ committed
    · exact h_ac ha r
  · intro r h; rw [h_rm] at h; simp only [Function.update_apply] at h
    revert h; split_ifs <;> intro h
    · simp at h  -- aborted ≠ committed
    · rw [h_msgs]; exact h_cm r h
  · rw [h_msgs]; exact h_ne
  · intro r b v ac h2b; rw [h_msgs] at h2b ⊢; exact h_2bs r b v ac h2b
  · intro r b v₁ v₂ h₁ h₂; rw [h_msgs] at h₁ h₂; exact h_2au r b v₁ v₂ h₁ h₂
  · intro r v hw; rw [h_rm] at hw; simp only [Function.update_apply] at hw
    revert hw; split_ifs <;> intro hw
    · simp at hw  -- aborted ≠ working
    · rw [h_msgs]; exact h_wn r v hw
  · -- pcAbortedImpliesPhase2a: rm becomes aborted via abort msg
    intro r ha; rw [h_rm] at ha; simp only [Function.update_apply] at ha
    revert ha; split_ifs <;> intro ha
    · -- r = rm: abort ∈ s.msgs
      exact Or.inr (h_msgs ▸ h_abort)
    · -- r ≠ rm: old state
      rw [h_msgs]; exact h_abi r ha
  · -- pcAbortMsgImpliesPhase2a: msgs unchanged
    intro ha; rw [h_msgs] at ha; rw [h_msgs]; exact h_ami ha
  · -- pcCommitNoWorking: rm→aborted, msgs unchanged
    -- commit ∈ s.msgs contradicts h_ne + h_abort
    intro hc; rw [h_msgs] at hc; exfalso; exact h_ne ⟨hc, h_abort⟩
  · -- pcPhase2aSafe: msgs unchanged, aState unchanged
    intro r b v h2a hb
    have h2a' : PCMessage.phase2a r b v ∈ s.msgs := h_msgs ▸ h2a
    obtain ⟨Q, hQ, hQpromise, hQvotes⟩ := h_p2as r b v h2a' hb
    refine ⟨Q, hQ, fun ac' hac => ?_, ?_⟩
    · obtain ⟨mb, hmb, bal, val, h1b⟩ := hQpromise ac' hac
      exact ⟨mb, hmb, bal, val, h_msgs ▸ h1b⟩
    · rcases hQvotes with hno | ⟨c, hcb, hcv, hcwit, hcgap⟩
      · left; exact fun ac' hac c' hcb v' hv' => hno ac' hac c' hcb v' (h_msgs ▸ hv')
      · right; exact ⟨c, hcb,
          fun ac' hac v' hv' => hcv ac' hac v' (h_msgs ▸ hv'),
          hcwit.imp fun ac ⟨hac, h⟩ => ⟨hac, h_msgs ▸ h⟩,
          fun ac' hac d hcd hdb v' hv' => hcgap ac' hac d hcd hdb v' (h_msgs ▸ hv')⟩
  · -- pcPhase1bSomeFaithful: msgs unchanged
    intro r mb c v ac' h1b; rw [h_msgs] at h1b
    obtain ⟨h1, h2, h3, h4⟩ := h_1bs r mb c v ac' h1b
    exact ⟨h1, h2, h_msgs ▸ h3, fun c' hc1 hc2 v' hv' => h4 c' hc1 hc2 v' (h_msgs ▸ hv')⟩
  · -- pcPhase1bNoneFaithful: msgs unchanged
    intro r mb ac' h1b; rw [h_msgs] at h1b
    intro c hc v' hv'; exact h_1bn r mb ac' h1b c hc v' (h_msgs ▸ hv')
  · -- pcAccStateValid: aState unchanged, msgs unchanged
    intro r ac'; rw [h_as]
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h_asv r ac'
    refine ⟨h1, fun c hc => ?_, fun c hc1 hc2 v hv => ?_,
      fun hn c hc v hv => ?_, h5,
      fun mb b v h1b => ?_, fun c v hv => ?_⟩
    · obtain ⟨hne, hm⟩ := h2 c hc; exact ⟨hne, h_msgs ▸ hm⟩
    · exact h3 c hc1 hc2 v (h_msgs ▸ hv)
    · exact h4 hn c hc v (h_msgs ▸ hv)
    · exact h6 mb b v (h_msgs ▸ h1b)
    · exact h7 c v (h_msgs ▸ hv)
  · -- pcPhase1bValNone: msgs unchanged
    intro r mb b' v ac' h1b; rw [h_msgs] at h1b; exact h_1bvn r mb b' v ac' h1b
  · -- pcCommitImpliesAllDecidedPrepared: msgs unchanged
    intro hc r
    have hc' : PCMessage.commit ∈ s.msgs := h_msgs ▸ hc
    obtain ⟨b, MS, hMS, hv⟩ := h_cid hc' r
    exact ⟨b, MS, hMS, fun ac' hac => h_msgs ▸ hv ac' hac⟩
  · -- pcAbortImpliesDecidedAborted: msgs unchanged
    intro ha
    have ha' : PCMessage.abort ∈ s.msgs := h_msgs ▸ ha
    obtain ⟨r, b, MS, hMS, hv⟩ := h_aid ha'
    exact ⟨r, b, MS, hMS, fun ac' hac => h_msgs ▸ hv ac' hac⟩
  · -- pcPreparedHasLowerEvidence: msgs unchanged
    intro r b h2a hb
    obtain ⟨c, hcb, ac', h2b⟩ := h_ple r b (h_msgs ▸ h2a) hb
    exact ⟨c, hcb, ac', h_msgs ▸ h2b⟩

-- Cross-ballot safety: if value v₁ is decided (majority voted) at ballot b₁,
-- then every phase2a at a different ballot b₂ > b₁ must carry the same value.
-- This is the core Paxos safety property. The proof goes by strong induction
-- on b₂: the pcSafeAt witness vote at the highest ballot c lets us apply
-- the inductive hypothesis when c > b₁.
lemma pcDecidedImpliesPhase2a
    (Majority : Set (Set Acceptor))
    (h_maj : ∀ S₁ ∈ Majority, ∀ S₂ ∈ Majority, (S₁ ∩ S₂).Nonempty)
    (h_2bs : pcPhase2bSafe s)
    (h_p2as : pcPhase2aSafe Majority s)
    {r : RM} {b₁ : ℕ} {v₁ : RMVal}
    (MS : Set Acceptor) (hMS : MS ∈ Majority)
    (hvotes : ∀ ac ∈ MS, PCMessage.phase2b r b₁ v₁ ac ∈ s.msgs)
    : ∀ b₂, b₁ < b₂ →
      ∀ v₂, PCMessage.phase2a r b₂ v₂ ∈ s.msgs → v₁ = v₂ := by
  intro b₂
  induction b₂ using Nat.strongRecOn with
  | _ b₂ ih => ?_
  intro hlt v₂ h2a₂
  -- safeAt for (r, b₂, v₂) since b₂ > b₁ ≥ 0 so b₂ ≥ 1
  obtain ⟨Q, hQ, _, hQvotes⟩ := h_p2as r b₂ v₂ h2a₂ (by omega)
  -- Q ∩ MS nonempty: some acceptor voted v₁ at b₁ and is in Q
  obtain ⟨ac_x, hac_x_Q, hac_x_MS⟩ := h_maj Q hQ MS hMS
  have hvote_x := hvotes ac_x hac_x_MS
  rcases hQvotes with hno | ⟨c, hcb, hcv, ⟨ac_w, hac_w_Q, hvote_w⟩, hcgap⟩
  · -- Case A: no Q-member voted below b₂. But ac_x voted v₁ at b₁ < b₂.
    exact absurd hvote_x (hno ac_x hac_x_Q b₁ hlt v₁)
  · -- Case B: Q-votes at c are v₂, witness vote at c, gap (c, b₂).
    -- ac_x voted at b₁. Gap (c, b₂) forbids Q-votes there, so b₁ ≤ c.
    have hb₁_le_c : b₁ ≤ c := by
      by_contra h; push_neg at h
      exact hcgap ac_x hac_x_Q b₁ h hlt v₁ hvote_x
    rcases Nat.eq_or_lt_of_le hb₁_le_c with rfl | hb₁_lt_c
    · -- b₁ = c: ac_x voted v₁ at c, must equal v₂
      exact hcv ac_x hac_x_Q v₁ hvote_x
    · -- b₁ < c < b₂: witness → phase2a at c, apply IH
      exact ih c hcb hb₁_lt_c v₂ (h_2bs r c v₂ ac_w hvote_w)

-- Paxos consensus: two decided values for the same RM must agree.
lemma pcAtMostOneDecision_of_inv
    (Majority : Set (Set Acceptor))
    (h_maj : ∀ S₁ ∈ Majority, ∀ S₂ ∈ Majority, (S₁ ∩ S₂).Nonempty)
    (h_2au : pcPhase2aUnique s)
    (h_2bs : pcPhase2bSafe s)
    (h_p2as : pcPhase2aSafe Majority s)
    {r : RM} {v₁ v₂ : RMVal}
    (hdec₁ : decided Majority s r v₁) (hdec₂ : decided Majority s r v₂) : v₁ = v₂ := by
  obtain ⟨b₁, MS₁, hMS₁, hv₁⟩ := hdec₁
  obtain ⟨b₂, MS₂, hMS₂, hv₂⟩ := hdec₂
  rcases Nat.lt_trichotomy b₁ b₂ with hlt | rfl | hgt
  · -- b₁ < b₂: decided at b₁, phase2a at b₂ (via phase2bSafe)
    obtain ⟨a, ha, _⟩ := h_maj MS₂ hMS₂ MS₂ hMS₂
    exact pcDecidedImpliesPhase2a Majority h_maj h_2bs h_p2as
      MS₁ hMS₁ hv₁ b₂ hlt v₂ (h_2bs r b₂ v₂ a (hv₂ a ha))
  · -- b₁ = b₂: phase2aUnique
    obtain ⟨a₁, ha₁, _⟩ := h_maj MS₁ hMS₁ MS₁ hMS₁
    obtain ⟨a₂, ha₂, _⟩ := h_maj MS₂ hMS₂ MS₂ hMS₂
    exact h_2au r b₁ v₁ v₂ (h_2bs r b₁ v₁ a₁ (hv₁ a₁ ha₁))
      (h_2bs r b₁ v₂ a₂ (hv₂ a₂ ha₂))
  · -- b₂ < b₁: symmetric
    obtain ⟨a, ha, _⟩ := h_maj MS₁ hMS₁ MS₁ hMS₁
    exact (pcDecidedImpliesPhase2a Majority h_maj h_2bs h_p2as
      MS₂ hMS₂ hv₂ b₁ hgt v₁ (h_2bs r b₁ v₁ a (hv₁ a ha))).symm

-- Decide: adds commit or abort message based on majority votes.
-- This is the key case requiring Paxos consensus safety.
lemma pcInvariant_decide (Majority : Set (Set Acceptor))
    (h_maj : ∀ S₁ ∈ Majority, ∀ S₂ ∈ Majority, (S₁ ∩ S₂).Nonempty)
    (s s' : PCState RM Acceptor) :
    pcInvariant Majority s → pcDecide Majority s s' →
    pcInvariant Majority s' := by
  intro ⟨h_con, h_ca, h_ac, h_cm, h_ne, h_2bs, h_2au, h_wn,
    h_abi, h_ami, h_cnw, h_p2as, h_1bs, h_1bn, h_asv, h_1bvn,
    h_cid, h_aid, h_ple⟩
    ⟨h_dec, h_rm, h_as⟩
  -- Helper: phase2a(rm, b, prepared) ∈ msgs implies phase2a(rm, 0, prepared) ∈ msgs,
  -- by chaining pcPreparedHasLowerEvidence down to ballot 0.
  have prepared_chains_to_0 : ∀ rm b,
      PCMessage.phase2a rm b RMVal.prepared ∈ s.msgs →
      PCMessage.phase2a rm 0 RMVal.prepared ∈ s.msgs := by
    intro rm' b
    induction b using Nat.strongRecOn with
    | _ b ih =>
      intro h2a
      by_cases hb : b = 0
      · exact hb ▸ h2a
      · obtain ⟨c, hcb, ac', h2b⟩ := h_ple rm' b h2a (Nat.pos_of_ne_zero hb)
        exact ih c hcb (h_2bs rm' c RMVal.prepared ac' h2b)
  rcases h_dec with ⟨h_all, h_msgs⟩ | ⟨⟨r_abt, h_abt⟩, h_msgs⟩
  · -- Commit case: all RMs decided prepared
    -- Derive that abort ∉ s.msgs: if abort ∈ msgs, h_aid gives decided(rm, aborted),
    -- h_all gives decided(rm, prepared), pcAtMostOneDecision_of_inv gives aborted = prepared.
    have h_no_abort : PCMessage.abort ∉ s.msgs := by
      intro ha
      obtain ⟨rm_abt, hdec_abt⟩ := h_aid ha
      have hdec_prep : decided Majority s rm_abt RMVal.prepared := h_all rm_abt
      have := pcAtMostOneDecision_of_inv Majority h_maj h_2au h_2bs h_p2as
        hdec_abt hdec_prep
      exact absurd this (by intro h; cases h)
    -- Derive that no RM is aborted in s: if rmState r = aborted, h_abi gives
    -- phase2a(r, 0, aborted) ∈ msgs or abort ∈ msgs. The latter contradicts h_no_abort.
    -- For phase2a(r, 0, aborted): h_all gives decided(r, prepared), chain to
    -- phase2a(r, 0, prepared), then phase2aUnique gives aborted = prepared.
    have h_no_abt_rm : ∀ r : RM, s.rmState r ≠ RMState.aborted := by
      intro r hr
      rcases h_abi r hr with h | h
      · -- phase2a(r, 0, aborted) ∈ msgs
        obtain ⟨bp, MSp, hMSp, hvp⟩ := h_all r
        obtain ⟨a, ha, _⟩ := h_maj MSp hMSp MSp hMSp
        have h2a_prep := h_2bs r bp RMVal.prepared a (hvp a ha)
        have h2a_0 := prepared_chains_to_0 r bp h2a_prep
        have := h_2au r 0 RMVal.aborted RMVal.prepared h h2a_0
        exact absurd this (by intro h; cases h)
      · exact h_no_abort h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rwa [pcConsistent, h_rm]
    · intro _ r; rw [h_rm]; exact h_no_abt_rm r
    · intro h r; rw [h_rm]; rw [h_msgs] at h; rcases h with h | h
      · exact h_ac h r
      · exact absurd (Set.mem_singleton_iff.mp h) (by intro h; cases h)
    · intro r h; rw [h_rm] at h; rw [h_msgs]; exact Or.inl (h_cm r h)
    · -- ¬(commit ∧ abort): abort ∉ s.msgs, and we only add commit
      intro ⟨_, ha'⟩; rw [h_msgs] at ha'; rcases ha' with ha' | ha'
      · exact h_no_abort ha'
      · exact absurd (Set.mem_singleton_iff.mp ha') (by intro h; cases h)
    · intro r b v ac h; rw [h_msgs] at h; rcases h with h | h
      · rw [h_msgs]; exact Or.inl (h_2bs r b v ac h)
      · exact absurd (Set.mem_singleton_iff.mp h) (by intro h; cases h)
    · intro r b v₁ v₂ h₁ h₂; rw [h_msgs] at h₁ h₂
      rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
      · exact h_2au r b v₁ v₂ h₁ h₂
      · exact absurd (Set.mem_singleton_iff.mp h₂) (by intro h; cases h)
      · exact absurd (Set.mem_singleton_iff.mp h₁) (by intro h; cases h)
      · exact absurd (Set.mem_singleton_iff.mp h₁) (by intro h; cases h)
    · intro r v hw; rw [h_rm] at hw; rw [h_msgs]; intro h; rcases h with h | h
      · exact h_wn r v hw h
      · exact absurd (Set.mem_singleton_iff.mp h) (by intro h; cases h)
    · -- pcAbortedImpliesPhase2a: rmState unchanged, msgs grow by commit
      intro r ha; rw [h_rm] at ha; rcases h_abi r ha with h | h
      · exact Or.inl (h_msgs ▸ Set.mem_union_left _ h)
      · exact Or.inr (h_msgs ▸ Set.mem_union_left _ h)
    · -- pcAbortMsgImpliesPhase2a: new msg is commit, not abort
      intro ha; rw [h_msgs] at ha; rcases ha with ha | ha
      · obtain ⟨r, b, hp⟩ := h_ami ha
        exact ⟨r, b, h_msgs ▸ Set.mem_union_left _ hp⟩
      · exact absurd (Set.mem_singleton_iff.mp ha) (by intro h; cases h)
    · -- pcCommitNoWorking: rmState unchanged, commit in s'.msgs
      -- All decided prepared ⇒ no RM working (needs cross-ballot for b > 0).
      intro _ r; rw [h_rm]
      intro hw
      -- If rm is working, h_wn says no phase2a at ballot 0.
      -- h_all gives decided prepared, hence phase2a(rm, b, prepared) for some b.
      obtain ⟨bp, MSp, hMSp, hvp⟩ := h_all r
      obtain ⟨a, ha, _⟩ := h_maj MSp hMSp MSp hMSp
      have h2a_prep := h_2bs r bp RMVal.prepared a (hvp a ha)
      -- If b = 0, contradicts h_wn. If b > 0, needs cross-ballot.
      by_cases hbp : bp = 0
      · exact h_wn r RMVal.prepared hw (hbp ▸ h2a_prep)
      · -- b > 0: by pcPreparedHasLowerEvidence, trace back to ballot 0.
        have : ∀ b, PCMessage.phase2a r b RMVal.prepared ∈ s.msgs →
            b > 0 → False := by
          intro b
          induction b using Nat.strongRecOn with
          | _ b ih =>
            intro h2a hb
            obtain ⟨c, hcb, ac', h2b⟩ := h_ple r b h2a hb
            have h2a_c := h_2bs r c RMVal.prepared ac' h2b
            by_cases hc : c = 0
            · exact h_wn r RMVal.prepared hw (hc ▸ h2a_c)
            · exact ih c hcb h2a_c (Nat.pos_of_ne_zero hc)
        exact this bp h2a_prep (Nat.pos_of_ne_zero hbp)
    · -- pcPhase2aSafe: msgs grow by commit (not phase2a/phase2b), aState unchanged
      intro r b v h2a hb
      rw [h_msgs] at h2a; rcases h2a with h2a | h2a
      · obtain ⟨Q, hQ, hQpromise, hQvotes⟩ := h_p2as r b v h2a hb
        refine ⟨Q, hQ, fun ac' hac => ?_, ?_⟩
        · obtain ⟨mb, hmb, bal, val, h1b⟩ := hQpromise ac' hac
          exact ⟨mb, hmb, bal, val, h_msgs ▸ Set.mem_union_left _ h1b⟩
        · rcases hQvotes with hno | ⟨c, hcb, hcv, hcwit, hcgap⟩
          · left; intro ac' hac c' hcb v' hv'
            rw [h_msgs] at hv'; rcases hv' with hv' | hv'
            · exact hno ac' hac c' hcb v' hv'
            · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h)
          · right; exact ⟨c, hcb, fun ac' hac v' hv' => by
              rw [h_msgs] at hv'; rcases hv' with hv' | hv'
              · exact hcv ac' hac v' hv'
              · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h),
              hcwit.imp fun ac ⟨hac, h⟩ => ⟨hac, h_msgs ▸ Set.mem_union_left _ h⟩,
              fun ac' hac d hcd hdb v' hv' => by
              rw [h_msgs] at hv'; rcases hv' with hv' | hv'
              · exact hcgap ac' hac d hcd hdb v' hv'
              · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h)⟩
      · exact absurd (Set.mem_singleton_iff.mp h2a) (by intro h; cases h)
    · -- pcPhase1bSomeFaithful: msgs grow by commit (not phase1b)
      intro r mb c v ac' h1b; rw [h_msgs] at h1b; rcases h1b with h1b | h1b
      · obtain ⟨h1, h2, h3, h4⟩ := h_1bs r mb c v ac' h1b
        exact ⟨h1, h2, h_msgs ▸ Set.mem_union_left _ h3,
          fun c' hc1 hc2 v' hv' => by
            rw [h_msgs] at hv'; rcases hv' with hv' | hv'
            · exact h4 c' hc1 hc2 v' hv'
            · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h)⟩
      · exact absurd (Set.mem_singleton_iff.mp h1b) (by intro h; cases h)
    · -- pcPhase1bNoneFaithful: msgs grow by commit (not phase1b/phase2b)
      intro r mb ac' h1b; rw [h_msgs] at h1b; rcases h1b with h1b | h1b
      · intro c hc v' hv'; rw [h_msgs] at hv'; rcases hv' with hv' | hv'
        · exact h_1bn r mb ac' h1b c hc v' hv'
        · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h)
      · exact absurd (Set.mem_singleton_iff.mp h1b) (by intro h; cases h)
    · -- pcAccStateValid: aState unchanged, msgs grow by commit
      intro r ac'; rw [h_as]
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h_asv r ac'
      refine ⟨h1, fun c hc => ?_, fun c hc1 hc2 v hv => ?_,
        fun hn c hc v hv => ?_, h5,
        fun mb b v h1b => ?_, fun c v hv => ?_⟩
      · obtain ⟨hne, hm⟩ := h2 c hc; exact ⟨hne, h_msgs ▸ Set.mem_union_left _ hm⟩
      · rw [h_msgs] at hv; rcases hv with hv | hv
        · exact h3 c hc1 hc2 v hv
        · exact absurd (Set.mem_singleton_iff.mp hv) (by intro h; cases h)
      · rw [h_msgs] at hv; rcases hv with hv | hv
        · exact h4 hn c hc v hv
        · exact absurd (Set.mem_singleton_iff.mp hv) (by intro h; cases h)
      · rw [h_msgs] at h1b; rcases h1b with h1b | h1b
        · exact h6 mb b v h1b
        · exact absurd (Set.mem_singleton_iff.mp h1b) (by intro h; cases h)
      · rw [h_msgs] at hv; rcases hv with hv | hv
        · exact h7 c v hv
        · exact absurd (Set.mem_singleton_iff.mp hv) (by intro h; cases h)
    · -- pcPhase1bValNone: msgs grow by commit (not phase1b)
      intro r mb b' v ac' h1b; rw [h_msgs] at h1b; rcases h1b with h1b | h1b
      · exact h_1bvn r mb b' v ac' h1b
      · exact absurd (Set.mem_singleton_iff.mp h1b) (by intro h; cases h)
    · -- pcCommitImpliesAllDecidedPrepared: commit may be new or old
      intro hc r; rw [h_msgs] at hc; rcases hc with hc | hc
      · obtain ⟨b, MS, hMS, hv⟩ := h_cid hc r
        exact ⟨b, MS, hMS, fun ac' hac => h_msgs ▸ Set.mem_union_left _ (hv ac' hac)⟩
      · -- New commit msg: h_all gives decided prepared for all rm
        have heq := Set.mem_singleton_iff.mp hc
        obtain ⟨b, MS, hMS, hvp⟩ := h_all r
        exact ⟨b, MS, hMS, fun ac' hac => h_msgs ▸ Set.mem_union_left _ (hvp ac' hac)⟩
    · -- pcAbortImpliesDecidedAborted: abort ∉ s'.msgs in commit case
      intro ha; rw [h_msgs] at ha; rcases ha with ha | ha
      · obtain ⟨r, b, MS, hMS, hv⟩ := h_aid ha
        exact ⟨r, b, MS, hMS, fun ac' hac => h_msgs ▸ Set.mem_union_left _ (hv ac' hac)⟩
      · exact absurd (Set.mem_singleton_iff.mp ha) (by intro h; cases h)
    · -- pcPreparedHasLowerEvidence: msgs grow by commit (not phase2a)
      intro r b h2a hb; rw [h_msgs] at h2a; rcases h2a with h2a | h2a
      · obtain ⟨c, hcb, ac', h2b⟩ := h_ple r b h2a hb
        exact ⟨c, hcb, ac', h_msgs ▸ Set.mem_union_left _ h2b⟩
      · exact absurd (Set.mem_singleton_iff.mp h2a) (by intro h; cases h)
  · -- Abort case: some RM decided aborted
    -- phase2a(r_abt, b_abt, aborted) ∈ s.msgs (from h_abt via h_2bs)
    obtain ⟨b_abt, MS_abt, hMS_abt, hv_abt⟩ := h_abt
    have h_some_abt_phase2a : ∃ rm : RM, ∃ b : ℕ,
        PCMessage.phase2a rm b RMVal.aborted ∈ s.msgs := by
      obtain ⟨a, ha⟩ := (h_maj MS_abt hMS_abt MS_abt hMS_abt)
      exact ⟨r_abt, b_abt, h_2bs r_abt b_abt RMVal.aborted a (hv_abt a ha.1)⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rwa [pcConsistent, h_rm]
    · intro h r; rw [h_rm]; rw [h_msgs] at h; rcases h with h | h
      · exact h_ca h r
      · exact absurd (Set.mem_singleton_iff.mp h) (by intro h; cases h)
    · -- abort → no committed. Adding abort msg. Need: no RM is committed.
      -- If rmState r = committed, then commit ∈ s.msgs (by h_cm).
      -- This requires: commit ∈ s.msgs → all decided prepared → contradiction
      -- with decided aborted via atMostOne. Needs pcCommitMsgImpliesDecided.
      intro _ r; rw [h_rm]; intro hc
      have hcommit := h_cm r hc
      have hdec_prep := h_cid hcommit r_abt
      have hdec_abt : decided Majority s r_abt RMVal.aborted :=
        ⟨b_abt, MS_abt, hMS_abt, hv_abt⟩
      exact absurd (pcAtMostOneDecision_of_inv Majority h_maj h_2au h_2bs h_p2as
        hdec_abt hdec_prep) (by intro h; cases h)
    · intro r h; rw [h_rm] at h; rw [h_msgs]; exact Or.inl (h_cm r h)
    · -- ¬(commit ∧ abort): we add abort; need commit ∉ s.msgs.
      intro ⟨hc, _⟩; rw [h_msgs] at hc; rcases hc with hc | hc
      · -- commit ∈ s.msgs: h_cid gives decided prepared for r_abt,
        -- but h_abt gives decided aborted for r_abt → contradiction
        have hdec_prep := h_cid hc r_abt
        have hdec_abt : decided Majority s r_abt RMVal.aborted :=
          ⟨b_abt, MS_abt, hMS_abt, hv_abt⟩
        exact absurd (pcAtMostOneDecision_of_inv Majority h_maj h_2au h_2bs h_p2as
          hdec_abt hdec_prep) (by intro h; cases h)
      · exact absurd (Set.mem_singleton_iff.mp hc) (by intro h; cases h)
    · intro r b v ac h; rw [h_msgs] at h; rcases h with h | h
      · rw [h_msgs]; exact Or.inl (h_2bs r b v ac h)
      · exact absurd (Set.mem_singleton_iff.mp h) (by intro h; cases h)
    · intro r b v₁ v₂ h₁ h₂; rw [h_msgs] at h₁ h₂
      rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
      · exact h_2au r b v₁ v₂ h₁ h₂
      · exact absurd (Set.mem_singleton_iff.mp h₂) (by intro h; cases h)
      · exact absurd (Set.mem_singleton_iff.mp h₁) (by intro h; cases h)
      · exact absurd (Set.mem_singleton_iff.mp h₁) (by intro h; cases h)
    · intro r v hw; rw [h_rm] at hw; rw [h_msgs]; intro h; rcases h with h | h
      · exact h_wn r v hw h
      · exact absurd (Set.mem_singleton_iff.mp h) (by intro h; cases h)
    · -- pcAbortedImpliesPhase2a: rmState unchanged, msgs grow by abort
      intro r ha; rw [h_rm] at ha; rcases h_abi r ha with h | h
      · exact Or.inl (h_msgs ▸ Set.mem_union_left _ h)
      · exact Or.inr (h_msgs ▸ Set.mem_union_left _ h)
    · -- pcAbortMsgImpliesPhase2a: abort added; use h_some_abt_phase2a
      intro ha; rw [h_msgs] at ha; rcases ha with ha | ha
      · obtain ⟨r, b, hp⟩ := h_ami ha
        exact ⟨r, b, h_msgs ▸ Set.mem_union_left _ hp⟩
      · -- The new msg is abort; use the decided aborted fact
        obtain ⟨r, b, hp⟩ := h_some_abt_phase2a
        exact ⟨r, b, h_msgs ▸ Set.mem_union_left _ hp⟩
    · -- pcCommitNoWorking: rmState unchanged, new msg is abort (not commit)
      intro hc r; rw [h_rm]; rw [h_msgs] at hc; rcases hc with hc | hc
      · exact h_cnw hc r
      · exact absurd (Set.mem_singleton_iff.mp hc) (by intro h; cases h)
    · -- pcPhase2aSafe: msgs grow by abort (not phase2a/phase2b), aState unchanged
      intro r b v h2a hb
      rw [h_msgs] at h2a; rcases h2a with h2a | h2a
      · obtain ⟨Q, hQ, hQpromise, hQvotes⟩ := h_p2as r b v h2a hb
        refine ⟨Q, hQ, fun ac' hac => ?_, ?_⟩
        · obtain ⟨mb, hmb, bal, val, h1b⟩ := hQpromise ac' hac
          exact ⟨mb, hmb, bal, val, h_msgs ▸ Set.mem_union_left _ h1b⟩
        · rcases hQvotes with hno | ⟨c, hcb, hcv, hcwit, hcgap⟩
          · left; intro ac' hac c' hcb v' hv'
            rw [h_msgs] at hv'; rcases hv' with hv' | hv'
            · exact hno ac' hac c' hcb v' hv'
            · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h)
          · right; exact ⟨c, hcb, fun ac' hac v' hv' => by
              rw [h_msgs] at hv'; rcases hv' with hv' | hv'
              · exact hcv ac' hac v' hv'
              · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h),
              hcwit.imp fun ac ⟨hac, h⟩ => ⟨hac, h_msgs ▸ Set.mem_union_left _ h⟩,
              fun ac' hac d hcd hdb v' hv' => by
              rw [h_msgs] at hv'; rcases hv' with hv' | hv'
              · exact hcgap ac' hac d hcd hdb v' hv'
              · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h)⟩
      · exact absurd (Set.mem_singleton_iff.mp h2a) (by intro h; cases h)
    · -- pcPhase1bSomeFaithful: msgs grow by abort (not phase1b)
      intro r mb c v ac' h1b; rw [h_msgs] at h1b; rcases h1b with h1b | h1b
      · obtain ⟨h1, h2, h3, h4⟩ := h_1bs r mb c v ac' h1b
        exact ⟨h1, h2, h_msgs ▸ Set.mem_union_left _ h3,
          fun c' hc1 hc2 v' hv' => by
            rw [h_msgs] at hv'; rcases hv' with hv' | hv'
            · exact h4 c' hc1 hc2 v' hv'
            · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h)⟩
      · exact absurd (Set.mem_singleton_iff.mp h1b) (by intro h; cases h)
    · -- pcPhase1bNoneFaithful: msgs grow by abort (not phase1b/phase2b)
      intro r mb ac' h1b; rw [h_msgs] at h1b; rcases h1b with h1b | h1b
      · intro c hc v' hv'; rw [h_msgs] at hv'; rcases hv' with hv' | hv'
        · exact h_1bn r mb ac' h1b c hc v' hv'
        · exact absurd (Set.mem_singleton_iff.mp hv') (by intro h; cases h)
      · exact absurd (Set.mem_singleton_iff.mp h1b) (by intro h; cases h)
    · -- pcAccStateValid: aState unchanged, msgs grow by abort
      intro r ac'; rw [h_as]
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h_asv r ac'
      refine ⟨h1, fun c hc => ?_, fun c hc1 hc2 v hv => ?_,
        fun hn c hc v hv => ?_, h5,
        fun mb b v h1b => ?_, fun c v hv => ?_⟩
      · obtain ⟨hne, hm⟩ := h2 c hc; exact ⟨hne, h_msgs ▸ Set.mem_union_left _ hm⟩
      · rw [h_msgs] at hv; rcases hv with hv | hv
        · exact h3 c hc1 hc2 v hv
        · exact absurd (Set.mem_singleton_iff.mp hv) (by intro h; cases h)
      · rw [h_msgs] at hv; rcases hv with hv | hv
        · exact h4 hn c hc v hv
        · exact absurd (Set.mem_singleton_iff.mp hv) (by intro h; cases h)
      · rw [h_msgs] at h1b; rcases h1b with h1b | h1b
        · exact h6 mb b v h1b
        · exact absurd (Set.mem_singleton_iff.mp h1b) (by intro h; cases h)
      · rw [h_msgs] at hv; rcases hv with hv | hv
        · exact h7 c v hv
        · exact absurd (Set.mem_singleton_iff.mp hv) (by intro h; cases h)
    · -- pcPhase1bValNone: msgs grow by abort (not phase1b)
      intro r mb b' v ac' h1b; rw [h_msgs] at h1b; rcases h1b with h1b | h1b
      · exact h_1bvn r mb b' v ac' h1b
      · exact absurd (Set.mem_singleton_iff.mp h1b) (by intro h; cases h)
    · -- pcCommitImpliesAllDecidedPrepared: new msg is abort, not commit
      intro hc r; rw [h_msgs] at hc; rcases hc with hc | hc
      · obtain ⟨b, MS, hMS, hv⟩ := h_cid hc r
        exact ⟨b, MS, hMS, fun ac' hac => h_msgs ▸ Set.mem_union_left _ (hv ac' hac)⟩
      · exact absurd (Set.mem_singleton_iff.mp hc) (by intro h; cases h)
    · -- pcAbortImpliesDecidedAborted: abort may be new or old
      intro ha; rw [h_msgs] at ha; rcases ha with ha | ha
      · obtain ⟨r, b, MS, hMS, hv⟩ := h_aid ha
        exact ⟨r, b, MS, hMS, fun ac' hac => h_msgs ▸ Set.mem_union_left _ (hv ac' hac)⟩
      · -- New abort msg: h_abt gives decided aborted for some rm
        exact ⟨r_abt, b_abt, MS_abt, hMS_abt,
          fun ac' hac => h_msgs ▸ Set.mem_union_left _ (hv_abt ac' hac)⟩
    · -- pcPreparedHasLowerEvidence: msgs grow by abort (not phase2a)
      intro r b h2a hb; rw [h_msgs] at h2a; rcases h2a with h2a | h2a
      · obtain ⟨c, hcb, ac', h2b⟩ := h_ple r b h2a hb
        exact ⟨c, hcb, ac', h_msgs ▸ Set.mem_union_left _ h2b⟩
      · exact absurd (Set.mem_singleton_iff.mp h2a) (by intro h; cases h)

-------------------------------------------------------------------------------
-- Inductive step
-------------------------------------------------------------------------------

set_option linter.unusedFintypeInType false in
lemma pcInvariant_step (Majority : Set (Set Acceptor))
    (h_maj : ∀ S₁ ∈ Majority, ∀ S₂ ∈ Majority, (S₁ ∩ S₂).Nonempty)
    (s s' : PCState RM Acceptor) :
    pcInvariant Majority s → pcNext Majority s s' →
    pcInvariant Majority s' := by
  intro h_inv h_next
  rcases h_next with ⟨rm, h_rm⟩ | ⟨bal, rm, h_lr⟩ | h_dec | ⟨acc, h_acc⟩
  · -- RM actions
    rcases h_rm with h | h | h | h
    · exact pcInvariant_rmPrepare Majority rm s s' h_inv h
    · exact pcInvariant_rmChooseToAbort Majority rm s s' h_inv h
    · exact pcInvariant_rmRcvCommitMsg Majority rm s s' h_inv h
    · exact pcInvariant_rmRcvAbortMsg Majority rm s s' h_inv h
  · -- Leader actions
    rcases h_lr with h | h
    · exact pcInvariant_phase1a Majority bal rm s s' h_inv h
    · exact pcInvariant_phase2a Majority bal rm s s' h_inv h
  · -- Decide
    exact pcInvariant_decide Majority h_maj s s' h_inv h_dec
  · -- Acceptor actions
    rcases h_acc with h | h
    · exact pcInvariant_phase1b Majority acc s s' h_inv h
    · exact pcInvariant_phase2b Majority acc s s' h_inv h

-- THEOREM PCSpec => TC!TCSpec  (TLA+ line 280)
-- The Paxos Commit protocol implements the Transaction Commit protocol.
set_option linter.unusedFintypeInType false in
theorem pcSpec (Majority : Set (Set Acceptor))
    (h_maj : ∀ S₁ ∈ Majority, ∀ S₂ ∈ Majority, (S₁ ∩ S₂).Nonempty)
    (s : PCState RM Acceptor) :
    PCReachable Majority s → pcConsistent s := by
  intro h
  suffices pcInvariant Majority s from this.1
  induction h with
  | init => exact pcInvariant_init Majority
  | step h_reach h_next ih => exact pcInvariant_step Majority h_maj _ _ ih h_next
