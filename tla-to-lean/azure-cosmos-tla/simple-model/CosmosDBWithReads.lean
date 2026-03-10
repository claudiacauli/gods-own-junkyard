import CosmosDBProps

/-!
# CosmosDB With Reads

Lean formalization of CosmosDBWithReads.tla.
This extends CosmosDBProps with concrete read operations, adding:
- Read state variables (read result, readKey, ReadConsistency)
- Five read actions (one per consistency level)
- Combined spec: RInit, RNext, RReachable
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.setOption false
set_option linter.flexible false

variable {Key : Type} [DecidableEq Key] [Inhabited Key]
variable {Value : Type} [DecidableEq Value] [Inhabited Value]

/- ================================================================
   Section 1: Extended State with Read Variables
   ================================================================ -/

-- The full system state, extending CosmosWState with read variables
-- (TLA+ line 4: VARIABLES read, readKey, ReadConsistency)
structure CosmosRState (Key Value : Type) where
  wstate : CosmosWState Key Value
  read : ReadResult Value
  readKey : Key
  readConsistency : ConsistencyLevel

/- ================================================================
   Section 2: Read Actions
   ================================================================ -/

-- DoStrongConsistencyRead (TLA+ lines 12-16)
def doStrongConsistencyRead (s s' : CosmosRState Key Value) (key : Key) : Prop :=
  s.readConsistency = ConsistencyLevel.strong
  ∧ readConsistencyOK s.wstate.cosmos.writeConsistencyLevel .strong
  ∧ strongConsistencyRead s.wstate.cosmos key s'.read
  ∧ s'.readKey = key

-- DoBoundedStalenessRead (TLA+ lines 18-21)
def doBoundedStalenessRead (s s' : CosmosRState Key Value) (key : Key) : Prop :=
  s.readConsistency = ConsistencyLevel.boundedStaleness
  ∧ readConsistencyOK s.wstate.cosmos.writeConsistencyLevel .boundedStaleness
  ∧ boundedStalenessRead s.wstate.cosmos key s'.read
  ∧ s'.readKey = key

-- DoSessionConsistencyRead (TLA+ lines 24-29)
-- Note: existentially quantifies over a token in MaybeSessionTokens
-- (epoch ≥ 1 ∨ token = noSessionToken)
def doSessionConsistencyRead (s s' : CosmosRState Key Value) (key : Key) : Prop :=
  s.readConsistency = ConsistencyLevel.session
  ∧ readConsistencyOK s.wstate.cosmos.writeConsistencyLevel .session
  ∧ ∃ token : SessionToken,
      (token.epoch ≥ 1 ∨ token = noSessionToken)
      ∧ sessionConsistencyRead s.wstate.cosmos token key s'.read
  ∧ s'.readKey = key

-- DoConsistentPrefixRead (TLA+ lines 31-35)
def doConsistentPrefixRead (s s' : CosmosRState Key Value) (key : Key) : Prop :=
  s.readConsistency = ConsistencyLevel.consistentPrefix
  ∧ readConsistencyOK s.wstate.cosmos.writeConsistencyLevel .consistentPrefix
  ∧ consistentPrefixRead s.wstate.cosmos key s'.read
  ∧ s'.readKey = key

-- DoEventualConsistencyRead (TLA+ lines 37-41)
def doEventualConsistencyRead (s s' : CosmosRState Key Value) (key : Key) : Prop :=
  s.readConsistency = ConsistencyLevel.eventual
  ∧ readConsistencyOK s.wstate.cosmos.writeConsistencyLevel .eventual
  ∧ eventualConsistencyRead s.wstate.cosmos key s'.read
  ∧ s'.readKey = key

/- ================================================================
   Section 3: Combined Actions and Spec
   ================================================================ -/

-- RInit (TLA+ lines 6-10)
-- ReadConsistency ∈ ConsistencyLevels, readKey ∈ Keys,
-- read = NotFoundReadResult, inner state = WInit
def rInit (wc : ConsistencyLevel) (rc : ConsistencyLevel) (key : Key) :
    CosmosRState Key Value where
  wstate := wInit wc
  read := notFoundReadResult
  readKey := key
  readConsistency := rc

-- RNext (TLA+ lines 43-53)
-- Either a read step (wstate and ReadConsistency unchanged, pick a key and read)
-- or a system step (read/readKey/ReadConsistency unchanged, inner WNext)
def rNext (sb vb : Nat)
    (s s' : CosmosRState Key Value) : Prop :=
  -- Read branch: UNCHANGED varsWithHistory, UNCHANGED ReadConsistency
  (s'.wstate = s.wstate
   ∧ s'.readConsistency = s.readConsistency
   ∧ ∃ key : Key,
       doStrongConsistencyRead s s' key
       ∨ doBoundedStalenessRead s s' key
       ∨ doSessionConsistencyRead s s' key
       ∨ doConsistentPrefixRead s s' key
       ∨ doEventualConsistencyRead s s' key)
  -- System branch: UNCHANGED <<read, readKey, ReadConsistency>>, WNext
  ∨ (s'.read = s.read
     ∧ s'.readKey = s.readKey
     ∧ s'.readConsistency = s.readConsistency
     ∧ wNext sb vb s.wstate s'.wstate)

-- Reachable states for the extended spec with reads
inductive RReachable (wc rc : ConsistencyLevel) (key : Key) (sb vb : Nat) :
    CosmosRState Key Value → Prop where
  | init : RReachable wc rc key sb vb (rInit wc rc key)
  | step {s s'} : RReachable wc rc key sb vb s → rNext sb vb s s' →
      RReachable wc rc key sb vb s'

/- ================================================================
   Section 4: Lifting Infrastructure
   ================================================================ -/

-- The key structural lemma: rNext either preserves wstate or takes a wNext step.
-- This is the foundation for lifting all CosmosWState invariants through rNext.
lemma wstate_rNext {s s' : CosmosRState Key Value} {sb vb : Nat}
    (hn : rNext sb vb s s') :
    s'.wstate = s.wstate ∨ wNext sb vb s.wstate s'.wstate := by
  rcases hn with ⟨h_ws, _, _⟩ | ⟨_, _, _, h_wn⟩
  · left; exact h_ws
  · right; exact h_wn

-- Generic lifting: any invariant on CosmosWState preserved by wNext
-- is preserved by rNext.
theorem lift_wstate_inv {Inv : CosmosWState Key Value → Prop} {sb vb : Nat}
    {s s' : CosmosRState Key Value}
    (h_pres : ∀ ws ws', Inv ws → wNext sb vb ws ws' → Inv ws')
    (hinv : Inv s.wstate)
    (hn : rNext sb vb s s') :
    Inv s'.wstate := by
  rcases wstate_rNext hn with h_eq | h_wn
  · rw [h_eq]; exact hinv
  · exact h_pres _ _ hinv h_wn

/- ================================================================
   Section 5: Lifted State Invariants
   ================================================================ -/

-- typesOK on the inner CosmosState, lifted through rNext.
-- typesOK is preserved by cosmosNext (typesOK_cosmosNext), and wNext
-- wraps cosmosNext, so we need a small bridging lemma.
private lemma typesOK_wNext {s s' : CosmosWState Key Value} {sb vb : Nat}
    (ht : typesOK s.cosmos) (hn : wNext sb vb s s') : typesOK s'.cosmos := by
  rcases hn with ⟨_, h_cn⟩ | h_write
  · exact typesOK_cosmosNext ht h_cn
  · rcases h_write with h_begin | h_succ | h_fail
    · obtain ⟨_, _, _, h_log, _, _, h_ci, h_ep, h_wcl⟩ := h_begin
      obtain ⟨h_e, h_rc, h_cl⟩ := ht
      refine ⟨by rw [h_ep]; exact h_e, by omega, ?_⟩
      rw [h_log]; simp; omega
    · obtain ⟨_, _, _, _, _, h_cosmos⟩ := h_succ; rw [h_cosmos]; exact ht
    · obtain ⟨_, _, _, _, h_cosmos⟩ := h_fail; rw [h_cosmos]; exact ht

theorem typesOK_rNext {s s' : CosmosRState Key Value} {sb vb : Nat}
    (ht : typesOK s.wstate.cosmos) (hn : rNext sb vb s s') :
    typesOK s'.wstate.cosmos := by
  rcases wstate_rNext hn with h_eq | h_wn
  · rw [h_eq]; exact ht
  · exact typesOK_wNext ht h_wn

theorem typesOK_rInit (wc rc : ConsistencyLevel) (key : Key) :
    typesOK (rInit wc rc key : CosmosRState Key Value).wstate.cosmos :=
  typesOK_init wc

-- Inductive: typesOK is an invariant of RReachable
theorem typesOK_rReachable {s : CosmosRState Key Value}
    {wc rc : ConsistencyLevel} {key : Key} {sb vb : Nat}
    (h : RReachable wc rc key sb vb s) : typesOK s.wstate.cosmos := by
  induction h with
  | init => exact typesOK_rInit wc rc key
  | step _ hn ih => exact typesOK_rNext ih hn

-- historyTokensBounded lifted through rNext.
-- Requires historyTokensEpochBounded as a precondition (same as wNext version).
theorem historyTokensBounded_rNext
    {s s' : CosmosRState Key Value} {sb vb : Nat}
    (hinv : historyTokensBounded s.wstate)
    (hinv_ep : historyTokensEpochBounded s.wstate)
    (hn : rNext sb vb s s') :
    historyTokensBounded s'.wstate := by
  rcases wstate_rNext hn with h_eq | h_wn
  · rw [h_eq]; exact hinv
  · exact historyTokensBounded_wNext hinv
      (fun r hr => hinv_ep r hr) h_wn

-- historyTokensEpochBounded lifted through rNext.
theorem historyTokensEpochBounded_rNext
    {s s' : CosmosRState Key Value} {sb vb : Nat}
    (hinv : historyTokensEpochBounded s.wstate)
    (hn : rNext sb vb s s') :
    historyTokensEpochBounded s'.wstate := by
  rcases wstate_rNext hn with h_eq | h_wn
  · rw [h_eq]; exact hinv
  · exact historyTokensEpochBounded_wNext hinv h_wn

-- historyTokensUnique lifted through rNext.
-- Requires historyTokensBounded and historyTokensEpochBounded.
theorem historyTokensUnique_rNext
    {s s' : CosmosRState Key Value} {sb vb : Nat}
    (hinv_u : historyTokensUnique s.wstate)
    (hinv_b : historyTokensBounded s.wstate)
    (hinv_ep : historyTokensEpochBounded s.wstate)
    (hn : rNext sb vb s s') :
    historyTokensUnique s'.wstate := by
  rcases wstate_rNext hn with h_eq | h_wn
  · rw [h_eq]; exact hinv_u
  · exact historyTokensUnique_wNext hinv_u hinv_b hinv_ep h_wn

-- initWriteLogConsistent lifted through rNext.
theorem initWriteLogConsistent_rNext
    {s s' : CosmosRState Key Value} {sb vb : Nat}
    (hinv : initWriteLogConsistent s.wstate)
    (hinv_b : historyTokensBounded s.wstate)
    (hinv_ep : historyTokensEpochBounded s.wstate)
    (hn : rNext sb vb s s') :
    initWriteLogConsistent s'.wstate := by
  rcases wstate_rNext hn with h_eq | h_wn
  · rw [h_eq]; exact hinv
  · exact initWriteLogConsistent_wNext hinv hinv_b hinv_ep h_wn

-- succeededWriteLogConsistent lifted through rNext.
theorem succeededWriteLogConsistent_rNext
    {s s' : CosmosRState Key Value} {sb vb : Nat}
    (hinv : succeededWriteLogConsistent s.wstate)
    (hinv_init : initWriteLogConsistent s.wstate)
    (hinv_tok : wTypesOK s.wstate)
    (hn : rNext sb vb s s') :
    succeededWriteLogConsistent s'.wstate := by
  rcases wstate_rNext hn with h_eq | h_wn
  · rw [h_eq]; exact hinv
  · exact succeededWriteLogConsistent_wNext hinv hinv_init hinv_tok h_wn

-- writeHistoryLogConsistent lifted through rNext.
theorem writeHistoryLogConsistent_rNext
    {s s' : CosmosRState Key Value} {sb vb : Nat}
    (hinv : writeHistoryLogConsistent s.wstate)
    (hn : rNext sb vb s s') :
    writeHistoryLogConsistent s'.wstate := by
  rcases wstate_rNext hn with h_eq | h_wn
  · rw [h_eq]; exact hinv
  · exact writeHistoryLogConsistent_wNext hinv h_wn

-- boundedStalenessIsBounded lifted through rNext.
-- The wNext preservation uses cosmosNext; we need to bridge through wNext.
private lemma boundedStalenessIsBounded_wNext
    {s s' : CosmosWState Key Value} {sb vb : Nat}
    (hinv : boundedStalenessIsBounded sb s.cosmos)
    (hn : wNext sb vb s s') :
    boundedStalenessIsBounded sb s'.cosmos := by
  rcases hn with ⟨_, h_cn⟩ | h_write
  · exact boundedStalenessIsBounded_cosmosNext hinv h_cn
  · rcases h_write with h_begin | h_succ | h_fail
    · -- writeBegin: log extends by 1, commitIndex unchanged.
      -- writesAccepted gives strict < for staleness, so +1 still ≤.
      obtain ⟨_, _, h_wa, h_log, _, _, h_ci, _, h_wcl⟩ := h_begin
      unfold boundedStalenessIsBounded at hinv ⊢
      intro hwc
      unfold writesAccepted at h_wa
      obtain ⟨_, h_sb⟩ := h_wa
      have h_lt := h_sb (by rw [← h_wcl]; exact hwc)
      rw [h_log, h_ci]; simp [List.length_append]; omega
    · obtain ⟨_, _, _, _, _, h_cosmos⟩ := h_succ; rw [h_cosmos]; exact hinv
    · obtain ⟨_, _, _, _, h_cosmos⟩ := h_fail; rw [h_cosmos]; exact hinv

theorem boundedStalenessIsBounded_rNext
    {s s' : CosmosRState Key Value} {sb vb : Nat}
    (hinv : boundedStalenessIsBounded sb s.wstate.cosmos)
    (hn : rNext sb vb s s') :
    boundedStalenessIsBounded sb s'.wstate.cosmos := by
  rcases wstate_rNext hn with h_eq | h_wn
  · rw [h_eq]; exact hinv
  · exact boundedStalenessIsBounded_wNext hinv h_wn

-- versionBoundOK lifted through rNext.
private lemma versionBoundOK_wNext
    {s s' : CosmosWState Key Value} {sb vb : Nat}
    (hinv : versionBoundOK vb s.cosmos)
    (hn : wNext sb vb s s') :
    versionBoundOK vb s'.cosmos := by
  rcases hn with ⟨_, h_cn⟩ | h_write
  · exact versionBoundOK_cosmosNext hinv h_cn
  · rcases h_write with h_begin | h_succ | h_fail
    · obtain ⟨_, _, h_wa, h_log, _, h_ri, _, _, _⟩ := h_begin
      unfold versionBoundOK at hinv ⊢
      unfold writesAccepted at h_wa
      obtain ⟨h_vb, _⟩ := h_wa
      rw [h_log, h_ri]; simp [List.length_append]; omega
    · obtain ⟨_, _, _, _, _, h_cosmos⟩ := h_succ; rw [h_cosmos]; exact hinv
    · obtain ⟨_, _, _, _, h_cosmos⟩ := h_fail; rw [h_cosmos]; exact hinv

theorem versionBoundOK_rNext
    {s s' : CosmosRState Key Value} {sb vb : Nat}
    (hinv : versionBoundOK vb s.wstate.cosmos)
    (hn : rNext sb vb s s') :
    versionBoundOK vb s'.wstate.cosmos := by
  rcases wstate_rNext hn with h_eq | h_wn
  · rw [h_eq]; exact hinv
  · exact versionBoundOK_wNext hinv h_wn

-- wclPreserved (writeConsistencyLevel unchanged) lifted through rNext.
lemma wclPreserved_rNext
    {s s' : CosmosRState Key Value} {sb vb : Nat}
    (hn : rNext sb vb s s') :
    s'.wstate.cosmos.writeConsistencyLevel = s.wstate.cosmos.writeConsistencyLevel := by
  rcases wstate_rNext hn with h_eq | h_wn
  · rw [h_eq]
  · exact wclPreserved_wNext h_wn

-- epochMonotone lifted through rNext.
lemma epochMonotone_rNext
    {s s' : CosmosRState Key Value} {sb vb : Nat}
    (hn : rNext sb vb s s') :
    s.wstate.cosmos.epoch ≤ s'.wstate.cosmos.epoch := by
  rcases wstate_rNext hn with h_eq | h_wn
  · rw [h_eq]
  · exact epochMonotone_wNext h_wn

/- ================================================================
   Section 6: Read Result Well-Formedness
   ================================================================ -/

-- The read result stored in CosmosRState is always well-formed.
-- At init: notFoundReadResult. After a read action: comes from generalReadResult.
-- After a system step: unchanged.

theorem readWellFormed_rInit (wc rc : ConsistencyLevel) (key : Key) :
    readResultWellFormed (rInit wc rc key : CosmosRState Key Value).read := by
  unfold rInit readResultWellFormed notFoundReadResult
  right; rfl

-- Helper: any of the five read actions produces a well-formed result.
-- All read operators go through checkReadConsistency → generalReadResult,
-- which produces well-formed results by generalReadResult_wellFormed.
-- Helper: extract generalReadResult from any of the five read actions,
-- then apply generalReadResult_wellFormed. Each read operator is defined
-- as checkReadConsistency wrapping generalReadResult.
private lemma readWellFormed_of_readAction
    {s s' : CosmosRState Key Value} {key : Key}
    (h : doStrongConsistencyRead s s' key
       ∨ doBoundedStalenessRead s s' key
       ∨ doSessionConsistencyRead s s' key
       ∨ doConsistentPrefixRead s s' key
       ∨ doEventualConsistencyRead s s' key) :
    readResultWellFormed s'.read := by
  rcases h with h | h | h | h | h
  · -- Strong
    obtain ⟨_, _, hr, _⟩ := h
    unfold strongConsistencyRead checkReadConsistency at hr
    exact generalReadResult_wellFormed hr.2
  · -- Bounded
    obtain ⟨_, _, hr, _⟩ := h
    unfold boundedStalenessRead checkReadConsistency at hr
    exact generalReadResult_wellFormed hr.2
  · -- Session: ∃ token extends to end, so readKey is inside the existential
    obtain ⟨_, _, _, _, hr, _⟩ := h
    unfold sessionConsistencyRead checkReadConsistency at hr
    obtain ⟨_, hr⟩ := hr
    split_ifs at hr with hep
    · exact generalReadResult_wellFormed hr
    · exact absurd hr id
  · -- ConsistentPrefix
    obtain ⟨_, _, hr, _⟩ := h
    unfold consistentPrefixRead checkReadConsistency at hr
    exact generalReadResult_wellFormed hr.2
  · -- Eventual
    obtain ⟨_, _, hr, _⟩ := h
    unfold eventualConsistencyRead checkReadConsistency at hr
    exact generalReadResult_wellFormed hr.2

theorem readWellFormed_rNext
    {s s' : CosmosRState Key Value} {sb vb : Nat}
    (hwf : readResultWellFormed s.read)
    (hn : rNext sb vb s s') :
    readResultWellFormed s'.read := by
  rcases hn with ⟨_, _, key, hread⟩ | ⟨h_r, _, _, _⟩
  · exact readWellFormed_of_readAction hread
  · rw [h_r]; exact hwf

-- Inductive: readResultWellFormed is an invariant of RReachable
theorem readWellFormed_rReachable {s : CosmosRState Key Value}
    {wc rc : ConsistencyLevel} {key : Key} {sb vb : Nat}
    (h : RReachable wc rc key sb vb s) : readResultWellFormed s.read := by
  induction h with
  | init => exact readWellFormed_rInit wc rc key
  | step _ hn ih => exact readWellFormed_rNext ih hn

/- ================================================================
   Section 7: Lifted Step Invariants (Temporal Q-Preservation)
   ================================================================ -/

-- All temporal step invariants from CosmosDBProps operate on CosmosWState
-- and are preserved by wNext. Since rNext either keeps wstate unchanged
-- or takes a wNext step, they all lift via the same pattern.

-- SessionTokensUniquelyIdentifyWrites: Q preserved by rNext.
theorem sessionTokensUniquelyIdentifyWrites_rStep
    {s s' : CosmosRState Key Value} {sb vb : Nat}
    {token : SessionToken} {key : Key} {value : Value}
    (hq : sessionTokensUniquelyIdentifyWritesQ s.wstate.cosmos token key value)
    (hn : rNext sb vb s s') :
    sessionTokensUniquelyIdentifyWritesQ s'.wstate.cosmos token key value := by
  rcases wstate_rNext hn with h_eq | h_wn
  · rw [h_eq]; exact hq
  · exact sessionTokensUniquelyIdentifyWrites_step hq h_wn

-- CommitIndexImpliesDurability: Q preserved by rNext.
theorem commitIndexImpliesDurability_rStep
    {s s' : CosmosRState Key Value} {sb vb : Nat}
    {checkpoint : Nat} {pfx : List (LogEntry Key Value)}
    (hq : commitIndexImpliesDurabilityQ s.wstate.cosmos checkpoint pfx)
    (htok : typesOK s.wstate.cosmos)
    (hn : rNext sb vb s s') :
    commitIndexImpliesDurabilityQ s'.wstate.cosmos checkpoint pfx := by
  rcases wstate_rNext hn with h_eq | h_wn
  · rw [h_eq]; exact hq
  · exact commitIndexImpliesDurability_step hq htok h_wn

-- StrongConsistencyCommittedWritesDurable: Q preserved by rNext.
theorem strongConsistencyCommittedWritesDurable_rStep
    {s s' : CosmosRState Key Value} {sb vb : Nat}
    {token : SessionToken} {key : Key}
    (hq : strongConsistencyCommittedWritesDurableQ s.wstate token key)
    (hn : rNext sb vb s s') :
    strongConsistencyCommittedWritesDurableQ s'.wstate token key := by
  rcases wstate_rNext hn with h_eq | h_wn
  · rw [h_eq]; exact hq
  · exact strongConsistencyCommittedWritesDurable_step hq h_wn

-- SessionReadMyWrites: Q preserved by rNext.
theorem sessionReadMyWrites_rStep
    {s s' : CosmosRState Key Value} {sb vb : Nat}
    {token1 : SessionToken} {key : Key} {value : Value}
    (hq : sessionReadMyWritesQ s.wstate token1 key value)
    (hn : rNext sb vb s s') :
    sessionReadMyWritesQ s'.wstate token1 key value := by
  rcases wstate_rNext hn with h_eq | h_wn
  · rw [h_eq]; exact hq
  · exact sessionReadMyWrites_step hq h_wn

-- SessionTokenValidEpoch: Q preserved by rNext.
theorem sessionTokenValidEpoch_rStep
    {s s' : CosmosRState Key Value} {sb vb : Nat}
    {token : SessionToken}
    (hq : sessionTokenValidEpochQ s.wstate.cosmos token)
    (hn : rNext sb vb s s') :
    sessionTokenValidEpochQ s'.wstate.cosmos token := by
  rcases wstate_rNext hn with h_eq | h_wn
  · rw [h_eq]; exact hq
  · exact sessionTokenValidEpoch_step hq h_wn

-- SessionTokenInvalid: Q preserved by rNext.
theorem sessionTokenInvalid_rStep
    {s s' : CosmosRState Key Value} {sb vb : Nat}
    {token : SessionToken}
    (hq : sessionTokenInvalidQ s.wstate.cosmos token)
    (hn : rNext sb vb s s') :
    sessionTokenInvalidQ s'.wstate.cosmos token := by
  rcases wstate_rNext hn with h_eq | h_wn
  · rw [h_eq]; exact hq
  · exact sessionTokenInvalid_step hq h_wn

/- ================================================================
   Section 8: Liveness — WritesEventuallyComplete
   ================================================================ -/

-- Lift writeCompleteForToken to CosmosRState: a system-branch rNext step
-- where the inner wNext completes our token.
def writeCompleteForTokenR (token : SessionToken)
    (s s' : CosmosRState Key Value) : Prop :=
  s'.read = s.read
  ∧ s'.readKey = s.readKey
  ∧ s'.readConsistency = s.readConsistency
  ∧ writeCompleteForToken token s.wstate s'.wstate

-- Lift writeInitiated and writeCompleted to CosmosRState.
def writeInitiatedR (token : SessionToken)
    (s : CosmosRState Key Value) : Prop :=
  writeInitiated token s.wstate

def writeCompletedR (token : SessionToken)
    (s : CosmosRState Key Value) : Prop :=
  writeCompleted token s.wstate

-- writeCompleteForTokenR is a special case of rNext (system branch).
lemma writeCompleteForTokenR_is_rNext {token : SessionToken} {sb vb : Nat}
    {s s' : CosmosRState Key Value}
    (h : writeCompleteForTokenR token s s') :
    rNext sb vb s s' := by
  obtain ⟨h_r, h_rk, h_rc, h_wc⟩ := h
  right
  refine ⟨h_r, h_rk, h_rc, ?_⟩
  -- writeCompleteForToken is writeSuccess ∨ writeFail, both are writeOps.
  -- wNext = stateOps ∨ writeOps, writeOps = writeBegin ∨ writeSuccess ∨ writeFail
  rcases h_wc with ⟨record, h_mem, h_init, h_tok, h_wcs, h_wh, h_cosmos⟩ |
                   ⟨record, h_mem, h_init, h_tok, h_wh, h_cosmos⟩
  · exact Or.inr (Or.inr (Or.inl ⟨record, h_mem, h_init, h_wcs, h_wh, h_cosmos⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨record, h_mem, h_init, h_wh, h_cosmos⟩))

-- Premise 1: P (writeInitiatedR) enables the token-specific action.
theorem writesCompleteR_enabled
    {token : SessionToken}
    (s : CosmosRState Key Value)
    (hp : writeInitiatedR token s) :
    enabled (writeCompleteForTokenR token) s := by
  obtain ⟨record, h_mem, h_tok, h_init⟩ := hp
  -- Construct successor: fail the record, keep read/readKey/readConsistency
  refine ⟨⟨⟨s.wstate.cosmos,
    (⟨record.token, record.key, record.value, .failed⟩ :
      WriteHistoryEntry Key Value) ::ₘ (s.wstate.writeHistory.erase record)⟩,
    s.read, s.readKey, s.readConsistency⟩, ?_⟩
  exact ⟨rfl, rfl, rfl, Or.inr ⟨record, h_mem, h_init, h_tok, rfl, rfl⟩⟩

-- Premise 2: when the action fires AND P holds, Q holds.
theorem writesCompleteR_achieves
    {token : SessionToken}
    (s s' : CosmosRState Key Value)
    (_hp : writeInitiatedR token s)
    (hact : writeCompleteForTokenR token s s') :
    writeCompletedR token s' := by
  obtain ⟨_, _, _, h_wc⟩ := hact
  exact writesComplete_achieves s.wstate s'.wstate _hp h_wc

-- Premise 3: non-action steps preserve P.
-- Read branch: wstate unchanged, so writeInitiated preserved.
-- System branch without our token: writesComplete_persist applies.
theorem writesCompleteR_persist
    {token : SessionToken} {sb vb : Nat}
    (s s' : CosmosRState Key Value)
    (hp : writeInitiatedR token s)
    (hn : rNext sb vb s s')
    (hna : ¬writeCompleteForTokenR token s s') :
    writeInitiatedR token s' := by
  rcases hn with ⟨h_ws, _, _⟩ | ⟨h_r, h_rk, h_rc, h_wn⟩
  · -- Read branch: wstate unchanged
    unfold writeInitiatedR; rw [h_ws]; exact hp
  · -- System branch: show ¬writeCompleteForToken on wstate
    have hna_w : ¬writeCompleteForToken token s.wstate s'.wstate := by
      intro h_wc; exact hna ⟨h_r, h_rk, h_rc, h_wc⟩
    exact writesComplete_persist s.wstate s'.wstate hp h_wn hna_w

-- The main liveness theorem: WritesEventuallyComplete for rNext traces.
-- Under weak fairness of writeCompleteForTokenR, any initiated write
-- eventually completes.
theorem writesEventuallyCompleteR
    {sb vb : Nat} {token : SessionToken}
    {σ : Trace (CosmosRState Key Value)}
    (h_exec : ∀ n, rNext sb vb (σ n) (σ (n + 1)))
    (h_fair : weakFair (writeCompleteForTokenR token) σ) :
    leadsTo (writeInitiatedR token) (writeCompletedR token) σ :=
  leadsTo_by_wf1 h_exec h_fair
    (fun s hp => writesCompleteR_enabled s hp)
    (fun s s' hp hact => writesCompleteR_achieves s s' hp hact)
    (fun s s' hp hn hna => Or.inl (writesCompleteR_persist s s' hp hn hna))

/- ================================================================
   Section 9: Composite Read-Correctness Theorems

   These are the "payoff" theorems: properties of the read operators
   and stored read results in RReachable states. They compose the
   lifted invariants (Section 5), temporal Q-preservation (Section 7),
   and the read derivation theorems from CosmosDBProps.

   Subsection A: Universal properties (hold for any CosmosState)
   Subsection B: Invariant-dependent properties
   Subsection C: Read consequences of temporal Q's
   Subsection D: Step invariants lifted through rNext
   ================================================================ -/

/- ---- Subsection A: Universal read properties ----
   These hold for any state — no reachability needed.
   We state them at the RReachable level for completeness. -/

-- Strong reads are deterministic: same state, same key → same result.
theorem strongConsistencyReadsConsistent_rReachable
    {s : CosmosRState Key Value}
    {wc rc : ConsistencyLevel} {key : Key} {sb vb : Nat}
    (_h : RReachable wc rc key sb vb s) :
    strongConsistencyReadsConsistent s.wstate.cosmos :=
  strongConsistencyReadsConsistent_holds s.wstate.cosmos

-- Strong reads return the latest committed value for the key.
-- No committed entry for the key can have a higher index than the read result.
theorem strongConsistencyReadsGiveLatestDurableValue_rReachable
    {s : CosmosRState Key Value}
    {wc rc : ConsistencyLevel} {key : Key} {sb vb : Nat}
    (_h : RReachable wc rc key sb vb s) :
    strongConsistencyReadsGiveLatestDurableSCValue s.wstate.cosmos :=
  strongConsistencyReadsGiveLatestDurableSCValue_holds s.wstate.cosmos

-- Eventual consistency reads are exactly consistent prefix reads
-- (when both consistency levels are valid).
theorem eventualReadsEquivConsistentPrefix_rReachable
    {s : CosmosRState Key Value}
    {wc rc : ConsistencyLevel} {key : Key} {sb vb : Nat}
    (_h : RReachable wc rc key sb vb s) :
    eventuallyConsistentReadsEquivalentToConsistentPrefix s.wstate.cosmos :=
  eventualReadsEquivConsistentPrefix s.wstate.cosmos

-- All five read operators produce well-formed results and valid session tokens.
theorem strongConsistencyReadsOK_rReachable
    {s : CosmosRState Key Value}
    {wc rc : ConsistencyLevel} {key : Key} {sb vb : Nat}
    (_h : RReachable wc rc key sb vb s) :
    strongConsistencyReadsOK s.wstate.cosmos :=
  strongConsistencyReadsOK_holds s.wstate.cosmos

theorem boundedStalenessReadsOK_rReachable
    {s : CosmosRState Key Value}
    {wc rc : ConsistencyLevel} {key : Key} {sb vb : Nat}
    (_h : RReachable wc rc key sb vb s) :
    boundedStalenessReadsOK s.wstate.cosmos :=
  boundedStalenessReadsOK_holds s.wstate.cosmos

theorem sessionConsistencyReadsOK_rReachable
    {s : CosmosRState Key Value}
    {wc rc : ConsistencyLevel} {key : Key} {sb vb : Nat}
    (_h : RReachable wc rc key sb vb s) :
    sessionConsistencyReadsOK s.wstate.cosmos :=
  sessionConsistencyReadsOK_holds s.wstate.cosmos

theorem consistentPrefixReadsOK_rReachable
    {s : CosmosRState Key Value}
    {wc rc : ConsistencyLevel} {key : Key} {sb vb : Nat}
    (_h : RReachable wc rc key sb vb s) :
    consistentPrefixReadsOK s.wstate.cosmos :=
  consistentPrefixReadsOK_holds s.wstate.cosmos

theorem eventualConsistencyReadsOK_rReachable
    {s : CosmosRState Key Value}
    {wc rc : ConsistencyLevel} {key : Key} {sb vb : Nat}
    (_h : RReachable wc rc key sb vb s) :
    eventualConsistencyReadsOK s.wstate.cosmos :=
  eventualConsistencyReadsOK_holds s.wstate.cosmos

-- Session tokens from reads are always acquirable.
theorem sessionTokenAlwaysAcquirableRead_rReachable
    {s : CosmosRState Key Value}
    {wc rc : ConsistencyLevel} {key : Key} {sb vb : Nat}
    (_h : RReachable wc rc key sb vb s) :
    sessionTokenAlwaysAcquirableRead s.wstate.cosmos :=
  sessionTokenAlwaysAcquirableRead_holds s.wstate.cosmos

-- The write init token is always acquirable at session consistency.
theorem sessionTokenAlwaysAcquirableWrite_rReachable
    {s : CosmosRState Key Value}
    {wc rc : ConsistencyLevel} {key : Key} {sb vb : Nat}
    (_h : RReachable wc rc key sb vb s) :
    sessionTokenAlwaysAcquirableWrite s.wstate.cosmos :=
  sessionTokenAlwaysAcquirableWrite_holds s.wstate.cosmos

-- Session tokens are valid (produce non-empty reads) when epoch matches.
theorem sessionTokenWhenValid_rReachable
    {s : CosmosRState Key Value}
    {wc rc : ConsistencyLevel} {key : Key} {sb vb : Nat}
    (_h : RReachable wc rc key sb vb s) :
    sessionTokenWhenValid s.wstate.cosmos :=
  sessionTokenWhenValid_holds s.wstate.cosmos

/- ---- Subsection B: Invariant-dependent read properties ---- -/

-- Strong reads reflect all successful writes: no succeeded write can have
-- a checkpoint beyond the read's logIndex. Requires succeededWriteLogConsistent,
-- which we establish from RReachable.
-- Combined invariant bundle for RReachable, proven by single induction.
-- This avoids repeating the induction for each invariant in the dependency chain.
private theorem writeInvariants_rReachable
    {s : CosmosRState Key Value}
    {wc rc : ConsistencyLevel} {key : Key} {sb vb : Nat}
    (h : RReachable wc rc key sb vb s) :
    historyTokensEpochBounded s.wstate
    ∧ historyTokensBounded s.wstate
    ∧ initWriteLogConsistent s.wstate
    ∧ succeededWriteLogConsistent s.wstate := by
  induction h with
  | init =>
    exact ⟨historyTokensEpochBounded_init wc,
           historyTokensBounded_init wc,
           initWriteLogConsistent_init wc,
           succeededWriteLogConsistent_init wc⟩
  | step _ hn ih =>
    obtain ⟨h_ep, h_b, h_init, h_succ⟩ := ih
    exact ⟨historyTokensEpochBounded_rNext h_ep hn,
           historyTokensBounded_rNext h_b h_ep hn,
           initWriteLogConsistent_rNext h_init h_b h_ep hn,
           succeededWriteLogConsistent_rNext h_succ h_init
             (typesOK_rReachable (by assumption)) hn⟩

theorem strongConsistencyReadsGiveLatestSuccessfulWrite_rReachable
    {s : CosmosRState Key Value}
    {wc rc : ConsistencyLevel} {key : Key} {sb vb : Nat}
    (h : RReachable wc rc key sb vb s) :
    strongConsistencyReadsGiveLatestSuccessfulWrite s.wstate :=
  strongConsistencyReadsGiveLatestSuccessfulWrite_holds
    (writeInvariants_rReachable h).2.2.2

/- ---- Subsection C: Read consequences of temporal Q's ----
   These connect the temporal step invariant Q (preserved by rNext,
   Section 7) to actual read guarantees. The pattern:
   Q holds → read operator constrained. -/

-- Strong consistency committed writes are durable: once Q holds (write committed
-- with strong consistency), any future strong read returns logIndex ≥ checkpoint.
-- This is the "read derivation" from the temporal Q.
theorem strongConsistencyCommittedWritesDurable_reads_R
    {s : CosmosRState Key Value}
    {token : SessionToken} {key : Key}
    (hq : strongConsistencyCommittedWritesDurableQ s.wstate token key) :
    s.wstate.cosmos.writeConsistencyLevel = .strong
    ∧ (∃ record : WriteHistoryEntry Key Value,
        record ∈ s.wstate.writeHistory ∧ record.token = token
        ∧ ∀ r : ReadResult Value, strongConsistencyRead s.wstate.cosmos record.key r →
            token.checkpoint ≤ r.logIndex) :=
  strongConsistencyCommittedWritesDurable_reads hq

-- Session read-my-writes: once Q holds (write committed in the session),
-- any future session read with a ≥ token returns logIndex ≥ checkpoint.
theorem sessionReadMyWrites_reads_R
    {s : CosmosRState Key Value}
    {token1 token2 : SessionToken} {key : Key} {value : Value}
    (hq : sessionReadMyWritesQ s.wstate token1 key value)
    (h_leq : sessionTokenLEQ token1 token2)
    (h_tok1_pos : token1.epoch ≥ 1 ∨ token1 = noSessionToken) :
    readConsistencyOK s.wstate.cosmos.writeConsistencyLevel .session
    ∧ ∀ r : ReadResult Value, sessionConsistencyRead s.wstate.cosmos token2 key r →
        readsLEQ ⟨token1.checkpoint, some value⟩ r :=
  sessionReadMyWrites_reads hq h_leq h_tok1_pos

-- Session token stays invalid: once Q holds (token's epoch has been surpassed),
-- session reads with that token are impossible.
theorem sessionTokenStaysInvalid_reads_R
    {s : CosmosRState Key Value}
    {token : SessionToken} {key : Key}
    (hq : sessionTokenInvalidQ s.wstate.cosmos token) :
    readConsistencyOK s.wstate.cosmos.writeConsistencyLevel .session
    ∧ ∀ r, ¬sessionConsistencyRead s.wstate.cosmos token key r :=
  sessionTokenStaysInvalid_reads hq

/- ---- Subsection D: Step invariants lifted through rNext ----
   Strong consistency reads are monotonic across rNext steps.
   Read branch: cosmos unchanged, trivially monotonic.
   System branch: either cosmosNext (use existing theorem) or
   write ops (cosmos unchanged for success/fail; for writeBegin,
   the new entry is beyond commitIndex and invisible to strong reads). -/

-- Strong consistency reads are monotonic across rNext.
-- Between consecutive states, strong reads never return a lower logIndex.
-- Strong reads monotonic through wNext: stateOps uses cosmosNext theorem,
-- writeBegin extends log beyond commitIndex (invisible to no-dirty reads),
-- writeSuccess/writeFail leave cosmos unchanged.
private lemma strongConsistencyReadsMonotonic_wNext
    {ws ws' : CosmosWState Key Value} {sb vb : Nat}
    (ht : typesOK ws.cosmos) (hn : wNext sb vb ws ws') :
    strongConsistencyReadsMonotonic ws.cosmos ws'.cosmos := by
  rcases hn with ⟨_, h_cn⟩ | h_write
  · exact strongConsistencyReadsMonotonic_cosmosNext ht h_cn
  · rcases h_write with h_begin | h_succ | h_fail
    · -- writeBegin: log extends, commitIndex unchanged.
      -- New entry at log.length + 1 > commitIndex, invisible to strong reads.
      obtain ⟨_, _, _, h_log, _, h_ri, h_ci, h_ep, h_wcl⟩ := h_begin
      unfold strongConsistencyReadsMonotonic
      intro hrc key r1 r2 hr1 hr2
      unfold strongConsistencyRead checkReadConsistency at hr1 hr2
      obtain ⟨_, hr1⟩ := hr1; obtain ⟨_, hr2⟩ := hr2
      -- r2 uses s'.commitIndex = s.commitIndex on the extended log.
      -- Entries at indices ≤ commitIndex are unchanged (log only appended).
      -- So generalReadResult gives the same result as on the old log.
      rw [h_ci] at hr2
      have h_ci_len : ws.cosmos.commitIndex ≤ ws.cosmos.log.length := ht.2.2
      have h_ci_len' : ws.cosmos.commitIndex ≤ ws'.cosmos.log.length := by
        rw [h_log]; simp; omega
      have hr1' : generalReadResult ws'.cosmos key ws.cosmos.commitIndex false r1 :=
        generalReadResult_nodirty_log_prefix h_ci_len h_ci_len' (fun j hj hj_len _ => by
          rw [h_log]
          simp only [List.getElem!_eq_getElem?_getD]
          rw [List.getElem?_append_left (by omega)]) hr1
      unfold readsLEQ
      exact le_of_eq (congrArg ReadResult.logIndex
        (generalReadResult_nodirty_unique hr1' hr2))
    · -- writeSuccess: cosmos unchanged, strong reads unique → equal
      obtain ⟨_, _, _, _, _, h_cosmos⟩ := h_succ
      rw [h_cosmos]; intro _ _ r1 r2 hr1 hr2
      unfold strongConsistencyRead checkReadConsistency at hr1 hr2
      exact le_of_eq (congrArg ReadResult.logIndex
        (generalReadResult_nodirty_unique hr1.2 hr2.2))
    · -- writeFail: cosmos unchanged
      obtain ⟨_, _, _, _, h_cosmos⟩ := h_fail
      rw [h_cosmos]; intro _ _ r1 r2 hr1 hr2
      unfold strongConsistencyRead checkReadConsistency at hr1 hr2
      exact le_of_eq (congrArg ReadResult.logIndex
        (generalReadResult_nodirty_unique hr1.2 hr2.2))

theorem strongConsistencyReadsMonotonic_rNext
    {s s' : CosmosRState Key Value} {sb vb : Nat}
    (ht : typesOK s.wstate.cosmos) (hn : rNext sb vb s s') :
    strongConsistencyReadsMonotonic s.wstate.cosmos s'.wstate.cosmos := by
  rcases wstate_rNext hn with h_eq | h_wn
  · rw [h_eq]; intro _ _ r1 r2 hr1 hr2
    unfold strongConsistencyRead checkReadConsistency at hr1 hr2
    exact le_of_eq (congrArg ReadResult.logIndex
      (generalReadResult_nodirty_unique hr1.2 hr2.2))
  · exact strongConsistencyReadsMonotonic_wNext ht h_wn
