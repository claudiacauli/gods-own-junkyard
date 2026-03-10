import CosmosDB
import Temporal
import Mathlib.Data.Multiset.Basic

/-!
# CosmosDB Properties - Write Lifecycle

Lean formalization of the write lifecycle from CosmosDBProps.tla.
This extends CosmosDB with:
- Write states (init, succeeded, failed)
- Write history tracking as a multiset (TLA+ Bag)
- Write actions: WriteBegin, WriteSuccess, WriteFail
- Combined spec: WInit, WNext, WReachable
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.setOption false
set_option linter.flexible false

variable {Key : Type} [DecidableEq Key] [Inhabited Key]
variable {Value : Type} [DecidableEq Value] [Inhabited Value]

/- ================================================================
   Section 1: Write States and History
   ================================================================ -/

-- Write states (TLA+ lines 4-12)
inductive WriteState where
  | init
  | succeeded
  | failed
  deriving DecidableEq

-- Write history entry (TLA+ lines 14-19)
structure WriteHistoryEntry (Key Value : Type) where
  token : SessionToken
  key : Key
  value : Value
  state : WriteState
  deriving DecidableEq

/- ================================================================
   Section 2: Extended State with Write History
   ================================================================ -/

-- The full system state, extending CosmosState with writeHistory (TLA+ lines 33-34)
-- writeHistory is modeled as a Multiset (TLA+ Bag)
structure CosmosWState (Key Value : Type) where
  cosmos : CosmosState Key Value
  writeHistory : Multiset (WriteHistoryEntry Key Value)

/- ================================================================
   Section 3: Type Invariant
   ================================================================ -/

-- WTypesOK (TLA+ lines 36-40)
def wTypesOK (s : CosmosWState Key Value) : Prop :=
  typesOK s.cosmos

/- ================================================================
   Section 4: Write Actions
   ================================================================ -/

-- WriteBegin (TLA+ lines 46-60)
-- A write begins: appends to log, records in history as init or succeeded.
-- The token is computed from the pre-write state (checkpoint = Len(log) + 1).
def writeBegin (stalenessBound versionBound : Nat)
    (s s' : CosmosWState Key Value) : Prop :=
  ∃ key : Key, ∃ value : Value,
  let token := writeInitToken s.cosmos
  let mkEntry (ws : WriteState) : WriteHistoryEntry Key Value :=
    ⟨token, key, value, ws⟩
  -- WritesAccepted
  writesAccepted stalenessBound versionBound s.cosmos
  -- WriteInit: append to log
  ∧ s'.cosmos.log = s.cosmos.log ++ [⟨key, value⟩]
  -- Either WriteCanSucceed and record as succeeded, or just record as init
  ∧ ((writeCanSucceed s.cosmos token
      ∧ s'.writeHistory = mkEntry .succeeded ::ₘ s.writeHistory)
     ∨ s'.writeHistory = mkEntry .init ::ₘ s.writeHistory)
  -- UNCHANGED readIndex, commitIndex, epoch, WriteConsistencyLevel
  ∧ s'.cosmos.readIndex = s.cosmos.readIndex
  ∧ s'.cosmos.commitIndex = s.cosmos.commitIndex
  ∧ s'.cosmos.epoch = s.cosmos.epoch
  ∧ s'.cosmos.writeConsistencyLevel = s.cosmos.writeConsistencyLevel

-- WriteSuccess (TLA+ lines 65-72)
-- An in-progress write succeeds: transitions record from init to succeeded.
def writeSuccess (s s' : CosmosWState Key Value) : Prop :=
  ∃ record : WriteHistoryEntry Key Value,
  record ∈ s.writeHistory
  ∧ record.state = WriteState.init
  ∧ writeCanSucceed s.cosmos record.token
  ∧ s'.writeHistory =
      (⟨record.token, record.key, record.value, .succeeded⟩ :
        WriteHistoryEntry Key Value) ::ₘ (s.writeHistory.erase record)
  ∧ s'.cosmos = s.cosmos

-- WriteFail (TLA+ lines 76-82)
-- An in-progress write fails: transitions record from init to failed.
-- Can happen at any time for any reason (no precondition beyond state = init).
def writeFail (s s' : CosmosWState Key Value) : Prop :=
  ∃ record : WriteHistoryEntry Key Value,
  record ∈ s.writeHistory
  ∧ record.state = WriteState.init
  ∧ s'.writeHistory =
      (⟨record.token, record.key, record.value, .failed⟩ :
        WriteHistoryEntry Key Value) ::ₘ (s.writeHistory.erase record)
  ∧ s'.cosmos = s.cosmos

/- ================================================================
   Section 5: Combined Actions and Spec
   ================================================================ -/

-- StateOps (TLA+ lines 84-86): internal state changes, history unchanged
def stateOps (s s' : CosmosWState Key Value) : Prop :=
  s'.writeHistory = s.writeHistory
  ∧ cosmosNext s.cosmos s'.cosmos

-- WriteOps (TLA+ lines 88-91)
def writeOps (stalenessBound versionBound : Nat)
    (s s' : CosmosWState Key Value) : Prop :=
  writeBegin stalenessBound versionBound s s'
  ∨ writeSuccess s s'
  ∨ writeFail s s'

-- WInit (TLA+ lines 93-95)
def wInit (wc : ConsistencyLevel) : CosmosWState Key Value where
  cosmos := cosmosInit wc
  writeHistory := 0

-- WNext (TLA+ lines 97-99)
def wNext (stalenessBound versionBound : Nat)
    (s s' : CosmosWState Key Value) : Prop :=
  stateOps s s'
  ∨ writeOps stalenessBound versionBound s s'

-- Reachable states for the extended spec
inductive WReachable (wc : ConsistencyLevel) (sb vb : Nat) :
    CosmosWState Key Value → Prop where
  | init : WReachable wc sb vb (wInit wc)
  | step {s s'} : WReachable wc sb vb s → wNext sb vb s s' → WReachable wc sb vb s'

/- ================================================================
   Section 6: Helper Predicates
   ================================================================ -/

-- A ReadResult is well-formed: either a valid result or NotFound (TLA+ lines 120-132)
-- In TLA+, ValidReadResults have logIndex ∈ LogIndices (> 0) and value ∈ Values.
def readResultWellFormed (r : ReadResult Value) : Prop :=
  (r.logIndex > 0 ∧ ∃ v, r.value = some v) ∨ r = notFoundReadResult

-- ReadsOK (TLA+ lines 122-127)
-- Read results are well-formed and yield valid session tokens.
def readsOK (s : CosmosState Key Value)
    (read : Key → ReadResult Value → Prop) : Prop :=
  ∀ key : Key, ∀ r : ReadResult Value, read key r →
    readResultWellFormed r
    ∧ sessionTokenIsValid s (updateTokenFromRead s noSessionToken r)

-- ObsoleteValues (TLA+ lines 224-228)
-- A value is obsolete for a key if it appears in the log at or before readIndex,
-- but a later entry for the same key also exists at or before readIndex.
def obsoleteValue (s : CosmosState Key Value) (key : Key) (v : Value) : Prop :=
  ∃ i, i > 0 ∧ i ≤ s.readIndex ∧ i ≤ s.log.length
    ∧ (s.log[i - 1]!).key = key
    ∧ (s.log[i - 1]!).value = v
    ∧ ∃ j, j > i ∧ j ≤ s.readIndex ∧ j ≤ s.log.length
        ∧ (s.log[j - 1]!).key = key

-- FollowsReadIndex (TLA+ lines 262-265)
-- No read should return a value that is obsolete.
-- Note: the TLA+ spec compares bare values with ReadResult records (a type
-- mismatch that makes the property vacuously true). We model the intended
-- semantics: no read result's value field should be an obsolete value.
def followsReadIndex (s : CosmosState Key Value)
    (read : Key → ReadResult Value → Prop) : Prop :=
  ∀ key : Key, ∀ v : Value, obsoleteValue s key v →
    ∀ r, read key r → r.value ≠ some v

-- IsConsistent (TLA+ lines 253-255)
-- At most one possible read result per key (cardinality ∈ {0, 1}).
def isConsistent (read : Key → ReadResult Value → Prop) : Prop :=
  ∀ key : Key, ∀ r1 r2 : ReadResult Value,
    read key r1 → read key r2 → r1 = r2

-- IsLowMonotonic (TLA+ lines 236-243) — step invariant
-- The minimum read result (by logIndex) advances monotonically between states.
-- If both reads are non-empty, the minimum of the current state ≤ the minimum
-- of the next state. Vacuously true if either read set is empty.
def isLowMonotonic
    (read : CosmosState Key Value → Key → ReadResult Value → Prop)
    (s s' : CosmosState Key Value) : Prop :=
  ∀ key : Key,
  ∀ low, read s key low → (∀ r, read s key r → readsLEQ low r) →
  ∀ low', read s' key low' → (∀ r, read s' key r → readsLEQ low' r) →
  readsLEQ low low'

/- ================================================================
   Section 7: Type-like Invariants
   ================================================================ -/

-- PointsValid (TLA+ lines 115-118) — step invariant
-- readIndex ≤ commitIndex, and both increase monotonically.
def pointsValid (s s' : CosmosState Key Value) : Prop :=
  s.readIndex ≤ s.commitIndex
  ∧ s.readIndex ≤ s'.readIndex
  ∧ s.commitIndex ≤ s'.commitIndex

-- NewSessionTokensOK (TLA+ lines 129-130)
-- All acquirable session tokens have epoch ≥ 1 (i.e., are in SessionTokens).
def newSessionTokensOK (s : CosmosState Key Value) : Prop :=
  ∀ token, acquirableSessionToken s token → token.epoch ≥ 1

-- StrongConsistencyReadsOK (TLA+ lines 132-134)
def strongConsistencyReadsOK (s : CosmosState Key Value) : Prop :=
  readConsistencyOK s.writeConsistencyLevel .strong →
  readsOK s (strongConsistencyRead s)

-- BoundedStalenessReadsOK (TLA+ lines 136-138)
def boundedStalenessReadsOK (s : CosmosState Key Value) : Prop :=
  readConsistencyOK s.writeConsistencyLevel .boundedStaleness →
  readsOK s (boundedStalenessRead s)

-- SessionConsistencyReadsOK (TLA+ lines 140-147)
-- Session reads are well-formed, and session tokens advance through reads.
def sessionConsistencyReadsOK (s : CosmosState Key Value) : Prop :=
  readConsistencyOK s.writeConsistencyLevel .session →
  ∀ token : SessionToken,
    (token.epoch ≥ 1 ∨ token = noSessionToken) →
    readsOK s (sessionConsistencyRead s token)
    ∧ ∀ key : Key, ∀ r : ReadResult Value,
        sessionConsistencyRead s token key r →
        sessionTokenLEQ token (updateTokenFromRead s token r)

-- ConsistentPrefixReadsOK (TLA+ lines 149-151)
def consistentPrefixReadsOK (s : CosmosState Key Value) : Prop :=
  readConsistencyOK s.writeConsistencyLevel .consistentPrefix →
  readsOK s (consistentPrefixRead s)

-- EventualConsistencyReadsOK (TLA+ lines 153-155)
def eventualConsistencyReadsOK (s : CosmosState Key Value) : Prop :=
  readConsistencyOK s.writeConsistencyLevel .eventual →
  readsOK s (eventualConsistencyRead s)

-- VersionBoundOK (TLA+ lines 157-158)
def versionBoundOK (versionBound : Nat) (s : CosmosState Key Value) : Prop :=
  s.log.length - s.readIndex ≤ versionBound

-- HistoryTokensUnique (TLA+ lines 162-166) — requires writeHistory
-- Write tokens are unique, and no record appears more than once.
def historyTokensUnique (s : CosmosWState Key Value) : Prop :=
  (∀ r1 r2 : WriteHistoryEntry Key Value,
    r1 ∈ s.writeHistory → r2 ∈ s.writeHistory → r1 ≠ r2 → r1.token ≠ r2.token)
  ∧ (∀ r : WriteHistoryEntry Key Value, s.writeHistory.count r ≤ 1)

/- ================================================================
   Section 8: Strong Consistency Properties
   ================================================================ -/

-- StrongConsistencyReadsGiveLatestDurableSCValue (TLA+ lines 276-283)
-- A strongly consistent read must not miss any committed log entry for the key.
def strongConsistencyReadsGiveLatestDurableSCValue
    (s : CosmosState Key Value) : Prop :=
  readConsistencyOK s.writeConsistencyLevel .strong →
  ∀ key : Key, ∀ r : ReadResult Value,
    strongConsistencyRead s key r →
    ¬∃ i, i > 0 ∧ i ≤ s.log.length ∧ i ≤ s.commitIndex
      ∧ (s.log[i - 1]!).key = key
      ∧ r.logIndex < i

-- StrongConsistencyReadsGiveLatestSuccessfulWrite (TLA+ lines 289-296)
-- A strongly consistent read must reflect all succeeded writes.
def strongConsistencyReadsGiveLatestSuccessfulWrite
    (s : CosmosWState Key Value) : Prop :=
  s.cosmos.writeConsistencyLevel = .strong →
  ∀ key : Key, ∀ r : ReadResult Value,
    strongConsistencyRead s.cosmos key r →
    ¬∃ record : WriteHistoryEntry Key Value,
      record ∈ s.writeHistory
      ∧ record.key = key
      ∧ record.state = .succeeded
      ∧ record.token.checkpoint > r.logIndex

-- StrongConsistencyReadsConsistent (TLA+ lines 298-300)
def strongConsistencyReadsConsistent (s : CosmosState Key Value) : Prop :=
  readConsistencyOK s.writeConsistencyLevel .strong →
  isConsistent (strongConsistencyRead s)

-- StrongConsistencyReadsMonotonic (TLA+ lines 319-325) — step invariant
-- Between consecutive states, strong consistency reads never go backwards.
def strongConsistencyReadsMonotonic
    (s s' : CosmosState Key Value) : Prop :=
  readConsistencyOK s.writeConsistencyLevel .strong →
  ∀ key : Key, ∀ r1 r2 : ReadResult Value,
    strongConsistencyRead s key r1 →
    strongConsistencyRead s' key r2 →
    readsLEQ r1 r2

-- StrongConsistencyReadsFollowReadIndex (TLA+ lines 327-329)
def strongConsistencyReadsFollowReadIndex
    (s : CosmosState Key Value) : Prop :=
  readConsistencyOK s.writeConsistencyLevel .strong →
  followsReadIndex s (strongConsistencyRead s)

/- ================================================================
   Section 9: Bounded Staleness Properties
   ================================================================ -/

-- BoundedStalenessReadsLowMonotonic (TLA+ lines 334-336) — step invariant
def boundedStalenessReadsLowMonotonic
    (s s' : CosmosState Key Value) : Prop :=
  readConsistencyOK s.writeConsistencyLevel .boundedStaleness →
  isLowMonotonic (fun st key r => boundedStalenessRead st key r) s s'

-- BoundedStalenessReadsFollowReadIndex (TLA+ lines 338-340)
def boundedStalenessReadsFollowReadIndex
    (s : CosmosState Key Value) : Prop :=
  readConsistencyOK s.writeConsistencyLevel .boundedStaleness →
  followsReadIndex s (boundedStalenessRead s)

-- BoundedStalenessIsBounded (TLA+ lines 347-350)
-- The principal bounded staleness guarantee: at most StalenessBound
-- non-durable writes at any time.
def boundedStalenessIsBounded (stalenessBound : Nat)
    (s : CosmosState Key Value) : Prop :=
  s.writeConsistencyLevel = .boundedStaleness →
  s.log.length - s.commitIndex ≤ stalenessBound

/- ================================================================
   Section 10: Session Consistency Properties
   ================================================================ -/

-- SessionConsistencyReadsMonotonicPerTokenSequence (TLA+ lines 365-377)
-- Within a session (token1 ≤ token2), reads are monotonic: every result in read2
-- has a predecessor in read1, and every result in read1 has a successor in read2.
def sessionConsistencyReadsMonotonicPerTokenSequence
    (s : CosmosState Key Value) : Prop :=
  ∀ token1 token2 : SessionToken,
    token1.epoch ≥ 1 → token2.epoch ≥ 1 →
    readConsistencyOK s.writeConsistencyLevel .session →
    sessionTokenLEQ token1 token2 →
    ∀ key : Key,
      (∀ r2, sessionConsistencyRead s token2 key r2 →
        ∃ r1, sessionConsistencyRead s token1 key r1 ∧ readsLEQ r1 r2)
      ∧ (∀ r1, sessionConsistencyRead s token1 key r1 →
        ∃ r2, sessionConsistencyRead s token2 key r2 ∧ readsLEQ r1 r2)

-- SessionConsistencyReadsLowMonotonic (TLA+ lines 401-404) — step invariant
def sessionConsistencyReadsLowMonotonic
    (s s' : CosmosState Key Value) : Prop :=
  readConsistencyOK s.writeConsistencyLevel .session →
  ∀ token : SessionToken,
    (token.epoch ≥ 1 ∨ token = noSessionToken) →
    isLowMonotonic (fun st key r => sessionConsistencyRead st token key r) s s'

-- SessionConsistencyReadsFollowReadIndex (TLA+ lines 406-409)
def sessionConsistencyReadsFollowReadIndex
    (s : CosmosState Key Value) : Prop :=
  ∀ token : SessionToken,
    (token.epoch ≥ 1 ∨ token = noSessionToken) →
    readConsistencyOK s.writeConsistencyLevel .session →
    followsReadIndex s (sessionConsistencyRead s token)

-- SessionTokenWhenValid (TLA+ lines 429-434)
-- A session token is valid (produces non-empty reads) when its epoch matches
-- the current epoch, or when it is NoSessionToken.
def sessionTokenWhenValid (s : CosmosState Key Value) : Prop :=
  ∀ token : SessionToken,
    (token.epoch ≥ 1 ∨ token = noSessionToken) →
    readConsistencyOK s.writeConsistencyLevel .session →
    (token.epoch = s.epoch ∨ token = noSessionToken) →
    ∀ key : Key, ∃ r, sessionConsistencyRead s token key r

-- SessionTokenAlwaysAcquirableRead (TLA+ lines 436-442)
-- Tokens derived from reads with NoSessionToken are always acquirable.
def sessionTokenAlwaysAcquirableRead (s : CosmosState Key Value) : Prop :=
  readConsistencyOK s.writeConsistencyLevel .session →
  ∀ key : Key, ∀ r : ReadResult Value,
    sessionConsistencyRead s noSessionToken key r →
    acquirableSessionToken s (updateTokenFromRead s noSessionToken r)

-- SessionTokenAlwaysAcquirableWrite (TLA+ lines 444-447)
-- The write init token is always acquirable at session consistency.
def sessionTokenAlwaysAcquirableWrite (s : CosmosState Key Value) : Prop :=
  s.writeConsistencyLevel = .session →
  acquirableSessionToken s (writeInitToken s)

/- ================================================================
   Section 11: Consistent Prefix and Eventual Consistency Properties
   ================================================================ -/

-- ConsistentPrefixReadsLowMonotonic (TLA+ lines 455-457) — step invariant
def consistentPrefixReadsLowMonotonic
    (s s' : CosmosState Key Value) : Prop :=
  readConsistencyOK s.writeConsistencyLevel .consistentPrefix →
  isLowMonotonic (fun st key r => consistentPrefixRead st key r) s s'

-- ConsistentPrefixReadsFollowReadIndex (TLA+ lines 459-461)
def consistentPrefixReadsFollowReadIndex
    (s : CosmosState Key Value) : Prop :=
  readConsistencyOK s.writeConsistencyLevel .consistentPrefix →
  followsReadIndex s (consistentPrefixRead s)

-- EventuallyConsistentReadsEquivalentToConsistentPrefix (TLA+ lines 469-473)
-- Under both read consistency levels, the two reads are extensionally equal.
def eventuallyConsistentReadsEquivalentToConsistentPrefix
    (s : CosmosState Key Value) : Prop :=
  readConsistencyOK s.writeConsistencyLevel .consistentPrefix →
  readConsistencyOK s.writeConsistencyLevel .eventual →
  ∀ key : Key, ∀ r : ReadResult Value,
    consistentPrefixRead s key r ↔ eventualConsistencyRead s key r

/- ================================================================
   Section 12: Proofs
   ================================================================ -/

-- typesOK holds at init
theorem typesOK_init (wc : ConsistencyLevel) :
    typesOK (cosmosInit wc : CosmosState Key Value) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [cosmosInit]

-- typesOK preserved by cosmosNext
theorem typesOK_cosmosNext {s s' : CosmosState Key Value}
    (ht : typesOK s) (hn : cosmosNext s s') : typesOK s' := by
  obtain ⟨h_epoch, h_ri_ci, h_ci_log⟩ := ht
  rcases hn with h_inc | h_trunc
  · -- increaseReadIndexAndOrCommitIndex
    obtain ⟨_, h_ci_log', _, h_ri_ci', h_log, h_ep, _⟩ := h_inc
    exact ⟨h_ep ▸ h_epoch, h_ri_ci', h_log ▸ h_ci_log'⟩
  · -- truncateLog
    obtain ⟨i, h_i_gt, h_i_le, h_log, h_ep, h_ri, h_ci, _⟩ := h_trunc
    refine ⟨by omega, by omega, ?_⟩
    rw [h_ci, h_log, List.length_take]
    exact Nat.le_min.mpr ⟨by omega, h_ci_log⟩

-- typesOK is an invariant of CosmosReachable
theorem typesOK_invariant {s : CosmosState Key Value} {wc : ConsistencyLevel}
    (h : CosmosReachable wc s) : typesOK s := by
  induction h with
  | init => exact typesOK_init wc
  | step _ hnext ih => exact typesOK_cosmosNext ih hnext

-- Consistent prefix and eventual consistency reads are equivalent (any state)
theorem eventualReadsEquivConsistentPrefix
    (s : CosmosState Key Value) :
    eventuallyConsistentReadsEquivalentToConsistentPrefix s := by
  intro hcp he key r
  simp only [consistentPrefixRead, eventualConsistencyRead, checkReadConsistency]
  exact ⟨fun ⟨_, h⟩ => ⟨he, h⟩, fun ⟨_, h⟩ => ⟨hcp, h⟩⟩

-- newSessionTokensOK follows from typesOK
theorem newSessionTokensOK_of_typesOK {s : CosmosState Key Value}
    (ht : typesOK s) : newSessionTokensOK s := by
  unfold newSessionTokensOK acquirableSessionToken
  intro token ⟨h_eq, _⟩
  unfold typesOK at ht
  omega

-- sessionTokenAlwaysAcquirableWrite holds for any state
theorem sessionTokenAlwaysAcquirableWrite_holds
    (s : CosmosState Key Value) :
    sessionTokenAlwaysAcquirableWrite s := by
  unfold sessionTokenAlwaysAcquirableWrite acquirableSessionToken writeInitToken
  intro _
  exact ⟨rfl, le_refl _⟩

-- pointsValid holds for every cosmosNext step (given typesOK)
theorem pointsValid_cosmosNext {s s' : CosmosState Key Value}
    (ht : typesOK s) (hn : cosmosNext s s') : pointsValid s s' := by
  obtain ⟨_, h_ri_ci, _⟩ := ht
  rcases hn with h_inc | h_trunc
  · obtain ⟨h_ci, _, h_ri, h_ri_ci', _, _, _⟩ := h_inc
    exact ⟨h_ri_ci, h_ri, h_ci⟩
  · obtain ⟨_, _, _, _, _, h_ri, h_ci, _⟩ := h_trunc
    unfold pointsValid
    rw [h_ri, h_ci]
    exact ⟨h_ri_ci, le_refl _, le_refl _⟩

-- Helper: writeConsistencyLevel is unchanged by cosmosNext.
lemma wclPreserved_cosmosNext {s s' : CosmosState Key Value}
    (hn : cosmosNext s s') : s'.writeConsistencyLevel = s.writeConsistencyLevel := by
  rcases hn with h | h
  · obtain ⟨_, _, _, _, _, _, hwc⟩ := h; exact hwc
  · obtain ⟨_, _, _, _, _, _, _, hwc⟩ := h; exact hwc

-- Helper: generalReadResult with allowDirty = false yields at most one result per key.
-- Proof sketch:
-- Case 2 (dirty read) is impossible since false ≠ true.
-- Case 1 vs Case 1: if two max indices i1, i2, use trichotomy to show i1 = i2.
-- Case 3 vs Case 3: both are notFoundReadResult.
-- Case 1 vs Case 3 (or reverse): existence contradicts non-existence.
theorem generalReadResult_nodirty_unique
    {s : CosmosState Key Value} {key : Key} {index : Nat}
    {r1 r2 : ReadResult Value}
    (h1 : generalReadResult s key index false r1)
    (h2 : generalReadResult s key index false r2) :
    r1 = r2 := by
  unfold generalReadResult at h1 h2
  -- Eliminate Case 2 (dirty read) in both: false ≠ true
  rcases h1 with ⟨i1, hi1_pos, hi1_len, hi1_idx, hi1_key, hi1_eq, hi1_max⟩ |
                 ⟨habs, _⟩ | ⟨h1_none, h1_eq⟩
  · -- h1 is Case 1 (found at i1)
    rcases h2 with ⟨i2, hi2_pos, hi2_len, hi2_idx, hi2_key, hi2_eq, hi2_max⟩ |
                   ⟨habs, _⟩ | ⟨h2_none, h2_eq⟩
    · -- Both Case 1: show i1 = i2 by trichotomy
      rcases Nat.lt_trichotomy i1 i2 with hlt | rfl | hgt
      · -- i1 < i2: contradicts i1 being max
        exact absurd hi2_key (hi1_max i2 hlt hi2_idx hi2_len)
      · -- i1 = i2: results equal
        rw [hi1_eq, hi2_eq]
      · -- i2 < i1: contradicts i2 being max
        exact absurd hi1_key (hi2_max i1 hgt hi1_idx hi1_len)
    · exact absurd habs (by decide)
    · -- Case 1 vs Case 3: entry at i1 contradicts "no entries"
      exact absurd hi1_key (h2_none i1 hi1_pos hi1_idx hi1_len)
  · exact absurd habs (by decide)
  · -- h1 is Case 3 (not found)
    rcases h2 with ⟨i2, hi2_pos, hi2_len, hi2_idx, hi2_key, _, _⟩ |
                   ⟨habs, _⟩ | ⟨_, h2_eq⟩
    · -- Case 3 vs Case 1: contradiction
      exact absurd hi2_key (h1_none i2 hi2_pos hi2_idx hi2_len)
    · exact absurd habs (by decide)
    · -- Both Case 3
      rw [h1_eq, h2_eq]

-- Strong consistency reads are consistent (at most one result per key).
-- Follows directly from generalReadResult_nodirty_unique since strong reads
-- use generalReadResult with allowDirty = false.
theorem strongConsistencyReadsConsistent_holds
    (s : CosmosState Key Value) :
    strongConsistencyReadsConsistent s := by
  unfold strongConsistencyReadsConsistent isConsistent
  intro _hrc key r1 r2 hr1 hr2
  unfold strongConsistencyRead checkReadConsistency at hr1 hr2
  exact generalReadResult_nodirty_unique hr1.2 hr2.2

-- Strong consistency reads give the latest durable value.
-- If there's a committed entry at index i for the key with i > r.logIndex,
-- generalReadResult's maximality condition gives a contradiction.
theorem strongConsistencyReadsGiveLatestDurableSCValue_holds
    (s : CosmosState Key Value) :
    strongConsistencyReadsGiveLatestDurableSCValue s := by
  unfold strongConsistencyReadsGiveLatestDurableSCValue
  intro _hrc key r hr
  unfold strongConsistencyRead checkReadConsistency at hr
  obtain ⟨_, hr⟩ := hr
  -- hr : generalReadResult s key s.commitIndex false r
  intro ⟨i, hi_pos, hi_len, hi_ci, hi_key, hi_lt⟩
  unfold generalReadResult at hr
  rcases hr with ⟨j, hj_pos, hj_len, hj_ci, hj_key, hj_eq, hj_max⟩ |
                 ⟨habs, _⟩ | ⟨h_none, _⟩
  · -- Case 1: r comes from max index j ≤ commitIndex
    -- r.logIndex = j, so j < i, but i ≤ commitIndex contradicts j being max
    rw [hj_eq] at hi_lt
    simp at hi_lt
    exact absurd hi_key (hj_max i hi_lt hi_ci hi_len)
  · exact absurd habs (by decide)
  · -- Case 3: no entry for key at or before commitIndex, but i is one
    exact absurd hi_key (h_none i hi_pos hi_ci hi_len)

-- Helper: any generalReadResult produces a well-formed ReadResult.
-- Case 1/2: logIndex > 0 and value = some _. Case 3: notFoundReadResult.
theorem generalReadResult_wellFormed
    {s : CosmosState Key Value} {key : Key} {index : Nat} {dirty : Bool}
    {r : ReadResult Value}
    (h : generalReadResult s key index dirty r) :
    readResultWellFormed r := by
  unfold generalReadResult at h
  unfold readResultWellFormed
  rcases h with ⟨i, hi_pos, _, _, _, hi_eq, _⟩ |
               ⟨_, i, hi_pos, _, _, _, hi_eq⟩ |
               ⟨_, hi_eq⟩
  · left; rw [hi_eq]; exact ⟨hi_pos, ⟨_, rfl⟩⟩
  · left; rw [hi_eq]; exact ⟨hi_pos, ⟨_, rfl⟩⟩
  · right; exact hi_eq

-- Helper: any generalReadResult gives a valid session token when combined
-- with noSessionToken via updateTokenFromRead.
-- The updated token is ⟨r.logIndex, s.epoch⟩; validity needs r.logIndex ≤ log.length + 1.
theorem generalReadResult_tokenValid
    {s : CosmosState Key Value} {key : Key} {index : Nat} {dirty : Bool}
    {r : ReadResult Value}
    (h : generalReadResult s key index dirty r) :
    sessionTokenIsValid s (updateTokenFromRead s noSessionToken r) := by
  unfold generalReadResult at h
  unfold sessionTokenIsValid sessionTokenLEQ updateTokenFromRead writeInitToken noSessionToken
  -- Goal: (max 0 r.logIndex epoch = epoch ∨ ...) ∧ max 0 r.logIndex ≤ log.length + 1
  -- max 0 n = n for Nat, and r.logIndex ≤ log.length in all cases
  rcases h with ⟨i, _, hi_len, _, _, hi_eq, _⟩ |
               ⟨_, i, _, hi_len, _, _, hi_eq⟩ |
               ⟨_, hi_eq⟩
  · rw [hi_eq]; simp; omega
  · rw [hi_eq]; simp; omega
  · rw [hi_eq]; simp [notFoundReadResult]

-- strongConsistencyReadsOK: strong reads are well-formed and yield valid tokens.
theorem strongConsistencyReadsOK_holds
    (s : CosmosState Key Value) :
    strongConsistencyReadsOK s := by
  unfold strongConsistencyReadsOK readsOK
  intro _ key r hr
  unfold strongConsistencyRead checkReadConsistency at hr
  exact ⟨generalReadResult_wellFormed hr.2, generalReadResult_tokenValid hr.2⟩

-- boundedStalenessReadsOK: bounded staleness reads are well-formed and yield valid tokens.
theorem boundedStalenessReadsOK_holds
    (s : CosmosState Key Value) :
    boundedStalenessReadsOK s := by
  unfold boundedStalenessReadsOK readsOK
  intro _ key r hr
  unfold boundedStalenessRead checkReadConsistency at hr
  exact ⟨generalReadResult_wellFormed hr.2, generalReadResult_tokenValid hr.2⟩

-- consistentPrefixReadsOK: consistent prefix reads are well-formed and yield valid tokens.
theorem consistentPrefixReadsOK_holds
    (s : CosmosState Key Value) :
    consistentPrefixReadsOK s := by
  unfold consistentPrefixReadsOK readsOK
  intro _ key r hr
  unfold consistentPrefixRead checkReadConsistency at hr
  exact ⟨generalReadResult_wellFormed hr.2, generalReadResult_tokenValid hr.2⟩

-- eventualConsistencyReadsOK: eventual consistency reads are well-formed and yield valid tokens.
theorem eventualConsistencyReadsOK_holds
    (s : CosmosState Key Value) :
    eventualConsistencyReadsOK s := by
  unfold eventualConsistencyReadsOK readsOK
  intro _ key r hr
  unfold eventualConsistencyRead checkReadConsistency at hr
  exact ⟨generalReadResult_wellFormed hr.2, generalReadResult_tokenValid hr.2⟩

-- Helper: any generalReadResult has logIndex ≤ log.length.
-- Cases 1/2: logIndex = i ≤ log.length. Case 3: logIndex = 0.
lemma generalReadResult_logIndex_le
    {s : CosmosState Key Value} {key : Key} {index : Nat} {dirty : Bool}
    {r : ReadResult Value}
    (h : generalReadResult s key index dirty r) :
    r.logIndex ≤ s.log.length := by
  unfold generalReadResult at h
  rcases h with ⟨i, _, hi_len, _, _, hi_eq, _⟩ |
               ⟨_, i, _, hi_len, _, _, hi_eq⟩ |
               ⟨_, hi_eq⟩
  · rw [hi_eq]; exact hi_len
  · rw [hi_eq]; exact hi_len
  · rw [hi_eq]; simp [notFoundReadResult]

-- sessionConsistencyReadsOK: session reads are well-formed, yield valid tokens,
-- and session tokens advance through reads.
-- The if-then-else in sessionConsistencyRead: when the if is false, no results
-- exist (predicate is False), so everything is vacuous. When true, the read is
-- a generalReadResult, and the token advancement uses le_max_left.
theorem sessionConsistencyReadsOK_holds
    (s : CosmosState Key Value) :
    sessionConsistencyReadsOK s := by
  unfold sessionConsistencyReadsOK
  intro hrc token _htoken
  constructor
  · -- Part 1: readsOK — well-formed results and valid tokens
    unfold readsOK
    intro key r hr
    unfold sessionConsistencyRead checkReadConsistency at hr
    obtain ⟨_, hr⟩ := hr
    split_ifs at hr with hep
    · exact ⟨generalReadResult_wellFormed hr, generalReadResult_tokenValid hr⟩
    · exact absurd hr id
  · -- Part 2: sessionTokenLEQ token (updateTokenFromRead s token r)
    -- The updated token has epoch = s.epoch and checkpoint = max token.checkpoint r.logIndex.
    -- Epoch condition: from the if-branch, token.epoch = s.epoch or token = noSessionToken.
    -- Checkpoint condition: token.checkpoint ≤ max token.checkpoint r.logIndex (le_max_left).
    intro key r hr
    unfold sessionConsistencyRead checkReadConsistency at hr
    obtain ⟨_, hr⟩ := hr
    split_ifs at hr with hep
    · unfold sessionTokenLEQ updateTokenFromRead
      refine ⟨?_, le_max_left _ _⟩
      rcases hep with h | h
      · left; exact h.symm
      · right; rw [h]; rfl
    · exact absurd hr id

-- sessionTokenAlwaysAcquirableRead: tokens from reads with noSessionToken
-- are always acquirable. The updated token has epoch = s.epoch (from
-- updateTokenFromRead) and checkpoint = r.logIndex ≤ log.length + 1.
theorem sessionTokenAlwaysAcquirableRead_holds
    (s : CosmosState Key Value) :
    sessionTokenAlwaysAcquirableRead s := by
  unfold sessionTokenAlwaysAcquirableRead
  intro _hrc key r hr
  unfold sessionConsistencyRead checkReadConsistency at hr
  obtain ⟨_, hr⟩ := hr
  -- noSessionToken = noSessionToken, so the if is true
  split_ifs at hr with hep
  · unfold acquirableSessionToken updateTokenFromRead noSessionToken
    simp
    -- Goal: r.logIndex ≤ s.log.length + 1
    exact Nat.le_succ_of_le (generalReadResult_logIndex_le hr)
  · exact absurd hr id

-- Helper: generalReadResult always has at least one result (existence).
-- Either Case 1 (there's a matching entry ≤ index, pick the max) or Case 3 (notFoundReadResult).
-- This requires classical reasoning to decide whether any entry matches.
theorem generalReadResult_exists
    (s : CosmosState Key Value) (key : Key) (index : Nat) (dirty : Bool) :
    ∃ r, generalReadResult s key index dirty r := by
  unfold generalReadResult
  -- Decide: does any entry at or before index match key?
  by_cases h : ∃ i, i > 0 ∧ i ≤ s.log.length ∧ i ≤ index ∧ (s.log[i - 1]!).key = key
  · -- There's at least one matching entry. We need the maximum such index.
    -- Use classical.choose on the well-ordered Nat to find the max.
    -- Among all matching indices in [1..min(index, log.length)], pick the largest.
    -- We use strong induction / well-ordering implicitly via by_contra.
    -- Claim: there exists a max. If every candidate has a larger one, we get
    -- an infinite ascending chain bounded by log.length, contradiction.
    have ⟨i, hi_pos, hi_len, hi_idx, hi_key⟩ := h
    -- Find the maximum: start from min(index, s.log.length) and go down
    -- Use classical existence of max in a bounded non-empty set
    suffices ∃ m, m > 0 ∧ m ≤ s.log.length ∧ m ≤ index
        ∧ (s.log[m - 1]!).key = key
        ∧ ∀ j, j > m → j ≤ index → j ≤ s.log.length → (s.log[j - 1]!).key ≠ key by
      obtain ⟨m, hm_pos, hm_len, hm_idx, hm_key, hm_max⟩ := this
      exact ⟨⟨m, some (s.log[m - 1]!).value⟩,
        Or.inl ⟨m, hm_pos, hm_len, hm_idx, hm_key, rfl, hm_max⟩⟩
    -- Prove existence of max by strong descent on (min index log.length - i)
    by_contra h_no_max
    push_neg at h_no_max
    -- h_no_max : ∀ m, m > 0 → m ≤ log.length → m ≤ index → key = key →
    --   ∃ j > m, j ≤ index ∧ j ≤ log.length ∧ key = key
    -- Starting from i, iterate to get j > i > ... all ≤ min(index, log.length).
    -- This gives an infinite ascending chain in a finite range, contradiction.
    have : ∀ m, m > 0 → m ≤ s.log.length → m ≤ index →
        (s.log[m - 1]!).key = key →
        ∃ j, j > m ∧ j ≤ index ∧ j ≤ s.log.length ∧ (s.log[j - 1]!).key = key := by
      intro m hm1 hm2 hm3 hm4
      have := h_no_max m hm1 hm2 hm3 hm4
      obtain ⟨j, hj_gt, hj_idx, hj_len, hj_key⟩ := this
      exact ⟨j, hj_gt, hj_idx, hj_len, hj_key⟩
    -- Build ascending chain: i < j1 < j2 < ..., all ≤ min(index, log.length)
    -- After at most min(index, log.length) steps, we exceed the bound.
    -- Use Nat.lt_irrefl on a chain of length > bound.
    -- Simpler: use well-founded recursion. The set {m | m > 0 ∧ m ≤ log.length ∧ ...}
    -- is finite, so it has a max. We prove by contradiction using Nat.find on the complement.
    -- Actually, simplest: iterate this from i, getting a sequence > log.length, contradiction.
    suffices ∀ n m, m > 0 → m ≤ s.log.length → m ≤ index →
        (s.log[m - 1]!).key = key → m + n ≤ s.log.length by
      exact absurd (this (s.log.length) i hi_pos hi_len hi_idx hi_key) (by omega)
    intro n
    induction n with
    | zero => intro m _ hm2 _ _; omega
    | succ n ih =>
      intro m hm1 hm2 hm3 hm4
      obtain ⟨j, hj_gt, hj_idx, hj_len, hj_key⟩ := this m hm1 hm2 hm3 hm4
      have := ih j (by omega) hj_len hj_idx hj_key
      omega
  · -- No matching entry: Case 3 (notFoundReadResult)
    push_neg at h
    refine ⟨notFoundReadResult, Or.inr (Or.inr ⟨?_, rfl⟩)⟩
    intro i hi_pos hi_idx hi_len
    exact h i hi_pos hi_len hi_idx

-- sessionTokenWhenValid: when a token's epoch matches the current epoch (or it's
-- noSessionToken), a session read always produces at least one result.
theorem sessionTokenWhenValid_holds
    (s : CosmosState Key Value) :
    sessionTokenWhenValid s := by
  unfold sessionTokenWhenValid
  intro token _htoken hrc hep key
  -- Build the session read from generalReadResult_exists
  have ⟨r, hr⟩ := generalReadResult_exists s key
    (max token.checkpoint s.readIndex) true
  refine ⟨r, ?_⟩
  unfold sessionConsistencyRead checkReadConsistency
  have hcond : s.epoch = token.epoch ∨ token = noSessionToken := by
    rcases hep with h | h
    · left; exact h.symm
    · right; exact h
  exact ⟨hrc, by rw [if_pos hcond]; exact hr⟩

-- Helper: List.take preserves elements before the take point.
-- Needed for truncateLog reasoning: log entries ≤ commitIndex are unchanged.
lemma list_getElem_bang_take {α : Type} [Inhabited α] {l : List α} {n i : Nat}
    (hi : i < n) (hn : n ≤ l.length) :
    (l.take n)[i]! = l[i]! := by
  have h1 : i < (l.take n).length := by
    rw [List.length_take]; omega
  have h2 : i < l.length := by omega
  -- Both [i]! reduce to safe indexing since in bounds, then List.getElem_take
  rw [getElem!_pos (l.take n) i h1, getElem!_pos l i h2, List.getElem_take]

-- Helper: if two states have identical log entries up to some bound ≥ index,
-- and allowDirty = false, then generalReadResult produces the same results.
-- This captures the key insight for truncateLog: strong reads only see entries
-- within commitIndex, and truncation preserves those.
lemma generalReadResult_nodirty_log_prefix
    {s s' : CosmosState Key Value} {key : Key} {index : Nat}
    {r : ReadResult Value}
    (h_idx : index ≤ s.log.length) (h_idx' : index ≤ s'.log.length)
    (h_entries : ∀ j, j < index → j < s.log.length → j < s'.log.length →
      s'.log[j]! = s.log[j]!)
    (h : generalReadResult s key index false r) :
    generalReadResult s' key index false r := by
  unfold generalReadResult at h ⊢
  -- Case 2 (dirty) impossible since allowDirty = false; handle Cases 1 and 3.
  -- Key idea: all relevant entries use index j-1 < index, so h_entries applies.
  rcases h with ⟨i, hi_pos, hi_len, hi_idx, hi_key, hi_eq, hi_max⟩ |
               ⟨habs, _⟩ | ⟨h_none, h_eq⟩
  · -- Case 1: found at max index i ≤ index
    left
    have hi_len' : i ≤ s'.log.length := by omega
    have h_entry : s'.log[i - 1]! = s.log[i - 1]! :=
      h_entries (i - 1) (by omega) (by omega) (by omega)
    refine ⟨i, hi_pos, hi_len', hi_idx, ?_, ?_, ?_⟩
    · rw [h_entry]; exact hi_key
    · rw [h_entry, hi_eq]
    · intro j hj_gt hj_idx hj_len
      have h_ej : s'.log[j - 1]! = s.log[j - 1]! :=
        h_entries (j - 1) (by omega) (by omega) (by omega)
      rw [h_ej]; exact hi_max j hj_gt hj_idx (by omega)
  · exact absurd habs (by decide)
  · -- Case 3: no matching entry at or before index
    right; right
    refine ⟨?_, h_eq⟩
    intro i hi_pos hi_idx hi_len
    have h_ei : s'.log[i - 1]! = s.log[i - 1]! :=
      h_entries (i - 1) (by omega) (by omega) (by omega)
    rw [h_ei]; exact h_none i hi_pos hi_idx (by omega)

-- Strong consistency reads are monotonic across cosmosNext steps.
-- Proof sketch:
-- increaseReadIndex: s'.log = s.log, s'.commitIndex ≥ s.commitIndex, so the max
--   index for key can only increase.
-- truncateLog: s'.commitIndex = s.commitIndex, log entries ≤ commitIndex preserved,
--   so strong reads produce the same result (by generalReadResult_nodirty_log_prefix).
theorem strongConsistencyReadsMonotonic_cosmosNext
    {s s' : CosmosState Key Value}
    (ht : typesOK s) (hn : cosmosNext s s') :
    strongConsistencyReadsMonotonic s s' := by
  unfold strongConsistencyReadsMonotonic
  intro hrc key r1 r2 hr1 hr2
  unfold strongConsistencyRead checkReadConsistency at hr1 hr2
  obtain ⟨_, hr1⟩ := hr1
  obtain ⟨_, hr2⟩ := hr2
  unfold readsLEQ
  -- hr1 : generalReadResult s key s.commitIndex false r1
  -- hr2 : generalReadResult s' key s'.commitIndex false r2
  obtain ⟨h_epoch, h_ri_ci, h_ci_log⟩ := ht
  rcases hn with h_inc | h_trunc
  · -- Case: increaseReadIndexAndOrCommitIndex
    -- s'.log = s.log, s'.commitIndex ≥ s.commitIndex
    obtain ⟨h_ci, h_ci_log', h_ri, _, h_log, _, _⟩ := h_inc
    -- r1 comes from generalReadResult at s.commitIndex
    -- r2 comes from generalReadResult at s'.commitIndex ≥ s.commitIndex
    -- Since s'.log = s.log, any entry valid at s is also valid at s'.
    -- So r1.logIndex ≤ r2.logIndex.
    unfold generalReadResult at hr1 hr2
    rcases hr1 with ⟨i1, h1p, h1l, h1i, h1k, h1e, h1m⟩ |
                    ⟨habs, _⟩ | ⟨h1n, h1e⟩
    · -- r1 is Case 1: found at max i1 ≤ s.commitIndex
      rcases hr2 with ⟨i2, h2p, h2l, h2i, h2k, h2e, h2m⟩ |
                      ⟨habs, _⟩ | ⟨h2n, _⟩
      · -- Both Case 1: i1 ≤ i2 since i1 is valid in s' range and i2 is max
        rw [h1e, h2e]; simp
        -- Show i1 ≤ i2 by contradiction: if i1 > i2, i2's max is contradicted
        by_contra h_not_le
        push_neg at h_not_le
        -- i1 > i2, but i1 ≤ s.commitIndex ≤ s'.commitIndex, i1 ≤ s.log.length = s'.log.length
        have : (s'.log[i1 - 1]!).key = key := by rw [h_log]; exact h1k
        exact absurd this (h2m i1 h_not_le (by omega) (by rw [h_log]; exact h1l))
      · exact absurd habs (by decide)
      · -- r1 Case 1, r2 Case 3: entry at i1 also valid in s' → contradiction
        have : (s'.log[i1 - 1]!).key = key := by rw [h_log]; exact h1k
        exact absurd this (h2n i1 h1p (by omega) (by rw [h_log]; exact h1l))
    · exact absurd habs (by decide)
    · -- r1 is Case 3: r1 = notFoundReadResult, logIndex = 0
      rw [h1e]; simp [notFoundReadResult]
  · -- Case: truncateLog
    -- s'.commitIndex = s.commitIndex, log entries ≤ commitIndex are preserved
    obtain ⟨ti, hti_gt, hti_le, h_log, _, _, h_ci, _⟩ := h_trunc
    -- Strong reads use commitIndex, which is unchanged.
    -- Log entries up to commitIndex are preserved (ti > commitIndex).
    -- So generalReadResult gives the same result in s and s'.
    have h_ci_s' : s.commitIndex ≤ s'.log.length := by
      rw [h_log, List.length_take]; omega
    have h_same : generalReadResult s' key s.commitIndex false r1 := by
      refine generalReadResult_nodirty_log_prefix h_ci_log h_ci_s' ?_ hr1
      intro j hj_idx _ _
      rw [h_log]
      have hj_ti : j < ti - 1 := by omega
      have hti_len : ti - 1 ≤ s.log.length := by omega
      exact list_getElem_bang_take hj_ti hti_len
    rw [h_ci] at hr2
    exact le_of_eq (congrArg ReadResult.logIndex
      (generalReadResult_nodirty_unique h_same hr2))

-- Helper: for generalReadResult with allowDirty = true on the same state,
-- increasing the index preserves a "lower bound" property.
-- Part 1: every result from idx2 ≥ idx1 has a ≤ counterpart from idx1.
-- Proof sketch by case on r2:
--   Case 1 (max m2 ≤ idx2): max m1 ≤ idx1 has m1 ≤ m2 (subset monotonicity),
--     or notFoundReadResult (logIndex 0). Either way, r1 ≤ r2.
--   Case 2 (dirty m2 > idx2 ≥ idx1): same entry is dirty for idx1. r1 = r2.
--   Case 3 (not found ≤ idx2): no entries ≤ idx1 either. r1 = r2 = notFound.
lemma generalReadResult_dirty_lower
    {s : CosmosState Key Value} {key : Key} {idx1 idx2 : Nat}
    (h_le : idx1 ≤ idx2)
    {r2 : ReadResult Value}
    (hr2 : generalReadResult s key idx2 true r2) :
    ∃ r1, generalReadResult s key idx1 true r1 ∧ readsLEQ r1 r2 := by
  unfold generalReadResult at hr2
  rcases hr2 with ⟨m2, hm2p, hm2l, hm2i, hm2k, hm2e, hm2m⟩ |
                  ⟨_, m2, hm2p, hm2l, hm2gt, hm2k, hm2e⟩ |
                  ⟨h2n, h2e⟩
  · -- r2 Case 1: max m2 ≤ idx2 for key. Construct r1 from idx1.
    -- Use generalReadResult_exists with allowDirty=false to avoid Case 2.
    -- Case 1 and Case 3 don't depend on allowDirty, so they lift to true.
    have ⟨r1, hr1f⟩ := generalReadResult_exists s key idx1 false
    unfold generalReadResult at hr1f
    rcases hr1f with ⟨m1, h1p, h1l, h1i, h1k, h1e, h1m⟩ |
                    ⟨habs, _⟩ | ⟨h1n, h1e⟩
    · -- r1 is Case 1 (max m1 ≤ idx1): lift to allowDirty=true
      refine ⟨r1, ?_, ?_⟩
      · unfold generalReadResult
        left; exact ⟨m1, h1p, h1l, h1i, h1k, h1e, h1m⟩
      · -- m1 ≤ m2: m1 ≤ idx1 ≤ idx2 with key; m2 is max ≤ idx2.
        -- If m1 > m2, m2's maximality is contradicted.
        unfold readsLEQ; rw [h1e, hm2e]; simp
        by_contra h_gt; push_neg at h_gt
        exact absurd h1k (hm2m m1 h_gt (by omega) h1l)
    · exact absurd habs (by decide)
    · -- r1 is Case 3 (not found ≤ idx1): lift to allowDirty=true
      refine ⟨r1, ?_, ?_⟩
      · unfold generalReadResult; right; right; exact ⟨h1n, h1e⟩
      · unfold readsLEQ; rw [h1e, hm2e]
        simp [notFoundReadResult]
  · -- r2 Case 2: dirty at m2 > idx2 ≥ idx1. Same entry is dirty for idx1.
    refine ⟨r2, ?_, le_refl _⟩
    unfold generalReadResult
    right; left
    exact ⟨rfl, m2, hm2p, hm2l, by omega, hm2k, hm2e⟩
  · -- r2 Case 3: no entry ≤ idx2. Since idx1 ≤ idx2, no entry ≤ idx1 either.
    refine ⟨notFoundReadResult, ?_, by rw [h2e]; exact le_refl _⟩
    unfold generalReadResult
    right; right
    exact ⟨fun i hip hii hil => h2n i hip (by omega) hil, rfl⟩

-- Helper: Part 2: every result from idx1 has a ≥ counterpart from idx2 ≥ idx1.
-- Proof sketch by case on r1:
--   Case 1 (max m1 ≤ idx1): max m2 ≤ idx2 has m2 ≥ m1 (superset). r2 ≥ r1.
--   Case 2 (dirty m1 > idx1): if m1 ≤ idx2, max m2 ≥ m1; if m1 > idx2, dirty for idx2.
--   Case 3 (not found): any r2 has logIndex ≥ 0.
lemma generalReadResult_dirty_upper
    {s : CosmosState Key Value} {key : Key} {idx1 idx2 : Nat}
    (h_le : idx1 ≤ idx2)
    {r1 : ReadResult Value}
    (hr1 : generalReadResult s key idx1 true r1) :
    ∃ r2, generalReadResult s key idx2 true r2 ∧ readsLEQ r1 r2 := by
  unfold generalReadResult at hr1
  rcases hr1 with ⟨m1, h1p, h1l, h1i, h1k, h1e, h1m⟩ |
                  ⟨_, m1, h1p, h1l, h1gt, h1k, h1e⟩ |
                  ⟨h1n, h1e⟩
  · -- r1 Case 1: max m1 ≤ idx1 ≤ idx2. Get r2 from idx2 (no dirty).
    have ⟨r2, hr2f⟩ := generalReadResult_exists s key idx2 false
    unfold generalReadResult at hr2f
    rcases hr2f with ⟨m2, h2p, h2l, h2i, h2k, h2e, h2m⟩ |
                    ⟨habs, _⟩ | ⟨h2n, _⟩
    · -- r2 Case 1 (max m2 ≤ idx2): m2 ≥ m1 by maximality of m2.
      refine ⟨r2, ?_, ?_⟩
      · unfold generalReadResult; left; exact ⟨m2, h2p, h2l, h2i, h2k, h2e, h2m⟩
      · unfold readsLEQ; rw [h1e, h2e]; simp
        -- m1 ≤ m2: if m1 > m2, then m1 > m2 with m1 ≤ idx1 ≤ idx2, contradicts m2 maximality
        by_contra h_gt; push_neg at h_gt
        exact absurd h1k (h2m m1 (by omega) (by omega) h1l)
    · exact absurd habs (by decide)
    · -- r2 Case 3: impossible since m1 ≤ idx1 ≤ idx2 is an entry for key
      exact absurd h1k (h2n m1 h1p (by omega) h1l)
  · -- r1 Case 2: dirty m1 > idx1. Subcase on m1 vs idx2.
    by_cases h_m1_idx2 : m1 ≤ idx2
    · -- m1 ≤ idx2: get r2 from idx2 (no dirty). m2 ≥ m1.
      have ⟨r2, hr2f⟩ := generalReadResult_exists s key idx2 false
      unfold generalReadResult at hr2f
      rcases hr2f with ⟨m2, h2p, h2l, h2i, h2k, h2e, h2m⟩ |
                      ⟨habs, _⟩ | ⟨h2n, _⟩
      · refine ⟨r2, ?_, ?_⟩
        · unfold generalReadResult; left; exact ⟨m2, h2p, h2l, h2i, h2k, h2e, h2m⟩
        · unfold readsLEQ; rw [h1e, h2e]; simp
          by_contra h_gt; push_neg at h_gt
          exact absurd h1k (h2m m1 (by omega) h_m1_idx2 h1l)
      · exact absurd habs (by decide)
      · exact absurd h1k (h2n m1 h1p h_m1_idx2 h1l)
    · -- m1 > idx2: same entry is dirty for idx2
      push_neg at h_m1_idx2
      refine ⟨r1, ?_, le_refl _⟩
      unfold generalReadResult; right; left
      exact ⟨rfl, m1, h1p, h1l, by omega, h1k, h1e⟩
  · -- r1 Case 3 (not found): any r2 works, logIndex ≥ 0.
    have ⟨r2, hr2⟩ := generalReadResult_exists s key idx2 true
    refine ⟨r2, hr2, ?_⟩
    unfold readsLEQ; rw [h1e]; simp [notFoundReadResult]

-- Session consistency reads are monotonic per token sequence.
-- For token1 ≤ token2 (same epoch, checkpoint1 ≤ checkpoint2),
-- session reads use generalReadResult at max(checkpoint, readIndex).
-- Since checkpoint1 ≤ checkpoint2, idx1 ≤ idx2, so the two helpers apply.
theorem sessionReadsMonotonicPerTokenSequence_holds
    (s : CosmosState Key Value) :
    sessionConsistencyReadsMonotonicPerTokenSequence s := by
  unfold sessionConsistencyReadsMonotonicPerTokenSequence
  intro token1 token2 h1ep h2ep hrc hleq key
  unfold sessionTokenLEQ at hleq
  obtain ⟨hep, hcp⟩ := hleq
  -- Since both epochs ≥ 1, noSessionToken (epoch=0) is impossible
  -- and token1.epoch = token2.epoch (the epoch=0 disjunct is ruled out)
  have h_ep_eq : token1.epoch = token2.epoch := by
    rcases hep with h | h
    · exact h
    · omega
  -- idx1 ≤ idx2 where idx = max checkpoint readIndex
  have h_idx_le : max token1.checkpoint s.readIndex ≤ max token2.checkpoint s.readIndex := by
    omega
  -- Both tokens have same epoch; derive epoch conditions for if-branches
  have h1cond : s.epoch = token1.epoch ∨ token1 = noSessionToken →
                s.epoch = token2.epoch ∨ token2 = noSessionToken := by
    intro h; rcases h with h | h
    · left; rw [h, h_ep_eq]
    · -- token1 = noSessionToken has epoch 0, contradicts h1ep ≥ 1
      have : token1.epoch = 0 := by rw [h]; rfl
      omega
  have h2cond : s.epoch = token2.epoch ∨ token2 = noSessionToken →
                s.epoch = token1.epoch ∨ token1 = noSessionToken := by
    intro h; rcases h with h | h
    · left; rw [h, ← h_ep_eq]
    · have : token2.epoch = 0 := by rw [h]; rfl
      omega
  constructor
  · -- Part 1: ∀ r2 from token2, ∃ r1 from token1 with r1 ≤ r2
    intro r2 hr2
    unfold sessionConsistencyRead checkReadConsistency at hr2
    obtain ⟨hrc2, hr2g⟩ := hr2
    split_ifs at hr2g with hcond2
    · have hcond1 := h2cond hcond2
      have ⟨r1, hr1, hle⟩ := generalReadResult_dirty_lower h_idx_le hr2g
      refine ⟨r1, ?_, hle⟩
      unfold sessionConsistencyRead checkReadConsistency
      exact ⟨hrc2, by simp [hcond1]; exact hr1⟩
    · exact absurd hr2g id
  · -- Part 2: ∀ r1 from token1, ∃ r2 from token2 with r1 ≤ r2
    intro r1 hr1
    unfold sessionConsistencyRead checkReadConsistency at hr1
    obtain ⟨hrc1, hr1g⟩ := hr1
    split_ifs at hr1g with hcond1
    · have hcond2 := h1cond hcond1
      have ⟨r2, hr2, hle⟩ := generalReadResult_dirty_upper h_idx_le hr1g
      refine ⟨r2, ?_, hle⟩
      unfold sessionConsistencyRead checkReadConsistency
      exact ⟨hrc1, by simp [hcond2]; exact hr2⟩
    · exact absurd hr1g id

-- Helper: generalReadResult only depends on the log, not other state fields.
-- If two states have the same log, generalReadResult is equivalent.
lemma generalReadResult_log_eq
    {s s' : CosmosState Key Value} (h_log : s'.log = s.log)
    {key : Key} {idx : Nat} {allowDirty : Bool} {r : ReadResult Value} :
    generalReadResult s' key idx allowDirty r ↔ generalReadResult s key idx allowDirty r := by
  unfold generalReadResult; simp only [h_log]

-- Low monotonicity for reads based on generalReadResult with allowDirty=true:
-- When the log is the same and the index can only increase, the minimum read increases.
-- Proof: low' (min in s') has a ≤ counterpart r1 in s (by dirty_lower on same log).
-- Since low is min in s, low ≤ r1 ≤ low'.
lemma lowMonotonic_sameLog_increasingIndex
    {s s' : CosmosState Key Value}
    (h_log : s'.log = s.log)
    {idx idx' : Nat} (h_idx : idx ≤ idx')
    {key : Key}
    {low : ReadResult Value}
    (_ : generalReadResult s key idx true low)
    (hlow_min : ∀ r, generalReadResult s key idx true r → readsLEQ low r)
    {low' : ReadResult Value}
    (hlow' : generalReadResult s' key idx' true low')
    (_ : ∀ r, generalReadResult s' key idx' true r → readsLEQ low' r) :
    readsLEQ low low' := by
  -- Translate low' to state s via log equality
  have hlow'_s : generalReadResult s key idx' true low' :=
    (generalReadResult_log_eq h_log).mp hlow'
  -- low' at idx' has a ≤ counterpart r1 at idx (dirty_lower)
  have ⟨r1, hr1, hle⟩ := generalReadResult_dirty_lower h_idx hlow'_s
  -- low is min at idx, so low ≤ r1
  have hlow_r1 := hlow_min r1 hr1
  -- low ≤ r1 ≤ low'
  exact le_trans hlow_r1 hle

-- For non-dirty generalReadResult, the logIndex is ≤ index.
lemma generalReadResult_nodirty_logIndex_le_index
    {s : CosmosState Key Value} {key : Key} {index : Nat}
    {r : ReadResult Value}
    (h : generalReadResult s key index false r) :
    r.logIndex ≤ index := by
  unfold generalReadResult at h
  rcases h with ⟨i, _, _, hi, _, he, _⟩ | ⟨habs, _⟩ | ⟨_, he⟩
  · rw [he]; exact hi
  · exact absurd habs (by decide)
  · rw [he]; simp [notFoundReadResult]

-- The minimum of generalReadResult with allowDirty=true has logIndex ≤ index.
-- Proof: a non-dirty result always exists with logIndex ≤ index, so the min ≤ that.
lemma generalReadResult_min_logIndex_le_index
    {s : CosmosState Key Value} {key : Key} {index : Nat}
    {low : ReadResult Value}
    (_ : generalReadResult s key index true low)
    (hlow_min : ∀ r, generalReadResult s key index true r → readsLEQ low r) :
    low.logIndex ≤ index := by
  have ⟨r_nd, hr_nd⟩ := generalReadResult_exists s key index false
  have hr_nd_le := generalReadResult_nodirty_logIndex_le_index hr_nd
  -- r_nd is also valid with allowDirty=true (Case 1/3 don't depend on allowDirty)
  have hr_nd_dirty : generalReadResult s key index true r_nd := by
    unfold generalReadResult at hr_nd ⊢
    rcases hr_nd with h | ⟨habs, _⟩ | h
    · left; exact h
    · exact absurd habs (by decide)
    · right; right; exact h
  have := hlow_min r_nd hr_nd_dirty
  unfold readsLEQ at this
  omega

-- Low monotonicity for truncateLog case: log gets truncated but entries ≤ commitIndex preserved.
-- The min read has logIndex ≤ idx ≤ commitIndex, so it only uses preserved log entries.
-- Key: show low' (min in s') is valid in s too, then low ≤ low' since low is min in s.
lemma lowMonotonic_truncateLog
    {s s' : CosmosState Key Value}
    (ht : typesOK s)
    (h_trunc : truncateLog s s')
    {idx : Nat} (h_idx_ci : idx ≤ s.commitIndex)
    {key : Key}
    {low : ReadResult Value}
    (_ : generalReadResult s key idx true low)
    (hlow_min : ∀ r, generalReadResult s key idx true r → readsLEQ low r)
    {low' : ReadResult Value}
    (hlow' : generalReadResult s' key idx true low')
    (hlow'_min : ∀ r, generalReadResult s' key idx true r → readsLEQ low' r) :
    readsLEQ low low' := by
  obtain ⟨ti, hti_gt, hti_le, h_log, _, _, h_ci, _⟩ := h_trunc
  obtain ⟨_, _, h_ci_log⟩ := ht
  -- low' has logIndex ≤ idx (the min can't be a dirty read)
  have hlow'_le := generalReadResult_min_logIndex_le_index hlow' hlow'_min
  -- low' is a generalReadResult in s'. Unfold to see which case it is.
  -- Since low'.logIndex ≤ idx and dirty reads have logIndex > idx,
  -- low' must be Case 1 or Case 3.
  unfold generalReadResult at hlow'
  rcases hlow' with ⟨m, hmp, hml, hmi, hmk, hme, hmm⟩ |
                    ⟨_, m, _, _, hmgt, _, hme⟩ |
                    ⟨h_none, hme⟩
  · -- low' is Case 1: max m ≤ idx in s'. Transfer to s.
    -- m ≤ idx ≤ commitIndex < ti, so s'.log[m-1]! = s.log[m-1]!
    have hm_s : m ≤ s.log.length := by
      rw [h_log, List.length_take] at hml; omega
    have hm_eq : s'.log[m - 1]! = s.log[m - 1]! := by
      rw [h_log]; exact list_getElem_bang_take (by omega) (by omega)
    -- low' is also valid in s as Case 1
    have hlow'_s : generalReadResult s key idx true low' := by
      unfold generalReadResult; left
      refine ⟨m, hmp, hm_s, hmi, by rw [← hm_eq]; exact hmk, by rw [hme]; congr 1; simp [hm_eq], ?_⟩
      intro j hj hji hjl
      have hjl' : j ≤ s'.log.length := by rw [h_log, List.length_take]; omega
      have hj_eq : s'.log[j - 1]! = s.log[j - 1]! := by
        rw [h_log]; exact list_getElem_bang_take (by omega) (by omega)
      rw [← hj_eq]; exact hmm j hj hji hjl'
    exact hlow_min low' hlow'_s
  · -- low' is Case 2 (dirty): logIndex = m > idx, contradicts low'.logIndex ≤ idx
    rw [hme] at hlow'_le; simp at hlow'_le; omega
  · -- low' is Case 3: notFoundReadResult. Transfer to s.
    have hlow'_s : generalReadResult s key idx true low' := by
      unfold generalReadResult; right; right
      constructor
      · intro j hjp hji hjl
        have hjl' : j ≤ s'.log.length := by rw [h_log, List.length_take]; omega
        have hj_eq : s'.log[j - 1]! = s.log[j - 1]! := by
          rw [h_log]; exact list_getElem_bang_take (by omega) (by omega)
        rw [← hj_eq]; exact h_none j hjp hji hjl'
      · exact hme
    exact hlow_min low' hlow'_s

-- Bounded staleness reads are low monotonic across cosmosNext.
theorem boundedStalenessReadsLowMonotonic_cosmosNext
    {s s' : CosmosState Key Value}
    (ht : typesOK s) (hn : cosmosNext s s') :
    boundedStalenessReadsLowMonotonic s s' := by
  unfold boundedStalenessReadsLowMonotonic isLowMonotonic
  intro hrc key low hlow hlow_min low' hlow' hlow'_min
  -- Extract the generalReadResult from boundedStalenessRead
  unfold boundedStalenessRead checkReadConsistency at hlow hlow' hlow_min hlow'_min
  obtain ⟨_, hlow⟩ := hlow; obtain ⟨_, hlow'⟩ := hlow'
  have hlow_min' : ∀ r, generalReadResult s key s.commitIndex true r → readsLEQ low r := by
    intro r hr; exact hlow_min r ⟨hrc, hr⟩
  have hlow'_min' : ∀ r, generalReadResult s' key s'.commitIndex true r → readsLEQ low' r := by
    intro r hr
    exact hlow'_min r ⟨wclPreserved_cosmosNext hn ▸ hrc, hr⟩
  rcases hn with h_inc | h_trunc
  · -- increaseReadIndexAndOrCommitIndex: same log, commitIndex increases
    obtain ⟨h_ci, _, _, _, h_log, _, _⟩ := h_inc
    exact lowMonotonic_sameLog_increasingIndex h_log h_ci hlow hlow_min' hlow' hlow'_min'
  · -- truncateLog: commitIndex unchanged, entries ≤ commitIndex preserved
    have h_ci : s'.commitIndex = s.commitIndex := h_trunc.choose_spec.2.2.2.2.2.1
    rw [h_ci] at hlow' hlow'_min'
    exact lowMonotonic_truncateLog ht h_trunc (le_refl _) hlow hlow_min' hlow' hlow'_min'

-- Consistent prefix reads are low monotonic across cosmosNext.
theorem consistentPrefixReadsLowMonotonic_cosmosNext
    {s s' : CosmosState Key Value}
    (ht : typesOK s) (hn : cosmosNext s s') :
    consistentPrefixReadsLowMonotonic s s' := by
  unfold consistentPrefixReadsLowMonotonic isLowMonotonic
  intro hrc key low hlow hlow_min low' hlow' hlow'_min
  unfold consistentPrefixRead checkReadConsistency at hlow hlow' hlow_min hlow'_min
  obtain ⟨_, hlow⟩ := hlow; obtain ⟨_, hlow'⟩ := hlow'
  have hlow_min' : ∀ r, generalReadResult s key s.readIndex true r → readsLEQ low r := by
    intro r hr; exact hlow_min r ⟨hrc, hr⟩
  have hlow'_min' : ∀ r, generalReadResult s' key s'.readIndex true r → readsLEQ low' r := by
    intro r hr
    have hrc' : readConsistencyOK s'.writeConsistencyLevel .consistentPrefix := by
      rcases hn with h | h
      · obtain ⟨_, _, _, _, _, _, hwc⟩ := h; rw [hwc]; exact hrc
      · obtain ⟨_, _, _, _, _, _, _, hwc⟩ := h; rw [hwc]; exact hrc
    exact hlow'_min r ⟨hrc', hr⟩
  rcases hn with h_inc | h_trunc
  · -- increaseReadIndexAndOrCommitIndex: same log, readIndex increases
    obtain ⟨_, _, h_ri, _, h_log, _, _⟩ := h_inc
    exact lowMonotonic_sameLog_increasingIndex h_log h_ri hlow hlow_min' hlow' hlow'_min'
  · -- truncateLog: readIndex unchanged, entries ≤ readIndex ≤ commitIndex preserved
    have h_ri : s'.readIndex = s.readIndex := h_trunc.choose_spec.2.2.2.2.1
    obtain ⟨h_ri_ci, _⟩ := ht.2
    rw [h_ri] at hlow' hlow'_min'
    exact lowMonotonic_truncateLog ht h_trunc (by omega) hlow hlow_min' hlow' hlow'_min'

-- Session consistency reads are low monotonic across cosmosNext.
theorem sessionConsistencyReadsLowMonotonic_cosmosNext
    {s s' : CosmosState Key Value}
    (ht : typesOK s) (hn : cosmosNext s s') :
    sessionConsistencyReadsLowMonotonic s s' := by
  unfold sessionConsistencyReadsLowMonotonic isLowMonotonic
  intro hrc token htok key low hlow hlow_min low' hlow' hlow'_min
  unfold sessionConsistencyRead checkReadConsistency at hlow hlow' hlow_min hlow'_min
  obtain ⟨_, hlow⟩ := hlow; obtain ⟨_, hlow'⟩ := hlow'
  -- Split the if-then-else for the epoch condition
  split_ifs at hlow with hcond_s
  · split_ifs at hlow' with hcond_s'
    · -- Both epochs match. Extract the generalReadResult.
      have hlow_min' : ∀ r, generalReadResult s key (max token.checkpoint s.readIndex) true r →
          readsLEQ low r := by
        intro r hr; exact hlow_min r ⟨hrc, by simp [hcond_s]; exact hr⟩
      have hlow'_min' : ∀ r, generalReadResult s' key (max token.checkpoint s'.readIndex) true r →
          readsLEQ low' r := by
        intro r hr
        have hrc' : readConsistencyOK s'.writeConsistencyLevel .session := by
          rcases hn with h | h
          · obtain ⟨_, _, _, _, _, _, hwc⟩ := h; rw [hwc]; exact hrc
          · obtain ⟨_, _, _, _, _, _, _, hwc⟩ := h; rw [hwc]; exact hrc
        exact hlow'_min r ⟨hrc', by simp [hcond_s']; exact hr⟩
      rcases hn with h_inc | h_trunc
      · -- increaseReadIndexAndOrCommitIndex: same log, readIndex increases
        obtain ⟨_, _, h_ri, _, h_log, _, _⟩ := h_inc
        have h_idx : max token.checkpoint s.readIndex ≤ max token.checkpoint s'.readIndex := by
          omega
        exact lowMonotonic_sameLog_increasingIndex h_log h_idx hlow hlow_min' hlow' hlow'_min'
      · -- truncateLog: epoch changes (s'.epoch = s.epoch + 1).
        -- If token.epoch ≥ 1 and s.epoch = token.epoch, then s'.epoch ≠ token.epoch
        -- and token ≠ noSessionToken, so hcond_s' is False.
        -- Only token = noSessionToken (checkpoint = 0) survives.
        have h_ep := h_trunc.choose_spec.2.2.2.1 -- s'.epoch = s.epoch + 1
        have h_ri : s'.readIndex = s.readIndex := h_trunc.choose_spec.2.2.2.2.1
        -- After truncateLog, epoch changes. The only way both epoch conditions
        -- hold is if token = noSessionToken (checkpoint = 0, epoch = 0).
        have h_cp0 : token.checkpoint = 0 := by
          rcases hcond_s' with hs'_ep | hs'_tok
          · -- s'.epoch = token.epoch and s.epoch = token.epoch (or token = noSessionToken)
            rcases hcond_s with hs_ep | hs_tok
            · -- s'.epoch = token.epoch + 1, contradiction
              omega
            · subst hs_tok; rfl
          · subst hs'_tok; rfl
        rw [h_ri] at hlow' hlow'_min'
        simp only [h_cp0, Nat.zero_max] at hlow hlow' hlow_min' hlow'_min'
        obtain ⟨h_ri_ci, _⟩ := ht.2
        exact lowMonotonic_truncateLog ht h_trunc (by omega) hlow hlow_min' hlow' hlow'_min'
    · -- epoch doesn't match in s' → low' from False
      exact absurd hlow' id
  · -- epoch doesn't match in s → low from False
    exact absurd hlow id

-- BoundedStalenessIsBounded is preserved by cosmosNext.
-- cosmosNext either increases commitIndex (decreasing gap) or truncates log (decreasing length).
theorem boundedStalenessIsBounded_cosmosNext
    {s s' : CosmosState Key Value} {sb : Nat}
    (hinv : boundedStalenessIsBounded sb s)
    (hn : cosmosNext s s') :
    boundedStalenessIsBounded sb s' := by
  unfold boundedStalenessIsBounded at hinv ⊢
  intro hwc'
  rcases hn with h_inc | h_trunc
  · -- increaseReadIndexAndOrCommitIndex: log same, commitIndex increases
    obtain ⟨h_ci, _, _, _, h_log, _, hwc⟩ := h_inc
    have := hinv (by rw [hwc] at hwc'; exact hwc')
    rw [h_log]; omega
  · -- truncateLog: commitIndex same, log shrinks
    obtain ⟨ti, _, hti_le, h_log, _, _, h_ci, hwc⟩ := h_trunc
    have := hinv (by rw [hwc] at hwc'; exact hwc')
    rw [h_log, List.length_take]; omega

-- versionBoundOK is preserved by cosmosNext.
-- cosmosNext either increases readIndex (decreasing gap) or truncates log (decreasing length).
theorem versionBoundOK_cosmosNext
    {s s' : CosmosState Key Value} {vb : Nat}
    (hinv : versionBoundOK vb s)
    (hn : cosmosNext s s') :
    versionBoundOK vb s' := by
  unfold versionBoundOK at hinv ⊢
  rcases hn with h_inc | h_trunc
  · obtain ⟨_, _, h_ri, _, h_log, _, _⟩ := h_inc
    rw [h_log]; omega
  · obtain ⟨_, _, _, h_log, _, h_ri, _, _⟩ := h_trunc
    rw [h_log, h_ri, List.length_take]; omega

-- historyTokensUnique: write tokens in writeHistory are unique.
-- Requires an inductive argument over WReachable.
-- Supporting invariant: all tokens in history have checkpoint ≤ log.length
-- and tokens with current epoch have unique checkpoints.

-- Supporting invariant: tokens at the current epoch have checkpoint ≤ log.length.
-- This is the key to showing writeInitToken (checkpoint = log.length + 1) is fresh.
-- After truncateLog, epoch increases so no existing entry has the new epoch (vacuous).
def historyTokensBounded (s : CosmosWState Key Value) : Prop :=
  ∀ r : WriteHistoryEntry Key Value,
    r ∈ s.writeHistory →
    r.token.epoch = s.cosmos.epoch → r.token.checkpoint ≤ s.cosmos.log.length

-- historyTokensBounded holds at init
theorem historyTokensBounded_init (wc : ConsistencyLevel) :
    historyTokensBounded (wInit wc : CosmosWState Key Value) := by
  unfold historyTokensBounded
  intro r hr
  simp [wInit] at hr

-- historyTokensBounded preserved by wNext
theorem historyTokensBounded_wNext
    {s s' : CosmosWState Key Value} {sb vb : Nat}
    (hinv : historyTokensBounded s)
    (hinv_ep : ∀ r : WriteHistoryEntry Key Value,
      r ∈ s.writeHistory → r.token.epoch ≤ s.cosmos.epoch)
    (hn : wNext sb vb s s') :
    historyTokensBounded s' := by
  unfold historyTokensBounded at hinv ⊢
  intro r hr hep
  unfold wNext at hn
  rcases hn with ⟨h_hist, h_cosmos⟩ | h_write
  · -- stateOps: writeHistory unchanged, cosmos changes
    rw [h_hist] at hr
    rcases h_cosmos with h_inc | h_trunc
    · -- increaseReadIndexAndOrCommitIndex: log same, epoch same
      obtain ⟨_, _, _, _, h_log, h_ep, _⟩ := h_inc
      rw [h_log]; exact hinv r hr (by rw [h_ep] at hep; exact hep)
    · -- truncateLog: epoch increases → no old entry has new epoch
      obtain ⟨_, _, _, _, h_ep, _, _, _⟩ := h_trunc
      -- r.token.epoch = s'.cosmos.epoch = s.cosmos.epoch + 1
      -- but all old entries have epoch ≤ s.cosmos.epoch
      have := hinv_ep r hr
      omega
  · -- writeOps
    rcases h_write with h_begin | h_succ | h_fail
    · -- writeBegin: adds new entry, appends to log, epoch unchanged
      obtain ⟨key, value, _, h_log, h_hist, _, _, h_ep, _⟩ := h_begin
      rcases h_hist with ⟨_, h_hist⟩ | h_hist <;> {
        rw [h_hist] at hr; rw [Multiset.mem_cons] at hr
        rcases hr with rfl | hr
        · -- new entry: token = ⟨log.length + 1, epoch⟩
          simp [writeInitToken] at hep ⊢
          rw [h_log]; simp [List.length_append]
        · -- old entry: checkpoint ≤ old log.length ≤ new log.length
          have := hinv r hr (by rw [h_ep] at hep; exact hep)
          rw [h_log]; simp [List.length_append]; omega
      }
    · -- writeSuccess: cosmos unchanged, history swaps state field
      obtain ⟨record, h_mem, _, _, h_hist, h_cosmos⟩ := h_succ
      rw [h_hist] at hr; rw [Multiset.mem_cons] at hr
      rw [h_cosmos] at hep ⊢
      rcases hr with rfl | hr
      · -- updated record: same token as original
        simp; exact hinv record h_mem hep
      · exact hinv r (Multiset.mem_of_mem_erase hr) hep
    · -- writeFail: cosmos unchanged, history swaps state field
      obtain ⟨record, h_mem, _, h_hist, h_cosmos⟩ := h_fail
      rw [h_hist] at hr; rw [Multiset.mem_cons] at hr
      rw [h_cosmos] at hep ⊢
      rcases hr with rfl | hr
      · simp; exact hinv record h_mem hep
      · exact hinv r (Multiset.mem_of_mem_erase hr) hep

-- Epoch bound: all tokens in writeHistory have epoch ≤ current epoch.
def historyTokensEpochBounded (s : CosmosWState Key Value) : Prop :=
  ∀ r : WriteHistoryEntry Key Value,
    r ∈ s.writeHistory → r.token.epoch ≤ s.cosmos.epoch

theorem historyTokensEpochBounded_init (wc : ConsistencyLevel) :
    historyTokensEpochBounded (wInit wc : CosmosWState Key Value) := by
  intro r hr; simp [wInit] at hr

theorem historyTokensEpochBounded_wNext
    {s s' : CosmosWState Key Value} {sb vb : Nat}
    (hinv : historyTokensEpochBounded s)
    (hn : wNext sb vb s s') :
    historyTokensEpochBounded s' := by
  unfold historyTokensEpochBounded at hinv ⊢
  intro r hr
  rcases hn with ⟨h_hist, h_cosmos⟩ | h_write
  · rw [h_hist] at hr
    rcases h_cosmos with h_inc | h_trunc
    · obtain ⟨_, _, _, _, _, h_ep, _⟩ := h_inc
      rw [h_ep]; exact hinv r hr
    · obtain ⟨_, _, _, _, h_ep, _, _, _⟩ := h_trunc
      rw [h_ep]; have := hinv r hr; omega
  · rcases h_write with h_begin | h_succ | h_fail
    · obtain ⟨_, _, _, _, h_hist, _, _, h_ep, _⟩ := h_begin
      rcases h_hist with ⟨_, h_hist⟩ | h_hist <;> {
        rw [h_hist] at hr; rw [Multiset.mem_cons] at hr
        rcases hr with rfl | hr
        · simp [writeInitToken]; omega
        · rw [h_ep]; exact hinv r hr
      }
    · obtain ⟨record, h_mem, _, _, h_hist, h_cosmos⟩ := h_succ
      rw [h_hist] at hr; rw [Multiset.mem_cons] at hr
      rw [h_cosmos]
      rcases hr with rfl | hr
      · simp; exact hinv record h_mem
      · exact hinv r (Multiset.mem_of_mem_erase hr)
    · obtain ⟨record, h_mem, _, h_hist, h_cosmos⟩ := h_fail
      rw [h_hist] at hr; rw [Multiset.mem_cons] at hr
      rw [h_cosmos]
      rcases hr with rfl | hr
      · simp; exact hinv record h_mem
      · exact hinv r (Multiset.mem_of_mem_erase hr)

-- historyTokensUnique holds at init
theorem historyTokensUnique_init (wc : ConsistencyLevel) :
    historyTokensUnique (wInit wc : CosmosWState Key Value) := by
  unfold historyTokensUnique
  constructor
  · intro r1 r2 hr1; simp [wInit] at hr1
  · intro r; simp [wInit]

-- historyTokensUnique preserved by wNext (using historyTokensBounded)
-- Key insight for writeBegin: new token ⟨log.length+1, epoch⟩ is fresh
-- because existing tokens at same epoch have checkpoint ≤ log.length.
theorem historyTokensUnique_wNext
    {s s' : CosmosWState Key Value} {sb vb : Nat}
    (hinv_u : historyTokensUnique s)
    (hinv_b : historyTokensBounded s)
    (_ : historyTokensEpochBounded s)
    (hn : wNext sb vb s s') :
    historyTokensUnique s' := by
  unfold historyTokensUnique at hinv_u ⊢
  obtain ⟨h_tok_ne, h_count⟩ := hinv_u
  rcases hn with ⟨h_hist, _⟩ | h_write
  · -- stateOps: writeHistory unchanged
    rw [h_hist]; exact ⟨h_tok_ne, h_count⟩
  · rcases h_write with h_begin | h_succ | h_fail
    · -- writeBegin: adds new entry with fresh token
      obtain ⟨key, value, _, h_log, h_hist, _, _, h_ep, _⟩ := h_begin
      set new_tok := writeInitToken s.cosmos with h_ntd
      have h_fresh : ∀ r ∈ s.writeHistory, r.token ≠ new_tok := by
        intro r hr heq
        have := hinv_b r hr (by
          rw [h_ntd, writeInitToken] at heq
          exact congr_arg SessionToken.epoch heq)
        rw [h_ntd, writeInitToken] at heq
        have := congr_arg SessionToken.checkpoint heq
        simp at this; omega
      -- For both subcases of h_hist, the proof is identical
      rcases h_hist with ⟨_, h_hist⟩ | h_hist <;> {
        constructor
        · intro r1 r2 hr1 hr2 hne
          rw [h_hist] at hr1 hr2; simp [Multiset.mem_cons] at hr1 hr2
          rcases hr1 with rfl | hr1 <;> rcases hr2 with rfl | hr2
          · exact absurd rfl hne
          · exact fun heq => absurd heq.symm (h_fresh r2 hr2)
          · exact fun heq => absurd heq (h_fresh r1 hr1)
          · exact h_tok_ne r1 r2 hr1 hr2 hne
        · intro r
          rw [h_hist, Multiset.count_cons]
          split
          · -- r = new entry: count in old history is 0 (fresh token)
            rename_i heq
            have : Multiset.count r s.writeHistory = 0 :=
              Multiset.count_eq_zero.mpr (fun hm => by
                have h := h_fresh r hm; rw [heq] at h; simp at h)
            omega
          · -- r ≠ new entry: count unchanged
            exact h_count r
      }
    · -- writeSuccess: erase record, cons updated (same token, new state)
      obtain ⟨record, h_mem, h_init, _, h_hist, h_cosmos⟩ := h_succ
      have h_nme : record ∉ s.writeHistory.erase record := by
        have hcr := h_count record
        rw [← Multiset.count_eq_zero]; rw [Multiset.count_erase_self]; omega
      set nr : WriteHistoryEntry Key Value :=
        ⟨record.token, record.key, record.value, .succeeded⟩
      have h_ne : nr ≠ record := by
        intro h; have := congr_arg WriteHistoryEntry.state h
        simp [nr] at this; rw [← this] at h_init; exact absurd h_init (by decide)
      have h_nm : nr ∉ s.writeHistory := by
        intro hm; exact absurd (rfl : nr.token = record.token)
          (h_tok_ne nr record hm h_mem h_ne)
      constructor
      · intro r1 r2 hr1 hr2 hne
        rw [h_hist] at hr1 hr2; simp [Multiset.mem_cons] at hr1 hr2
        rcases hr1 with rfl | hr1 <;> rcases hr2 with rfl | hr2
        · exact absurd rfl hne
        · have hr2' := Multiset.mem_of_mem_erase hr2
          intro heq; have : nr.token = r2.token := heq; simp [nr] at this
          have hne2 : r2 ≠ record := fun h => by subst h; exact h_nme hr2
          exact absurd this (h_tok_ne record r2 h_mem hr2' hne2.symm)
        · have hr1' := Multiset.mem_of_mem_erase hr1
          intro heq; have : r1.token = nr.token := heq; simp [nr] at this
          have hne1 : r1 ≠ record := fun h => by subst h; exact h_nme hr1
          exact absurd this.symm (h_tok_ne record r1 h_mem hr1' hne1.symm)
        · exact h_tok_ne r1 r2 (Multiset.mem_of_mem_erase hr1)
            (Multiset.mem_of_mem_erase hr2) hne
      · intro r; rw [h_hist, Multiset.count_cons]
        split
        · rename_i heq; subst heq
          rw [Multiset.count_erase_of_ne h_ne]
          have := Multiset.count_eq_zero.mpr h_nm; omega
        · have : Multiset.count r (s.writeHistory.erase record) ≤
              Multiset.count r s.writeHistory := by
            by_cases h : r = record
            · subst h; rw [Multiset.count_erase_self]; omega
            · rw [Multiset.count_erase_of_ne h]
          exact le_trans this (h_count r)
    · -- writeFail: identical structure to writeSuccess
      obtain ⟨record, h_mem, h_init, h_hist, h_cosmos⟩ := h_fail
      have h_nme : record ∉ s.writeHistory.erase record := by
        have hcr := h_count record
        rw [← Multiset.count_eq_zero]; rw [Multiset.count_erase_self]; omega
      set nr : WriteHistoryEntry Key Value :=
        ⟨record.token, record.key, record.value, .failed⟩
      have h_ne : nr ≠ record := by
        intro h; have := congr_arg WriteHistoryEntry.state h
        simp [nr] at this; rw [← this] at h_init; exact absurd h_init (by decide)
      have h_nm : nr ∉ s.writeHistory := by
        intro hm; exact absurd (rfl : nr.token = record.token)
          (h_tok_ne nr record hm h_mem h_ne)
      constructor
      · intro r1 r2 hr1 hr2 hne
        rw [h_hist] at hr1 hr2; simp [Multiset.mem_cons] at hr1 hr2
        rcases hr1 with rfl | hr1 <;> rcases hr2 with rfl | hr2
        · exact absurd rfl hne
        · have hr2' := Multiset.mem_of_mem_erase hr2
          intro heq; have : nr.token = r2.token := heq; simp [nr] at this
          have hne2 : r2 ≠ record := fun h => by subst h; exact h_nme hr2
          exact absurd this (h_tok_ne record r2 h_mem hr2' hne2.symm)
        · have hr1' := Multiset.mem_of_mem_erase hr1
          intro heq; have : r1.token = nr.token := heq; simp [nr] at this
          have hne1 : r1 ≠ record := fun h => by subst h; exact h_nme hr1
          exact absurd this.symm (h_tok_ne record r1 h_mem hr1' hne1.symm)
        · exact h_tok_ne r1 r2 (Multiset.mem_of_mem_erase hr1)
            (Multiset.mem_of_mem_erase hr2) hne
      · intro r; rw [h_hist, Multiset.count_cons]
        split
        · rename_i heq; subst heq
          rw [Multiset.count_erase_of_ne h_ne]
          have := Multiset.count_eq_zero.mpr h_nm; omega
        · have : Multiset.count r (s.writeHistory.erase record) ≤
              Multiset.count r s.writeHistory := by
            by_cases h : r = record
            · subst h; rw [Multiset.count_erase_self]; omega
            · rw [Multiset.count_erase_of_ne h]
          exact le_trans this (h_count r)

/- ================================================================
   Section 13: StrongConsistencyReadsGiveLatestSuccessfulWrite
   ================================================================ -/

-- Supporting invariant: for init writes with current epoch and checkpoint in log range,
-- the log entry at that checkpoint has the correct key.
-- This is needed because writeBegin places the entry at log.length+1 and appends,
-- and the entry persists as long as the epoch doesn't change (truncateLog bumps epoch).
def initWriteLogConsistent (s : CosmosWState Key Value) : Prop :=
  ∀ record : WriteHistoryEntry Key Value,
    record ∈ s.writeHistory →
    record.state = .init →
    record.token.epoch = s.cosmos.epoch →
    record.token.checkpoint ≤ s.cosmos.log.length →
    record.token.checkpoint > 0 →
    (s.cosmos.log[record.token.checkpoint - 1]!).key = record.key

-- Supporting invariant (for strong consistency only): succeeded writes have
-- checkpoint ≤ commitIndex, and when checkpoint > 0 the log entry matches.
-- writeCanSucceed for strong gives checkpoint ≤ commitIndex. Since commitIndex
-- only increases and truncation preserves entries ≤ commitIndex, this is preserved.
def succeededWriteLogConsistent (s : CosmosWState Key Value) : Prop :=
  s.cosmos.writeConsistencyLevel = .strong →
  ∀ record : WriteHistoryEntry Key Value,
    record ∈ s.writeHistory →
    record.state = .succeeded →
    record.token.checkpoint ≤ s.cosmos.commitIndex
    ∧ (record.token.checkpoint > 0 →
        record.token.checkpoint ≤ s.cosmos.log.length
        ∧ (s.cosmos.log[record.token.checkpoint - 1]!).key = record.key)

-- Helper: if log has an entry for key at position c ≤ index, then any non-dirty
-- generalReadResult for that key has logIndex ≥ c (by maximality of Case 1).
lemma generalReadResult_nodirty_geq_matching
    {s : CosmosState Key Value} {key : Key} {index c : Nat}
    {r : ReadResult Value}
    (hr : generalReadResult s key index false r)
    (hc_pos : c > 0) (hc_len : c ≤ s.log.length) (hc_idx : c ≤ index)
    (hc_key : (s.log[c - 1]!).key = key) :
    r.logIndex ≥ c := by
  -- Proof: Case 1 has a max index i with log[i-1].key = key and i ≤ index.
  -- Since c ≤ index and log[c-1].key = key, the max i ≥ c. r.logIndex = i ≥ c.
  -- Case 2 impossible (dirty=false). Case 3: no entry for key contradicts hc_key.
  unfold generalReadResult at hr
  rcases hr with ⟨i, hi_pos, hi_len, hi_idx, hi_key, hi_eq, hi_max⟩ |
                 ⟨habs, _⟩ | ⟨h_none, _⟩
  · rw [hi_eq]; simp
    by_contra h; push_neg at h
    -- h : i < c, so c > i and c ≤ index and c ≤ log.length
    exact absurd hc_key (hi_max c h hc_idx hc_len)
  · exact absurd habs (by decide)
  · exact absurd hc_key (h_none c hc_pos hc_idx hc_len)

lemma initWriteLogConsistent_init (wc : ConsistencyLevel) :
    initWriteLogConsistent (wInit wc : CosmosWState Key Value) := by
  intro record hm; simp [wInit] at hm

lemma initWriteLogConsistent_wNext
    {s s' : CosmosWState Key Value} {sb vb : Nat}
    (hinv : initWriteLogConsistent s)
    (hinv_b : historyTokensBounded s)
    (hinv_ep : historyTokensEpochBounded s)
    (hn : wNext sb vb s s') :
    initWriteLogConsistent s' := by
  unfold initWriteLogConsistent
  unfold wNext writeOps at hn
  rcases hn with ⟨h_hist, h_cn⟩ | h_wb | h_succ | h_fail
  · -- stateOps: history unchanged, case on cosmosNext
    intro record h_mem h_init h_ep h_cp h_pos
    rw [h_hist] at h_mem
    rcases h_cn with h_inc | h_trunc
    · -- increaseReadIndexAndOrCommitIndex: log, epoch unchanged
      obtain ⟨_, _, _, _, h_log, h_epoch, _⟩ := h_inc
      rw [h_epoch] at h_ep; rw [h_log]
      have : record.token.checkpoint ≤ s.cosmos.log.length := by rw [← h_log]; exact h_cp
      exact hinv record h_mem h_init h_ep this h_pos
    · -- truncateLog: epoch increases, so epoch condition fails for old records
      obtain ⟨_, _, _, _, h_epoch, _, _, _⟩ := h_trunc
      -- s'.epoch = s.epoch + 1, but old records have epoch ≤ s.epoch
      have h_ep_bound := hinv_ep record h_mem
      rw [h_epoch] at h_ep; omega
  · -- writeBegin: new record at checkpoint = log.length+1, old records preserved
    obtain ⟨key, value, _, h_log, h_wh, _, _, h_epoch, _⟩ := h_wb
    -- Helper for old records: log extends, old positions preserved
    have old_record_ok : ∀ record : WriteHistoryEntry Key Value,
        record ∈ s.writeHistory → record.state = .init →
        record.token.epoch = s'.cosmos.epoch →
        record.token.checkpoint ≤ s'.cosmos.log.length →
        record.token.checkpoint > 0 →
        (s'.cosmos.log[record.token.checkpoint - 1]!).key = record.key := by
      intro r hr hi he hc hp
      -- Use historyTokensBounded: old record at current epoch has checkpoint ≤ log.length
      have h_old_cp : r.token.checkpoint ≤ s.cosmos.log.length :=
        hinv_b r hr (by rw [h_epoch] at he; exact he)
      have h_key := hinv r hr hi (by rw [h_epoch] at he; exact he) h_old_cp hp
      rw [h_log]; have hlt : r.token.checkpoint - 1 < s.cosmos.log.length := by omega
      -- Append preserves old entries: getElem! at index < old length
      have : (s.cosmos.log ++ [⟨key, value⟩])[r.token.checkpoint - 1]! =
          s.cosmos.log[r.token.checkpoint - 1]! := by
        simp only [List.getElem!_eq_getElem?_getD,
          List.getElem?_append_left hlt, List.getElem?_eq_getElem hlt]
      rw [this]; exact h_key
    intro record h_mem h_init h_ep h_cp h_pos
    rcases h_wh with ⟨_, h_wh⟩ | h_wh <;> rw [h_wh] at h_mem <;>
      simp [Multiset.mem_cons] at h_mem <;> rcases h_mem with rfl | h_mem
    · -- record is the new succeeded entry (not init)
      simp at h_init
    · exact old_record_ok record h_mem h_init h_ep h_cp h_pos
    · -- record is the new init entry: checkpoint = log.length + 1
      -- After append, log'[log.length] = ⟨key, value⟩
      simp only [writeInitToken] at h_init h_ep h_cp h_pos ⊢
      rw [h_log]
      have h_len : s.cosmos.log.length + 1 - 1 = s.cosmos.log.length := by omega
      rw [h_len]
      simp only [List.getElem!_eq_getElem?_getD,
        List.getElem?_append_right (le_refl _)]
      simp
    · exact old_record_ok record h_mem h_init h_ep h_cp h_pos
  · -- writeSuccess: cosmos unchanged, new record is succeeded (not init)
    obtain ⟨record', h_mem', h_init', _, h_hist, h_cosmos⟩ := h_succ
    intro record h_mem h_init h_ep h_cp h_pos
    rw [h_hist] at h_mem; simp [Multiset.mem_cons] at h_mem
    rcases h_mem with rfl | h_mem
    · simp at h_init -- new record has state = .succeeded
    · have h_mem_old := Multiset.mem_of_mem_erase h_mem
      rw [h_cosmos]; exact hinv record h_mem_old h_init (by rw [← h_cosmos]; exact h_ep)
        (by rw [← h_cosmos]; exact h_cp) h_pos
  · -- writeFail: cosmos unchanged, new record is failed (not init)
    obtain ⟨record', h_mem', h_init', h_hist, h_cosmos⟩ := h_fail
    intro record h_mem h_init h_ep h_cp h_pos
    rw [h_hist] at h_mem; simp [Multiset.mem_cons] at h_mem
    rcases h_mem with rfl | h_mem
    · simp at h_init -- new record has state = .failed
    · have h_mem_old := Multiset.mem_of_mem_erase h_mem
      rw [h_cosmos]; exact hinv record h_mem_old h_init (by rw [← h_cosmos]; exact h_ep)
        (by rw [← h_cosmos]; exact h_cp) h_pos

lemma succeededWriteLogConsistent_init (wc : ConsistencyLevel) :
    succeededWriteLogConsistent (wInit wc : CosmosWState Key Value) := by
  intro _ record hm; simp [wInit] at hm

lemma succeededWriteLogConsistent_wNext
    {s s' : CosmosWState Key Value} {sb vb : Nat}
    (hinv : succeededWriteLogConsistent s)
    (hinv_init : initWriteLogConsistent s)
    (hinv_tok : wTypesOK s)
    (hn : wNext sb vb s s') :
    succeededWriteLogConsistent s' := by
  unfold succeededWriteLogConsistent
  -- Helper: apply old invariant to old succeeded records, adapting writeConsistencyLevel
  unfold wNext writeOps at hn
  rcases hn with ⟨h_hist, h_cn⟩ | h_wb | h_succ | h_fail
  · -- stateOps: history unchanged, case on cosmosNext
    intro h_strong record h_mem h_succ_st
    rw [h_hist] at h_mem
    rcases h_cn with h_inc | h_trunc
    · -- increaseReadIndexAndOrCommitIndex: log unchanged, commitIndex ≥ old
      obtain ⟨h_ci_ge, _, _, _, h_log, _, h_wcl⟩ := h_inc
      have ⟨h_ci, h_rest⟩ := hinv (h_wcl ▸ h_strong) record h_mem h_succ_st
      exact ⟨le_trans h_ci h_ci_ge, fun hp => by
        have ⟨hl, hk⟩ := h_rest hp; exact ⟨h_log ▸ hl, h_log ▸ hk⟩⟩
    · -- truncateLog: log.take (i-1) where i > commitIndex.
      obtain ⟨i, h_i_gt, h_i_le, h_log, _, _, h_ci_eq, h_wcl⟩ := h_trunc
      have ⟨h_ci, h_rest⟩ := hinv (h_wcl ▸ h_strong) record h_mem h_succ_st
      constructor
      · rw [h_ci_eq]; exact h_ci
      · intro hp
        have ⟨h_len, h_key⟩ := h_rest hp
        constructor
        · rw [h_log, List.length_take]; omega
        · rw [h_log]
          have h_lt : record.token.checkpoint - 1 < i - 1 := by omega
          simp only [List.getElem!_eq_getElem?_getD, List.getElem?_take,
            if_pos h_lt] at h_key ⊢; exact h_key
  · -- writeBegin: for strong consistency, new writes can't immediately succeed
    -- (writeInitToken.checkpoint = log.length+1 > commitIndex ≥ log.length from typesOK).
    obtain ⟨key, value, _, h_log, h_wh, _, h_ci_eq, _, h_wcl⟩ := h_wb
    intro h_strong record h_mem h_succ_st
    have h_strong_old : s.cosmos.writeConsistencyLevel = .strong := h_wcl ▸ h_strong
    -- Helper for old records: append preserves entries
    have old_ok : record ∈ s.writeHistory →
        record.token.checkpoint ≤ s'.cosmos.commitIndex ∧
        (record.token.checkpoint > 0 →
          record.token.checkpoint ≤ s'.cosmos.log.length ∧
          (s'.cosmos.log[record.token.checkpoint - 1]!).key = record.key) := by
      intro hm
      have ⟨h_ci, h_rest⟩ := hinv h_strong_old record hm h_succ_st
      constructor
      · rw [h_ci_eq]; exact h_ci
      · intro hp; have ⟨h_len, h_key⟩ := h_rest hp
        constructor
        · rw [h_log]; simp; omega
        · rw [h_log]
          have hlt : record.token.checkpoint - 1 < s.cosmos.log.length := by omega
          simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append_left hlt,
            List.getElem?_eq_getElem hlt] at h_key ⊢; exact h_key
    rcases h_wh with ⟨h_wcs, h_wh⟩ | h_wh <;> rw [h_wh] at h_mem <;>
      simp [Multiset.mem_cons] at h_mem <;> rcases h_mem with rfl | h_mem
    · -- New succeeded entry: contradiction (checkpoint = log.length+1 > commitIndex)
      -- writeCanSucceed for strong: checkpoint ≤ commitIndex
      -- But checkpoint = (writeInitToken s.cosmos).checkpoint = log.length + 1
      -- And typesOK gives commitIndex ≤ log.length. Contradiction.
      unfold writeCanSucceed at h_wcs
      have h_cp := (h_wcs.2 h_strong_old).2
      simp [writeInitToken] at h_cp
      unfold wTypesOK typesOK at hinv_tok; omega
    · exact old_ok h_mem
    · simp at h_succ_st
    · exact old_ok h_mem
  · -- writeSuccess: cosmos unchanged. New succeeded record from initWriteLogConsistent.
    obtain ⟨record', h_mem', h_init', h_wcs, h_hist_eq, h_cosmos⟩ := h_succ
    intro h_strong record h_mem h_succ_st
    rw [h_hist_eq] at h_mem; simp [Multiset.mem_cons] at h_mem
    rcases h_mem with rfl | h_mem
    · -- New succeeded record: same token as old init record'
      have h_strong_old : s.cosmos.writeConsistencyLevel = .strong := h_cosmos ▸ h_strong
      unfold writeCanSucceed at h_wcs
      have ⟨h_ep, h_cp_ci⟩ := h_wcs.2 h_strong_old
      simp; constructor
      · rw [h_cosmos]; exact h_cp_ci
      · intro hp
        have h_cp_len : record'.token.checkpoint ≤ s.cosmos.log.length := by
          unfold wTypesOK typesOK at hinv_tok; omega
        have h_key := hinv_init record' h_mem' h_init' h_ep h_cp_len hp
        simp only [List.getElem!_eq_getElem?_getD] at h_key
        exact ⟨h_cosmos ▸ h_cp_len, h_cosmos ▸ h_key⟩
    · -- Old succeeded record from erased history
      have h_mem_old := Multiset.mem_of_mem_erase h_mem
      have ⟨h_ci, h_rest⟩ := hinv (h_cosmos ▸ h_strong) record h_mem_old h_succ_st
      exact ⟨h_cosmos ▸ h_ci, fun hp => by
        have ⟨hl, hk⟩ := h_rest hp; exact ⟨h_cosmos ▸ hl, h_cosmos ▸ hk⟩⟩
  · -- writeFail: new record is failed, not succeeded; old records preserved
    obtain ⟨record', _, _, h_hist_eq, h_cosmos⟩ := h_fail
    intro h_strong record h_mem h_succ_st
    rw [h_hist_eq] at h_mem; simp [Multiset.mem_cons] at h_mem
    rcases h_mem with rfl | h_mem
    · simp at h_succ_st
    · have h_mem_old := Multiset.mem_of_mem_erase h_mem
      have ⟨h_ci, h_rest⟩ := hinv (h_cosmos ▸ h_strong) record h_mem_old h_succ_st
      exact ⟨h_cosmos ▸ h_ci, fun hp => by
        have ⟨hl, hk⟩ := h_rest hp; exact ⟨h_cosmos ▸ hl, h_cosmos ▸ hk⟩⟩

-- Main theorem: combine the invariants with the read structure.
-- For strong consistency, succeeded writes have checkpoint ≤ commitIndex,
-- and the read returns the max entry ≤ commitIndex for the key, so
-- logIndex ≥ checkpoint for any matching succeeded write.
theorem strongConsistencyReadsGiveLatestSuccessfulWrite_holds
    {s : CosmosWState Key Value}
    (hinv : succeededWriteLogConsistent s) :
    strongConsistencyReadsGiveLatestSuccessfulWrite s := by
  unfold strongConsistencyReadsGiveLatestSuccessfulWrite
  intro h_strong key r hr
  unfold strongConsistencyRead checkReadConsistency at hr
  obtain ⟨_, hr⟩ := hr
  intro ⟨record, h_mem, h_key, h_succ, h_gt⟩
  have ⟨h_ci, h_rest⟩ := hinv h_strong record h_mem h_succ
  -- If checkpoint = 0, then checkpoint > r.logIndex is impossible (Nat)
  -- If checkpoint > 0, use log key match + generalReadResult_nodirty_geq_matching
  by_cases hp : record.token.checkpoint > 0
  · have ⟨h_len, h_log_key⟩ := h_rest hp
    have h_geq := generalReadResult_nodirty_geq_matching hr hp h_len h_ci
      (by rw [h_log_key, h_key])
    omega
  · omega

-- Helper: epoch is monotonically non-decreasing across wNext.
lemma epochMonotone_wNext
    {s s' : CosmosWState Key Value} {sb vb : Nat}
    (hn : wNext sb vb s s') :
    s.cosmos.epoch ≤ s'.cosmos.epoch := by
  unfold wNext writeOps at hn
  rcases hn with ⟨_, h_cn⟩ | h_wb | h_succ | h_fail
  · rcases h_cn with h_inc | h_trunc
    · obtain ⟨_, _, _, _, _, h_ep, _⟩ := h_inc; omega
    · obtain ⟨_, _, _, _, h_ep, _, _, _⟩ := h_trunc; omega
  · obtain ⟨_, _, _, _, _, _, _, h_ep, _⟩ := h_wb; omega
  · obtain ⟨_, _, _, _, _, h_cosmos⟩ := h_succ; rw [h_cosmos]
  · obtain ⟨_, _, _, _, h_cosmos⟩ := h_fail; rw [h_cosmos]

-- Helper: writeConsistencyLevel is unchanged by all wNext actions.
lemma wclPreserved_wNext
    {s s' : CosmosWState Key Value} {sb vb : Nat}
    (hn : wNext sb vb s s') :
    s'.cosmos.writeConsistencyLevel = s.cosmos.writeConsistencyLevel := by
  unfold wNext writeOps at hn
  rcases hn with ⟨_, h_cn⟩ | h_wb | h_succ | h_fail
  · rcases h_cn with h_inc | h_trunc
    · obtain ⟨_, _, _, _, _, _, h_wcl⟩ := h_inc; exact h_wcl
    · obtain ⟨_, _, _, _, _, _, _, h_wcl⟩ := h_trunc; exact h_wcl
  · obtain ⟨_, _, _, _, _, _, _, _, h_wcl⟩ := h_wb; exact h_wcl
  · obtain ⟨_, _, _, _, _, h_cosmos⟩ := h_succ; rw [h_cosmos]
  · obtain ⟨_, _, _, _, h_cosmos⟩ := h_fail; rw [h_cosmos]

/- ================================================================
   Section 14: SessionTokensUniquelyIdentifyWrites
   ================================================================ -/

-- The TLA+ property SessionTokensUniquelyIdentifyWrites (lines 177-187) has the
-- temporal pattern [](P => []Q). We decompose it into a step invariant:
-- "if epoch is unchanged across a step, all existing log entries are preserved."
-- This is the core fact: the only action that can destroy log entries is truncateLog,
-- which always bumps the epoch.

-- Step invariant: log entries at positions < old log.length are preserved when epoch
-- is unchanged. This holds because:
-- - increaseReadIndexAndOrCommitIndex: log unchanged
-- - truncateLog: epoch changes (so precondition fails)
-- - writeBegin: log extends (old entries preserved)
-- - writeSuccess/writeFail: cosmos unchanged
lemma logEntryPreservedSameEpoch
    {s s' : CosmosWState Key Value} {sb vb : Nat}
    (hn : wNext sb vb s s')
    (h_epoch : s'.cosmos.epoch = s.cosmos.epoch)
    {i : Nat} (hi : i < s.cosmos.log.length) :
    i < s'.cosmos.log.length ∧ s'.cosmos.log[i]! = s.cosmos.log[i]! := by
  unfold wNext writeOps at hn
  rcases hn with ⟨_, h_cn⟩ | h_wb | h_succ | h_fail
  · -- stateOps: cosmosNext
    rcases h_cn with h_inc | h_trunc
    · -- increaseReadIndexAndOrCommitIndex: log unchanged
      obtain ⟨_, _, _, _, h_log, _, _⟩ := h_inc
      rw [h_log]; exact ⟨hi, rfl⟩
    · -- truncateLog: epoch changes, contradicts h_epoch
      obtain ⟨_, _, _, _, h_ep, _, _, _⟩ := h_trunc; omega
  · -- writeBegin: log extends by append
    obtain ⟨key, value, _, h_log, _, _, _, h_ep, _⟩ := h_wb
    rw [h_log]; constructor
    · simp; omega
    · simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append_left hi,
        List.getElem?_eq_getElem hi]
  · -- writeSuccess: cosmos unchanged
    obtain ⟨_, _, _, _, _, h_cosmos⟩ := h_succ
    rw [h_cosmos]; exact ⟨hi, rfl⟩
  · -- writeFail: cosmos unchanged
    obtain ⟨_, _, _, _, h_cosmos⟩ := h_fail
    rw [h_cosmos]; exact ⟨hi, rfl⟩

-- Strengthened Q for SessionTokensUniquelyIdentifyWrites.
-- Uses strict < for epoch to ensure monotonicity: once token.epoch < epoch,
-- it stays < since epochs only increase. The second disjunct requires
-- token.epoch = s.epoch and the log entry to be in range and matching.
def sessionTokensUniquelyIdentifyWritesQ
    (s : CosmosState Key Value) (token : SessionToken)
    (key : Key) (value : Value) : Prop :=
  token.epoch < s.epoch ∨
    (token.epoch = s.epoch
    ∧ token.checkpoint > 0
    ∧ token.checkpoint ≤ s.log.length
    ∧ (s.log[token.checkpoint - 1]!).key = key
    ∧ (s.log[token.checkpoint - 1]!).value = value)

-- P implies Q (base case: P provides all conjuncts of the second disjunct)
lemma sessionTokensUniquelyIdentifyWrites_base
    {s : CosmosState Key Value} {token : SessionToken}
    {key : Key} {value : Value}
    (h_ep : token.epoch = s.epoch)
    (h_cp : token.checkpoint > 0)
    (h_len : token.checkpoint ≤ s.log.length)
    (h_key : (s.log[token.checkpoint - 1]!).key = key)
    (h_val : (s.log[token.checkpoint - 1]!).value = value) :
    sessionTokensUniquelyIdentifyWritesQ s token key value := by
  right; exact ⟨h_ep, h_cp, h_len, h_key, h_val⟩

-- Q is preserved by wNext (induction step).
-- Proof sketch:
-- - First disjunct (token.epoch < s.epoch): epochs only increase, so still < s'.epoch.
-- - Second disjunct (epoch matches, log entry matches):
--   - If epoch unchanged: log entries preserved by logEntryPreservedSameEpoch.
--     Log may grow (writeBegin) but old entries kept. checkpoint ≤ old length ≤ new.
--   - If epoch changed: must be truncateLog (only action that bumps epoch).
--     token.epoch = s.epoch < s.epoch + 1 = s'.epoch → first disjunct of Q(s').
theorem sessionTokensUniquelyIdentifyWrites_step
    {s s' : CosmosWState Key Value} {sb vb : Nat}
    {token : SessionToken} {key : Key} {value : Value}
    (hq : sessionTokensUniquelyIdentifyWritesQ s.cosmos token key value)
    (hn : wNext sb vb s s') :
    sessionTokensUniquelyIdentifyWritesQ s'.cosmos token key value := by
  unfold sessionTokensUniquelyIdentifyWritesQ at hq ⊢
  rcases hq with h_lt | ⟨h_ep, h_pos, h_len, h_key, h_val⟩
  · -- First disjunct: token.epoch < s.epoch, epochs only increase
    left; have := epochMonotone_wNext hn; omega
  · -- Second disjunct: epoch matches and log entry matches
    by_cases h_ep' : s'.cosmos.epoch = s.cosmos.epoch
    · -- Epoch unchanged → log entries preserved, checkpoint still in range
      right
      have hi : token.checkpoint - 1 < s.cosmos.log.length := by omega
      have ⟨hi', h_eq⟩ := logEntryPreservedSameEpoch hn h_ep' hi
      exact ⟨by omega, h_pos, by omega, by rw [h_eq]; exact h_key,
        by rw [h_eq]; exact h_val⟩
    · -- Epoch changed → token.epoch = s.epoch < s'.epoch → first disjunct
      left; have := epochMonotone_wNext hn; omega

/- ================================================================
   Section 15: CommitIndexImpliesDurability
   ================================================================ -/

-- Strengthened Q for CommitIndexImpliesDurability.
-- The key strengthening is tracking checkpoint ≤ commitIndex (not just ≤ log.length).
-- This is needed because truncateLog can remove entries after commitIndex,
-- so we need checkpoint to be at or before commitIndex to ensure preservation.
def commitIndexImpliesDurabilityQ
    (s : CosmosState Key Value) (checkpoint : Nat)
    (pfx : List (LogEntry Key Value)) : Prop :=
  checkpoint ≤ s.commitIndex ∧ s.log.take checkpoint = pfx

-- Base case: P → Q.
-- P: checkpoint = commitIndex and the log prefix matches.
lemma commitIndexImpliesDurability_base
    {s : CosmosState Key Value} {checkpoint : Nat}
    {pfx : List (LogEntry Key Value)}
    (htok : typesOK s)
    (h_eq : checkpoint = s.commitIndex)
    (h_pfx : (s.log = [] ∧ pfx = []) ∨ s.log.take checkpoint = pfx) :
    commitIndexImpliesDurabilityQ s checkpoint pfx := by
  unfold commitIndexImpliesDurabilityQ
  constructor
  · omega
  · rcases h_pfx with ⟨h_log, h_pref⟩ | h_take
    · subst h_pref; rw [h_eq]
      have : s.commitIndex = 0 := by
        have := htok.2.2; rw [h_log] at this; simp at this; omega
      rw [this]; simp
    · exact h_take

-- Step invariant: Q preserved by wNext.
-- Proof sketch:
-- - increaseReadIndexAndOrCommitIndex: log unchanged, commitIndex grows → both conjuncts preserved
-- - truncateLog: checkpoint ≤ commitIndex < i, so take (i-1) preserves first checkpoint entries;
--   commitIndex unchanged; use List.take_take
-- - writeBegin: log appended, take checkpoint of (l ++ [x]) = take checkpoint l since
--   checkpoint ≤ commitIndex ≤ log.length; commitIndex unchanged
-- - writeSuccess/writeFail: cosmos unchanged
theorem commitIndexImpliesDurability_step
    {s s' : CosmosWState Key Value} {sb vb : Nat}
    {checkpoint : Nat} {pfx : List (LogEntry Key Value)}
    (hq : commitIndexImpliesDurabilityQ s.cosmos checkpoint pfx)
    (htok : typesOK s.cosmos)
    (hn : wNext sb vb s s') :
    commitIndexImpliesDurabilityQ s'.cosmos checkpoint pfx := by
  unfold commitIndexImpliesDurabilityQ at hq ⊢
  obtain ⟨h_ci, h_take⟩ := hq
  unfold wNext writeOps at hn
  rcases hn with ⟨_, h_cn⟩ | h_wb | h_succ | h_fail
  · -- stateOps: cosmosNext
    rcases h_cn with h_inc | h_trunc
    · -- increaseReadIndexAndOrCommitIndex: log unchanged, commitIndex grows
      obtain ⟨h_ci', _, _, _, h_log, _, _⟩ := h_inc
      rw [h_log]; exact ⟨by omega, h_take⟩
    · -- truncateLog: s'.log = s.log.take (i-1), commitIndex unchanged
      obtain ⟨i, h_gt, h_le, h_log, _, h_ri', h_ci', _⟩ := h_trunc
      constructor
      · rw [h_ci']; omega
      · rw [h_log]
        -- checkpoint ≤ commitIndex < i, so checkpoint ≤ i - 1
        -- (s.log.take (i-1)).take checkpoint = s.log.take (min (i-1) checkpoint)
        -- = s.log.take checkpoint = pfx
        have h_le_ci : checkpoint ≤ s.cosmos.commitIndex := h_ci
        rw [List.take_take, Nat.min_eq_left (by omega)]
        exact h_take
  · -- writeBegin: log appended, commitIndex unchanged
    obtain ⟨key, value, _, h_log, _, h_ri, h_ci', h_ep, h_wcl⟩ := h_wb
    constructor
    · rw [h_ci']; omega
    · rw [h_log]
      -- checkpoint ≤ commitIndex ≤ log.length, so take of append = take of original
      have h_le : checkpoint ≤ s.cosmos.log.length := by
        have := htok.2.2; omega
      rw [List.take_append_of_le_length h_le]
      exact h_take
  · -- writeSuccess: cosmos unchanged
    obtain ⟨_, _, _, _, _, h_cosmos⟩ := h_succ
    rw [h_cosmos]; exact ⟨h_ci, h_take⟩
  · -- writeFail: cosmos unchanged
    obtain ⟨_, _, _, _, h_cosmos⟩ := h_fail
    rw [h_cosmos]; exact ⟨h_ci, h_take⟩

/- ================================================================
   Section 16: StrongConsistencyCommittedWritesDurable
   ================================================================ -/

-- Strengthened Q for StrongConsistencyCommittedWritesDurable.
-- Instead of tracking the read property directly (which isn't inductive),
-- we track the underlying log-level facts that imply it:
-- (1) WCL = Strong (unchanged by all actions)
-- (2) The record with our token exists in writeHistory
-- (3) token.checkpoint ≤ commitIndex (commitIndex only grows)
-- (4) If checkpoint > 0, the log entry at checkpoint-1 has the right key
-- The original TLA+ Q follows from (3)+(4) via generalReadResult_nodirty_geq_matching.
def strongConsistencyCommittedWritesDurableQ
    (s : CosmosWState Key Value) (token : SessionToken) (key : Key) : Prop :=
  s.cosmos.writeConsistencyLevel = .strong
  ∧ (∃ record : WriteHistoryEntry Key Value,
      record ∈ s.writeHistory ∧ record.token = token ∧ record.key = key)
  ∧ token.checkpoint ≤ s.cosmos.commitIndex
  ∧ (token.checkpoint > 0 →
      token.checkpoint ≤ s.cosmos.log.length
      ∧ (s.cosmos.log[token.checkpoint - 1]!).key = key)

-- Base case: P → Q.
-- P: WCL = Strong, ∃ succeeded record with given token.
-- Uses succeededWriteLogConsistent to get checkpoint ≤ commitIndex and log match.
lemma strongConsistencyCommittedWritesDurable_base
    {s : CosmosWState Key Value}
    {token : SessionToken}
    (hinv : succeededWriteLogConsistent s)
    (h_strong : s.cosmos.writeConsistencyLevel = .strong)
    (record : WriteHistoryEntry Key Value)
    (h_mem : record ∈ s.writeHistory)
    (h_tok : record.token = token)
    (h_succ : record.state = .succeeded) :
    strongConsistencyCommittedWritesDurableQ s token record.key := by
  unfold strongConsistencyCommittedWritesDurableQ
  have ⟨h_ci, h_rest⟩ := hinv h_strong record h_mem h_succ
  exact ⟨h_strong, ⟨record, h_mem, h_tok, rfl⟩, by rw [← h_tok]; exact h_ci,
    by rw [← h_tok]; exact h_rest⟩

-- Step invariant: Q preserved by wNext.
-- Proof sketch:
-- - WCL unchanged by all actions.
-- - Record persists: writeSuccess/writeFail only operate on init-state records;
--   writeBegin adds new records (doesn't remove). stateOps don't change history.
--   When the exact record is the target of writeSuccess/writeFail, the replacement
--   has the same token and key (only state changes).
-- - checkpoint ≤ commitIndex: commitIndex only grows or stays same.
-- - Log entry preserved: checkpoint ≤ commitIndex, and truncateLog only removes
--   entries > commitIndex; writeBegin appends; others don't change log.
theorem strongConsistencyCommittedWritesDurable_step
    {s s' : CosmosWState Key Value} {sb vb : Nat}
    {token : SessionToken} {key : Key}
    (hq : strongConsistencyCommittedWritesDurableQ s token key)
    (hn : wNext sb vb s s') :
    strongConsistencyCommittedWritesDurableQ s' token key := by
  unfold strongConsistencyCommittedWritesDurableQ at hq ⊢
  obtain ⟨h_wcl, ⟨record, h_mem, h_tok, h_key⟩, h_ci, h_log_entry⟩ := hq
  unfold wNext writeOps at hn
  rcases hn with ⟨h_hist, h_cn⟩ | h_wb | h_succ | h_fail
  · -- stateOps: writeHistory unchanged, cosmos changes
    rcases h_cn with h_inc | h_trunc
    · -- increaseReadIndexAndOrCommitIndex: log/epoch unchanged, commitIndex grows
      obtain ⟨h_ci', _, _, _, h_log, _, h_wcl'⟩ := h_inc
      have h_mem' : record ∈ s'.writeHistory := by rw [h_hist]; exact h_mem
      refine ⟨by rw [h_wcl']; exact h_wcl, ⟨record, h_mem', h_tok, h_key⟩, by omega, ?_⟩
      intro h_pos; rw [h_log]; exact h_log_entry h_pos
    · -- truncateLog: log shrinks but only after commitIndex
      obtain ⟨i, h_gt, h_le, h_log, _, _, h_ci', h_wcl'⟩ := h_trunc
      have h_mem' : record ∈ s'.writeHistory := by rw [h_hist]; exact h_mem
      refine ⟨by rw [h_wcl']; exact h_wcl, ⟨record, h_mem', h_tok, h_key⟩,
              by omega, ?_⟩
      intro h_pos
      have ⟨h_len, h_key_eq⟩ := h_log_entry h_pos
      simp only [List.getElem!_eq_getElem?_getD] at h_key_eq
      constructor
      · rw [h_log]; simp [List.length_take]; omega
      · rw [h_log]
        have h_lt : token.checkpoint - 1 < s.cosmos.log.length := by omega
        simp only [List.getElem!_eq_getElem?_getD,
          List.getElem?_take, if_pos (by omega : token.checkpoint - 1 < i - 1)]
        exact h_key_eq
  · -- writeBegin: log appended, commitIndex unchanged, new record added
    obtain ⟨wkey, wvalue, _, h_log, h_wh, h_ri, h_ci', h_ep, h_wcl'⟩ := h_wb
    -- Record persists (it's in the old history, writeBegin only adds)
    have h_mem' : record ∈ s'.writeHistory := by
      rcases h_wh with ⟨_, h_wh'⟩ | h_wh'
      · rw [h_wh']; exact Multiset.mem_cons_of_mem h_mem
      · rw [h_wh']; exact Multiset.mem_cons_of_mem h_mem
    refine ⟨by rw [h_wcl']; exact h_wcl, ⟨record, h_mem', h_tok, h_key⟩,
            by omega, ?_⟩
    intro h_pos
    have ⟨h_len, h_key_eq⟩ := h_log_entry h_pos
    constructor
    · rw [h_log]; simp; omega
    · rw [h_log]
      have h_lt : token.checkpoint - 1 < s.cosmos.log.length := by omega
      simp only [List.getElem!_eq_getElem?_getD,
        List.getElem?_append_left h_lt, List.getElem?_eq_getElem h_lt]
      simp only [List.getElem!_eq_getElem?_getD,
        List.getElem?_eq_getElem h_lt] at h_key_eq
      exact h_key_eq
  · -- writeSuccess: cosmos unchanged, record persists (token/key preserved)
    obtain ⟨rec2, h_mem2, h_init2, _, h_wh', h_cosmos⟩ := h_succ
    rw [h_cosmos]
    have h_mem' : ∃ r : WriteHistoryEntry Key Value,
        r ∈ s'.writeHistory ∧ r.token = token ∧ r.key = key := by
      rw [h_wh']
      by_cases heq : record = rec2
      · -- record = rec2: the new entry has same token and key
        exact ⟨⟨rec2.token, rec2.key, rec2.value, .succeeded⟩,
          Multiset.mem_cons_self _ _,
          by subst heq; exact h_tok,
          by subst heq; exact h_key⟩
      · exact ⟨record, Multiset.mem_cons_of_mem
          ((Multiset.mem_erase_of_ne heq).mpr h_mem), h_tok, h_key⟩
    exact ⟨h_wcl, h_mem', h_ci, h_log_entry⟩
  · -- writeFail: cosmos unchanged, record persists (token/key preserved)
    obtain ⟨rec2, h_mem2, h_init2, h_wh', h_cosmos⟩ := h_fail
    rw [h_cosmos]
    have h_mem' : ∃ r : WriteHistoryEntry Key Value,
        r ∈ s'.writeHistory ∧ r.token = token ∧ r.key = key := by
      rw [h_wh']
      by_cases heq : record = rec2
      · exact ⟨⟨rec2.token, rec2.key, rec2.value, .failed⟩,
          Multiset.mem_cons_self _ _,
          by subst heq; exact h_tok,
          by subst heq; exact h_key⟩
      · exact ⟨record, Multiset.mem_cons_of_mem
          ((Multiset.mem_erase_of_ne heq).mpr h_mem), h_tok, h_key⟩
    exact ⟨h_wcl, h_mem', h_ci, h_log_entry⟩

-- Derive original TLA+ property from Q_strong.
-- If Q_strong holds, all strong reads of the key have logIndex ≥ token.checkpoint.
theorem strongConsistencyCommittedWritesDurable_reads
    {s : CosmosWState Key Value}
    {token : SessionToken} {key : Key}
    (hq : strongConsistencyCommittedWritesDurableQ s token key) :
    s.cosmos.writeConsistencyLevel = .strong
    ∧ (∃ record : WriteHistoryEntry Key Value,
        record ∈ s.writeHistory ∧ record.token = token
        ∧ ∀ r : ReadResult Value, strongConsistencyRead s.cosmos record.key r →
            token.checkpoint ≤ r.logIndex) := by
  obtain ⟨h_wcl, ⟨record, h_mem, h_tok, h_key⟩, h_ci, h_log_entry⟩ := hq
  refine ⟨h_wcl, record, h_mem, h_tok, ?_⟩
  intro r hr
  unfold strongConsistencyRead checkReadConsistency at hr
  obtain ⟨_, hr⟩ := hr
  by_cases h_pos : token.checkpoint > 0
  · have ⟨h_len, h_key_eq⟩ := h_log_entry h_pos
    exact generalReadResult_nodirty_geq_matching hr h_pos h_len h_ci
      (by rw [h_key_eq, h_key])
  · omega -- token.checkpoint = 0 ≤ anything

/- ================================================================
   Section 17: SessionConsistencyReadMyWritesPerTokenSequence
   ================================================================ -/

-- Invariant: for every record in writeHistory, the log entry (if still in the
-- same epoch) matches the record's key and value. This is a lifting of
-- sessionTokensUniquelyIdentifyWritesQ to all records.
def writeHistoryLogConsistent (s : CosmosWState Key Value) : Prop :=
  ∀ record : WriteHistoryEntry Key Value,
    record ∈ s.writeHistory →
    sessionTokensUniquelyIdentifyWritesQ s.cosmos record.token record.key record.value

lemma writeHistoryLogConsistent_init (wc : ConsistencyLevel) :
    writeHistoryLogConsistent (wInit wc : CosmosWState Key Value) := by
  intro record hm; simp [wInit] at hm

lemma writeHistoryLogConsistent_wNext
    {s s' : CosmosWState Key Value} {sb vb : Nat}
    (hinv : writeHistoryLogConsistent s)
    (hn : wNext sb vb s s') :
    writeHistoryLogConsistent s' := by
  unfold writeHistoryLogConsistent
  intro record h_mem
  unfold wNext writeOps at hn
  rcases hn with ⟨h_hist, h_cn⟩ | h_wb | h_succ | h_fail
  · -- stateOps: writeHistory unchanged, cosmos changes via cosmosNext
    rw [h_hist] at h_mem
    exact sessionTokensUniquelyIdentifyWrites_step (hinv record h_mem)
      (show wNext sb vb s s' from Or.inl ⟨h_hist, h_cn⟩)
  · -- writeBegin: new record added, log extended
    obtain ⟨key, value, h_wa, h_log, h_wh, h_ri, h_ci, h_ep, h_wcl⟩ := h_wb
    have h_wNext : wNext sb vb s s' := by
      right; left; exact ⟨key, value, h_wa, h_log, h_wh, h_ri, h_ci, h_ep, h_wcl⟩
    -- Helper: prove Q for the new record (writeInitToken, key, value)
    have new_record_ok : sessionTokensUniquelyIdentifyWritesQ s'.cosmos
        (writeInitToken s.cosmos) key value := by
      unfold sessionTokensUniquelyIdentifyWritesQ
      right
      simp only [writeInitToken]
      refine ⟨by rw [h_ep], by omega, by rw [h_log]; simp, ?_, ?_⟩
      · rw [h_log]
        simp only [List.getElem!_eq_getElem?_getD]
        simp
      · rw [h_log]
        simp only [List.getElem!_eq_getElem?_getD]
        simp
    rcases h_wh with ⟨_, h_wh'⟩ | h_wh'
    · rw [h_wh'] at h_mem
      rcases Multiset.mem_cons.mp h_mem with rfl | h_old
      · exact new_record_ok
      · exact sessionTokensUniquelyIdentifyWrites_step (hinv record h_old) h_wNext
    · rw [h_wh'] at h_mem
      rcases Multiset.mem_cons.mp h_mem with rfl | h_old
      · exact new_record_ok
      · exact sessionTokensUniquelyIdentifyWrites_step (hinv record h_old) h_wNext
  · -- writeSuccess: cosmos unchanged, record token/key/value preserved
    obtain ⟨rec2, h_mem2, _, _, h_wh', h_cosmos⟩ := h_succ
    rw [h_cosmos]
    rw [h_wh'] at h_mem
    rcases Multiset.mem_cons.mp h_mem with rfl | h_old
    · exact hinv rec2 h_mem2
    · exact hinv record (Multiset.mem_of_mem_erase h_old)
  · -- writeFail: cosmos unchanged, record token/key/value preserved
    obtain ⟨rec2, h_mem2, _, h_wh', h_cosmos⟩ := h_fail
    rw [h_cosmos]
    rw [h_wh'] at h_mem
    rcases Multiset.mem_cons.mp h_mem with rfl | h_old
    · exact hinv rec2 h_mem2
    · exact hinv record (Multiset.mem_of_mem_erase h_old)

-- Helper: generalReadResult with any allowDirty flag, if there's a matching entry
-- at position c ≤ index, then logIndex ≥ c.
lemma generalReadResult_geq_matching
    {s : CosmosState Key Value} {key : Key} {index c : Nat}
    {allowDirty : Bool} {r : ReadResult Value}
    (hr : generalReadResult s key index allowDirty r)
    (hc_pos : c > 0) (hc_len : c ≤ s.log.length) (hc_idx : c ≤ index)
    (hc_key : (s.log[c - 1]!).key = key) :
    r.logIndex ≥ c := by
  unfold generalReadResult at hr
  rcases hr with ⟨i, hi_pos, hi_len, hi_idx, hi_key, hi_eq, hi_max⟩ |
                 ⟨_, i, hi_pos, hi_len, hi_gt, _, hi_eq⟩ |
                 ⟨h_none, _⟩
  · rw [hi_eq]; simp
    by_contra h; push_neg at h
    exact absurd hc_key (hi_max c h hc_idx hc_len)
  · rw [hi_eq]; simp; omega
  · exact absurd hc_key (h_none c hc_pos hc_idx hc_len)

-- Strengthened Q for SessionConsistencyReadMyWritesPerTokenSequence.
def sessionReadMyWritesQ
    (s : CosmosWState Key Value)
    (token1 : SessionToken) (key : Key) (value : Value) : Prop :=
  readConsistencyOK s.cosmos.writeConsistencyLevel .session
  ∧ sessionTokensUniquelyIdentifyWritesQ s.cosmos token1 key value

-- Base case: P + invariants → Q.
lemma sessionReadMyWrites_base
    {s : CosmosWState Key Value}
    {token1 : SessionToken} {key : Key} {value : Value}
    (hinv : writeHistoryLogConsistent s)
    (h_rco : readConsistencyOK s.cosmos.writeConsistencyLevel .session)
    (record : WriteHistoryEntry Key Value)
    (h_mem : record ∈ s.writeHistory)
    (h_tok : record.token = token1)
    (h_key : record.key = key)
    (h_val : record.value = value) :
    sessionReadMyWritesQ s token1 key value := by
  exact ⟨h_rco, by have hq := hinv record h_mem; rw [h_tok, h_key, h_val] at hq; exact hq⟩

-- Step: Q preserved by wNext.
theorem sessionReadMyWrites_step
    {s s' : CosmosWState Key Value} {sb vb : Nat}
    {token1 : SessionToken} {key : Key} {value : Value}
    (hq : sessionReadMyWritesQ s token1 key value)
    (hn : wNext sb vb s s') :
    sessionReadMyWritesQ s' token1 key value := by
  obtain ⟨h_rco, h_writes⟩ := hq
  refine ⟨?_, sessionTokensUniquelyIdentifyWrites_step h_writes hn⟩
  -- readConsistencyOK preserved: WCL unchanged
  rw [wclPreserved_wNext hn]; exact h_rco

-- Derive original TLA+ reads property from Q.
-- Case split on sessionTokensUniquelyIdentifyWritesQ:
-- - token1.epoch < s.epoch: if token1.epoch = token2.epoch, session read invalid;
--   if token1.epoch = 0, sessionTokenLEQ forces token2.checkpoint ≥ token1.checkpoint,
--   but noSessionToken case forces checkpoint = 0.
-- - token1.epoch = s.epoch: log entry matches, use generalReadResult_geq_matching.
theorem sessionReadMyWrites_reads
    {s : CosmosWState Key Value}
    {token1 token2 : SessionToken} {key : Key} {value : Value}
    (hq : sessionReadMyWritesQ s token1 key value)
    (h_leq : sessionTokenLEQ token1 token2)
    (h_tok1_pos : token1.epoch ≥ 1 ∨ token1 = noSessionToken) :
    readConsistencyOK s.cosmos.writeConsistencyLevel .session
    ∧ ∀ r : ReadResult Value, sessionConsistencyRead s.cosmos token2 key r →
        readsLEQ ⟨token1.checkpoint, some value⟩ r := by
  obtain ⟨h_rco, h_writes⟩ := hq
  refine ⟨h_rco, ?_⟩
  intro r hr
  unfold readsLEQ; simp
  by_cases h_pos : token1.checkpoint > 0
  · unfold sessionTokensUniquelyIdentifyWritesQ at h_writes
    rcases h_writes with h_lt | ⟨h_ep, _, h_len, h_key_eq, _⟩
    · -- token1.epoch < s.epoch
      obtain ⟨h_ep_leq, h_cp_leq⟩ := h_leq
      rcases h_ep_leq with h_ep_eq | h_ep_zero
      · -- token1.epoch = token2.epoch, both < s.epoch → session read invalid
        unfold sessionConsistencyRead checkReadConsistency at hr
        obtain ⟨_, hr⟩ := hr
        have : ¬(s.cosmos.epoch = token2.epoch ∨ token2 = noSessionToken) := by
          push_neg; constructor
          · omega
          · intro h_no; subst h_no; simp [noSessionToken] at h_cp_leq; omega
        simp [this] at hr
      · -- token1.epoch = 0 → token1 = noSessionToken → checkpoint = 0
        rcases h_tok1_pos with h_ge | h_eq
        · omega
        · simp [h_eq, noSessionToken] at h_pos
    · -- token1.epoch = s.epoch: log entry exists and matches
      unfold sessionConsistencyRead checkReadConsistency at hr
      obtain ⟨_, hr⟩ := hr
      have h_tok2_ep : token2.epoch = s.cosmos.epoch := by
        rcases h_leq.1 with h | h
        · omega
        · -- token1.epoch = 0 contradicts either h_tok1_pos or h_ep
          rcases h_tok1_pos with h_ge | h_eq
          · omega
          · simp [h_eq, noSessionToken] at h_pos
      simp [h_tok2_ep] at hr
      exact generalReadResult_geq_matching hr h_pos h_len
        (by have := h_leq.2; omega) h_key_eq
  · omega -- token1.checkpoint = 0 ≤ anything

/- ================================================================
   Section 18: SessionTokenDoesNotBecomeValidTwice
   ================================================================ -/

-- The TLA+ property (lines 415-424) has the temporal pattern [](P ⇒ [](Q ⇒ []R)):
-- P: ReadConsistencyOK(Session) ∧ reads non-empty (token is valid)
-- Q: ReadConsistencyOK(Session) ∧ reads empty (token became invalid)
-- R: ReadConsistencyOK(Session) ∧ reads empty (token stays invalid)
--
-- Key insight: session reads are valid iff epoch = token.epoch ∨ token = noSessionToken.
-- Since epochs only increase, once epoch > token.epoch, the token can never become
-- valid again. And noSessionToken is always valid, so Q can never hold for it.
-- We decompose into two levels:
-- Level 1 (outer []): P → token.epoch ≤ epoch (preserved by epoch monotonicity)
-- Level 2 (inner []): Q ∧ Level1 → token.epoch < epoch (preserved by epoch monotonicity)
-- Derivation: Level2 → R

-- Level 1: Q_mid = token.epoch ≤ s.epoch
-- Base: P (reads non-empty) → epoch ≥ token.epoch
-- Step: epoch only increases → preserved
def sessionTokenValidEpochQ
    (s : CosmosState Key Value) (token : SessionToken) : Prop :=
  token.epoch ≤ s.epoch

-- P: readConsistencyOK ∧ ∃ r, sessionConsistencyRead. This means the if-condition
-- is true: s.epoch = token.epoch ∨ token = noSessionToken. Either way, epoch ≥ token.epoch.
lemma sessionTokenValidEpoch_base
    {s : CosmosState Key Value} {token : SessionToken} {key : Key}
    {r : ReadResult Value}
    (_h_rco : readConsistencyOK s.writeConsistencyLevel .session)
    (h_read : sessionConsistencyRead s token key r) :
    sessionTokenValidEpochQ s token := by
  unfold sessionTokenValidEpochQ
  unfold sessionConsistencyRead checkReadConsistency at h_read
  obtain ⟨_, h_read⟩ := h_read
  -- The if-condition must be true for h_read to be satisfiable
  by_cases h : s.epoch = token.epoch ∨ token = noSessionToken
  · rcases h with h | h
    · omega
    · simp [h, noSessionToken]
  · simp [h] at h_read

theorem sessionTokenValidEpoch_step
    {s s' : CosmosWState Key Value} {sb vb : Nat}
    {token : SessionToken}
    (hq : sessionTokenValidEpochQ s.cosmos token)
    (hn : wNext sb vb s s') :
    sessionTokenValidEpochQ s'.cosmos token := by
  unfold sessionTokenValidEpochQ at hq ⊢
  have := epochMonotone_wNext hn; omega

-- Level 2: Q_inner = token.epoch < s.epoch ∧ token ≠ noSessionToken
--   ∧ readConsistencyOK
-- Base: Q (reads empty with readConsistencyOK) ∧ Q_mid → Q_inner
-- Step: epoch increases, token/noSessionToken static, WCL static → preserved
def sessionTokenInvalidQ
    (s : CosmosState Key Value) (token : SessionToken) : Prop :=
  token.epoch < s.epoch
  ∧ token ≠ noSessionToken
  ∧ readConsistencyOK s.writeConsistencyLevel .session

-- Q: readConsistencyOK ∧ reads empty for key.
-- With Q_mid (epoch ≥ token.epoch) and sessionTokenWhenValid (contrapositive):
-- reads empty → ¬(epoch = token.epoch ∨ noSessionToken) → epoch ≠ token.epoch → epoch > token.epoch
-- Also: token ≠ noSessionToken (otherwise reads would be non-empty).
lemma sessionTokenInvalid_base
    {s : CosmosState Key Value} {token : SessionToken} {key : Key}
    (h_tok_pos : token.epoch ≥ 1 ∨ token = noSessionToken)
    (h_mid : sessionTokenValidEpochQ s token)
    (h_rco : readConsistencyOK s.writeConsistencyLevel .session)
    (h_empty : ∀ r, ¬sessionConsistencyRead s token key r) :
    sessionTokenInvalidQ s token := by
  unfold sessionTokenInvalidQ sessionTokenValidEpochQ at *
  -- Use sessionTokenWhenValid to derive ¬(epoch = token.epoch ∨ noSessionToken)
  -- If the epoch condition held, reads would be non-empty (contradiction with h_empty)
  have h_not_valid : ¬(token.epoch = s.epoch ∨ token = noSessionToken) := by
    intro h_valid
    have h_valid' : token.epoch = s.epoch ∨ token = noSessionToken := by
      rcases h_valid with h | h
      · left; exact h
      · right; exact h
    have ⟨r, hr⟩ := sessionTokenWhenValid_holds s token h_tok_pos h_rco h_valid' key
    exact h_empty r hr
  push_neg at h_not_valid
  exact ⟨by omega, h_not_valid.2, h_rco⟩

theorem sessionTokenInvalid_step
    {s s' : CosmosWState Key Value} {sb vb : Nat}
    {token : SessionToken}
    (hq : sessionTokenInvalidQ s.cosmos token)
    (hn : wNext sb vb s s') :
    sessionTokenInvalidQ s'.cosmos token := by
  unfold sessionTokenInvalidQ at hq ⊢
  obtain ⟨h_lt, h_ne, h_rco⟩ := hq
  exact ⟨by have := epochMonotone_wNext hn; omega,
         h_ne,
         by rw [wclPreserved_wNext hn]; exact h_rco⟩

-- Derivation: Q_inner → R (readConsistencyOK ∧ reads empty).
-- token.epoch < epoch → ¬(epoch = token.epoch). With token ≠ noSessionToken,
-- the if-condition in sessionConsistencyRead is false, so all reads return False.
theorem sessionTokenStaysInvalid_reads
    {s : CosmosState Key Value} {token : SessionToken} {key : Key}
    (hq : sessionTokenInvalidQ s token) :
    readConsistencyOK s.writeConsistencyLevel .session
    ∧ ∀ r, ¬sessionConsistencyRead s token key r := by
  obtain ⟨h_lt, h_ne, h_rco⟩ := hq
  refine ⟨h_rco, fun r hr => ?_⟩
  unfold sessionConsistencyRead checkReadConsistency at hr
  obtain ⟨_, hr⟩ := hr
  have : ¬(s.epoch = token.epoch ∨ token = noSessionToken) := by
    push_neg; exact ⟨by omega, h_ne⟩
  simp [this] at hr

/- ================================================================
   Section 19: WritesEventuallyComplete (Liveness)

   TLA+ property (lines 208-219):
     ∀ token ∈ SessionTokens:
       (∃ record with record.token = token ∧ record.state = WriteInitState)
       ~>
       (∃ record with record.token = token ∧ record.state ∈ {Succeeded, Failed})

   The TLA+ spec assumes WF_varsWithHistory(WriteSuccess ∨ WriteFail).
   Since this action is nondeterministic over which record it operates on,
   WF only guarantees SOME write completes — not a specific one. For a
   deductive proof (vs. finite-state model checking), we need WF for the
   token-specific completion action. This is a standard refinement:
   WF(∀ token. complete(token)) implies WF(∃ token. complete(token)).
   ================================================================ -/

-- Token-specific completion action: WriteSuccess or WriteFail on a record
-- with the given token. This is the action whose fairness we assume.
def writeCompleteForToken (token : SessionToken)
    (s s' : CosmosWState Key Value) : Prop :=
  (∃ record : WriteHistoryEntry Key Value,
    record ∈ s.writeHistory
    ∧ record.state = WriteState.init
    ∧ record.token = token
    ∧ writeCanSucceed s.cosmos record.token
    ∧ s'.writeHistory =
        (⟨record.token, record.key, record.value, .succeeded⟩ :
          WriteHistoryEntry Key Value) ::ₘ (s.writeHistory.erase record)
    ∧ s'.cosmos = s.cosmos)
  ∨ (∃ record : WriteHistoryEntry Key Value,
    record ∈ s.writeHistory
    ∧ record.state = WriteState.init
    ∧ record.token = token
    ∧ s'.writeHistory =
        (⟨record.token, record.key, record.value, .failed⟩ :
          WriteHistoryEntry Key Value) ::ₘ (s.writeHistory.erase record)
    ∧ s'.cosmos = s.cosmos)

-- P: there exists an init record with the given token
def writeInitiated (token : SessionToken)
    (s : CosmosWState Key Value) : Prop :=
  ∃ record : WriteHistoryEntry Key Value,
    record ∈ s.writeHistory
    ∧ record.token = token
    ∧ record.state = WriteState.init

-- Q: there exists a completed (succeeded or failed) record with the given token
def writeCompleted (token : SessionToken)
    (s : CosmosWState Key Value) : Prop :=
  ∃ record : WriteHistoryEntry Key Value,
    record ∈ s.writeHistory
    ∧ record.token = token
    ∧ (record.state = WriteState.succeeded ∨ record.state = WriteState.failed)

-- Premise 1: P enables the token-specific action.
-- WriteFail has no precondition beyond state = init, so if our init record
-- exists, we can always fail it.
theorem writesComplete_enabled
    {token : SessionToken}
    (s : CosmosWState Key Value)
    (hp : writeInitiated token s) :
    enabled (writeCompleteForToken token) s := by
  obtain ⟨record, h_mem, h_tok, h_init⟩ := hp
  -- Construct successor state via WriteFail on this record
  refine ⟨⟨s.cosmos,
    (⟨record.token, record.key, record.value, .failed⟩ :
      WriteHistoryEntry Key Value) ::ₘ (s.writeHistory.erase record)⟩, ?_⟩
  right
  exact ⟨record, h_mem, h_init, h_tok, rfl, rfl⟩

-- Premise 2: when the token-specific action fires AND P holds, Q holds.
-- The record with our token transitions to succeeded or failed.
theorem writesComplete_achieves
    {token : SessionToken}
    (s s' : CosmosWState Key Value)
    (_hp : writeInitiated token s)
    (hact : writeCompleteForToken token s s') :
    writeCompleted token s' := by
  cases hact with
  | inl h_succ =>
    obtain ⟨record, _, _, h_tok, _, h_wh, _⟩ := h_succ
    exact ⟨⟨record.token, record.key, record.value, .succeeded⟩,
           by rw [h_wh]; exact Multiset.mem_cons_self _ _,
           by simp [h_tok],
           Or.inl rfl⟩
  | inr h_fail =>
    obtain ⟨record, _, _, h_tok, h_wh, _⟩ := h_fail
    exact ⟨⟨record.token, record.key, record.value, .failed⟩,
           by rw [h_wh]; exact Multiset.mem_cons_self _ _,
           by simp [h_tok],
           Or.inr rfl⟩

-- Premise 3: non-token-specific-act steps preserve P.
-- Our init record survives stateOps, writeBegin, and writeSuccess/writeFail
-- on other records (those are ¬writeCompleteForToken for our token).
-- Key insight: if a wNext step does NOT complete our token, then either
-- writeHistory is unchanged, or a different record was modified, so our
-- init record persists.
theorem writesComplete_persist
    {token : SessionToken} {sb vb : Nat}
    (s s' : CosmosWState Key Value)
    (hp : writeInitiated token s)
    (hn : wNext sb vb s s')
    (hna : ¬writeCompleteForToken token s s') :
    writeInitiated token s' := by
  obtain ⟨myRecord, h_mem, h_tok, h_init⟩ := hp
  cases hn with
  | inl h_state =>
    -- stateOps: writeHistory unchanged
    obtain ⟨h_wh, _⟩ := h_state
    exact ⟨myRecord, by rw [h_wh]; exact h_mem, h_tok, h_init⟩
  | inr h_write =>
    cases h_write with
    | inl h_begin =>
      -- writeBegin: adds a new record, existing records persist
      obtain ⟨key, value, _, h_log, h_hist, _, _, _, _⟩ := h_begin
      cases h_hist with
      | inl h_succ =>
        -- writeBegin with immediate success: adds succeeded record
        obtain ⟨_, h_wh⟩ := h_succ
        exact ⟨myRecord,
               by rw [h_wh]; exact Multiset.mem_cons_of_mem h_mem,
               h_tok, h_init⟩
      | inr h_wh =>
        -- writeBegin without immediate success: adds init record
        exact ⟨myRecord,
               by rw [h_wh]; exact Multiset.mem_cons_of_mem h_mem,
               h_tok, h_init⟩
    | inr h_succ_or_fail =>
      cases h_succ_or_fail with
      | inl h_succ =>
        -- writeSuccess on some record
        obtain ⟨record, h_rmem, h_rinit, h_rcan, h_wh, h_cosmos⟩ := h_succ
        -- Is this record our record?
        by_cases heq : record = myRecord
        · -- writeSuccess on our record → this IS writeCompleteForToken
          exfalso; apply hna
          left
          exact ⟨myRecord, h_mem,
                 by rw [← heq]; exact h_rinit,
                 h_tok,
                 by rw [← heq]; exact h_rcan,
                 by rw [← heq]; exact h_wh,
                 h_cosmos⟩
        · -- writeSuccess on a different record → our record persists
          have h_in_erase : myRecord ∈ s.writeHistory.erase record :=
            (Multiset.mem_erase_of_ne (Ne.symm heq)).mpr h_mem
          exact ⟨myRecord,
                 by rw [h_wh]; exact Multiset.mem_cons_of_mem h_in_erase,
                 h_tok, h_init⟩
      | inr h_fail =>
        -- writeFail on some record
        obtain ⟨record, h_rmem, h_rinit, h_wh, h_cosmos⟩ := h_fail
        by_cases heq : record = myRecord
        · -- writeFail on our record → this IS writeCompleteForToken
          exfalso; apply hna
          right
          exact ⟨myRecord, h_mem,
                 by rw [← heq]; exact h_rinit,
                 h_tok,
                 by rw [← heq]; exact h_wh,
                 h_cosmos⟩
        · -- writeFail on a different record → our record persists
          have h_in_erase : myRecord ∈ s.writeHistory.erase record :=
            (Multiset.mem_erase_of_ne (Ne.symm heq)).mpr h_mem
          exact ⟨myRecord,
                 by rw [h_wh]; exact Multiset.mem_cons_of_mem h_in_erase,
                 h_tok, h_init⟩

-- The main theorem: WritesEventuallyComplete
-- Under weak fairness of writeCompleteForToken for each token,
-- any initiated write eventually completes.
theorem writesEventuallyComplete
    {sb vb : Nat} {token : SessionToken}
    {σ : Trace (CosmosWState Key Value)}
    (h_exec : ∀ n, wNext sb vb (σ n) (σ (n + 1)))
    (h_fair : weakFair (writeCompleteForToken token) σ) :
    leadsTo (writeInitiated token) (writeCompleted token) σ :=
  leadsTo_by_wf1 h_exec h_fair
    (fun s hp => writesComplete_enabled s hp)
    (fun s s' hp hact => writesComplete_achieves s s' hp hact)
    (fun s s' hp hn hna => Or.inl (writesComplete_persist s s' hp hn hna))
