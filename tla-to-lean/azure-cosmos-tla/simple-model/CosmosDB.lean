import Mathlib.Data.Fintype.Basic

/-!
# CosmosDB

Lean formalization of the Azure Cosmos DB consistency model (CosmosDB.tla).
This specification models:
- Five consistency levels (Strong, BoundedStaleness, Session, ConsistentPrefix, Eventual)
- A replicated log with commitIndex, readIndex, and epoch
- Write acceptance conditions (staleness bound, version bound)
- Read operators at each consistency level (GeneralRead pattern)
- Log truncation modeling data loss with epoch advancement
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.setOption false
set_option linter.flexible false

/- ================================================================
   Section 1: Constants and Types
   ================================================================ -/

-- The five consistency levels (TLA+ lines 4-6)
inductive ConsistencyLevel where
  | strong
  | boundedStaleness
  | session
  | consistentPrefix
  | eventual
  deriving DecidableEq

-- Keys and Values are abstract types parameterizing the spec
variable {Key : Type} [DecidableEq Key] [Inhabited Key]
variable {Value : Type} [DecidableEq Value] [Inhabited Value]

-- A log entry contains one key-value pair (TLA+ lines 148-152)
structure LogEntry (Key Value : Type) where
  key : Key
  value : Value
  deriving DecidableEq, Inhabited

-- A session token is a (checkpoint, epoch) pair (TLA+ lines 75-78)
-- epoch = 0 is special: the "no session token" sentinel (TLA+ lines 93-96)
structure SessionToken where
  checkpoint : Nat
  epoch : Nat
  deriving DecidableEq

-- The "not a session token" sentinel (TLA+ lines 93-96)
-- epoch = 0 means it is valid at all epochs
def noSessionToken : SessionToken := ⟨0, 0⟩

-- Session token partial order (TLA+ lines 105-107)
-- token1 ≤ token2 iff same epoch (or token1.epoch = 0) and checkpoint ≤
def sessionTokenLEQ (token1 token2 : SessionToken) : Prop :=
  (token1.epoch = token2.epoch ∨ token1.epoch = 0)
  ∧ token1.checkpoint ≤ token2.checkpoint

-- A read result: logIndex and value (TLA+ lines 120-123)
-- logIndex = 0 with noValue represents "not found" (TLA+ lines 126-129)
structure ReadResult (Value : Type) where
  logIndex : Nat
  value : Option Value  -- None represents NoValue
  deriving DecidableEq

def notFoundReadResult : ReadResult Value := ⟨0, none⟩

def readsLEQ (r1 r2 : ReadResult Value) : Prop := r1.logIndex ≤ r2.logIndex

def readsLT (r1 r2 : ReadResult Value) : Prop := r1.logIndex < r2.logIndex

/- ================================================================
   Section 2: System State
   ================================================================ -/

-- StalenessBound and VersionBound are positive naturals (TLA+ lines 51-53)
-- We model them as Nat parameters with positivity assumed at use sites

structure CosmosState (Key Value : Type) where
  log : List (LogEntry Key Value)
  commitIndex : Nat
  readIndex : Nat
  epoch : Nat
  writeConsistencyLevel : ConsistencyLevel

/- ================================================================
   Section 3: Helpers
   ================================================================ -/

-- WritesAccepted (TLA+ lines 220-225)
-- Whether the database accepts new writes given current state
def writesAccepted (stalenessBound versionBound : Nat)
    (s : CosmosState Key Value) : Prop :=
  s.log.length - s.readIndex < versionBound
  ∧ (s.writeConsistencyLevel = ConsistencyLevel.boundedStaleness →
      s.log.length - s.commitIndex < stalenessBound)

-- WriteInitToken: the token representing a new write (TLA+ lines 241-244)
def writeInitToken (s : CosmosState Key Value) : SessionToken :=
  ⟨s.log.length + 1, s.epoch⟩

-- SessionTokenIsValid (TLA+ lines 246-247)
def sessionTokenIsValid (s : CosmosState Key Value) (token : SessionToken) : Prop :=
  sessionTokenLEQ token (writeInitToken s)

-- WriteCanSucceed (TLA+ lines 257-261)
def writeCanSucceed (s : CosmosState Key Value) (token : SessionToken) : Prop :=
  sessionTokenIsValid s token
  ∧ (s.writeConsistencyLevel = ConsistencyLevel.strong →
      token.epoch = s.epoch ∧ token.checkpoint ≤ s.commitIndex)

-- ReadConsistencyOK (TLA+ lines 269-279)
-- Whether a read consistency level is valid given the write consistency level
def readConsistencyOK (writeLevel readLevel : ConsistencyLevel) : Prop :=
  match writeLevel with
  | ConsistencyLevel.strong => True
  | ConsistencyLevel.boundedStaleness => readLevel ≠ ConsistencyLevel.strong
  | ConsistencyLevel.session =>
      readLevel ≠ ConsistencyLevel.strong ∧ readLevel ≠ ConsistencyLevel.boundedStaleness
  | ConsistencyLevel.consistentPrefix =>
      readLevel = ConsistencyLevel.consistentPrefix ∨ readLevel = ConsistencyLevel.eventual
  | ConsistencyLevel.eventual => readLevel = ConsistencyLevel.eventual

-- UpdateTokenFromRead (TLA+ lines 249-252)
def updateTokenFromRead (s : CosmosState Key Value)
    (origToken : SessionToken) (read : ReadResult Value) : SessionToken :=
  ⟨max origToken.checkpoint read.logIndex, s.epoch⟩

/- ================================================================
   Section 4: Read Operators
   ================================================================ -/

-- GeneralRead (TLA+ lines 306-321)
-- Returns the set of possible read results for a given key at a given index.
-- - For entries at or before `index`, include the latest value for `key`
-- - If allowDirty, also include entries beyond `index`
-- - If no entry found at or before index, include NotFoundReadResult
--
-- We model this as a predicate on ReadResult rather than a Set,
-- following the pattern of modeling TLA+ operators as Prop.
def generalReadResult (s : CosmosState Key Value)
    (key : Key) (index : Nat) (allowDirty : Bool)
    (result : ReadResult Value) : Prop :=
  -- Case 1: result comes from the latest entry at or before index
  (∃ i, i > 0 ∧ i ≤ s.log.length ∧ i ≤ index
    ∧ (s.log[i - 1]!).key = key
    ∧ result = ⟨i, some (s.log[i - 1]!).value⟩
    -- i is the maximum such index
    ∧ ∀ j, j > i → j ≤ index → j ≤ s.log.length → (s.log[j - 1]!).key ≠ key)
  -- Case 2: result comes from a dirty read (beyond index)
  ∨ (allowDirty = true
    ∧ ∃ i, i > 0 ∧ i ≤ s.log.length ∧ i > index
      ∧ (s.log[i - 1]!).key = key
      ∧ result = ⟨i, some (s.log[i - 1]!).value⟩)
  -- Case 3: no entry for key at or before index → NotFound
  ∨ ((∀ i, i > 0 → i ≤ index → i ≤ s.log.length → (s.log[i - 1]!).key ≠ key)
    ∧ result = notFoundReadResult)

-- CheckReadConsistency: if read consistency is invalid, no results (TLA+ lines 285-288)
def checkReadConsistency (writeLevel readLevel : ConsistencyLevel)
    (readPred : ReadResult Value → Prop)
    (result : ReadResult Value) : Prop :=
  readConsistencyOK writeLevel readLevel ∧ readPred result

-- StrongConsistencyRead (TLA+ lines 323-326)
def strongConsistencyRead (s : CosmosState Key Value) (key : Key)
    (result : ReadResult Value) : Prop :=
  checkReadConsistency s.writeConsistencyLevel ConsistencyLevel.strong
    (generalReadResult s key s.commitIndex false) result

-- BoundedStalenessRead (TLA+ lines 328-331)
def boundedStalenessRead (s : CosmosState Key Value) (key : Key)
    (result : ReadResult Value) : Prop :=
  checkReadConsistency s.writeConsistencyLevel ConsistencyLevel.boundedStaleness
    (generalReadResult s key s.commitIndex true) result

-- SessionConsistencyRead (TLA+ lines 333-349)
def sessionConsistencyRead (s : CosmosState Key Value) (token : SessionToken) (key : Key)
    (result : ReadResult Value) : Prop :=
  checkReadConsistency s.writeConsistencyLevel ConsistencyLevel.session
    (if s.epoch = token.epoch ∨ token = noSessionToken
     then generalReadResult s key (max token.checkpoint s.readIndex) true
     else fun _ => False)
    result

-- ConsistentPrefixRead (TLA+ lines 351-360)
def consistentPrefixRead (s : CosmosState Key Value) (key : Key)
    (result : ReadResult Value) : Prop :=
  checkReadConsistency s.writeConsistencyLevel ConsistencyLevel.consistentPrefix
    (generalReadResult s key s.readIndex true) result

-- EventualConsistencyRead (TLA+ lines 362-365)
def eventualConsistencyRead (s : CosmosState Key Value) (key : Key)
    (result : ReadResult Value) : Prop :=
  checkReadConsistency s.writeConsistencyLevel ConsistencyLevel.eventual
    (generalReadResult s key s.readIndex true) result

/- ================================================================
   Section 5: Initial State
   ================================================================ -/

-- Init (TLA+ lines 390-395)
def cosmosInit (wc : ConsistencyLevel) : CosmosState Key Value where
  log := []
  readIndex := 0
  commitIndex := 0
  epoch := 1
  writeConsistencyLevel := wc

/- ================================================================
   Section 6: Actions
   ================================================================ -/

-- WriteInit (TLA+ lines 231-235)
-- Appends a key-value pair to the log
def writeInit (key : Key) (value : Value)
    (s s' : CosmosState Key Value) : Prop :=
  s'.log = s.log ++ [⟨key, value⟩]

-- AcquirableSessionTokens (TLA+ lines 209-212)
-- Tokens that could be acquired during the current state
def acquirableSessionToken (s : CosmosState Key Value) (token : SessionToken) : Prop :=
  token.epoch = s.epoch
  ∧ token.checkpoint ≤ s.log.length + 1

-- IncreaseReadIndexAndOrCommitIndex (TLA+ lines 374-377)
def increaseReadIndexAndOrCommitIndex
    (s s' : CosmosState Key Value) : Prop :=
  s'.commitIndex ≥ s.commitIndex
  ∧ s'.commitIndex ≤ s.log.length
  ∧ s'.readIndex ≥ s.readIndex
  ∧ s'.readIndex ≤ s'.commitIndex
  -- UNCHANGED log, epoch, WriteConsistencyLevel
  ∧ s'.log = s.log
  ∧ s'.epoch = s.epoch
  ∧ s'.writeConsistencyLevel = s.writeConsistencyLevel

-- TruncateLog (TLA+ lines 384-388)
-- Any uncommitted suffix of the log can be lost; epoch increments
def truncateLog (s s' : CosmosState Key Value) : Prop :=
  ∃ i, i > s.commitIndex ∧ i ≤ s.log.length
    ∧ s'.log = s.log.take (i - 1)
    ∧ s'.epoch = s.epoch + 1
    -- UNCHANGED readIndex, commitIndex, WriteConsistencyLevel
    ∧ s'.readIndex = s.readIndex
    ∧ s'.commitIndex = s.commitIndex
    ∧ s'.writeConsistencyLevel = s.writeConsistencyLevel

-- Next (TLA+ lines 401-403)
def cosmosNext (s s' : CosmosState Key Value) : Prop :=
  increaseReadIndexAndOrCommitIndex s s'
  ∨ truncateLog s s'

/- ================================================================
   Section 7: Type Invariant and Reachability
   ================================================================ -/

-- TypesOK (TLA+ lines 193-198)
-- Most type constraints are enforced by Lean's type system.
-- The structural constraints that remain:
def typesOK (s : CosmosState Key Value) : Prop :=
  s.epoch ≥ 1
  ∧ s.readIndex ≤ s.commitIndex
  ∧ s.commitIndex ≤ s.log.length

-- Reachable states
inductive CosmosReachable (wc : ConsistencyLevel) :
    CosmosState Key Value → Prop where
  | init : CosmosReachable wc (cosmosInit wc)
  | step {s s'} : CosmosReachable wc s → cosmosNext s s' → CosmosReachable wc s'
