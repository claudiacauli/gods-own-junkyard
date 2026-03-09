import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

/-!
# RaftMongo

Lean formalization of the Raft consensus algorithm in MongoDB (RaftMongo.tla).
This specification models a simplified Raft protocol with:
- Oplog replication (AppendOplog)
- Log rollback (RollbackOplog)
- Leader election by magic (BecomePrimaryByMagic)
- Client writes (ClientWrite)
- Commit point advancement and propagation (AdvanceCommitPoint, LearnCommitPointFromSyncSource)

We specify only safety properties:
- NeverRollbackCommitted: committed log entries are never rolled back
- NeverRollbackBeforeCommitPoint: rollback never goes below the commit point
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.setOption false
set_option linter.flexible false

variable {Server : Type} [Fintype Server] [DecidableEq Server]

/- ================================================================
   Section 1: Types
   ================================================================ -/

-- Server states (TLA+ line 10-11)
inductive ServerState where
  | Follower
  | Candidate
  | Leader
  deriving DecidableEq

-- A log entry contains just a term number (TLA+ line 143)
structure LogEntry where
  term : Nat
  deriving DecidableEq

-- A commit point is a (term, index) pair (TLA+ line 68)
structure CommitPoint where
  term : Nat
  index : Nat
  deriving DecidableEq

/- ================================================================
   Section 2: System State
   ================================================================ -/

structure RaftState (Server : Type) where
  -- Global variables
  globalCurrentTerm : Nat
  -- Per-server variables
  state : Server → ServerState
  commitPoint : Server → CommitPoint
  log : Server → List LogEntry

/- ================================================================
   Section 3: Helpers
   ================================================================ -/

-- TLA+ uses 1-based indexing for sequences. We keep 1-based index semantics
-- in the interface: getTerm xlog 0 = 0, getTerm xlog k = xlog[k-1].term.
-- List.length corresponds to TLA+ Len.

-- The term of the entry at 1-based index in a log, or 0 if index = 0 (TLA+ line 54)
def getTerm (xlog : List LogEntry) (index : Nat) : Nat :=
  if index = 0 then 0
  else match xlog[index - 1]? with
    | some entry => entry.term
    | none => 0  -- out of bounds: shouldn't happen in well-formed states

-- LogTerm(i, index) == GetTerm(log[i], index) (TLA+ line 55)
def logTerm (s : RaftState Server) (i : Server) (index : Nat) : Nat :=
  getTerm (s.log i) index

-- LastTerm(xlog) == GetTerm(xlog, Len(xlog)) (TLA+ line 56)
def lastTerm (xlog : List LogEntry) : Nat :=
  getTerm xlog xlog.length

-- Quorum: a set of servers whose cardinality is a strict majority (TLA+ line 51)
def isQuorum (q : Finset Server) : Prop :=
  q.card * 2 > Fintype.card Server

-- Any two quorums must overlap: if both q₁ and q₂ have more than half the
-- servers, there must be at least one server in both.
lemma quorums_overlap (q₁ q₂ : Finset Server)
    (h₁ : isQuorum q₁) (h₂ : isQuorum q₂) : (q₁ ∩ q₂).Nonempty := by
  apply Finset.inter_nonempty_of_card_lt_card_add_card
    (Finset.subset_univ q₁) (Finset.subset_univ q₂)
  simp only [Finset.card_univ]
  unfold isQuorum at h₁ h₂
  omega

/- ================================================================
   Section 4: Initial State
   ================================================================ -/

def raftInit : RaftState Server where
  globalCurrentTerm := 0
  state := fun _ => ServerState.Follower
  commitPoint := fun _ => ⟨0, 0⟩
  log := fun _ => []

/- ================================================================
   Section 5: Guard Predicates
   ================================================================ -/

-- CanRollbackOplog(i, j): whether i can roll back against j (TLA+ lines 84-92)
-- i has a non-empty log with a strictly smaller last term than j's last term,
-- and either i's log is longer than j's, or the terms at i's length position differ.
def canRollbackOplog (i j : Server) (s : RaftState Server) : Prop :=
  (s.log i).length > 0
  ∧ lastTerm (s.log i) < lastTerm (s.log j)
  ∧ ((s.log i).length > (s.log j).length
    ∨ ((s.log i).length ≤ (s.log j).length
       ∧ lastTerm (s.log i) ≠ logTerm s j (s.log i).length))

-- Agree(me, logIndex): set of servers that agree with me at logIndex (TLA+ lines 102-105)
-- A server node agrees if its log is at least as long as logIndex and the terms match.
def agree (s : RaftState Server) (me : Server) (logIndex : Nat) : Finset Server :=
  Finset.univ.filter fun node =>
    (s.log node).length ≥ logIndex ∧ logTerm s me logIndex = logTerm s node logIndex

-- IsCommitted(me, logIndex): the entry at logIndex is committed (TLA+ lines 107-113)
-- The agree set forms a quorum AND the entry's term equals the current global term.
def isCommitted (s : RaftState Server) (me : Server) (logIndex : Nat) : Prop :=
  isQuorum (agree s me logIndex)
  ∧ logTerm s me logIndex = s.globalCurrentTerm

-- CommitPointLessThan(i, j): i's commit point is strictly less than j's (TLA+ lines 157-160)
def commitPointLessThan (s : RaftState Server) (i j : Server) : Prop :=
  (s.commitPoint i).term < (s.commitPoint j).term
  ∨ ((s.commitPoint i).term = (s.commitPoint j).term
     ∧ (s.commitPoint i).index < (s.commitPoint j).index)

-- The guard of AppendOplog, used by ENABLED AppendOplog in LearnCommitPointFromSyncSource.
-- This captures the preconditions of AppendOplog without the state transition.
def appendOplogEnabled (i j : Server) (s : RaftState Server) : Prop :=
  (s.log i).length < (s.log j).length
  ∧ lastTerm (s.log i) = logTerm s j (s.log i).length

/- ================================================================
   Section 6: Actions
   ================================================================ -/

-- Each action is modeled as a relation on (s, s') : RaftState × RaftState.
-- UNCHANGED clauses are explicit equalities on the unchanged fields.

-- AppendOplog(i, j): follower i appends one entry from j's log (TLA+ lines 77-82)
def appendOplog (i j : Server) (s s' : RaftState Server) : Prop :=
  (s.log i).length < (s.log j).length
  ∧ lastTerm (s.log i) = logTerm s j (s.log i).length
  ∧ (∃ entry : LogEntry,
      (s.log j)[(s.log i).length]? = some entry
      ∧ s'.log = Function.update s.log i ((s.log i) ++ [entry]))
  -- UNCHANGED serverVars
  ∧ s'.globalCurrentTerm = s.globalCurrentTerm
  ∧ s'.state = s.state
  ∧ s'.commitPoint = s.commitPoint

-- RollbackOplog(i, j): i rolls back one oplog entry (TLA+ lines 94-99)
def rollbackOplog (i j : Server) (s s' : RaftState Server) : Prop :=
  canRollbackOplog i j s
  -- Rollback 1 entry: new log is log[i] with last element dropped
  ∧ s'.log = Function.update s.log i ((s.log i).dropLast)
  -- UNCHANGED serverVars
  ∧ s'.globalCurrentTerm = s.globalCurrentTerm
  ∧ s'.state = s.state
  ∧ s'.commitPoint = s.commitPoint

-- BecomePrimaryByMagic(i): i becomes leader (TLA+ lines 127-137)
-- i must have a quorum of "aye voters" — servers not more up-to-date than i.
-- ayeVoters: servers whose logs are not more up-to-date than i's
def ayeVoters (i : Server) (s : RaftState Server) : Finset Server :=
  Finset.univ.filter fun j =>
    lastTerm (s.log i) > lastTerm (s.log j)
    ∨ (lastTerm (s.log i) = lastTerm (s.log j)
       ∧ (s.log i).length ≥ (s.log j).length)

def becomePrimaryByMagic (i : Server) (s s' : RaftState Server) : Prop :=
  isQuorum (ayeVoters i s)
  ∧ s'.state = (fun idx => if idx = i then ServerState.Leader else ServerState.Follower)
  ∧ s'.globalCurrentTerm = s.globalCurrentTerm + 1
  -- UNCHANGED commitPoint, logVars
  ∧ s'.commitPoint = s.commitPoint
  ∧ s'.log = s.log

-- ClientWrite(i): leader i appends a new log entry (TLA+ lines 141-146)
def clientWrite (i : Server) (s s' : RaftState Server) : Prop :=
  s.state i = ServerState.Leader
  ∧ s'.log = Function.update s.log i ((s.log i) ++ [⟨s.globalCurrentTerm⟩])
  -- UNCHANGED serverVars
  ∧ s'.globalCurrentTerm = s.globalCurrentTerm
  ∧ s'.state = s.state
  ∧ s'.commitPoint = s.commitPoint

-- AdvanceCommitPoint: a leader advances its own commit point (TLA+ lines 149-154)
def advanceCommitPoint (s s' : RaftState Server) : Prop :=
  ∃ leader : Server,
    s.state leader = ServerState.Leader
    ∧ isCommitted s leader (s.log leader).length
    ∧ s'.commitPoint = Function.update s.commitPoint leader
        ⟨lastTerm (s.log leader), (s.log leader).length⟩
    -- UNCHANGED electionVars, logVars
    ∧ s'.globalCurrentTerm = s.globalCurrentTerm
    ∧ s'.state = s.state
    ∧ s'.log = s.log

-- LearnCommitPointFromSyncSourceNeverBeyondLastApplied(i, j) (TLA+ lines 176-185)
-- Guarded by: AppendOplog(i, j) is enabled AND i's commit point < j's commit point.
-- Clamps learned commit point: if j's commitPoint.term ≤ lastTerm(log[i]), use j's;
-- otherwise clamp to ⟨lastTerm(log[i]), len(log[i])⟩.
def learnCommitPointFromSyncSource (i j : Server) (s s' : RaftState Server) : Prop :=
  appendOplogEnabled i j s
  ∧ commitPointLessThan s i j
  ∧ s'.commitPoint = Function.update s.commitPoint i
      (if (s.commitPoint j).term ≤ lastTerm (s.log i)
       then s.commitPoint j
       else ⟨lastTerm (s.log i), (s.log i).length⟩)
  -- UNCHANGED electionVars, logVars
  ∧ s'.globalCurrentTerm = s.globalCurrentTerm
  ∧ s'.state = s.state
  ∧ s'.log = s.log

/- ================================================================
   Section 7: Next Relation and Reachability
   ================================================================ -/

def raftNext (s s' : RaftState Server) : Prop :=
  -- Replication protocol
  (∃ i j : Server, appendOplog i j s s')
  ∨ (∃ i j : Server, rollbackOplog i j s s')
  ∨ (∃ i : Server, becomePrimaryByMagic i s s')
  ∨ (∃ i : Server, clientWrite i s s')
  -- Commit point learning protocol
  ∨ advanceCommitPoint s s'
  ∨ (∃ i j : Server, learnCommitPointFromSyncSource i j s s')

-- Reachable states

inductive RaftReachable : RaftState Server → Prop where
  | init : RaftReachable raftInit
  | step {s s'} : RaftReachable s → raftNext s s' → RaftReachable s'

/- ================================================================
   Section 8: Safety Properties
   ================================================================ -/

-- RollbackCommitted(i): i can roll back AND its last entry is committed (TLA+ lines 117-120)
def rollbackCommitted (s : RaftState Server) (i : Server) : Prop :=
  ∃ j : Server,
    canRollbackOplog i j s
    ∧ isCommitted s i (s.log i).length

-- NeverRollbackCommitted (TLA+ lines 122-123)
def neverRollbackCommitted (s : RaftState Server) : Prop :=
  ∀ i : Server, ¬ rollbackCommitted s i

-- RollbackBeforeCommitPoint(i): i can roll back AND its log tip is at or below
-- its commit point (TLA+ lines 236-241)
def rollbackBeforeCommitPoint (s : RaftState Server) (i : Server) : Prop :=
  (∃ j : Server, canRollbackOplog i j s)
  ∧ (lastTerm (s.log i) < (s.commitPoint i).term
    ∨ (lastTerm (s.log i) = (s.commitPoint i).term
       ∧ (s.log i).length ≤ (s.commitPoint i).index))

-- NeverRollbackBeforeCommitPoint (TLA+ line 244)
def neverRollbackBeforeCommitPoint (s : RaftState Server) : Prop :=
  ∀ i : Server, ¬ rollbackBeforeCommitPoint s i

/- ================================================================
   Section 9: Strengthened Inductive Invariant
   ================================================================ -/

-- The two safety properties alone are not inductive. We strengthen them
-- with 16 auxiliary invariants (18 conjuncts total) capturing bounds on
-- terms, leader uniqueness, log matching, quorum-backed commit points,
-- and rollback safety. See `raftInvariant` for the full conjunction.

-- Auxiliary: the current term is an upper bound on all log entry terms
def termsAreBounded (s : RaftState Server) : Prop :=
  ∀ (i : Server) (e : LogEntry), e ∈ s.log i → e.term ≤ s.globalCurrentTerm

-- Auxiliary: every server's commit point term is ≤ globalCurrentTerm.
def commitPointBounded (s : RaftState Server) : Prop :=
  ∀ i : Server, (s.commitPoint i).term ≤ s.globalCurrentTerm

-- Auxiliary: each server's commit point is weakly below its log tip.
-- "Weakly below" means: cpTerm < lastTerm, or cpTerm = lastTerm ∧ cpIndex ≤ len.
-- This allows the commit point to be exactly at the log tip (as set by advanceCommitPoint).
def commitPointWeaklyBelowLogTip (s : RaftState Server) : Prop :=
  ∀ i : Server,
    (s.commitPoint i).term < lastTerm (s.log i)
    ∨ ((s.commitPoint i).term = lastTerm (s.log i) ∧ (s.commitPoint i).index ≤ (s.log i).length)

-- Auxiliary: log terms are monotonically non-decreasing.
-- For all positions p < q in a server's log, the term at p ≤ term at q.
-- This is a standard Raft invariant needed for safety of log matching.
def logTermsMonotonic (s : RaftState Server) : Prop :=
  ∀ (i : Server) (p q : Nat),
    p ≤ q → q ≤ (s.log i).length → logTerm s i p ≤ logTerm s i q

-- Auxiliary: if a server is Leader, then every entry with term = globalCurrentTerm
-- in any server's log is also reflected in the leader's log at the same position.
-- This captures: entries with the current term only exist because the leader wrote
-- them (via clientWrite) or they were copied from a prefix-agreeing log (via
-- appendOplog). Key use: proving logMatching is preserved by clientWrite.
def currentTermMatchesLeader (s : RaftState Server) : Prop :=
  ∀ (ldr b : Server) (p : Nat),
    s.state ldr = ServerState.Leader →
    p ≤ (s.log b).length →
    logTerm s b p = s.globalCurrentTerm →
    logTerm s ldr p = s.globalCurrentTerm

-- Auxiliary: at most one leader at any time.
-- becomePrimaryByMagic sets exactly one leader (all others become Follower).
-- No other action changes state. Needed for currentTermMatchesLeader proofs.
def leaderUnique (s : RaftState Server) : Prop :=
  ∀ (a b : Server), s.state a = ServerState.Leader →
    s.state b = ServerState.Leader → a = b

-- Auxiliary: Log Matching Property.
-- If two logs agree at 1-based position p (same term, both long enough),
-- then they agree at all positions ≤ p.
-- This is the standard Raft Log Matching Property, needed so that when
-- appendOplog extends server i's log (checked via lastTerm match against j),
-- we can transfer canRollbackOplog witnesses between servers.
def logMatching (s : RaftState Server) : Prop :=
  ∀ (i j : Server) (p : Nat),
    p ≤ (s.log i).length → p ≤ (s.log j).length →
    logTerm s i p = logTerm s j p →
    ∀ q : Nat, q ≤ p → logTerm s i q = logTerm s j q

-- Auxiliary: Leader Completeness for Commit Points.
-- If a leader exists, its log contains all entries up to any server's commit point:
--   (1) len(leader) ≥ cpIdx(server)
--   (2) the leader's log agrees with the server's log at all positions p ≤ cpIdx
--       (for positions within both logs)
-- This is a key Raft safety property: a newly elected leader's log must contain all
-- previously committed entries. It follows from quorum overlap: the election quorum
-- and the commit quorum share at least one server, so the leader is at least as
-- up-to-date as any committed entry.
def leaderCompletenessForCommitPoints (s : RaftState Server) : Prop :=
  ∀ (ldr i : Server),
    s.state ldr = ServerState.Leader →
    (s.commitPoint i).index ≤ (s.log ldr).length ∧
    ∀ p, p ≤ (s.commitPoint i).index → p ≤ (s.log i).length →
      logTerm s ldr p = logTerm s i p

-- Auxiliary (new): Every quorum contains a member whose log covers every
-- server's commit point. This is the commit-point analog of TLAPS's
-- ActiveConfigsOverlapWithCommittedEntry. It's the key invariant that lets
-- us prove leaderCompletenessForCommitPoints through leader elections: any
-- election quorum has a witness with the committed entries.
def commitPointsBackedByQuorums (s : RaftState Server) : Prop :=
  ∀ (srv : Server), ∃ (Q : Finset Server), isQuorum Q ∧
    (∀ n, n ∈ Q →
      (s.commitPoint srv).index ≤ (s.log n).length ∧
      (s.commitPoint srv).term ≤ lastTerm (s.log n) ∧
      logTerm s n (s.commitPoint srv).index = (s.commitPoint srv).term) ∧
    (∀ n₁ n₂, n₁ ∈ Q → n₂ ∈ Q →
      ∀ p, p ≤ (s.commitPoint srv).index →
        logTerm s n₁ p = logTerm s n₂ p)

-- Auxiliary (new): If a server's log has a term strictly greater than
-- another server's commit point term, then the first server's log covers
-- the second server's commit point. This is the commit-point analog of
-- TLAPS's LogsLaterThanCommittedMustHaveCommitted.
-- Used in the "lastTerm(leader) > lastTerm(voter)" case of the election argument.
def logsLaterThanCommitPointHaveEntries (s : RaftState Server) : Prop :=
  ∀ (a b : Server),
    lastTerm (s.log a) > (s.commitPoint b).term →
    (s.commitPoint b).index ≤ (s.log a).length ∧
    ∀ p, p ≤ (s.commitPoint b).index → p ≤ (s.log b).length →
      logTerm s a p = logTerm s b p

-- Auxiliary: if server a's lastTerm equals server b's commit point term,
-- and a's log is long enough to cover the commit point index, then a agrees
-- with b on all positions up to the commit point index.
-- Intuition: the commit point (T, idx) was created by a leader with lastTerm T
-- and log length ≥ idx. That leader's entries up to idx were committed by a
-- quorum. Any server with lastTerm = T and log length ≥ idx must have gotten
-- its term-T entries from the same leader (by election safety), so it has the
-- same entries at those positions.
def commitPointAgreement (s : RaftState Server) : Prop :=
  ∀ (a b : Server),
    lastTerm (s.log a) = (s.commitPoint b).term →
    (s.log a).length ≥ (s.commitPoint b).index →
    ∀ p, p ≤ (s.commitPoint b).index → p ≤ (s.log b).length →
      logTerm s a p = logTerm s b p

-- Auxiliary: if a server is Leader, its lastTerm is at least as large as any
-- server's commit point term. This is established at election time (the leader's
-- aye-voter quorum overlaps with any cpbq quorum, giving lastTerm(leader) ≥
-- cpTerm via the aye-voter condition) and maintained by subsequent actions.
-- Key use: in clientWrite, canRollbackOplog srv i s' in the h_below_lt case
-- requires lastTerm(srv) < cpTerm. With this property, lastTerm(leader) ≥ cpTerm
-- > lastTerm(srv), so the leader is always a valid old-state witness for the
-- third-condition-fails argument, eliminating the hard sub-case entirely.
def leaderLastTermGeCommitPointTerm (s : RaftState Server) : Prop :=
  ∀ (ldr srv : Server),
    s.state ldr = ServerState.Leader →
    lastTerm (s.log ldr) ≥ (s.commitPoint srv).term

-- Auxiliary: Uniform Log Entries In Term.
-- If term T first appears at position i in server a's log (all earlier
-- positions have different terms), then no server b has term T at any
-- position j < i. Equivalently, entries with a given term always start
-- at the same position across all logs.
def uniformLogEntriesInTerm (s : RaftState Server) : Prop :=
  ∀ (a b : Server) (i j : Nat),
    1 ≤ i → i ≤ (s.log a).length →
    1 ≤ j → j ≤ (s.log b).length →
    logTerm s a i = logTerm s b j →
    logTerm s a i ≠ 0 →
    -- i is the first occurrence of this term in a's log
    (∀ k, 1 ≤ k → k < i → logTerm s a k ≠ logTerm s a i) →
    -- then j cannot be earlier than i
    j ≥ i

-- Auxiliary: in every server's log, entries at positions at or below the server's
-- commit point index have term ≤ the commit point term.
-- At commit time, the leader has lastTerm = cpTerm and log length = cpIdx,
-- so logTerm(leader, p) ≤ cpTerm for p ≤ cpIdx by monotonicity. By replication,
-- the quorum members have the same entries. Since committed entries are never
-- rolled back, this property is preserved across all transitions.
-- Key use: in appendOplog, when lastTerm(s'.log i) > cpTerm(b), we need to show
-- cpIdx(b) ≤ len(s'.log i). This invariant lets us derive that all entries in
-- j's log at positions ≤ cpIdx(b) have term ≤ cpTerm(b), so the first entry
-- with term > cpTerm(b) must be at a position > cpIdx(b).
def commitPointEntryTermsBounded (s : RaftState Server) : Prop :=
  ∀ (b : Server) (p : Nat),
    p ≤ (s.commitPoint b).index → p ≤ (s.log b).length →
    logTerm s b p ≤ (s.commitPoint b).term

-- Auxiliary: if a server's log can be rolled back (canRollbackOplog i j s),
-- then the commit point term is at most the second-to-last entry's term.
-- Intuition: the last entry is from a "losing" term that will be rolled back.
-- The committed entries (backed by a quorum) lie in the stable prefix below
-- the divergence point, so cp.term ≤ lastTerm(dropLast(log)).
-- Key use: when proving neverRollbackBeforeCommitPoint and
-- commitPointWeaklyBelowLogTip are preserved by rollbackOplog.
def rollbackSafeCommitPoint (s : RaftState Server) : Prop :=
  ∀ (i : Server), (∃ j, canRollbackOplog i j s) →
    (s.commitPoint i).term ≤ lastTerm (s.log i).dropLast

--- Auxiliary: if appendOplogEnabled i j s holds and i can be rolled back,
--- then j's commit point is weakly below i's log tip. This is the minimal
--- fact needed to preserve neverRollbackBeforeCommitPoint across
--- learnCommitPointFromSyncSource, which copies j's commit point to i.
def rollbackWithSyncSourceImpliesCommitPointBelowTip (s : RaftState Server) : Prop :=
  ∀ (i j : Server),
    appendOplogEnabled i j s →
    (∃ k, canRollbackOplog i k s) →
      ¬ (lastTerm (s.log i) < (s.commitPoint j).term
        ∨ (lastTerm (s.log i) = (s.commitPoint j).term
           ∧ (s.log i).length ≤ (s.commitPoint j).index))

-- The full strengthened invariant: a conjunction of the safety properties
-- and auxiliary invariants needed for induction.
def raftInvariant (s : RaftState Server) : Prop :=
  neverRollbackCommitted s
  ∧ neverRollbackBeforeCommitPoint s
  ∧ termsAreBounded s
  ∧ commitPointBounded s
  ∧ logTermsMonotonic s
  ∧ currentTermMatchesLeader s
  ∧ leaderUnique s
  ∧ logMatching s
  ∧ leaderCompletenessForCommitPoints s
  ∧ commitPointsBackedByQuorums s
  ∧ logsLaterThanCommitPointHaveEntries s
  ∧ commitPointAgreement s
  ∧ leaderLastTermGeCommitPointTerm s
  ∧ uniformLogEntriesInTerm s
  ∧ commitPointWeaklyBelowLogTip s
  ∧ commitPointEntryTermsBounded s
  ∧ rollbackSafeCommitPoint s
  ∧ rollbackWithSyncSourceImpliesCommitPointBelowTip s

/- ================================================================
   Section 10: Reusable Proof Infrastructure
   ================================================================ -/

-- These lift predicates across state changes when relevant fields are unchanged.

-- canRollbackOplog depends only on the log field
lemma canRollbackOplog_of_log_eq {i j : Server} {s s' : RaftState Server}
    (h_log : s'.log = s.log) :
    canRollbackOplog i j s' ↔ canRollbackOplog i j s := by
  unfold canRollbackOplog lastTerm logTerm getTerm
  simp [h_log]

-- rollbackCommitted depends on log and globalCurrentTerm
-- Note: rollbackCommitted uses (s.log i).length inside isCommitted, so when
-- lifting between states, we need h_log to equate those lengths too.
lemma rollbackCommitted_of_eq {s s' : RaftState Server} {i : Server}
    (h_log : s'.log = s.log) (h_term : s'.globalCurrentTerm = s.globalCurrentTerm) :
    rollbackCommitted s' i ↔ rollbackCommitted s i := by
  unfold rollbackCommitted isCommitted isQuorum agree canRollbackOplog
    logTerm lastTerm getTerm
  simp [h_log, h_term]

-- rollbackBeforeCommitPoint depends on log and commitPoint
lemma rollbackBeforeCommitPoint_of_eq {s s' : RaftState Server} {i : Server}
    (h_log : s'.log = s.log) (h_cp : s'.commitPoint = s.commitPoint) :
    rollbackBeforeCommitPoint s' i ↔ rollbackBeforeCommitPoint s i := by
  unfold rollbackBeforeCommitPoint
  simp [canRollbackOplog_of_log_eq h_log, h_log, h_cp]

-- termsAreBounded: if log unchanged, term can only grow
lemma termsAreBounded_of_log_eq_term_ge {s s' : RaftState Server}
    (h_log : s'.log = s.log) (h_ge : s.globalCurrentTerm ≤ s'.globalCurrentTerm)
    (h_tb : termsAreBounded s) : termsAreBounded s' := by
  intro i e he
  rw [h_log] at he
  exact Nat.le_trans (h_tb i e he) h_ge

-- commitPointBounded: if commitPoint unchanged, term can only grow
lemma commitPointBounded_of_cp_eq_term_ge {s s' : RaftState Server}
    (h_cp : s'.commitPoint = s.commitPoint) (h_ge : s.globalCurrentTerm ≤ s'.globalCurrentTerm)
    (h_cpb : commitPointBounded s) : commitPointBounded s' := by
  intro i
  rw [h_cp]
  exact Nat.le_trans (h_cpb i) h_ge

-- commitPointWeaklyBelowLogTip depends on log and commitPoint
lemma commitPointWeaklyBelowLogTip_of_eq {s s' : RaftState Server}
    (h_log : s'.log = s.log) (h_cp : s'.commitPoint = s.commitPoint)
    (h_cwb : commitPointWeaklyBelowLogTip s) : commitPointWeaklyBelowLogTip s' := by
  intro srv; rw [h_log, h_cp]; exact h_cwb srv

-- commitPointsBackedByQuorums depends on log and commitPoint
lemma commitPointsBackedByQuorums_of_log_cp_eq {s s' : RaftState Server}
    (h_log : s'.log = s.log) (h_cp : s'.commitPoint = s.commitPoint)
    (h_cpbq : commitPointsBackedByQuorums s) : commitPointsBackedByQuorums s' := by
  intro srv
  obtain ⟨Q, hQ, hcover, hagree⟩ := h_cpbq srv
  refine ⟨Q, hQ, fun n hn => ?_, fun n₁ n₂ hn₁ hn₂ p hp => ?_⟩
  · obtain ⟨hlen, hterm, hlt⟩ := hcover n hn
    refine ⟨by rw [h_cp, h_log]; exact hlen, by rw [h_cp, h_log]; exact hterm, ?_⟩
    unfold logTerm getTerm at hlt ⊢; rw [h_log, h_cp]; exact hlt
  · unfold logTerm getTerm at hagree ⊢; rw [h_log]
    exact hagree n₁ n₂ hn₁ hn₂ p (by rw [h_cp] at hp; exact hp)

-- Derived: from ∃ Q formulation, any quorum Q' has a member covering the commit point
lemma cpbq_witness_in_quorum {s : RaftState Server}
    (h : commitPointsBackedByQuorums s) (srv : Server)
    (Q : Finset Server) (hQ : isQuorum Q) :
    ∃ n, n ∈ Q ∧
      (s.commitPoint srv).index ≤ (s.log n).length ∧
      (s.commitPoint srv).term ≤ lastTerm (s.log n) := by
  obtain ⟨Q₀, hQ₀, hcover, _⟩ := h srv
  obtain ⟨w, hw⟩ := quorums_overlap Q Q₀ hQ hQ₀
  rw [Finset.mem_inter] at hw
  exact ⟨w, hw.1, (hcover w hw.2).1, (hcover w hw.2).2.1⟩

-- logsLaterThanCommitPointHaveEntries depends on log and commitPoint
lemma logsLaterThanCommitPointHaveEntries_of_log_cp_eq {s s' : RaftState Server}
    (h_log : s'.log = s.log) (h_cp : s'.commitPoint = s.commitPoint)
    (h_llcp : logsLaterThanCommitPointHaveEntries s) :
    logsLaterThanCommitPointHaveEntries s' := by
  intro a b h_gt
  have h_gt' : lastTerm (s.log a) > (s.commitPoint b).term := by
    rw [h_log, h_cp] at h_gt; exact h_gt
  obtain ⟨hlen, hagree⟩ := h_llcp a b h_gt'
  refine ⟨by rw [h_log, h_cp]; exact hlen, fun p hp hpl => ?_⟩
  unfold logTerm getTerm at hagree ⊢; rw [h_log]
  exact hagree p (by rw [h_cp] at hp; exact hp) (by rw [h_log] at hpl; exact hpl)

-- commitPointAgreement depends on log and commitPoint
lemma commitPointAgreement_of_log_cp_eq {s s' : RaftState Server}
    (h_log : s'.log = s.log) (h_cp : s'.commitPoint = s.commitPoint)
    (h_cpa : commitPointAgreement s) : commitPointAgreement s' := by
  intro a b h_lt h_len p hp hpl
  have h_lt' : lastTerm (s.log a) = (s.commitPoint b).term := by
    rw [h_log, h_cp] at h_lt; exact h_lt
  have h_len' : (s.log a).length ≥ (s.commitPoint b).index := by
    rw [h_log, h_cp] at h_len; exact h_len
  have : logTerm s' a p = logTerm s a p := by unfold logTerm getTerm; rw [h_log]
  have : logTerm s' b p = logTerm s b p := by unfold logTerm getTerm; rw [h_log]
  rw [‹logTerm s' a p = _›, ‹logTerm s' b p = _›]
  exact h_cpa a b h_lt' h_len' p (by rw [h_cp] at hp; exact hp)
    (by rw [h_log] at hpl; exact hpl)

-- uniformLogEntriesInTerm depends only on log
lemma uniformLogEntriesInTerm_of_log_eq {s s' : RaftState Server}
    (h_log : s'.log = s.log) (h_ulet : uniformLogEntriesInTerm s) :
    uniformLogEntriesInTerm s' := by
  intro a b i j hi hia hj hjb h_eq h_ne h_first
  have hia' : i ≤ (s.log a).length := by rwa [h_log] at hia
  have hjb' : j ≤ (s.log b).length := by rwa [h_log] at hjb
  have h_eq' : logTerm s a i = logTerm s b j := by
    unfold logTerm getTerm at h_eq ⊢; rw [h_log] at h_eq; exact h_eq
  have h_ne' : logTerm s a i ≠ 0 := by
    unfold logTerm getTerm at h_ne ⊢; rw [h_log] at h_ne; exact h_ne
  have h_first' : ∀ k, 1 ≤ k → k < i → logTerm s a k ≠ logTerm s a i := by
    intro k hk1 hki; unfold logTerm getTerm at h_first ⊢
    rw [h_log] at h_first; exact h_first k hk1 hki
  exact h_ulet a b i j hi hia' hj hjb' h_eq' h_ne' h_first'

-- commitPointEntryTermsBounded depends on log and commitPoint
lemma commitPointEntryTermsBounded_of_log_cp_eq {s s' : RaftState Server}
    (h_log : s'.log = s.log) (h_cp : s'.commitPoint = s.commitPoint)
    (h_cpetb : commitPointEntryTermsBounded s) :
    commitPointEntryTermsBounded s' := by
  intro b p hp hpl
  rw [h_cp] at hp; rw [h_log] at hpl
  have := h_cpetb b p hp hpl
  unfold logTerm getTerm at this ⊢; rw [h_log, h_cp]; exact this

-- logTermsMonotonic depends only on log
lemma logTermsMonotonic_of_log_eq {s s' : RaftState Server}
    (h_log : s'.log = s.log) (h_mono : logTermsMonotonic s) : logTermsMonotonic s' := by
  intro srv p q hpq hq
  unfold logTerm getTerm; rw [h_log]
  have : q ≤ (s.log srv).length := by rwa [h_log] at hq
  exact h_mono srv p q hpq this

-- currentTermMatchesLeader: if log, state, and gCT unchanged, transfers directly
lemma currentTermMatchesLeader_of_log_state_eq
    {s s' : RaftState Server}
    (h_log : s'.log = s.log)
    (h_state : s'.state = s.state)
    (h_term : s'.globalCurrentTerm = s.globalCurrentTerm)
    (h_ctml : currentTermMatchesLeader s) :
    currentTermMatchesLeader s' := by
  intro ldr b p h_ldr h_len h_eq
  rw [h_state] at h_ldr; rw [h_log] at h_len
  unfold logTerm getTerm at h_eq ⊢
  rw [h_log] at h_eq ⊢; rw [h_term] at h_eq ⊢
  exact h_ctml ldr b p h_ldr h_len h_eq

-- logMatching: if log unchanged, transfers directly
lemma logMatching_of_log_eq {s s' : RaftState Server}
    (h_log : s'.log = s.log)
    (h_lm : logMatching s) : logMatching s' := by
  intro a b p hp hpb h_eq q hq
  unfold logTerm getTerm at h_eq ⊢
  rw [h_log] at hp hpb h_eq ⊢
  exact h_lm a b p hp hpb h_eq q hq

-- leaderUnique: if state unchanged, transfers directly
lemma leaderUnique_of_state_eq {s s' : RaftState Server}
    (h_state : s'.state = s.state)
    (h_lu : leaderUnique s) : leaderUnique s' := by
  intro a b ha hb; rw [h_state] at ha hb; exact h_lu a b ha hb

-- getTerm on an appended list: for indices within the old list, same as old list;
-- for the new entry at position length+1, returns the new entry's term.
lemma getTerm_append_singleton (xlog : List LogEntry) (entry : LogEntry) (idx : Nat) :
    getTerm (xlog ++ [entry]) idx =
      if idx ≤ xlog.length then getTerm xlog idx
      else if idx = xlog.length + 1 then entry.term
      else 0 := by
  unfold getTerm
  split
  · -- idx = 0
    next h => subst h; simp
  · next h_ne =>
    split_ifs with h_le h_eq
    · -- idx ≤ xlog.length, so idx - 1 < xlog.length
      have h_bound : idx - 1 < xlog.length := by omega
      rw [List.getElem?_append_left h_bound]
    · -- idx = xlog.length + 1
      subst h_eq
      rw [List.getElem?_append_right (by omega)]
      simp [Nat.sub_self]
    · -- idx > xlog.length + 1: out of bounds on both lists
      rw [List.getElem?_append_right (by omega)]
      rw [List.getElem?_eq_none (by simp; omega)]

-- logTerm with term > globalCurrentTerm is impossible when termsAreBounded
lemma logTerm_le_globalCurrentTerm {s : RaftState Server} (h_tb : termsAreBounded s)
    (srv : Server) (idx : Nat) :
    logTerm s srv idx ≤ s.globalCurrentTerm := by
  unfold logTerm getTerm
  split
  · omega
  · next h_ne =>
    split
    · next entry h_some =>
      -- entry is in the log, so its term is bounded
      have h_mem : entry ∈ s.log srv := List.mem_of_getElem? h_some
      exact h_tb srv entry h_mem
    · omega

-- logTermsMonotonic preserved when appending one entry whose term ≥ lastTerm.
-- For server i whose log becomes `old_log ++ [entry]`, we need:
-- (1) old log is monotonic, (2) entry.term ≥ all old entry terms.
-- For other servers, log unchanged → use IH.
lemma logTermsMonotonic_append_entry {s s' : RaftState Server}
    {i : Server}
    (h_log : s'.log = Function.update s.log i ((s.log i) ++ [⟨s.globalCurrentTerm⟩]))
    (h_mono : logTermsMonotonic s)
    (h_tb : termsAreBounded s) :
    logTermsMonotonic s' := by
  intro srv p q hpq hq
  -- Work at the logTerm level without early unfolding
  unfold logTerm
  rw [h_log]
  simp only [Function.update_apply]
  by_cases h_eq : srv = i
  · -- srv = i: log is s.log i ++ [{term := gCT}]
    subst h_eq
    simp only [ite_true] at hq ⊢
    rw [h_log] at hq; simp only [Function.update_apply, ite_true,
      List.length_append, List.length_singleton] at hq
    rw [getTerm_append_singleton, getTerm_append_singleton]
    -- Case split on whether q is in old log or at the new entry
    split_ifs with hp_le hp_eq hq_le hq_eq hq_le' hq_eq'
    -- p ≤ len, q ≤ len: both in old log
    · have := h_mono srv p q hpq hp_eq; unfold logTerm at this; exact this
    -- p ≤ len, q = len + 1: new entry has term = gCT ≥ old terms
    · have := logTerm_le_globalCurrentTerm h_tb srv p; unfold logTerm at this; omega
    -- p ≤ len, q out of bounds (impossible)
    · omega
    -- p = len + 1, q ≤ len (impossible since p ≤ q)
    · omega
    -- p = len + 1, q = len + 1
    · omega
    -- p = len + 1, q out of bounds (impossible)
    · omega
    -- p out of bounds (impossible since p ≤ q ≤ len + 1)
    · omega
    · omega
    · omega
  · -- srv ≠ i: log unchanged
    simp only [if_neg h_eq] at hq ⊢
    have hq' : q ≤ (s.log srv).length := by rw [h_log] at hq; simp [h_eq] at hq; exact hq
    have := h_mono srv p q hpq hq'; unfold logTerm at this; exact this

-- neverRollbackCommitted follows directly from termsAreBounded.
-- Proof: rollbackCommitted requires both canRollbackOplog (lastTerm(log_i) < lastTerm(log_j))
-- and isCommitted (logTerm at last index = globalCurrentTerm, i.e., lastTerm = globalCurrentTerm).
-- Combined with termsAreBounded (lastTerm(log_j) ≤ globalCurrentTerm), we get
-- globalCurrentTerm < globalCurrentTerm — contradiction.
lemma neverRollbackCommitted_of_termsAreBounded {s : RaftState Server}
    (h_tb : termsAreBounded s) : neverRollbackCommitted s := by
  intro i ⟨j, h_can, h_comm⟩
  unfold canRollbackOplog at h_can
  obtain ⟨_, h_lt, _⟩ := h_can
  unfold isCommitted at h_comm
  obtain ⟨_, h_eq⟩ := h_comm
  -- h_eq : logTerm s i (s.log i).length = s.globalCurrentTerm
  -- h_lt : lastTerm (s.log i) < lastTerm (s.log j)
  -- logTerm at length = lastTerm
  unfold logTerm at h_eq
  have h_bound := logTerm_le_globalCurrentTerm h_tb j (s.log j).length
  unfold logTerm at h_bound
  unfold lastTerm at h_lt
  omega

-- rollbackSafeCommitPoint depends on log and commitPoint
lemma rollbackSafeCommitPoint_of_log_cp_eq
    {s s' : RaftState Server}
    (h_log : s'.log = s.log)
    (h_cp : s'.commitPoint = s.commitPoint)
    (h_rsc : rollbackSafeCommitPoint s) :
    rollbackSafeCommitPoint s' := by
  intro srv ⟨j, h_can⟩
  rw [h_cp, h_log]
  exact h_rsc srv ⟨j, (canRollbackOplog_of_log_eq h_log).mp h_can⟩

-- appendOplogEnabled depends only on log
lemma appendOplogEnabled_of_log_eq
    {i j : Server} {s s' : RaftState Server}
    (h_log : s'.log = s.log) :
    appendOplogEnabled i j s' ↔ appendOplogEnabled i j s := by
  unfold appendOplogEnabled lastTerm logTerm getTerm
  simp [h_log]

-- rollbackWithSyncSourceImpliesCommitPointBelowTip depends on log and commitPoint
lemma rollbackWithSyncSourceImpliesCommitPointBelowTip_of_log_cp_eq
    {s s' : RaftState Server}
    (h_log : s'.log = s.log)
    (h_cp : s'.commitPoint = s.commitPoint)
    (h_rwss : rollbackWithSyncSourceImpliesCommitPointBelowTip s) :
    rollbackWithSyncSourceImpliesCommitPointBelowTip s' := by
  intro a b h_aoe h_can h_below
  rw [h_log, h_cp] at h_below
  have h_aoe_s : appendOplogEnabled a b s := by
    unfold appendOplogEnabled lastTerm logTerm getTerm at h_aoe ⊢
    rwa [h_log] at h_aoe
  have h_can_s : ∃ k, canRollbackOplog a k s := by
    obtain ⟨k, hk⟩ := h_can
    exact ⟨k, (canRollbackOplog_of_log_eq h_log).mp hk⟩
  exact h_rwss a b h_aoe_s h_can_s h_below

-- logTerm at the commit point index equals the commit point term.
-- This is the core invariant: every server's log agrees with the commit point
-- at exactly the commit point's index.
-- Proof: use a cpbq quorum witness n₀; case-split on lastTerm(n₀) vs cpTerm:
--   if lastTerm(n₀) > cpTerm: h_llcp gives agreement srv↔n₀,
--     and cpbq gives logTerm n₀ cp.idx = cpTerm
--   if lastTerm(n₀) = cpTerm: h_cpa gives agreement srv↔n₀, same conclusion
lemma logTerm_at_commitPoint_eq_term
    (s : RaftState Server) (srv : Server)
    (h_cpbq : commitPointsBackedByQuorums s)
    (h_llcp : logsLaterThanCommitPointHaveEntries s)
    (h_cpa : commitPointAgreement s)
    (h_cp_le : (s.commitPoint srv).index ≤ (s.log srv).length) :
    logTerm s srv (s.commitPoint srv).index = (s.commitPoint srv).term := by
  obtain ⟨Q₀, hQ₀, hcover, _⟩ := h_cpbq srv
  have hQ₀_ne : Q₀.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h_empty
    subst h_empty; unfold isQuorum at hQ₀; simp at hQ₀
  obtain ⟨n₀, hn₀_mem⟩ := hQ₀_ne
  have hn₀ := hcover n₀ hn₀_mem
  rcases Nat.lt_or_ge (s.commitPoint srv).term (lastTerm (s.log n₀)) with h_gt | h_le
  · -- lastTerm(n₀) > cpTerm: use h_llcp to chain n₀ → srv
    rw [← (h_llcp n₀ srv h_gt).2 _ (le_refl _) h_cp_le]
    exact hn₀.2.2
  · -- lastTerm(n₀) = cpTerm: use h_cpa to chain n₀ → srv
    have h_eq_n : lastTerm (s.log n₀) = (s.commitPoint srv).term :=
      Nat.le_antisymm h_le hn₀.2.1
    rw [← h_cpa n₀ srv h_eq_n hn₀.1 _ (le_refl _) h_cp_le]
    exact hn₀.2.2

-------------------------------------------------------------------------------
-- Function.update log helpers
--
-- These lemmas factor out the boilerplate of translating logTerm, log length,
-- and lastTerm across state changes where exactly one server's log is updated
-- via Function.update.
-------------------------------------------------------------------------------

-- logTerm is unchanged for servers other than the updated one
lemma logTerm_update_ne {s s' : RaftState Server} {i : Server} {newLog : List LogEntry}
    (h_log : s'.log = Function.update s.log i newLog)
    {srv : Server} (h_ne : srv ≠ i) (idx : Nat) :
    logTerm s' srv idx = logTerm s srv idx := by
  unfold logTerm getTerm; rw [h_log]
  simp only [Function.update_apply, if_neg h_ne]

-- logTerm at old indices is unchanged when appending one entry
lemma logTerm_update_self_append_old {s s' : RaftState Server} {i : Server} {entry : LogEntry}
    (h_log : s'.log = Function.update s.log i (s.log i ++ [entry]))
    {idx : Nat} (h_idx : idx ≤ (s.log i).length) :
    logTerm s' i idx = logTerm s i idx := by
  unfold logTerm getTerm; rw [h_log]
  simp only [Function.update_apply, ite_true]
  split; · rfl
  · next h_ne => rw [List.getElem?_append_left (by omega)]

-- logTerm at the new position equals the appended entry's term
lemma logTerm_update_self_append_new {s s' : RaftState Server} {i : Server} {entry : LogEntry}
    (h_log : s'.log = Function.update s.log i (s.log i ++ [entry])) :
    logTerm s' i ((s.log i).length + 1) = entry.term := by
  unfold logTerm getTerm; rw [h_log]
  simp only [Function.update_apply,
    show (s.log i).length + 1 ≠ 0 from by omega, ↓reduceIte]
  rw [List.getElem?_append_right (by omega)]
  simp [Nat.sub_self]

-- logTerm at indices within dropLast is unchanged
lemma logTerm_update_self_dropLast {s s' : RaftState Server} {i : Server}
    (h_log : s'.log = Function.update s.log i (s.log i).dropLast)
    {idx : Nat} (h_idx : idx ≤ (s.log i).dropLast.length) :
    logTerm s' i idx = logTerm s i idx := by
  unfold logTerm getTerm; rw [h_log]
  simp only [Function.update_apply, ite_true]
  split; · rfl
  · next h_ne =>
    rw [List.getElem?_dropLast]
    rw [if_pos (by rw [List.length_dropLast] at h_idx; omega)]

-- Log length is unchanged for servers other than the updated one
lemma length_update_ne {s s' : RaftState Server} {i : Server} {newLog : List LogEntry}
    (h_log : s'.log = Function.update s.log i newLog)
    {srv : Server} (h_ne : srv ≠ i) :
    (s'.log srv).length = (s.log srv).length := by
  have := congr_fun h_log srv
  simp [h_ne] at this; rw [this]

-- Log length increases by 1 when appending one entry
lemma length_update_self_append {s s' : RaftState Server} {i : Server} {entry : LogEntry}
    (h_log : s'.log = Function.update s.log i (s.log i ++ [entry])) :
    (s'.log i).length = (s.log i).length + 1 := by
  have : s'.log i = (s.log i) ++ [entry] := by
    have := congr_fun h_log i; simp at this; exact this
  rw [this, List.length_append, List.length_singleton]

-- Log length after dropLast equals the dropLast length
lemma length_update_self_dropLast {s s' : RaftState Server} {i : Server}
    (h_log : s'.log = Function.update s.log i (s.log i).dropLast) :
    (s'.log i).length = (s.log i).dropLast.length := by
  have := congr_fun h_log i; simp at this; rw [this]

-- lastTerm is unchanged for servers other than the updated one
lemma lastTerm_update_ne {s s' : RaftState Server} {i : Server} {newLog : List LogEntry}
    (h_log : s'.log = Function.update s.log i newLog)
    {srv : Server} (h_ne : srv ≠ i) :
    lastTerm (s'.log srv) = lastTerm (s.log srv) := by
  have : s'.log srv = s.log srv := by
    have := congr_fun h_log srv; simp [h_ne] at this; exact this
  simp [this]

-- lastTerm of a log with one appended entry equals the entry's term
lemma lastTerm_append_entry (xlog : List LogEntry) (entry : LogEntry) :
    lastTerm (xlog ++ [entry]) = entry.term := by
  unfold lastTerm getTerm
  rw [List.length_append, List.length_singleton]
  simp only [show xlog.length + 1 ≠ 0 from by omega, ↓reduceIte]
  rw [List.getElem?_append_right (by omega)]
  simp [Nat.sub_self]

/- ================================================================
   Section 11: Base Case
   ================================================================ -/

lemma raftInvariant_init : raftInvariant (raftInit : RaftState Server) := by
  unfold raftInvariant
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- 1. NeverRollbackCommitted: all logs empty, canRollbackOplog requires length > 0.
  · intro i ⟨j, hcan, _⟩
    unfold canRollbackOplog at hcan; simp [raftInit] at hcan
  -- 2. NeverRollbackBeforeCommitPoint: same reason
  · intro i ⟨⟨j, hcan⟩, _⟩
    unfold canRollbackOplog at hcan; simp [raftInit] at hcan
  -- 3. termsAreBounded: all logs empty, vacuously true
  · intro i e he; simp [raftInit] at he
  -- 4. commitPointBounded: all commit points have term 0
  · intro i; simp [raftInit]
  -- 5. logTermsMonotonic: all logs empty, vacuously true
  · intro i p q hpq hq
    simp only [raftInit, List.length_nil] at hq
    have hp : p = 0 := by omega
    have hq0 : q = 0 := by omega
    subst hp; subst hq0; rfl
  -- 6. currentTermMatchesLeader: no leader in init state
  · intro ldr _ _ h_ldr; simp [raftInit] at h_ldr
  -- 7. leaderUnique: no leader in init state
  · intro a _ ha; simp [raftInit] at ha
  -- 8. logMatching: all logs empty, vacuously true
  · intro i j p hp _hpj _h_eq q hq
    simp only [raftInit, List.length_nil] at hp
    have : p = 0 := by omega
    have : q = 0 := by omega
    subst_vars; rfl
  -- 9. leaderCompletenessForCommitPoints: no leader in init state
  · intro ldr _ h_ldr; simp [raftInit] at h_ldr
  -- 10. commitPointsBackedByQuorums: cp = (0,0), cpIdx = 0 ≤ any log length
  · intro srv
    -- Use Finset.univ as the quorum (always a quorum since Server is nonempty)
    refine ⟨Finset.univ, ?_, fun n _ => ?_, fun n₁ n₂ _ _ p hp => ?_⟩
    · unfold isQuorum; rw [Finset.card_univ]
      have : Fintype.card Server > 0 := @Fintype.card_pos Server _ ⟨srv⟩
      omega
    · simp [raftInit, lastTerm, getTerm, logTerm]
    · simp [raftInit] at hp; subst hp; unfold logTerm getTerm; simp
  -- 11. logsLaterThanCommitPointHaveEntries: all logs empty, lastTerm = 0, cp.term = 0
  · intro a _b h_gt; simp [raftInit, lastTerm, getTerm] at h_gt
  -- 12. commitPointAgreement: all logs empty, cp.index = 0, vacuously true
  · intro a _b _h_lt h_len p hp _hpl
    simp [raftInit] at h_len; simp [raftInit] at hp; subst hp
    unfold logTerm getTerm; simp
  -- 13. leaderLastTermGeCommitPointTerm: no leader in init state
  · intro ldr _ h_ldr; simp [raftInit] at h_ldr
  -- 14. uniformLogEntriesInTerm: all logs empty, vacuously true
  · intro a _ i _ hi hia; simp [raftInit] at hia; omega
  -- 15. commitPointWeaklyBelowLogTip: all logs empty, cp = ⟨0,0⟩
  · intro srv; right; simp [raftInit, lastTerm, getTerm]
  -- 16. commitPointEntryTermsBounded: cp.index = 0, vacuously true
  · intro b p hp; simp [raftInit] at hp; subst hp; simp [logTerm, getTerm]
  -- 17. rollbackSafeCommitPoint: all logs empty, canRollbackOplog requires length > 0
  · intro srv ⟨j, h_can⟩; simp [canRollbackOplog, raftInit] at h_can
  -- 18. rollbackWithSyncSourceImpliesCommitPointBelowTip: appendOplogEnabled requires
  --     len(i) < len(j), but all logs are empty in init, so vacuously true.
  · intro i j h_aoe; simp [appendOplogEnabled, raftInit] at h_aoe

/- ================================================================
   Section 12: Inductive Step — Per-Action Preservation
   ================================================================ -/

lemma raftInvariant_appendOplog (i j : Server) (s s' : RaftState Server) :
    raftInvariant s → appendOplog i j s s' → raftInvariant s' := by
  -- appendOplog changes: log (appends one entry from j to i)
  -- Unchanged: globalCurrentTerm, state, commitPoint
  -- The appended entry comes from j's log, so its term is ≤ globalCurrentTerm.
  intro ⟨h_nrc, h_nrbcp, h_tb, h_cpb, h_mono, h_ctml, h_lu, h_lm,
         h_lccp, h_cpbq, h_llcp, h_cpa, h_lgt, h_ulet, h_cwb, h_cpetb, h_rsc, h_rwss⟩
    ⟨h_len, h_match, ⟨entry, h_get, h_log⟩, h_term, h_state, h_cp⟩
  -- Shared helpers: restate the logTerm/lastTerm rewriting lemmas with h_log fixed,
  -- so sub-goal proofs can reference them without re-unfolding definitions.
  have lt_ne : ∀ srv, srv ≠ i → ∀ idx, logTerm s' srv idx = logTerm s srv idx :=
    fun srv h_ne idx => logTerm_update_ne h_log h_ne idx
  have lt_old : ∀ idx, idx ≤ (s.log i).length → logTerm s' i idx = logTerm s i idx :=
    fun idx h_idx => logTerm_update_self_append_old h_log h_idx
  have lt_new : logTerm s' i ((s.log i).length + 1) = entry.term :=
    logTerm_update_self_append_new h_log
  have h_lastTerm_app : lastTerm (s.log i ++ [entry]) = entry.term :=
    lastTerm_append_entry (s.log i) entry
  -- First establish termsAreBounded s' (needed for neverRollbackCommitted)
  have h_tb' : termsAreBounded s' := by
    intro srv e he
    rw [h_log] at he
    simp only [Function.update_apply] at he
    split_ifs at he with h_eq
    · rw [h_term]
      rcases List.mem_append.mp he with h_old | h_new
      · exact h_tb _ e h_old
      · simp only [List.mem_singleton] at h_new; rw [h_new]
        exact h_tb j entry (List.mem_of_getElem? h_get)
    · rw [h_term]; exact h_tb srv e he
  -- Shared helper: logTerm s j at the new position equals entry.term.
  have h_entry_eq : logTerm s j ((s.log i).length + 1) = entry.term := by
    unfold logTerm getTerm
    simp only [show (s.log i).length + 1 ≠ 0 from by omega, ↓reduceIte,
      show (s.log i).length + 1 - 1 = (s.log i).length from by omega]
    simp [h_get]
  -- Shared helper: entry.term ≥ lastTerm(s.log i).
  -- entry comes from j's log; by logTermsMonotonic on j, j's term at that position ≥ lastTerm(i).
  have h_entry_ge : entry.term ≥ lastTerm (s.log i) := by
    have := h_mono j (s.log i).length ((s.log i).length + 1) (by omega) (by omega)
    rw [h_match]; rw [h_entry_eq] at this; exact this
  -- Shared helper: len(s'.log i) = oldLen + 1
  have h_new_len : (s'.log i).length = (s.log i).length + 1 := by
    have : s'.log i = (s.log i) ++ [entry] := by
      have := congr_fun h_log i; simp at this; exact this
    rw [this, List.length_append, List.length_singleton]
  -- Shared helper: len(s'.log srv) = len(s.log srv) for srv ≠ i
  have h_len_ne : ∀ srv, srv ≠ i → (s'.log srv).length = (s.log srv).length := by
    intro srv h_ne; have := congr_fun h_log srv
    simp [h_ne] at this; rw [this]
  -- Shared helper: logMatching between i and j at all positions up to len(s.log i)
  have h_ij_match : ∀ r, r ≤ (s.log i).length →
      logTerm s i r = logTerm s j r :=
    h_lm i j (s.log i).length (le_refl _) (by omega) h_match
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- 1. neverRollbackCommitted: follows from termsAreBounded
  · exact neverRollbackCommitted_of_termsAreBounded h_tb'
  -- 2. neverRollbackBeforeCommitPoint
  · -- appendOplog appends entry to server i's log; commitPoint unchanged.
    intro srv h_rbcp
    unfold rollbackBeforeCommitPoint at h_rbcp
    obtain ⟨⟨k, h_can⟩, h_below⟩ := h_rbcp
    by_cases h_srv_i : srv = i
    · -- srv = i: log grew, cp unchanged. Show commit-point condition (B) fails.
      subst h_srv_i
      have h_log_i : s'.log srv = s.log srv ++ [entry] := by rw [h_log]; simp
      rw [h_log_i, h_lastTerm_app, h_cp,
        show (s.log srv ++ [entry]).length = (s.log srv).length + 1 from
          by rw [List.length_append, List.length_singleton]] at h_below
      -- h_below contradicts h_cwb + h_entry_ge:
      -- h_cwb says cpTerm ≤ lastTerm(srv) (weakly below log tip)
      -- h_entry_ge says entry.term ≥ lastTerm(srv)
      -- h_below says entry.term < cpTerm ∨ (entry.term = cpTerm ∧ srvLen+1 ≤ cpIdx)
      -- Both disjuncts are impossible.
      rcases h_cwb srv with h_cp_lt | ⟨h_cp_eq, h_cp_le⟩
      · -- cpTerm < lastTerm(srv) ≤ entry.term, contradicts h_below
        rcases h_below with h_bl | ⟨h_beq, _⟩ <;> omega
      · -- cpTerm = lastTerm(srv) ∧ cpIdx ≤ srvLen
        -- entry.term ≥ lastTerm(srv) = cpTerm
        rcases h_below with h_bl | ⟨_, h_bidx⟩ <;> omega
    · -- srv ≠ i: log and cp unchanged for srv
      have h_log_srv : s'.log srv = s.log srv := by rw [h_log]; simp [h_srv_i]
      rw [h_log_srv, h_cp] at h_below
      unfold canRollbackOplog at h_can
      rw [h_log] at h_can
      simp only [Function.update_apply, if_neg h_srv_i] at h_can
      by_cases h_k_i : k = i
      · -- k = i: i's log changed to (s.log i) ++ [entry]
        rw [h_k_i, if_pos rfl] at h_can
        obtain ⟨h_len_pos, h_lt_last, h_disj⟩ := h_can
        rw [h_lastTerm_app] at h_lt_last
        -- Try j as canRollbackOplog witness in s (entry.term ≤ lastTerm(j) by mono)
        by_cases h3j : (s.log srv).length > (s.log j).length
            ∨ ((s.log srv).length ≤ (s.log j).length
              ∧ lastTerm (s.log srv) ≠ logTerm s j (s.log srv).length)
        · -- Third condition holds for j → witness in s
          have h_lt_j : lastTerm (s.log srv) < lastTerm (s.log j) := by
            -- entry.term ≤ logTerm s j (s.log j).length = lastTerm(s.log j)
            have h_mono_j := h_mono j ((s.log i).length + 1) (s.log j).length
              (by omega) (le_refl _)
            -- logTerm s j len(j) = lastTerm(s.log j) by definition
            have : logTerm s j (s.log j).length = lastTerm (s.log j) := rfl
            omega
          exact h_nrbcp srv ⟨⟨j, h_len_pos, h_lt_j, h3j⟩, h_below⟩
        · -- Third condition fails for j → derive contradiction
          push_neg at h3j
          obtain ⟨h_le_lenj, h_imp_termj⟩ := h3j
          have h_eq_termj : lastTerm (s.log srv) = logTerm s j (s.log srv).length :=
            h_imp_termj h_le_lenj
          -- By logMatching on srv and j at len(srv):
          have h_srv_j_match : ∀ q, q ≤ (s.log srv).length →
              logTerm s srv q = logTerm s j q :=
            h_lm srv j (s.log srv).length (le_refl _) h_le_lenj h_eq_termj
          rcases Nat.lt_or_ge (s.log i).length (s.log srv).length with h_srv_gt | h_srv_le
          · -- len(srv) > len(i): entry.term ≤ lastTerm(srv), contradiction
            have h1 : logTerm s srv ((s.log i).length + 1) = entry.term := by
              rw [h_srv_j_match ((s.log i).length + 1) (by omega), h_entry_eq]
            have h2 := h_mono srv ((s.log i).length + 1) (s.log srv).length
              (by omega) (le_refl _)
            -- logTerm s srv len(srv) = lastTerm(s.log srv) by definition
            have : logTerm s srv (s.log srv).length = lastTerm (s.log srv) := rfl
            omega
          · -- len(srv) ≤ len(i): logTerm s' i len(srv) = lastTerm(srv), so
            -- third condition of canRollbackOplog srv i s' fails.
            have h_lt_eq : logTerm s i (s.log srv).length =
                logTerm s j (s.log srv).length :=
              h_ij_match (s.log srv).length h_srv_le
            rw [← h_eq_termj] at h_lt_eq
            -- logTerm s' i len(srv) = logTerm s i len(srv) (within old log)
            have h_lt_s' := lt_old (s.log srv).length h_srv_le
            have h_app_len : (s.log i ++ [entry]).length = (s.log i).length + 1 :=
              by rw [List.length_append, List.length_singleton]
            rw [h_lt_s', h_lt_eq, h_app_len] at h_disj
            rcases h_disj with h_big | ⟨_, h_ne⟩
            · omega  -- len(srv) > len(i)+1 contradicts len(srv) ≤ len(i)
            · exact absurd rfl h_ne  -- lastTerm(srv) ≠ lastTerm(srv)
      · -- k ≠ i: both logs unchanged, canRollbackOplog transfers directly
        simp only [if_neg h_k_i] at h_can
        -- h_can still references logTerm s'; convert to logTerm s
        simp only [lt_ne k h_k_i (s.log srv).length] at h_can
        exact h_nrbcp srv ⟨⟨k, h_can⟩, h_below⟩
  -- 3. termsAreBounded
  · exact h_tb'
  -- 4. commitPointBounded: commitPoint unchanged, globalCurrentTerm unchanged
  · intro srv; rw [h_cp, h_term]; exact h_cpb srv
  -- 5. logTermsMonotonic
  · -- For server i, log became (s.log i) ++ [entry].
    -- entry.term ≥ lastTerm(s.log i) by shared h_entry_ge.
    -- For p ≤ len(old), getTerm(old, p) ≤ lastTerm(old) ≤ entry.term by mono.
    -- For other servers, log unchanged → use IH.
    intro srv p q hpq hq
    unfold logTerm
    by_cases h_eq : srv = i
    · -- srv = i: log is s.log i ++ [entry]
      subst h_eq
      have h_log_i : s'.log srv = s.log srv ++ [entry] := by rw [h_log]; simp
      rw [h_log_i] at hq ⊢
      rw [List.length_append, List.length_singleton] at hq
      -- Case split on q position
      rcases Nat.lt_or_ge q ((s.log srv).length + 1) with hq_old | hq_new
      · -- q ≤ len: both p and q in old log; use getTerm_append_singleton + IH
        rw [getTerm_append_singleton, if_pos (by omega),
            getTerm_append_singleton, if_pos (by omega)]
        exact h_mono srv p q hpq (by omega)
      · -- q = len + 1 (the new entry)
        have hq_eq : q = (s.log srv).length + 1 := by omega
        subst hq_eq
        -- Rewrite the RHS to entry.term via getTerm_append_singleton
        conv_rhs => rw [getTerm_append_singleton, if_neg (by omega), if_pos rfl]
        rcases Nat.lt_or_ge p ((s.log srv).length + 1) with hp_old | hp_new
        · -- p ≤ len: getTerm(old, p) ≤ lastTerm(old) ≤ entry.term
          rw [getTerm_append_singleton, if_pos (by omega)]
          have : getTerm (s.log srv) p ≤ lastTerm (s.log srv) :=
            h_mono srv p (s.log srv).length (by omega) (le_refl _)
          omega
        · -- p = len + 1 = q: trivial
          have hp_eq : p = (s.log srv).length + 1 := by omega
          subst hp_eq
          rw [getTerm_append_singleton, if_neg (by omega), if_pos rfl]
    · -- srv ≠ i: log unchanged
      have h_log_srv : s'.log srv = s.log srv := by rw [h_log]; simp [h_eq]
      rw [h_log_srv] at hq ⊢
      exact h_mono srv p q hpq hq
  -- 6. currentTermMatchesLeader: state/gCT unchanged, log i grew by entry from j
  · intro ldr b p h_ldr' h_len' h_eq'
    rw [h_state] at h_ldr'; rw [h_term]
    by_cases h_ldr_i : ldr = i
    · -- ldr = i: i's log grew
      rw [h_ldr_i]
      by_cases h_b_i : b = i
      · -- b = i: h_eq' gives logTerm s' i p = gCT, which is the goal
        rw [h_b_i] at h_eq'; rw [h_term] at h_eq'; exact h_eq'
      · -- b ≠ i: b's log unchanged
        have h_eq_s : logTerm s b p = s.globalCurrentTerm := by
          rw [lt_ne b h_b_i p, h_term] at h_eq'; exact h_eq'
        have h_len_s : p ≤ (s.log b).length := by
          rw [h_log] at h_len'
          simp only [Function.update_apply, if_neg h_b_i] at h_len'
          exact h_len'
        have h_old := h_ctml i b p (h_ldr_i ▸ h_ldr') h_len_s h_eq_s
        -- logTerm s i p = gCT. Transfer to s'.
        rcases Nat.lt_or_ge p ((s.log i).length + 1) with h_sm | h_bg
        · rw [lt_old p (by omega)]; exact h_old
        · -- p > old length: logTerm s i p = 0, gCT = 0
          have : logTerm s i p = 0 := by
            unfold logTerm getTerm; split; · omega
            · next h_ne => rw [List.getElem?_eq_none (by omega)]
          rw [h_old] at this
          have := logTerm_le_globalCurrentTerm h_tb' i p
          rw [h_term] at this; omega
    · -- ldr ≠ i: ldr's log unchanged
      rw [lt_ne ldr h_ldr_i p]
      by_cases h_b_i : b = i
      · -- b = i: b's log grew
        rw [h_b_i] at h_eq' h_len'
        rw [h_log] at h_len'
        simp only [Function.update_apply, ite_true] at h_len'
        rw [List.length_append, List.length_singleton] at h_len'
        rcases Nat.lt_or_ge p ((s.log i).length + 1) with h_sm | h_bg
        · -- p ≤ old length
          have h_eq_s : logTerm s i p = s.globalCurrentTerm := by
            rw [lt_old p (by omega), h_term] at h_eq'; exact h_eq'
          exact h_ctml ldr i p h_ldr' (by omega) h_eq_s
        · -- p = old length + 1 (the new entry)
          have h_p_eq : p = (s.log i).length + 1 := by omega
          rw [h_p_eq]
          rw [h_p_eq, lt_new, h_term] at h_eq'
          -- entry.term = gCT → logTerm s j (len+1) = gCT → use h_ctml
          rw [← h_entry_eq] at h_eq'
          exact h_ctml ldr j _ h_ldr' (by omega) h_eq'
      · -- b ≠ i: both logs unchanged, use old h_ctml directly
        have h_eq_s : logTerm s b p = s.globalCurrentTerm := by
          rw [lt_ne b h_b_i p, h_term] at h_eq'; exact h_eq'
        have h_len_s : p ≤ (s.log b).length := by
          rw [h_log] at h_len'
          simp only [Function.update_apply, if_neg h_b_i] at h_len'
          exact h_len'
        exact h_ctml ldr b p h_ldr' h_len_s h_eq_s
  -- 7. leaderUnique: state unchanged
  · exact leaderUnique_of_state_eq h_state h_lu
  -- 8. logMatching
  · intro a b p h_len_a h_len_b h_eq q h_qp
    -- Case split on whether a or b is i
    by_cases h_a : a = i <;> by_cases h_b : b = i
    · -- a = i, b = i: trivial
      rw [h_a, h_b]
    · -- a = i, b ≠ i
      rw [h_a] at h_len_a h_eq ⊢
      rw [lt_ne b h_b] at h_eq
      rw [lt_ne b h_b]
      have h_len_b_s : p ≤ (s.log b).length := by
        rw [h_len_ne b h_b] at h_len_b; exact h_len_b
      rcases Nat.lt_or_ge p ((s.log i).length + 1) with h_small | h_big
      · -- p ≤ oldLen
        rw [lt_old p (by omega)] at h_eq
        rw [lt_old q (by omega)]
        exact h_lm i b p (by omega) h_len_b_s h_eq q h_qp
      · -- p = oldLen + 1
        have h_p : p = (s.log i).length + 1 := by
          rw [h_new_len] at h_len_a; omega
        rw [h_p] at h_eq
        rw [lt_new] at h_eq
        -- h_eq : entry.term = logTerm s b (oldLen+1)
        -- entry.term = logTerm s j (oldLen+1), so logTerm s j (oldLen+1) = logTerm s b (oldLen+1)
        have h_jb : logTerm s j ((s.log i).length + 1) = logTerm s b ((s.log i).length + 1) := by
          rw [h_entry_eq]; exact h_eq
        -- By logMatching on j and b at oldLen+1:
        have h_jb_match : ∀ r, r ≤ (s.log i).length + 1 →
            logTerm s j r = logTerm s b r :=
          h_lm j b ((s.log i).length + 1) (by omega)
            (by rw [h_p] at h_len_b_s; exact h_len_b_s) h_jb
        rcases Nat.lt_or_ge q ((s.log i).length + 1) with h_q_sm | h_q_bg
        · -- q ≤ oldLen
          rw [lt_old q (by omega)]
          rw [h_ij_match q (by omega)]
          exact h_jb_match q (by omega)
        · -- q = oldLen+1 = p
          have h_q_p : q = p := by omega
          rw [h_q_p, h_p, lt_new, ← h_entry_eq]
          exact h_jb_match ((s.log i).length + 1) (le_refl _)
    · -- a ≠ i, b = i: symmetric
      rw [h_b] at h_len_b h_eq ⊢
      have h_len_a_s : p ≤ (s.log a).length := by
        rw [h_len_ne a h_a] at h_len_a; exact h_len_a
      rcases Nat.lt_or_ge p ((s.log i).length + 1) with h_small | h_big
      · rw [lt_ne a h_a, lt_old p (by omega)] at h_eq
        rw [lt_ne a h_a, lt_old q (by omega)]
        exact h_lm a i p h_len_a_s (by omega) h_eq q h_qp
      · have h_p : p = (s.log i).length + 1 := by
          rw [h_new_len] at h_len_b; omega
        rw [h_p, lt_ne a h_a, lt_new] at h_eq
        -- h_eq : logTerm s a (oldLen+1) = entry.term
        have h_aj : logTerm s a ((s.log i).length + 1) = logTerm s j ((s.log i).length + 1) := by
          rw [h_eq, h_entry_eq]
        have h_aj_match : ∀ r, r ≤ (s.log i).length + 1 →
            logTerm s a r = logTerm s j r :=
          h_lm a j ((s.log i).length + 1)
            (by rw [h_p] at h_len_a_s; exact h_len_a_s) (by omega) h_aj
        rcases Nat.lt_or_ge q ((s.log i).length + 1) with h_q_sm | h_q_bg
        · rw [lt_ne a h_a, lt_old q (by omega)]
          rw [h_aj_match q (by omega), ← h_ij_match q (by omega)]
        · have h_q_p : q = p := by omega
          rw [h_q_p, h_p, lt_ne a h_a, lt_new, ← h_entry_eq]
          exact h_aj_match ((s.log i).length + 1) (le_refl _)
    · -- a ≠ i, b ≠ i: both logs unchanged
      rw [lt_ne a h_a] at h_eq ⊢
      rw [lt_ne b h_b] at h_eq ⊢
      have h_len_a_s : p ≤ (s.log a).length := by
        rw [h_len_ne a h_a] at h_len_a; exact h_len_a
      have h_len_b_s : p ≤ (s.log b).length := by
        rw [h_len_ne b h_b] at h_len_b; exact h_len_b
      exact h_lm a b p h_len_a_s h_len_b_s h_eq q h_qp
  -- 9. leaderCompletenessForCommitPoints: log i grew, state/cp unchanged
  · intro ldr srv h_ldr'
    rw [h_state] at h_ldr'
    rw [h_cp]
    obtain ⟨h_idx, h_agree⟩ := h_lccp ldr srv h_ldr'
    by_cases h_ldr_i : ldr = i <;> by_cases h_srv_i : srv = i
    · -- Case ldr = i, srv = i: comparing i's log with itself — trivial
      rw [h_ldr_i, h_srv_i] at h_idx ⊢
      exact ⟨by rw [h_new_len]; omega, fun _ _ _ => rfl⟩
    · -- Case ldr = i, srv ≠ i: leader's log grew, cpIdx(srv) ≤ len(old log) ≤ len(new log)
      rw [h_ldr_i] at h_idx h_agree ⊢
      refine ⟨by rw [h_new_len]; omega, fun p h_p_cp h_p_log => ?_⟩
      rw [h_len_ne srv h_srv_i] at h_p_log
      rw [lt_old p (by omega), lt_ne srv h_srv_i]
      exact h_agree p h_p_cp h_p_log
    · -- Case ldr ≠ i, srv = i: the hard sub-case
      rw [h_srv_i] at h_idx h_agree ⊢
      refine ⟨by rw [h_len_ne ldr h_ldr_i]; exact h_idx, fun p h_p_cp h_p_log => ?_⟩
      rw [h_new_len] at h_p_log
      rw [lt_ne ldr h_ldr_i]
      rcases Nat.lt_or_ge p ((s.log i).length + 1) with h_small | h_big
      · -- p ≤ len(old log): logTerm unchanged, use old invariant
        rw [lt_old p (by omega)]
        exact h_agree p h_p_cp (by omega)
      · -- p = len(old log) + 1: need logTerm s ldr p = entry.term
        have h_p_eq : p = (s.log i).length + 1 := by omega
        rw [h_p_eq, lt_new, ← h_entry_eq]
        -- Goal: logTerm s ldr (len_i + 1) = logTerm s j (len_i + 1)
        -- Step 1: ldr agrees with i at len_i (from h_agree)
        have h_ldr_i_at_len : logTerm s ldr (s.log i).length = logTerm s i (s.log i).length :=
          h_agree (s.log i).length (by omega) (le_refl _)
        -- Step 3: Case split on entry.term vs gCT
        have h_entry_le_gct : entry.term ≤ s.globalCurrentTerm :=
          h_tb j entry (List.mem_of_getElem? h_get)
        rcases Nat.eq_or_lt_of_le h_entry_le_gct with h_entry_gct | h_lt_gct
        · -- entry.term = gCT: use h_ctml
          have h_j_gct : logTerm s j ((s.log i).length + 1) = s.globalCurrentTerm := by
            rw [h_entry_eq]; exact h_entry_gct
          rw [h_j_gct]
          exact h_ctml ldr j ((s.log i).length + 1) h_ldr' (by omega) h_j_gct
        · -- entry.term < gCT: use h_lccp ldr j (leader completeness wrt j)
          obtain ⟨h_cpj_idx, h_cpj_agree⟩ := h_lccp ldr j h_ldr'
          rcases Nat.lt_or_ge ((s.log i).length + 1) ((s.commitPoint j).index + 1) with
            h_cpj_big | h_cpj_small
          · -- cpIdx(j) ≥ len_i+1: direct from h_lccp ldr j
            exact h_cpj_agree ((s.log i).length + 1) (by omega) (by omega)
          · -- cpIdx(j) < len_i+1: need deeper argument
            -- cpIdx(i) > len_i, so lastTerm(log i) ≤ cpTerm(i) (h_llcp i i contrapositive)
            have h_lt_cp : lastTerm (s.log i) ≤ (s.commitPoint i).term := by
              by_contra h_neg; push_neg at h_neg
              exact absurd (h_llcp i i h_neg).1 (by omega)
            -- lastTerm(log ldr) ≥ cpTerm(i) (from h_lgt)
            -- Use h_llcp or h_cpa on ldr and j based on lastTerm(ldr) vs cpTerm(j)
            rcases Nat.lt_or_ge (s.commitPoint j).term (lastTerm (s.log ldr)) with
              h_ldr_gt | h_ldr_le
            · -- Vacuous: h_cwb i contradicts h_lt_cp and cpIdx(i) > len_i
              exfalso
              rcases h_cwb i with h_lt | ⟨_, h_le⟩
              · omega
              · omega
            · -- Vacuous: same contradiction as above
              exfalso
              rcases h_cwb i with h_lt | ⟨_, h_le⟩
              · omega
              · omega
    · -- Case ldr ≠ i, srv ≠ i: neither log changed — direct from h_lccp
      refine ⟨by rw [h_len_ne ldr h_ldr_i]; exact h_idx, fun p h_p_cp h_p_log => ?_⟩
      rw [h_len_ne srv h_srv_i] at h_p_log
      rw [lt_ne ldr h_ldr_i, lt_ne srv h_srv_i]
      exact h_agree p h_p_cp h_p_log
  -- 10. commitPointsBackedByQuorums: log i grew, cp unchanged
  -- With ∃ Q formulation: same Q₀ works. All members have len ≥ cpIdx,
  -- so positions ≤ cpIdx are in the unchanged prefix. No sorry needed.
  · intro srv
    obtain ⟨Q₀, hQ₀, hcover₀, hagree₀⟩ := h_cpbq srv
    refine ⟨Q₀, hQ₀, fun n hn => ?_, fun n₁ n₂ hn₁ hn₂ p hp => ?_⟩
    · -- Coverage: cpIdx ≤ len(s'.log n), cpTerm ≤ lastTerm(s'.log n), logTerm = cpTerm
      obtain ⟨hlen, hterm, hlt⟩ := hcover₀ n hn
      rw [h_cp]
      refine ⟨?_, ?_, ?_⟩
      · -- cpIdx ≤ len(s'.log n): log grew or unchanged
        rw [h_log]; by_cases h_n : n = i
        · subst h_n; simp; omega
        · simp [h_n]; exact hlen
      · -- cpTerm ≤ lastTerm(s'.log n): lastTerm grew or unchanged
        rw [h_log]; by_cases h_n : n = i
        · subst h_n; simp
          rw [h_lastTerm_app]; omega
        · simp [h_n]; exact hterm
      · -- logTerm s' n cp.index = cp.term: cp.index ≤ len(n), so in prefix
        have lt_pres_n : logTerm s' n (s.commitPoint srv).index =
            logTerm s n (s.commitPoint srv).index := by
          by_cases h_n : n = i
          · subst h_n; exact lt_old _ hlen
          · exact lt_ne n h_n _
        rw [lt_pres_n]; exact hlt
    · -- Pairwise agreement: p ≤ cpIdx ≤ len(n) for all Q₀ members,
      -- so p is in the unchanged prefix of every member's log.
      rw [h_cp] at hp
      have lt_pres : ∀ m, m ∈ Q₀ → logTerm s' m p = logTerm s m p := by
        intro m hm
        have hlen_m := (hcover₀ m hm).1
        by_cases h_m : m = i
        · subst h_m; exact lt_old p (by omega)
        · exact lt_ne m h_m p
      rw [lt_pres n₁ hn₁, lt_pres n₂ hn₂]
      exact hagree₀ n₁ n₂ hn₁ hn₂ p hp
  -- 11. logsLaterThanCommitPointHaveEntries: log i grew, cp unchanged
  · -- Proof sketch:
    -- For a ≠ i: log a unchanged, lastTerm unchanged → use h_llcp directly.
    -- For a = i: lastTerm(s'.log i) = entry.term > cp(b).term.
    --   If lastTerm(s.log i) > cp(b).term: h_llcp gives cp.index ≤ len(s.log i),
    --     positions in unchanged prefix.
    --   If lastTerm(s.log i) ≤ cp(b).term: use h_cpetb on b to show entries in
    --     j's log at positions ≤ cp.index have term ≤ cp.term. Since entry.term >
    --     cp.term at position len(i)+1, we get cp.index ≤ len(i).
    -- Helper: lastTerm(s'.log i) = entry.term
    have h_lastTerm_new : lastTerm (s'.log i) = entry.term := by
      have : s'.log i = s.log i ++ [entry] := by rw [h_log]; simp
      rw [this, h_lastTerm_app]
    -- Helper: lastTerm(s.log j) > cp(b).term when entry.term > cp(b).term
    have h_j_gt : ∀ b, entry.term > (s.commitPoint b).term →
        lastTerm (s.log j) > (s.commitPoint b).term := by
      intro b h_gt
      have h1 := h_mono j ((s.log i).length + 1) ((s.log j).length)
        (by omega) (le_refl _)
      rw [h_entry_eq] at h1
      have : lastTerm (s.log j) = logTerm s j (s.log j).length := rfl
      omega
    -- Helper: cp(b).index ≤ len(s.log b) (from h_cwb)
    have h_cp_le_log : ∀ b, (s.commitPoint b).index ≤ (s.log b).length := by
      intro b; rcases h_cwb b with h_lt | ⟨_, h_le⟩
      · exact (h_llcp b b h_lt).1
      · exact h_le
    intro a b h_gt
    rw [h_cp] at h_gt ⊢
    by_cases h_a : a = i
    · -- a = i: log grew
      subst a
      rw [h_lastTerm_new] at h_gt
      -- entry.term > cp(b).term
      -- Use h_llcp on j: lastTerm(j) > cp(b).term → agreement between j and b
      have h_j_llcp := h_llcp j b (h_j_gt b h_gt)
      obtain ⟨h_cpidx_le_j, h_j_agree⟩ := h_j_llcp
      -- Key: show cp(b).index ≤ len(s.log i) + 1 = len(s'.log i)
      -- From h_cpetb: logTerm(b, p) ≤ cp(b).term for p ≤ cp(b).index, p ≤ len(log b)
      -- From h_j_agree: logTerm(j, p) = logTerm(b, p) for p ≤ cp(b).index
      -- So logTerm(j, p) ≤ cp(b).term for p ≤ cp(b).index
      -- But logTerm(j, len(i)+1) = entry.term > cp(b).term
      -- So cp(b).index < len(i)+1, i.e., cp(b).index ≤ len(i)
      have h_cpidx_le_i : (s.commitPoint b).index ≤ (s.log i).length := by
        by_contra h_contra
        push_neg at h_contra
        -- cp(b).index > len(s.log i), so cp(b).index ≥ len(s.log i) + 1
        have h_ge : (s.commitPoint b).index ≥ (s.log i).length + 1 := by omega
        have h_cp_b := h_cp_le_log b
        -- logTerm(j, len(i)+1) = entry.term > cp(b).term
        -- But logTerm(j, len(i)+1) = logTerm(b, len(i)+1) by h_j_agree
        have h_at : logTerm s j ((s.log i).length + 1) =
            logTerm s b ((s.log i).length + 1) :=
          h_j_agree _ h_ge (by omega)
        -- And logTerm(b, len(i)+1) ≤ cp(b).term by h_cpetb
        have h_le : logTerm s b ((s.log i).length + 1) ≤ (s.commitPoint b).term :=
          h_cpetb b _ h_ge (by omega)
        -- But logTerm(j, len(i)+1) = entry.term > cp(b).term
        rw [h_entry_eq] at h_at; omega
      constructor
      · -- cp(b).index ≤ len(s'.log i)
        rw [h_new_len]; omega
      · -- Agreement: logTerm s' i p = logTerm s' b p
        intro p h_p_cp h_p_log
        -- p ≤ cp(b).index ≤ len(s.log i): in unchanged prefix
        have h_p_old : p ≤ (s.log i).length := by omega
        rw [lt_old p h_p_old]
        -- logTerm(i, p) = logTerm(j, p) by prefix relationship
        rw [h_ij_match p h_p_old]
        -- logTerm(j, p) = logTerm(b, p) by h_j_agree
        by_cases h_b : b = i
        · -- b = i: logTerm s' b p = logTerm s' i p, use same rewrite
          rw [h_b]; rw [lt_old p h_p_old, h_ij_match p h_p_old]
        · rw [lt_ne b h_b]
          exact h_j_agree p h_p_cp (by
            have h_log_b : s'.log b = s.log b := by
              have := congr_fun h_log b; simp [h_b] at this; exact this
            rw [h_log_b] at h_p_log; exact h_p_log)
    · -- a ≠ i: log a unchanged
      have h_log_a : s'.log a = s.log a := by
        have := congr_fun h_log a; simp [h_a] at this; exact this
      have h_last_eq : lastTerm (s'.log a) = lastTerm (s.log a) := by
        unfold lastTerm getTerm; rw [h_log]; simp [h_a]
      rw [h_last_eq] at h_gt
      obtain ⟨h_len_a, h_agree⟩ := h_llcp a b h_gt
      constructor
      · -- cp(b).index ≤ len(s.log a) = len(s'.log a)
        rw [h_log_a]; exact h_len_a
      · intro p h_p_cp h_p_log
        rw [lt_ne a h_a]
        by_cases h_b : b = i
        · -- b = i: log b grew, but p ≤ cp(b).index ≤ len(s.log i)
          subst b
          have h_cp_i := h_cp_le_log i
          rw [lt_old p (by omega)]
          exact h_agree p h_p_cp (by omega)
        · rw [lt_ne b h_b]
          have h_log_b : s'.log b = s.log b := by
            have := congr_fun h_log b; simp [h_b] at this; exact this
          exact h_agree p h_p_cp (by rw [h_log_b] at h_p_log; exact h_p_log)
  -- 12. commitPointAgreement: log i grew, cp unchanged
  · -- Proof sketch: i's new log is a longer prefix of j's log. So logTerm s' i p
    -- = logTerm s j p for p in range. Then use h_llcp or h_cpa on (j, b).
    -- For a ≠ i: log a unchanged, reduce to old invariant.
    -- Helper: lastTerm(s'.log i) = entry.term
    have h_lastTerm_new : lastTerm (s'.log i) = entry.term := by
      have h_log_i : s'.log i = s.log i ++ [entry] := by rw [h_log]; simp
      rw [h_log_i, h_lastTerm_app]
    -- Helper: logTerm s' i p = logTerm s j p for p ≤ len(s.log i) + 1
    have h_new_prefix : ∀ p, p ≤ (s.log i).length + 1 →
        logTerm s' i p = logTerm s j p := by
      intro p hp
      rcases Nat.eq_or_lt_of_le hp with rfl | h_lt
      · -- p = len(s.log i) + 1: new entry matches j
        exact lt_new.trans h_entry_eq.symm
      · -- p ≤ len(s.log i): in old prefix
        rw [lt_old p (by omega), h_ij_match p (by omega)]
    -- Helper: cp(b).index ≤ len(s.log b) for all b
    have h_cp_le_log : ∀ b, (s.commitPoint b).index ≤ (s.log b).length := by
      intro b; rcases h_cwb b with h_lt | ⟨_, h_le⟩
      · exact (h_llcp b b h_lt).1
      · exact h_le
    -- Helper: lastTerm(s.log j) ≥ entry.term (by monotonicity)
    have h_j_last_ge : lastTerm (s.log j) ≥ entry.term := by
      have h1 := h_mono j ((s.log i).length + 1) ((s.log j).length) (by omega) (le_refl _)
      rw [h_entry_eq] at h1; exact h1
    -- Main proof
    intro a b h_lt h_len p h_p_cp h_p_log
    rw [h_cp] at h_p_cp h_lt h_len
    by_cases h_a : a = i
    · -- a = i: log grew, lastTerm(s'.log i) = entry.term
      subst a
      rw [h_lastTerm_new] at h_lt
      -- entry.term = cp(b).term
      have h_p_le : p ≤ (s.log i).length + 1 := by omega
      rw [h_new_prefix p h_p_le]
      -- Need: logTerm s j p = logTerm s' b p
      by_cases h_b : b = i
      · -- b = i: use h_new_prefix again
        subst b; rw [h_new_prefix p h_p_le]
      · -- b ≠ i: logTerm s' b p = logTerm s b p
        rw [lt_ne b h_b]
        -- Need: logTerm s j p = logTerm s b p
        -- lastTerm(s.log j) ≥ entry.term = cp(b).term and len(s.log j) ≥ cp(b).index
        have h_j_len : (s.log j).length ≥ (s.commitPoint b).index := by
          rw [h_new_len] at h_len; omega
        have h_p_log_s : p ≤ (s.log b).length := by
          have : s'.log b = s.log b := by
            have := congr_fun h_log b; simp [h_b] at this; exact this
          rw [this] at h_p_log; exact h_p_log
        rcases Nat.lt_or_ge (s.commitPoint b).term (lastTerm (s.log j)) with h_gt | h_le
        · -- lastTerm(s.log j) > cp(b).term: use h_llcp
          exact (h_llcp j b h_gt).2 p h_p_cp h_p_log_s
        · -- lastTerm(s.log j) = cp(b).term (since ≥ and ≤)
          have h_eq : lastTerm (s.log j) = (s.commitPoint b).term := by omega
          exact h_cpa j b h_eq h_j_len p h_p_cp h_p_log_s
    · -- a ≠ i: log a unchanged
      have h_log_a : s'.log a = s.log a := by
        have := congr_fun h_log a; simp [h_a] at this; exact this
      have h_last_eq : lastTerm (s'.log a) = lastTerm (s.log a) := by
        unfold lastTerm getTerm; rw [h_log]; simp [h_a]
      rw [h_last_eq] at h_lt; rw [h_log_a] at h_len
      by_cases h_b : b = i
      · -- b = i: log b grew, but p ≤ cp(i).index ≤ len(s.log i)
        subst b
        have h_cp_i := h_cp_le_log i
        rw [lt_ne a h_a, lt_old p (by omega)]
        exact h_cpa a i h_lt h_len p h_p_cp (by omega)
      · -- b ≠ i: both logs unchanged
        rw [lt_ne a h_a, lt_ne b h_b]
        have h_log_b : s'.log b = s.log b := by
          have := congr_fun h_log b; simp [h_b] at this; exact this
        rw [h_log_b] at h_p_log
        exact h_cpa a b h_lt h_len p h_p_cp h_p_log
  -- 13. leaderLastTermGeCommitPointTerm: state/cp unchanged, log i grew
  · intro ldr srv h_ldr
    rw [h_state] at h_ldr; rw [h_cp]
    by_cases h_eq : ldr = i
    · subst h_eq
      have h_log_ldr : s'.log ldr = s.log ldr ++ [entry] := by rw [h_log]; simp
      rw [h_log_ldr, h_lastTerm_app]
      exact le_trans (h_lgt ldr srv h_ldr) h_entry_ge
    · have h_log_ldr : s'.log ldr = s.log ldr := by rw [h_log]; simp [h_eq]
      rw [h_log_ldr]
      exact h_lgt ldr srv h_ldr
  -- 14. uniformLogEntriesInTerm: i's log grew by entry from j
  · -- i's new log is old_log_i ++ [entry_from_j]. Since i's old log was a prefix
    -- of j's log (logMatching via h_match), the new log of i is a longer prefix.
    -- For all positions in the new log: logTerm s' i p = logTerm s j p.
    -- This lets us reduce every case involving i to the old invariant on j.
    -- Key: logTerm s' i p = logTerm s j p for all p ≤ new length
    have lt_i_j : ∀ p, p ≤ (s.log i).length + 1 →
        logTerm s' i p = logTerm s j p := by
      intro p hp
      rcases Nat.lt_or_ge p ((s.log i).length + 1) with h_sm | h_bg
      · rw [lt_old p (by omega), h_ij_match p (by omega)]
      · have : p = (s.log i).length + 1 := by omega
        subst this; exact lt_new.trans h_entry_eq.symm
    intro a' b' p q hp hpa hq hqb h_eq' h_ne' h_first'
    by_cases h_a : a' = i <;> by_cases h_b : b' = i
    · -- a' = i, b' = i: both are new log of i; reduce to j,j via prefix
      subst h_a; subst h_b
      exact h_ulet j j p q hp (by omega) hq (by omega)
        (by rw [← lt_i_j p (by omega), ← lt_i_j q (by omega)]; exact h_eq')
        (by rw [← lt_i_j p (by omega)]; exact h_ne')
        (fun k hk1 hkp => by
          rw [← lt_i_j k (by omega), ← lt_i_j p (by omega)]
          exact h_first' k hk1 hkp)
    · -- a' = i, b' ≠ i: i's new log is prefix of j; b unchanged
      subst h_a
      exact h_ulet j b' p q hp (by omega) hq
        (by rw [h_len_ne b' h_b] at hqb; exact hqb)
        (by rw [← lt_i_j p (by omega), ← lt_ne b' h_b q]; exact h_eq')
        (by rw [← lt_i_j p (by omega)]; exact h_ne')
        (fun k hk1 hkp => by
          rw [← lt_i_j k (by omega), ← lt_i_j p (by omega)]
          exact h_first' k hk1 hkp)
    · -- a' ≠ i, b' = i: a unchanged; i's new log is prefix of j
      subst h_b
      exact h_ulet a' j p q hp
        (by rw [h_len_ne a' h_a] at hpa; exact hpa) hq (by omega)
        (by rw [← lt_ne a' h_a p, ← lt_i_j q (by omega)]; exact h_eq')
        (by rw [← lt_ne a' h_a p]; exact h_ne')
        (fun k hk1 hkp => by
          rw [← lt_ne a' h_a k, ← lt_ne a' h_a p]
          exact h_first' k hk1 hkp)
    · -- a' ≠ i, b' ≠ i: both logs unchanged
      exact h_ulet a' b' p q hp
        (by rw [h_len_ne a' h_a] at hpa; exact hpa) hq
        (by rw [h_len_ne b' h_b] at hqb; exact hqb)
        (by rw [← lt_ne a' h_a p, ← lt_ne b' h_b q]; exact h_eq')
        (by rw [← lt_ne a' h_a p]; exact h_ne')
        (fun k hk1 hkp => by
          rw [← lt_ne a' h_a k, ← lt_ne a' h_a p]
          exact h_first' k hk1 hkp)
  -- 15. commitPointWeaklyBelowLogTip: cp unchanged, log i grew
  · intro srv
    rw [h_cp]
    by_cases h_eq : srv = i
    · subst h_eq
      have h_log_srv : s'.log srv = s.log srv ++ [entry] := by rw [h_log]; simp
      rw [h_log_srv, h_lastTerm_app,
        show (s.log srv ++ [entry]).length = (s.log srv).length + 1 from
          by rw [List.length_append, List.length_singleton]]
      rcases h_cwb srv with h_lt | ⟨h_eq_t, h_le⟩
      · left; omega
      · rcases Nat.lt_or_ge (s.commitPoint srv).term entry.term with h1 | h2
        · left; exact h1
        · right; exact ⟨by omega, by omega⟩
    · have : s'.log srv = s.log srv := by rw [h_log]; simp [h_eq]
      rw [this]; exact h_cwb srv
  -- 16. commitPointEntryTermsBounded: cp unchanged, log i grew
  · -- For b ≠ i: log and cp unchanged, use h_cpetb directly.
    -- For b = i: cp(i) unchanged, positions ≤ cp(i).index are in unchanged prefix.
    intro b p hp hpl
    rw [h_cp] at hp
    by_cases h_b : b = i
    · subst h_b
      -- cp(b).index ≤ len(s.log b) from h_cwb
      have h_cp_le : (s.commitPoint b).index ≤ (s.log b).length := by
        rcases h_cwb b with h_lt | ⟨_, h_le⟩
        · exact (h_llcp b b h_lt).1
        · exact h_le
      have hpl_old : p ≤ (s.log b).length := by omega
      rw [lt_old p hpl_old, h_cp]; exact h_cpetb b p hp hpl_old
    · rw [lt_ne b h_b p, h_cp]; exact h_cpetb b p hp (by rwa [h_len_ne b h_b] at hpl)
  -- 17. rollbackSafeCommitPoint: cp unchanged, log i grew (append)
  --   For srv = i: dropLast of appended log = original log, use h_cwb.
  --   For srv ≠ i: find canRollbackOplog witness in s (j works via logMatching).
  · intro srv ⟨k, h_can⟩
    rw [h_cp]
    by_cases h_srv_i : srv = i
    · -- srv = i: (s'.log i).dropLast = s.log i
      subst h_srv_i
      have h_log_srv : s'.log srv = s.log srv ++ [entry] := by rw [h_log]; simp
      rw [h_log_srv]
      simp only [List.dropLast_concat]
      -- Goal: (s.commitPoint srv).term ≤ lastTerm (s.log srv)
      rcases h_cwb srv with h_lt | ⟨h_eq_t, _⟩
      · exact Nat.le_of_lt h_lt
      · exact Nat.le_of_eq h_eq_t
    · -- srv ≠ i: logs unchanged
      have h_log_srv : s'.log srv = s.log srv := by rw [h_log]; simp [h_srv_i]
      rw [h_log_srv]
      -- Find witness for canRollbackOplog srv ? s
      by_cases h_k_i : k = i
      · -- k = i: use j as witness
        have h_log_i : s'.log i = s.log i ++ [entry] := by rw [h_log]; simp
        -- From canRollbackOplog: lastTerm(s.log srv) < lastTerm(s'.log i) = entry.term
        unfold canRollbackOplog at h_can
        rw [h_k_i, h_log_srv, h_log_i] at h_can
        obtain ⟨h_pos, h_lt_last, h_div⟩ := h_can
        rw [h_lastTerm_app] at h_lt_last
        -- entry.term ≤ lastTerm(s.log j) by monotonicity
        have h_entry_le_j : entry.term ≤ lastTerm (s.log j) := by
          have := h_mono j ((s.log i).length + 1) (s.log j).length (by omega) (le_refl _)
          rw [h_entry_eq] at this; exact this
        have h_lt_j : lastTerm (s.log srv) < lastTerm (s.log j) := by omega
        -- Third condition: by_contra, use logMatching to derive contradiction
        have h_third : (s.log srv).length > (s.log j).length
            ∨ ((s.log srv).length ≤ (s.log j).length
              ∧ lastTerm (s.log srv) ≠ logTerm s j (s.log srv).length) := by
          by_contra h_neg
          push_neg at h_neg
          obtain ⟨h_le_j, h_eq_term⟩ := h_neg
          -- logTerm s srv (s.log srv).length = logTerm s j (s.log srv).length
          -- by logMatching, srv and j agree on all positions ≤ (s.log srv).length
          have h_srv_j_match : ∀ q, q ≤ (s.log srv).length →
              logTerm s srv q = logTerm s j q :=
            h_lm srv j (s.log srv).length (le_refl _) h_le_j (h_eq_term h_le_j)
          -- i and j agree on all positions ≤ (s.log i).length (from h_match)
          -- From canRollbackOplog third condition in s'
          rw [List.length_append, List.length_singleton] at h_div
          rcases h_div with h_div_a | ⟨h_div_le, h_div_ne⟩
          · -- (s.log srv).length > (s.log i).length + 1
            -- srv has entries at position (s.log i).length + 1, and
            -- logTerm s srv ((s.log i).length + 1)
            --   = logTerm s j ((s.log i).length + 1) = entry.term
            -- By monotonicity: lastTerm(s.log srv) ≥ entry.term, contradicts h_lt_last
            have h_eq_entry : logTerm s srv ((s.log i).length + 1) = entry.term := by
              rw [h_srv_j_match ((s.log i).length + 1) (by omega), h_entry_eq]
            have h_mono_srv : entry.term ≤ lastTerm (s.log srv) := by
              have := h_mono srv ((s.log i).length + 1) (s.log srv).length (by omega) (le_refl _)
              rw [h_eq_entry] at this; exact this
            omega
          · -- (s.log srv).length ≤ (s.log i).length + 1
            -- logTerm s' i (s.log srv).length: need to show it equals lastTerm(s.log srv)
            -- for contradiction with h_div_ne
            rcases Nat.lt_or_ge (s.log srv).length ((s.log i).length + 1) with h_sm | h_bg
            · -- (s.log srv).length ≤ (s.log i).length
              have h_pos_le : (s.log srv).length ≤ (s.log i).length := by omega
              -- lastTerm(srv) = logTerm s i (srv.length) via j
              have h_srv_i_eq :
                  logTerm s srv (s.log srv).length = logTerm s i (s.log srv).length := by
                rw [h_srv_j_match _ (le_refl _), ← h_ij_match _ h_pos_le]
              -- logTerm s' i (srv.length) = logTerm s i (srv.length) (in unchanged prefix)
              have h_s'_i_eq :
                  logTerm s' i (s.log srv).length = logTerm s i (s.log srv).length :=
                lt_old _ h_pos_le
              -- So lastTerm(srv) = logTerm s' i (srv.length), contradicts h_div_ne
              have : lastTerm (s.log srv) = logTerm s' i (s.log srv).length := by
                rw [h_s'_i_eq]; exact h_srv_i_eq
              exact absurd this h_div_ne
            · -- (s.log srv).length = (s.log i).length + 1
              have h_eq_len : (s.log srv).length = (s.log i).length + 1 := by omega
              -- lastTerm(srv) = logTerm s j (srv.length) = entry.term, contradicts h_lt_last
              have h_eq := h_eq_term h_le_j
              rw [h_eq_len] at h_eq
              -- h_eq : lastTerm(srv) = logTerm s j ((s.log i).length + 1) = entry.term
              rw [h_entry_eq] at h_eq
              -- lastTerm(srv) = entry.term contradicts lastTerm(srv) < entry.term
              omega
        exact h_rsc srv ⟨j, h_pos, h_lt_j, h_third⟩
      · -- k ≠ i: both logs unchanged, transfer directly
        have h_log_k : s'.log k = s.log k := by rw [h_log]; simp [h_k_i]
        have h_can_s : canRollbackOplog srv k s := by
          unfold canRollbackOplog logTerm getTerm at h_can ⊢
          rw [h_log_srv, h_log_k] at h_can
          exact h_can
        exact h_rsc srv ⟨k, h_can_s⟩
  -- 18. rollbackWithSyncSourceImpliesCommitPointBelowTip
  -- Proof: case split on a = i and b = i. appendOplog only changes server i's log
  -- (appends entry). We transfer appendOplogEnabled and canRollbackOplog between s' and s.
  · intro a b h_aoe h_can_ex h_below
    rw [h_cp] at h_below
    by_cases h_a : a = i <;> by_cases h_b : b = i
    · -- Case a = i, b = i: appendOplogEnabled i i s' requires len < len, impossible
      subst h_a; subst h_b
      exact Nat.lt_irrefl _ h_aoe.1
    · -- Case a = i, b ≠ i: a's log grew (appended entry), b's log unchanged
      -- Strategy: same as rollbackOplog L2747. Take k₀ from h_can_ex.
      -- inr: entry.term = cp.term < lastTerm(k₀). h_llcp gives agreement at len(a)+1.
      -- inl: monotonicity forces cp.index > len(a)+1. Sub-case on lastTerm(k₀) vs cp.term.
      --   lastTerm(k₀) > cp.term: same as inr.
      --   lastTerm(k₀) ≤ cp.term: same blocker as rollbackOplog L2790.
      subst h_a
      unfold appendOplogEnabled at h_aoe
      rw [h_new_len, h_len_ne b h_b] at h_aoe
      obtain ⟨h_aoe_len, h_aoe_match⟩ := h_aoe
      have h_log_a' : s'.log a = s.log a ++ [entry] := by
        have := congr_fun h_log a; simp at this; exact this
      rw [h_log_a', h_lastTerm_app] at h_aoe_match
      rw [lt_ne b h_b] at h_aoe_match
      -- h_aoe_match : entry.term = logTerm s b ((s.log a).length + 1)
      rw [h_log_a', h_lastTerm_app,
          show (s.log a ++ [entry]).length = (s.log a).length + 1 from
            by rw [List.length_append, List.length_singleton]] at h_below
      -- h_below : entry.term < cp(b).term ∨ (entry.term = cp(b).term ∧ len(a)+1 ≤ cp.index)
      have h_cp_le_b : (s.commitPoint b).index ≤ (s.log b).length := by
        rcases h_cwb b with h_lt_cwb | ⟨_, h_le_cwb⟩
        · exact (h_llcp b b h_lt_cwb).1
        · exact h_le_cwb
      have h_lt_cp : logTerm s b (s.commitPoint b).index = (s.commitPoint b).term :=
        logTerm_at_commitPoint_eq_term s b h_cpbq h_llcp h_cpa h_cp_le_b
      obtain ⟨k₀, h_can_k₀⟩ := h_can_ex
      have h_k₀_ne : k₀ ≠ a := by
        intro heq; subst heq
        exact absurd h_can_k₀.2.1 (lt_irrefl _)
      have h_lt_k₀ : entry.term < lastTerm (s.log k₀) := by
        have := h_can_k₀.2.1
        rw [h_log_a', h_lastTerm_app,
            show s'.log k₀ = s.log k₀ from by
              have := congr_fun h_log k₀; simp [h_k₀_ne] at this; exact this] at this
        exact this
      rcases h_below with h_lt | ⟨h_eq, h_le⟩
      · -- inl: entry.term < cp(b).term
        -- Monotonicity forces cp.index > len(a)+1
        have h_cp_gt : (s.log a).length + 1 < (s.commitPoint b).index := by
          by_contra h; push_neg at h
          have h_m := h_mono b _ _ h (by omega : (s.log a).length + 1 ≤ (s.log b).length)
          rw [h_lt_cp, ← h_aoe_match] at h_m; omega
        rcases Nat.lt_or_ge (s.commitPoint b).term (lastTerm (s.log k₀)) with h_k₀_gt | h_k₀_le
        · obtain ⟨h_cp_le_k₀, h_agree_k₀⟩ := h_llcp k₀ b h_k₀_gt
          have h_k₀_match : logTerm s k₀ ((s.log a).length + 1) = entry.term :=
            (h_agree_k₀ _ (by omega) (by omega)).trans h_aoe_match.symm
          rcases h_can_k₀.2.2 with h_gt | ⟨_, h_ne⟩
          · rw [h_new_len, h_len_ne k₀ h_k₀_ne] at h_gt; omega
          · rw [h_new_len, lt_ne k₀ h_k₀_ne, h_log_a', h_lastTerm_app] at h_ne
            exact h_ne h_k₀_match.symm
        · -- lastTerm(k₀) ≤ cp(b).term: same blocker as rollbackOplog L2790
          -- STUCK: not provable with current invariants.
          --
          -- Counter-example (5 servers, quorum = 3, gCT = 5, all Followers):
          --   a: log = [],           cp = {0, 0}
          --   b: log = [1, 5, 5, 5], cp = {5, 3}
          --   k₀: log = [4],         cp = {0, 0}
          --   q1: log = [1, 5, 5, 5], cp = {0, 0}
          --   q2: log = [1, 5, 5, 5], cp = {0, 0}
          -- All 18 invariants hold in s (checked exhaustively).
          -- Transition: appendOplog a q1 — a appends ⟨1⟩, giving s'.log a = [1].
          -- In s': appendOplogEnabled a b (1<4, lastTerm=1=logTerm(b,1)),
          --   canRollbackOplog a k₀ (len=1>0, 1<4, 1≤1 ∧ 1≠4),
          --   entry.term=1 < 5=cp(b).term, lastTerm(k₀)=4 ≤ 5=cp(b).term.
          -- So the goal ¬(1<5 ∨ ...) = False. Invariant 19 violated in s'.
          --
          -- Root cause: canRollbackOplog a k₀ is *freshly created* by the
          -- append (a had empty log in s, so canRollbackOplog a k s fails
          -- for all k due to len(a)=0). This means h_rwss (inv 18 in s)
          -- cannot be applied for (a, b) — its precondition ∃k, canRollbackOplog
          -- a k s is unsatisfiable. Meanwhile, no other invariant connects k₀
          -- to cp(b) when lastTerm(k₀) ≤ cp(b).term: logsLaterThanCommitPoint
          -- needs >, commitPointAgreement needs =, and logMatching can't link
          -- k₀ to b (different terms at position 1).
          --
          -- Potential fix: a new invariant constraining canRollbackOplog
          -- witnesses relative to commit points, e.g.:
          --   ∀ a k b, canRollbackOplog a k s →
          --     lastTerm(k) ≤ cp(b).term →
          --     cp(b).index ≤ len(a)
          -- or equivalently, ensuring that a divergent log (k₀) with
          -- lastTerm(k₀) ≤ cp(b).term cannot coexist with cp(b).index
          -- beyond the rollback-target's log length. This would also
          -- close the identical sorry at rollbackOplog (L2820).
          sorry
      · -- inr: entry.term = cp(b).term ∧ len(a)+1 ≤ cp.index
        -- h_lt_k₀ + h_eq give lastTerm(k₀) > cp(b).term directly
        have h_k₀_gt : (s.commitPoint b).term < lastTerm (s.log k₀) := h_eq ▸ h_lt_k₀
        obtain ⟨h_cp_le_k₀, h_agree_k₀⟩ := h_llcp k₀ b h_k₀_gt
        have h_k₀_match : logTerm s k₀ ((s.log a).length + 1) = entry.term :=
          (h_agree_k₀ _ (by omega) (by omega)).trans h_aoe_match.symm
        rcases h_can_k₀.2.2 with h_gt | ⟨_, h_ne⟩
        · rw [h_new_len, h_len_ne k₀ h_k₀_ne] at h_gt; omega
        · rw [h_new_len, lt_ne k₀ h_k₀_ne, h_log_a', h_lastTerm_app] at h_ne
          exact h_ne h_k₀_match.symm
    · -- Case a ≠ i, b = i: a's log unchanged, b's log grew
      -- appendOplogEnabled a i s' means len(a) < len(i)+1 and lastTerm(a) = logTerm s' i len(a)
      -- Two subcases: len(a) < len(i) (transfer to appendOplogEnabled a i s) or
      -- len(a) = len(i) (use j as appendOplogEnabled witness instead)
      rw [h_b] at h_aoe h_below
      have h_log_a : s'.log a = s.log a := by
        have := congr_fun h_log a; simp only [Function.update_apply, if_neg h_a] at this; exact this
      unfold appendOplogEnabled at h_aoe
      rw [h_log_a, h_new_len] at h_aoe
      obtain ⟨h_aoe_len, h_aoe_match⟩ := h_aoe
      rw [h_log_a] at h_below
      -- Transfer canRollbackOplog from s' to s
      have h_can_s : ∃ k, canRollbackOplog a k s := by
        obtain ⟨k, hk⟩ := h_can_ex
        by_cases h_k : k = i
        · -- k = i: use j as witness (same pattern as a≠i,b≠i,k=i case below)
          unfold canRollbackOplog at hk
          have h_log_k' : s'.log k = s.log i ++ [entry] := by
            rw [h_k]; have := congr_fun h_log i; simp at this; exact this
          rw [h_log_a, h_log_k'] at hk
          obtain ⟨h_pos', h_lt', h_third'⟩ := hk
          rw [h_lastTerm_app] at h_lt'
          have h_entry_le_j : entry.term ≤ lastTerm (s.log j) := by
            have := h_mono j ((s.log i).length + 1) (s.log j).length (by omega) (le_refl _)
            rw [h_entry_eq] at this; exact this
          have h_lt_j : lastTerm (s.log a) < lastTerm (s.log j) := by omega
          have h_third_j : (s.log a).length > (s.log j).length
              ∨ ((s.log a).length ≤ (s.log j).length
                ∧ lastTerm (s.log a) ≠ logTerm s j (s.log a).length) := by
            by_contra h_neg
            push_neg at h_neg
            obtain ⟨h_le_j, h_eq_term⟩ := h_neg
            have h_a_j_match : ∀ q, q ≤ (s.log a).length →
                logTerm s a q = logTerm s j q :=
              h_lm a j (s.log a).length (le_refl _) h_le_j (h_eq_term h_le_j)
            rw [List.length_append, List.length_singleton] at h_third'
            rcases h_third' with h_div_a | ⟨h_div_le, h_div_ne⟩
            · have h_eq_entry : logTerm s a ((s.log i).length + 1) = entry.term := by
                rw [h_a_j_match ((s.log i).length + 1) (by omega), h_entry_eq]
              have h_mono_a : entry.term ≤ lastTerm (s.log a) := by
                have := h_mono a ((s.log i).length + 1) (s.log a).length (by omega) (le_refl _)
                rw [h_eq_entry] at this; exact this
              omega
            · rw [h_k] at h_div_ne
              rcases Nat.lt_or_ge (s.log a).length ((s.log i).length + 1) with h_sm | h_bg
              · have h_pos_le : (s.log a).length ≤ (s.log i).length := by omega
                have h_a_i_eq :
                    logTerm s a (s.log a).length = logTerm s i (s.log a).length := by
                  rw [h_a_j_match _ (le_refl _), ← h_ij_match _ h_pos_le]
                have h_s'_i_eq :
                    logTerm s' i (s.log a).length = logTerm s i (s.log a).length := by
                  exact lt_old _ h_pos_le
                have : lastTerm (s.log a) = logTerm s' i (s.log a).length := by
                  rw [h_s'_i_eq]; exact h_a_i_eq
                exact absurd this h_div_ne
              · have h_eq_len : (s.log a).length = (s.log i).length + 1 := by omega
                have h_eq := h_eq_term h_le_j
                rw [h_eq_len] at h_eq
                rw [h_entry_eq] at h_eq
                omega
          exact ⟨j, h_pos', h_lt_j, h_third_j⟩
        · exact ⟨k, by
            unfold canRollbackOplog at hk ⊢
            rw [h_log_a, h_log] at hk; simp [h_k, lt_ne k h_k] at hk; exact hk⟩
      -- Case split: len(a) < len(i) vs len(a) = len(i)
      rcases Nat.lt_or_ge (s.log a).length (s.log i).length with h_lt_i | h_ge_i
      · -- len(a) < len(i): logTerm s' i len(a) = logTerm s i len(a) (in old prefix)
        have h_le_old : (s.log a).length ≤ (s.log i).length := Nat.le_of_lt h_lt_i
        have h_aoe_match_s : lastTerm (s.log a) = logTerm s i (s.log a).length := by
          rw [lt_old _ h_le_old] at h_aoe_match; exact h_aoe_match
        exact h_rwss a i ⟨h_lt_i, h_aoe_match_s⟩ h_can_s h_below
      · -- len(a) ≥ len(i): len(a) = len(i) (since len(a) < len(i)+1)
        have h_eq_len : (s.log a).length = (s.log i).length := by omega
        -- lastTerm(a) = logTerm s' i len(a) = logTerm s i len(i) = lastTerm(i)
        -- (position len(a) = len(i) is within old prefix)
        have h_lt_eq : lastTerm (s.log a) = lastTerm (s.log i) := by
          have h1 := h_aoe_match
          rw [h_eq_len] at h1
          rw [h1, lt_old _ (le_refl _)]; unfold logTerm lastTerm; rfl
        -- Transfer canRollbackOplog from a to i (same len, same lastTerm)
        obtain ⟨k₀, h_can_k₀⟩ := h_can_s
        have h_can_i : ∃ k, canRollbackOplog i k s := by
          obtain ⟨h1, h2, h3⟩ := h_can_k₀
          refine ⟨k₀, by omega, by omega, ?_⟩
          rcases h3 with h3l | ⟨h3a, h3b⟩
          · exact Or.inl (by omega)
          · exact Or.inr ⟨by omega, by rw [h_eq_len, h_lt_eq] at h3b; exact h3b⟩
        -- h_nrbcp i: canRollbackOplog i k s AND commit point at/above tip → False
        -- h_cwb i eliminates most of h_below; remaining case gives len(i) ≤ cp.index
        apply h_nrbcp i
        unfold rollbackBeforeCommitPoint
        refine ⟨h_can_i, ?_⟩
        rcases h_cwb i with h_lt_cwb | ⟨h_eq_cwb, h_le_cwb⟩
        · -- cp.term < lastTerm(i) = lastTerm(a): contradicts both disjuncts of h_below
          rcases h_below with h1 | ⟨h2, _⟩ <;> omega
        · -- cp.term = lastTerm(i), cp.index ≤ len(i)
          -- h_below gives lastTerm(a) = cp.term ∧ len(a) ≤ cp.index (first disjunct impossible)
          rcases h_below with h1 | ⟨_, h_le_idx⟩
          · omega
          · exact Or.inr ⟨h_eq_cwb.symm, by omega⟩
    · -- Case a ≠ i, b ≠ i: both logs unchanged, transfer directly to s
      have h_aoe_s : appendOplogEnabled a b s := by
        unfold appendOplogEnabled at h_aoe ⊢
        rw [h_log] at h_aoe; simp [h_a, h_b, lt_ne b h_b] at h_aoe; exact h_aoe
      have h_can_s : ∃ k, canRollbackOplog a k s := by
        obtain ⟨k, hk⟩ := h_can_ex
        by_cases h_k : k = i
        · -- k = i: s'.log i = s.log i ++ [entry]. Use j as witness instead.
          unfold canRollbackOplog at hk
          have h_log_a' : s'.log a = s.log a := by
            have := congr_fun h_log a; simp only [Function.update_apply, if_neg h_a] at this
            exact this
          have h_log_k' : s'.log k = s.log i ++ [entry] := by
            rw [h_k]; have := congr_fun h_log i; simp at this; exact this
          rw [h_log_a', h_log_k'] at hk
          obtain ⟨h_pos', h_lt', h_third'⟩ := hk
          rw [h_lastTerm_app] at h_lt'
          -- lastTerm(a) < entry.term ≤ lastTerm(j) by monotonicity on j
          have h_entry_le_j : entry.term ≤ lastTerm (s.log j) := by
            have := h_mono j ((s.log i).length + 1) (s.log j).length (by omega) (le_refl _)
            rw [h_entry_eq] at this; exact this
          have h_lt_j : lastTerm (s.log a) < lastTerm (s.log j) := by omega
          -- Third condition for j: by_contra + logMatching argument
          have h_third_j : (s.log a).length > (s.log j).length
              ∨ ((s.log a).length ≤ (s.log j).length
                ∧ lastTerm (s.log a) ≠ logTerm s j (s.log a).length) := by
            by_contra h_neg
            push_neg at h_neg
            obtain ⟨h_le_j, h_eq_term⟩ := h_neg
            -- a and j agree on all positions ≤ (s.log a).length by logMatching
            have h_a_j_match : ∀ q, q ≤ (s.log a).length →
                logTerm s a q = logTerm s j q :=
              h_lm a j (s.log a).length (le_refl _) h_le_j (h_eq_term h_le_j)
            -- Case split on h_third' (canRollbackOplog third condition in s')
            rw [List.length_append, List.length_singleton] at h_third'
            rcases h_third' with h_div_a | ⟨h_div_le, h_div_ne⟩
            · -- len(a) > len(i) + 1: a has entry at pos len(i)+1
              -- logTerm s a (len(i)+1) = logTerm s j (len(i)+1) = entry.term
              -- By monotonicity: entry.term ≤ lastTerm(a), contradicts h_lt'
              have h_eq_entry : logTerm s a ((s.log i).length + 1) = entry.term := by
                rw [h_a_j_match ((s.log i).length + 1) (by omega), h_entry_eq]
              have h_mono_a : entry.term ≤ lastTerm (s.log a) := by
                have := h_mono a ((s.log i).length + 1) (s.log a).length (by omega) (le_refl _)
                rw [h_eq_entry] at this; exact this
              omega
            · -- len(a) ≤ len(i) + 1
              -- h_div_ne : lastTerm(a) ≠ logTerm s' k (s.log a).length
              rw [h_k] at h_div_ne
              rcases Nat.lt_or_ge (s.log a).length ((s.log i).length + 1) with h_sm | h_bg
              · -- len(a) ≤ len(i): logTerm s' i len(a) = logTerm s i len(a) (in old prefix)
                have h_pos_le : (s.log a).length ≤ (s.log i).length := by omega
                have h_a_i_eq :
                    logTerm s a (s.log a).length = logTerm s i (s.log a).length := by
                  rw [h_a_j_match _ (le_refl _), ← h_ij_match _ h_pos_le]
                have h_s'_i_eq :
                    logTerm s' i (s.log a).length = logTerm s i (s.log a).length := by
                  exact lt_old _ h_pos_le
                have : lastTerm (s.log a) = logTerm s' i (s.log a).length := by
                  rw [h_s'_i_eq]; exact h_a_i_eq
                exact absurd this h_div_ne
              · -- len(a) = len(i) + 1
                have h_eq_len : (s.log a).length = (s.log i).length + 1 := by omega
                have h_eq := h_eq_term h_le_j
                rw [h_eq_len] at h_eq
                rw [h_entry_eq] at h_eq
                omega
          exact ⟨j, h_pos', h_lt_j, h_third_j⟩
        · exact ⟨k, by
            unfold canRollbackOplog at hk ⊢
            rw [h_log] at hk; simp [h_a, h_k, lt_ne k h_k] at hk; exact hk⟩
      have h_log_a : s'.log a = s.log a := by rw [h_log]; simp [h_a]
      rw [h_log_a] at h_below
      exact h_rwss a b h_aoe_s h_can_s h_below

lemma raftInvariant_rollbackOplog (i j : Server) (s s' : RaftState Server) :
    raftInvariant s → rollbackOplog i j s s' → raftInvariant s' := by
  -- rollbackOplog changes: log (drops last entry from server i)
  -- Unchanged: globalCurrentTerm, state, commitPoint
  -- The shortened log is a sublist of the original, so termsAreBounded is preserved.
  intro ⟨h_nrc, h_nrbcp, h_tb, h_cpb, h_mono, h_ctml, h_lu, h_lm,
         h_lccp, h_cpbq, h_llcp, h_cpa, h_lgt, h_ulet, h_cwb, h_cpetb, h_rsc, h_rwss⟩
    ⟨h_can, h_log, h_term, h_state, h_cp⟩
  have h_tb' : termsAreBounded s' := by
    intro srv e he
    rw [h_log] at he
    simp only [Function.update_apply] at he
    split_ifs at he
    · rw [h_term]; exact h_tb _ e (List.mem_of_mem_dropLast he)
    · rw [h_term]; exact h_tb srv e he
  -- Shared helpers visible to all 18 sub-goals.
  -- Basic log equalities derived from h_log.
  have h_log_i : s'.log i = (s.log i).dropLast := by
    have := congr_fun h_log i; simp at this; exact this
  have h_log_ne : ∀ k, k ≠ i → s'.log k = s.log k := fun k hk => by
    have := congr_fun h_log k; simp [hk] at this; exact this
  -- Log length strictly positive at i (from canRollbackOplog precondition).
  have h_pos : (s.log i).length > 0 := h_can.1
  -- Length facts after the update.
  have h_len_i : (s'.log i).length = (s.log i).dropLast.length :=
    length_update_self_dropLast h_log
  have h_len_ne : ∀ srv, srv ≠ i → (s'.log srv).length = (s.log srv).length :=
    fun srv h => length_update_ne h_log h
  -- lastTerm of the shortened log equals the logTerm at the drop boundary.
  have h_lastTerm_drop_eq : lastTerm (s.log i).dropLast =
      logTerm s i (s.log i).dropLast.length := by
    unfold lastTerm logTerm getTerm
    split
    · rfl
    · next h_ne =>
      congr 1
      rw [List.getElem?_dropLast]
      rw [if_pos (by rw [List.length_dropLast] at h_ne ⊢; omega)]
  -- The shortened log's lastTerm is ≤ the original lastTerm (by monotonicity).
  have h_mono_drop : lastTerm (s.log i).dropLast ≤ lastTerm (s.log i) := by
    rw [h_lastTerm_drop_eq]
    exact h_mono i _ _ (by rw [List.length_dropLast]; omega) (le_refl _)
  -- Every server's commit point index is within its log length.
  -- Proof: commitPointWeaklyBelowLogTip gives cpTerm < lastTerm (use h_llcp) or
  -- cpTerm = lastTerm ∧ cpIdx ≤ logLen (direct).
  have h_cp_le_srv : ∀ srv, (s.commitPoint srv).index ≤ (s.log srv).length := fun srv => by
    rcases h_cwb srv with h_lt | ⟨_, h_le⟩
    · exact (h_llcp srv srv h_lt).1
    · exact h_le
  -- logTerm translation helpers: s' agrees with s on all logTerm queries that
  -- don't touch the dropped entry.
  have lt_ne : ∀ srv, srv ≠ i → ∀ idx, logTerm s' srv idx = logTerm s srv idx :=
    fun srv h idx => logTerm_update_ne h_log h idx
  have lt_drop : ∀ idx, idx ≤ (s.log i).dropLast.length →
      logTerm s' i idx = logTerm s i idx :=
    fun idx h => logTerm_update_self_dropLast h_log h
  have h_lastTerm_i : lastTerm (s'.log i) = lastTerm (s.log i).dropLast := by
    unfold lastTerm; rw [h_log_i]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- 1. neverRollbackCommitted: follows from termsAreBounded
  · exact neverRollbackCommitted_of_termsAreBounded h_tb'
  -- 2. neverRollbackBeforeCommitPoint
  -- Proof sketch:
  -- For srv = i: h_rsc gives cp.term ≤ lastTerm(dropLast), killing the first branch.
  --   For the second branch, h_llcp shows: any k with lastTerm(s.log k) > cp.term must
  --   have logTerm s k (dropLast.length) = logTerm s i (dropLast.length) = lastTerm(dropLast),
  --   so canRollbackOplog i k s' third condition fails. Contradiction.
  -- For srv ≠ i: logs/cp unchanged for srv, so the commit-point condition is the same
  --   as in s. We transfer canRollbackOplog srv k s' → canRollbackOplog srv ? s, giving
  --   rollbackBeforeCommitPoint s srv, contradicting h_nrbcp.
  · intro srv h_rbcp'
    unfold rollbackBeforeCommitPoint at h_rbcp'
    obtain ⟨⟨k, h_can'⟩, h_below'⟩ := h_rbcp'
    obtain ⟨h_pos', h_lt', h_third'⟩ := h_can'
    by_cases h_srv_i : srv = i
    · -- Case srv = i: log shortened to dropLast, cp unchanged
      -- Rewrite srv→i in s' hypotheses using h_srv_i : srv = i
      have h_log_srv_eq : s'.log srv = (s.log i).dropLast := h_srv_i ▸ h_log_i
      have h_cp_srv_eq : s'.commitPoint srv = s.commitPoint i := by
        rw [congr_fun h_cp srv, h_srv_i]
      rw [h_log_srv_eq] at h_pos' h_lt' h_third'
      rw [h_log_srv_eq, h_cp_srv_eq] at h_below'
      -- h_rsc gives cp.term ≤ lastTerm(dropLast), ruling out first branch
      have h_rsc_i := h_rsc i ⟨j, h_can⟩
      rcases h_below' with h_lt_cp | ⟨h_eq_cp, h_len_cp⟩
      · exact absurd h_rsc_i (not_le.mpr h_lt_cp)
      · -- Equality branch. k ≠ i (strict lt would be reflexive otherwise)
        have h_k_ne : k ≠ i := by
          intro h_eq
          rw [h_eq, h_log_i] at h_lt'
          exact absurd h_lt' (lt_irrefl _)
        rw [h_log_ne k h_k_ne] at h_lt' h_third'
        -- lastTerm(s.log k) > cp.term
        have h_gt_cp : lastTerm (s.log k) > (s.commitPoint i).term := by
          rw [← h_eq_cp]; exact h_lt'
        obtain ⟨h_cpidx_k, h_agree⟩ := h_llcp k i h_gt_cp
        -- logTerm s k (dropLast.length) = lastTerm(dropLast) via h_llcp
        have h_agree_drop :
            logTerm s k (s.log i).dropLast.length = lastTerm (s.log i).dropLast := by
          rw [h_lastTerm_drop_eq]
          exact h_agree _ h_len_cp (by rw [List.length_dropLast]; omega)
        -- Third condition of canRollbackOplog srv k s' fails
        rcases h_third' with h_gt_len | ⟨h_le_len, h_ne⟩
        · -- len(dropLast) > len(s.log k): contradicts cp.idx ≤ len(k) ≥ len(dropLast)
          exact absurd h_gt_len (Nat.not_lt.mpr
            (calc (s.log i).dropLast.length ≤ (s.commitPoint i).index := h_len_cp
              _ ≤ (s.log k).length := h_cpidx_k))
        · -- lastTerm(dropLast) ≠ logTerm s' k (dropLast.length): false from h_agree_drop
          have h_logterm_k :
              logTerm s' k (s.log i).dropLast.length = lastTerm (s.log i).dropLast := by
            unfold logTerm; rw [h_log_ne k h_k_ne]; exact h_agree_drop
          exact absurd h_logterm_k (Ne.symm h_ne)
    · -- Case srv ≠ i: logs/cp unchanged for srv, transfer to s
      have h_log_srv : s'.log srv = s.log srv := h_log_ne srv h_srv_i
      rw [h_log_srv] at h_below' h_lt' h_third' h_pos'
      rw [congr_fun h_cp srv] at h_below'
      -- Construct rollbackBeforeCommitPoint s srv
      apply h_nrbcp srv
      unfold rollbackBeforeCommitPoint
      refine ⟨?_, h_below'⟩
      by_cases h_k_i : k = i
      · -- k = i: construct canRollbackOplog srv i s
        -- Avoid subst (it eliminates i not k); instead rewrite k → i then s'.log i → dropLast
        rw [h_k_i, h_log_i] at h_lt' h_third'
        -- Third condition for s: transfer from s' (with dropLast) to s
        have h_third_s :
            (s.log srv).length > (s.log i).length ∨
            ((s.log srv).length ≤ (s.log i).length ∧
              lastTerm (s.log srv) ≠ logTerm s i (s.log srv).length) := by
          rcases h_third' with h_gt | ⟨h_le, h_ne⟩
          · -- len(srv) > len(dropLast) = len(i) - 1
            rw [List.length_dropLast] at h_gt
            rcases Nat.lt_or_ge (s.log srv).length (s.log i).length with h_lt_i | h_ge_i
            · -- gap impossible: len(i)-1 < len(srv) < len(i) has no natural solution
              omega
            · -- h_ge_i : len(i) ≤ len(srv); split on strict vs equal
              rcases Nat.lt_or_ge (s.log i).length (s.log srv).length with h_gt_i | h_le_i
              · -- len(srv) > len(i): Or.inl
                exact Or.inl h_gt_i
              · -- len(srv) = len(i) from antisymmetry
                have h_eq : (s.log srv).length = (s.log i).length := Nat.le_antisymm h_le_i h_ge_i
                refine Or.inr ⟨h_le_i, ?_⟩
                -- logTerm s i (s.log i).length = lastTerm (s.log i) by definition
                rw [h_eq]
                exact ne_of_lt (lt_of_lt_of_le h_lt' h_mono_drop)
          · -- len(srv) ≤ len(dropLast): logTerm s' i = logTerm s i at this position
            rw [lt_drop _ h_le] at h_ne
            exact Or.inr ⟨by rw [List.length_dropLast] at h_le; omega, h_ne⟩
        exact ⟨i, h_pos', lt_of_lt_of_le h_lt' h_mono_drop, h_third_s⟩
      · -- k ≠ i: logs of srv and k both unchanged, transfer directly
        refine ⟨k, h_pos', ?_, ?_⟩
        · rw [h_log_ne k h_k_i] at h_lt'; exact h_lt'
        · rw [h_log_ne k h_k_i] at h_lt' h_third'
          rcases h_third' with h_gt | ⟨h_le, h_ne⟩
          · exact Or.inl h_gt
          · exact Or.inr ⟨h_le, by unfold logTerm at h_ne ⊢; rwa [h_log_ne k h_k_i] at h_ne⟩
  -- 3. termsAreBounded
  · exact h_tb'
  -- 4. commitPointBounded: commitPoint unchanged, globalCurrentTerm unchanged
  · intro srv; rw [h_cp, h_term]; exact h_cpb srv
  -- 5. logTermsMonotonic: dropLast is a prefix, so logTerm is unchanged for
  -- positions within it (lt_drop / lt_ne), and h_mono applies in the old state.
  · intro srv p q hpq hq
    by_cases h_eq : srv = i
    · -- srv = i: use lt_drop to translate logTerm s' i → logTerm s i
      have hq' : q ≤ (s.log i).dropLast.length := by rw [← h_len_i, ← h_eq]; exact hq
      rw [h_eq, lt_drop p (by omega), lt_drop q hq']
      exact h_mono i p q hpq (by rw [List.length_dropLast] at hq'; omega)
    · rw [lt_ne srv h_eq p, lt_ne srv h_eq q]
      exact h_mono srv p q hpq (h_len_ne srv h_eq ▸ hq)
  -- 6. currentTermMatchesLeader: state/gCT unchanged, log i shortened (dropLast)
  --    Shared lt_drop and lt_ne cover all logTerm translations needed here.
  · intro ldr b p h_ldr' h_len' h_eq'
    rw [h_state] at h_ldr'; rw [h_term]
    -- Translate h_len' and h_eq' from s' to s using shared helpers.
    have h_len_s : p ≤ (s.log b).length := by
      by_cases h_b : b = i
      · subst h_b; rw [h_len_i, List.length_dropLast] at h_len'; omega
      · rw [← h_len_ne b h_b]; exact h_len'
    have h_eq_s : logTerm s b p = s.globalCurrentTerm := by
      by_cases h_b : b = i
      · subst h_b
        rw [lt_drop p (h_len_i ▸ h_len'), h_term] at h_eq'; exact h_eq'
      · rw [lt_ne b h_b, h_term] at h_eq'; exact h_eq'
    -- Apply old currentTermMatchesLeader, then transfer back to s'.
    have h_old := h_ctml ldr b p h_ldr' h_len_s h_eq_s
    by_cases h_l : ldr = i
    · rw [h_l] at h_old ⊢
      by_cases h_b : b = i
      · -- ldr = b = i: p is within dropLast (h_len' gives the bound directly).
        rw [lt_drop p (h_len_i ▸ h_b ▸ h_len')]; exact h_old
      · -- ldr = i, b ≠ i: p might equal or exceed dropLast.length.
        -- h_old says logTerm s i p = gCT; we show p ≤ dropLast.length by contradiction.
        rcases Nat.lt_or_ge p ((s.log i).dropLast.length + 1) with h_sm | h_bg
        · rw [lt_drop p (by omega)]; exact h_old
        · rw [List.length_dropLast] at h_bg
          rcases Nat.lt_or_ge p ((s.log i).length + 1) with h_in | h_out
          · -- p = (s.log i).length: logTerm s i p = lastTerm(s.log i),
            -- but canRollbackOplog says lastTerm(s.log i) < lastTerm(s.log j) ≤ gCT.
            have h_p_len : p = (s.log i).length := by omega
            rw [h_p_len] at h_old
            obtain ⟨_, h_lt, _⟩ := h_can
            have h_bound := logTerm_le_globalCurrentTerm h_tb j (s.log j).length
            unfold logTerm at h_old h_bound; unfold lastTerm at h_lt; omega
          · -- p > (s.log i).length: logTerm s i p = 0, so gCT = 0. Contradiction.
            have h_oob : logTerm s i p = 0 := by
              unfold logTerm getTerm; split; · omega
              · next h_ne => rw [List.getElem?_eq_none (by omega)]
            rw [h_old] at h_oob
            have := logTerm_le_globalCurrentTerm h_tb' i p
            rw [h_term] at this; omega
    · rw [lt_ne ldr h_l]; exact h_old
  -- 7. leaderUnique: state unchanged
  · exact leaderUnique_of_state_eq h_state h_lu
  -- 8. logMatching: dropLast preserves prefix, so logTerm at positions ≤ len-1 unchanged
  · intro a b p h_len_a h_len_b h_eq q h_qp
    by_cases h_a : a = i <;> by_cases h_b : b = i
    · rw [h_a, h_b]
    · rw [h_a] at h_len_a h_eq ⊢
      rw [lt_ne b h_b] at h_eq ⊢
      have h_len_a_drop : p ≤ (s.log i).dropLast.length := by rw [h_len_i] at h_len_a; exact h_len_a
      have h_len_b_s : p ≤ (s.log b).length := by rw [h_len_ne b h_b] at h_len_b; exact h_len_b
      rw [lt_drop p h_len_a_drop] at h_eq
      rw [lt_drop q (by omega)]
      exact h_lm i b p (by rw [List.length_dropLast] at h_len_a_drop; omega)
        h_len_b_s h_eq q h_qp
    · rw [h_b] at h_len_b h_eq ⊢
      rw [lt_ne a h_a] at h_eq ⊢
      have h_len_b_drop : p ≤ (s.log i).dropLast.length := by rw [h_len_i] at h_len_b; exact h_len_b
      have h_len_a_s : p ≤ (s.log a).length := by rw [h_len_ne a h_a] at h_len_a; exact h_len_a
      rw [lt_drop p h_len_b_drop] at h_eq
      rw [lt_drop q (by omega)]
      exact h_lm a i p h_len_a_s (by rw [List.length_dropLast] at h_len_b_drop; omega)
        h_eq q h_qp
    · rw [lt_ne a h_a] at h_eq ⊢
      rw [lt_ne b h_b] at h_eq ⊢
      exact h_lm a b p (by rw [h_len_ne a h_a] at h_len_a; exact h_len_a)
        (by rw [h_len_ne b h_b] at h_len_b; exact h_len_b) h_eq q h_qp
  -- 9. leaderCompletenessForCommitPoints: log i shortened (dropLast), state/cp unchanged
  · intro ldr srv h_ldr_s
    rw [h_state] at h_ldr_s
    obtain ⟨h_idx, h_agree⟩ := h_lccp ldr srv h_ldr_s
    rw [h_cp]
    by_cases h_ldr_i : ldr = i
    · -- ldr = i: leader's log shortened. Need cpIndex(srv) ≤ len(dropLast).
      -- From h_nrbcp + canRollbackOplog i j: cpIndex(i) < len(log i).
      -- For srv ≠ i: need cpIndex(srv) < len(log i), which requires additional argument.
      rw [h_ldr_i]
      rw [h_ldr_i] at h_idx h_agree h_ldr_s
      -- Key: cpIdx(srv) < len(s.log i), so cpIdx ≤ len(dropLast)
      have h_cp_strict : (s.commitPoint srv).index < (s.log i).length := by
        by_contra h_not
        push_neg at h_not
        have h_eq_len : (s.commitPoint srv).index = (s.log i).length :=
          Nat.le_antisymm h_idx h_not
        obtain ⟨_, h_lt_term, h_third⟩ := h_can
        have h_ge_cp := h_lgt i srv h_ldr_s
        -- cpTerm(srv) ≤ lastTerm(i) < lastTerm(j), so cpTerm(srv) < lastTerm(j)
        obtain ⟨h_idx_j, h_agree_j⟩ := h_llcp j srv (by omega)
        rcases h_third with h_gt | ⟨h_le, h_ne⟩
        · -- len(i) > len(j) but cpIdx = len(i) ≤ len(j) from h_llcp. Contradiction.
          omega
        · -- len(i) ≤ len(j) ∧ lastTerm(i) ≠ logTerm s j len(i)
          -- We derive logTerm s j len(i) = lastTerm(i) through srv, contradicting h_ne.
          have h1 := h_agree _ (le_refl _) (h_cp_le_srv srv)
          have h2 := h_agree_j _ (le_refl _) (h_cp_le_srv srv)
          rw [h_eq_len] at h1 h2
          exact absurd (h1.trans h2.symm) h_ne
      -- Part 1: cpIdx ≤ len(dropLast), Part 2: agreement
      refine ⟨by rw [h_log_i, List.length_dropLast]; omega, ?_⟩
      intro p h_p h_p_len
      by_cases h_srv_i : srv = i
      · -- srv = i: both sides equal logTerm s' i p
        rw [h_srv_i]
      · -- srv ≠ i: transfer to old state
        rw [lt_ne srv h_srv_i, lt_drop p (by rw [List.length_dropLast]; omega)]
        exact h_agree p h_p (by
          have : s'.log srv = s.log srv := by
            have := congr_fun h_log srv; simp [h_srv_i] at this; exact this
          rw [this] at h_p_len; exact h_p_len)
    · -- ldr ≠ i: leader's log unchanged
      have h_log_ldr : s'.log ldr = s.log ldr := by
        have := congr_fun h_log ldr; simp [h_ldr_i] at this; exact this
      refine ⟨by rw [h_log_ldr]; exact h_idx, ?_⟩
      intro p h_p_cp h_p_len
      rw [lt_ne ldr h_ldr_i]
      by_cases h_srv_i : srv = i
      · -- srv = i: log shortened (dropLast)
        rw [h_srv_i] at h_p_len ⊢
        rw [h_log_i] at h_p_len
        rw [lt_drop p h_p_len]
        rw [← h_srv_i]
        exact h_agree p h_p_cp (by rw [h_srv_i]; rw [List.length_dropLast] at h_p_len; omega)
      · -- srv ≠ i: log unchanged
        rw [lt_ne srv h_srv_i]
        have h_log_srv : s'.log srv = s.log srv := by
          have := congr_fun h_log srv; simp [h_srv_i] at this; exact this
        exact h_agree p h_p_cp (by rw [h_log_srv] at h_p_len; exact h_p_len)
  -- 10. commitPointsBackedByQuorums: log i shortened, cp unchanged
  -- Proof sketch:
  -- Use same Q₀ from h_cpbq. For n ≠ i: coverage/agreement transfer trivially.
  -- For n = i: cp(srv).index < len(i) (so ≤ dropLast.length) by contradiction
  -- using h_llcp + canRollbackOplog third condition.
  -- cp(srv).term ≤ lastTerm(dropLast) follows from: if cp(srv).term ≤ cp(i).term,
  -- use h_rsc. Otherwise, use the chain Q₀→srv→j to contradict canRollbackOplog.
  -- Agreement at positions ≤ cp(srv).index is in the prefix, so logTerm unchanged.
  · -- Q₀ members agree with srv at positions ≤ cp(srv).index
    -- (via h_cpa when lastTerm = cp.term, h_llcp when lastTerm > cp.term)
    have h_q_agree_srv : ∀ srv, ∀ Q : Finset Server,
        (∀ n, n ∈ Q → (s.commitPoint srv).index ≤ (s.log n).length ∧
          (s.commitPoint srv).term ≤ lastTerm (s.log n)) →
        (∀ n₁ n₂, n₁ ∈ Q → n₂ ∈ Q →
          ∀ p, p ≤ (s.commitPoint srv).index → logTerm s n₁ p = logTerm s n₂ p) →
        ∀ n, n ∈ Q → ∀ p, p ≤ (s.commitPoint srv).index →
          logTerm s n p = logTerm s srv p := by
      intro srv Q hcover hagree n hn p hp
      obtain ⟨hlen_n, hterm_n⟩ := hcover n hn
      rcases Nat.eq_or_lt_of_le hterm_n with h_eq | h_gt
      · -- lastTerm(n) = cp(srv).term: use h_cpa
        exact h_cpa n srv h_eq.symm hlen_n p hp (by have := h_cp_le_srv srv; omega)
      · -- lastTerm(n) > cp(srv).term: use h_llcp
        exact (h_llcp n srv h_gt).2 p hp (by have := h_cp_le_srv srv; omega)
    -- Main proof
    intro srv
    obtain ⟨Q₀, hQ₀, hcover₀, hagree₀⟩ := h_cpbq srv
    rw [h_cp]
    -- Key: cp(srv).index < len(i) when i ∈ Q₀
    have h_cp_strict : ∀ _ : i ∈ Q₀, (s.commitPoint srv).index < (s.log i).length := by
      intro h_i_in
      by_contra h_not
      push_neg at h_not
      obtain ⟨hlen_i, hterm_i⟩ := hcover₀ i h_i_in
      have h_eq_len : (s.commitPoint srv).index = (s.log i).length :=
        Nat.le_antisymm hlen_i h_not
      obtain ⟨_, h_lt_term, h_third⟩ := h_can
      -- cp(srv).term ≤ lastTerm(i) < lastTerm(j), so h_llcp applies to j
      obtain ⟨h_idx_j, h_agree_j⟩ := h_llcp j srv (by omega)
      rcases h_third with h_gt | ⟨h_le, h_ne⟩
      · -- len(i) > len(j) but cp.index = len(i) ≤ len(j) from h_llcp. Contradiction.
        omega
      · -- len(i) ≤ len(j) ∧ lastTerm(i) ≠ logTerm s j len(i)
        -- Chain: logTerm s i len(i) = logTerm s srv len(i) = logTerm s j len(i)
        have h_q_srv := h_q_agree_srv srv Q₀
          (fun n hn => let ⟨a, b, _⟩ := hcover₀ n hn; ⟨a, b⟩) hagree₀ i h_i_in
        have h1 : logTerm s i (s.commitPoint srv).index =
            logTerm s srv (s.commitPoint srv).index :=
          h_q_srv _ (le_refl _)
        have h2 : logTerm s j (s.commitPoint srv).index =
            logTerm s srv (s.commitPoint srv).index :=
          h_agree_j _ (le_refl _) (h_cp_le_srv srv)
        rw [h_eq_len] at h1 h2
        exact absurd (h1.trans h2.symm) h_ne
    -- Use Q₀ for s'. For n ≠ i: trivial. For n = i: index and term bounds hold.
    refine ⟨Q₀, hQ₀, fun n hn => ?_, fun n₁ n₂ hn₁ hn₂ p hp => ?_⟩
    · -- Coverage
      obtain ⟨hlen, hterm, hlt⟩ := hcover₀ n hn
      by_cases h_n : n = i
      · -- n = i: need cp.index ≤ dropLast.length, cp.term ≤ lastTerm(dropLast),
        -- and logTerm s' n cp.index = cp.term.
        subst h_n
        have h_strict := h_cp_strict hn
        have h_dl_len : (s.commitPoint srv).index ≤
            (s.log n).dropLast.length := by
          rw [List.length_dropLast]; omega
        refine ⟨?_, ?_, ?_⟩
        · -- Index bound: cp(srv).index ≤ dropLast.length
          rw [h_len_i, List.length_dropLast]; omega
        · -- Term bound: cp(srv).term ≤ lastTerm(dropLast)
          -- Chain: cp.term = logTerm s n cp.index (by hlt)
          --        ≤ logTerm s n dropLast.length (by monotonicity)
          --        = logTerm s' n dropLast.length (by lt_drop)
          --        = lastTerm(s'.log n) (by defn, since s'.log n = dropLast)
          have h_mono_step := h_mono n (s.commitPoint srv).index
            (s.log n).dropLast.length h_dl_len
            (by rw [List.length_dropLast]; omega)
          have h_lt_eq : logTerm s' n (s.log n).dropLast.length =
              logTerm s n (s.log n).dropLast.length :=
            lt_drop _ (le_refl _)
          -- lastTerm(s'.log n) = logTerm s' n dropLast.length
          have h_lastTerm : lastTerm (s'.log n) =
              logTerm s' n (s.log n).dropLast.length := by
            unfold lastTerm logTerm; rw [h_len_i]
          rw [h_lastTerm, h_lt_eq, hlt.symm]; exact h_mono_step
        · -- logTerm s' n cp.index = cp.term: in prefix, so unchanged
          rw [lt_drop _ h_dl_len]; exact hlt
      · -- n ≠ i: log unchanged
        exact ⟨by rw [h_len_ne n h_n]; exact hlen,
          by unfold lastTerm; rw [h_log]; simp [h_n]; exact hterm,
          by rw [lt_ne n h_n]; exact hlt⟩
    · -- Pairwise agreement: positions ≤ cp(srv).index are in the prefix
      have lt_pres : ∀ m, m ∈ Q₀ → logTerm s' m p = logTerm s m p := by
        intro m hm
        by_cases h_m : m = i
        · subst h_m
          exact lt_drop p (by rw [List.length_dropLast]; have := h_cp_strict hm; omega)
        · exact lt_ne m h_m p
      rw [lt_pres n₁ hn₁, lt_pres n₂ hn₂]
      exact hagree₀ n₁ n₂ hn₁ hn₂ p hp
  -- 11. logsLaterThanCommitPointHaveEntries: log i shortened, cp unchanged
  -- Proof sketch:
  -- For a ≠ i: log a unchanged, lastTerm unchanged → use h_llcp directly.
  -- For a = i: lastTerm(dropLast) > cp(b).term. By monotonicity,
  -- lastTerm(s.log i) ≥ lastTerm(dropLast) > cp(b).term. By h_llcp,
  -- cp(b).index ≤ len(s.log i). Show strict (= len would give lastTerm ≤ cp.term
  -- via h_cpetb, contradiction). So cp(b).index ≤ len(dropLast). Agreement is
  -- in the unchanged prefix.
  · have h_lastTerm_i : lastTerm (s'.log i) = lastTerm (s.log i).dropLast := by
      unfold lastTerm; rw [h_log_i]
    intro a b h_gt
    rw [h_cp] at h_gt ⊢
    by_cases h_a : a = i
    · -- a = i: log shortened
      subst a
      rw [h_lastTerm_i] at h_gt
      have h_old_gt : lastTerm (s.log i) > (s.commitPoint b).term := by omega
      obtain ⟨h_len_old, h_agree_old⟩ := h_llcp i b h_old_gt
      -- cp(b).index < len(s.log i): if equal, h_cpetb gives lastTerm ≤ cp.term
      have h_strict : (s.commitPoint b).index < (s.log i).length := by
        by_contra h_not
        push_neg at h_not
        have h_eq : (s.commitPoint b).index = (s.log i).length :=
          Nat.le_antisymm h_len_old h_not
        have h1 : logTerm s i (s.commitPoint b).index =
            logTerm s b (s.commitPoint b).index :=
          h_agree_old _ (le_refl _) (h_cp_le_srv b)
        have h2 : logTerm s b (s.commitPoint b).index ≤ (s.commitPoint b).term :=
          h_cpetb b _ (le_refl _) (h_cp_le_srv b)
        rw [h_eq] at h1 h2
        have : logTerm s i (s.log i).length = lastTerm (s.log i) := rfl
        omega
      constructor
      · -- cp(b).index ≤ len(s'.log i) = len(dropLast)
        rw [h_len_i, List.length_dropLast]; omega
      · -- Agreement: positions ≤ cp(b).index are in the prefix
        intro p h_p_cp h_p_log
        have h_p_drop : p ≤ (s.log i).dropLast.length := by
          rw [List.length_dropLast]; omega
        rw [lt_drop p h_p_drop]
        by_cases h_b : b = i
        · subst b; rw [lt_drop p h_p_drop]
        · rw [lt_ne b h_b]
          exact h_agree_old p h_p_cp (by rw [h_len_ne b h_b] at h_p_log; exact h_p_log)
    · -- a ≠ i: log a unchanged
      have h_last_eq : lastTerm (s'.log a) = lastTerm (s.log a) := by
        unfold lastTerm; rw [h_log]; simp [h_a]
      rw [h_last_eq] at h_gt
      obtain ⟨h_len_a, h_agree_a⟩ := h_llcp a b h_gt
      constructor
      · rw [h_len_ne a h_a]; exact h_len_a
      · intro p h_p_cp h_p_log
        rw [lt_ne a h_a]
        by_cases h_b : b = i
        · subst b
          rw [lt_drop p (by rw [← h_len_i]; exact h_p_log)]
          exact h_agree_a p h_p_cp
            (by rw [h_len_i, List.length_dropLast] at h_p_log; omega)
        · rw [lt_ne b h_b]
          exact h_agree_a p h_p_cp (by rw [h_len_ne b h_b] at h_p_log; exact h_p_log)
  -- 12. commitPointAgreement: log i shortened, cp unchanged
  · have h_lastTerm_i : lastTerm (s'.log i) = lastTerm (s.log i).dropLast := by
      unfold lastTerm; rw [h_log_i]
    intro a b h_lt h_len p h_p_cp h_p_log
    rw [h_cp] at h_p_cp h_lt h_len
    by_cases h_a : a = i <;> by_cases h_b : b = i
    · -- a = i, b = i: both sides are logTerm s' i p, trivially equal
      rw [h_a, h_b]
    · -- a = i, b ≠ i: server a's log shortened, b's log unchanged
      rw [h_a] at h_lt h_len ⊢
      rw [lt_ne b h_b]
      -- p ≤ cp(b).index ≤ len(dropLast) < len(s.log i), so logTerm s' i p = logTerm s i p
      have h_p_drop : p ≤ (s.log i).dropLast.length := by
        rw [← h_len_i]; omega
      rw [lt_drop p h_p_drop]
      have h_p_log_s : p ≤ (s.log b).length := by rw [← h_len_ne b h_b]; exact h_p_log
      -- Case split: lastTerm(s.log i) = cp(b).term or lastTerm(s.log i) > cp(b).term
      -- We know lastTerm(dropLast) = cp(b).term from h_lt.
      -- By logTermsMonotonic, lastTerm(dropLast) ≤ lastTerm(s.log i).
      rw [h_lastTerm_i] at h_lt
      -- Case split on lastTerm(s.log i) vs cp(b).term
      rcases Nat.lt_or_ge (s.commitPoint b).term (lastTerm (s.log i)) with h_cp_lt | h_cp_ge
      · -- lastTerm(s.log i) > cp(b).term: use h_llcp
        exact (h_llcp i b h_cp_lt).2 p h_p_cp h_p_log_s
      · -- cp(b).term ≥ lastTerm(s.log i): derive lastTerm(s.log i) = cp(b).term
        -- lastTerm(dropLast) ≤ lastTerm(s.log i) by logTermsMonotonic
        have h_gt_eq : ∀ k, k ≤ (s.log i).dropLast.length →
            getTerm (s.log i).dropLast k = getTerm (s.log i) k := by
          intro k hk; unfold getTerm
          split; · rfl
          · next h_ne =>
            rw [List.getElem?_dropLast,
              if_pos (by rw [List.length_dropLast] at hk; omega)]
        have h_mono_last : lastTerm (s.log i).dropLast ≤ lastTerm (s.log i) := by
          unfold lastTerm
          rcases Nat.eq_or_lt_of_le (Nat.zero_le (s.log i).dropLast.length) with h_z | h_pos_dl
          · rw [← h_z]; simp [getTerm]
          · rw [h_gt_eq _ (le_refl _)]
            change logTerm s i _ ≤ logTerm s i _
            exact h_mono i _ _ (by rw [List.length_dropLast]; omega) (le_refl _)
        have h_eq : lastTerm (s.log i) = (s.commitPoint b).term := by
          have := h_mono_last; rw [h_lt] at this; omega
        have h_len_s : (s.log i).length ≥ (s.commitPoint b).index := by
          rw [h_len_i, List.length_dropLast] at h_len; omega
        exact h_cpa i b h_eq h_len_s p h_p_cp h_p_log_s
    · -- a ≠ i, b = i: server b's log shortened, a's log unchanged
      rw [h_b] at h_lt h_len h_p_cp h_p_log ⊢
      rw [lt_ne a h_a]
      -- p ≤ len(s'.log i) = len(dropLast), so logTerm s' i p = logTerm s i p
      have h_p_drop : p ≤ (s.log i).dropLast.length := by rw [← h_len_i]; exact h_p_log
      rw [lt_drop p h_p_drop]
      -- a's log is unchanged, so lastTerm(s'.log a) = lastTerm(s.log a)
      have h_lt_s : lastTerm (s.log a) = (s.commitPoint i).term := by
        rw [h_log_ne a h_a] at h_lt; exact h_lt
      have h_len_s : (s.log a).length ≥ (s.commitPoint i).index := by
        rw [h_log_ne a h_a] at h_len; exact h_len
      have h_p_log_s : p ≤ (s.log i).length := by
        rw [List.length_dropLast] at h_p_drop; omega
      exact h_cpa a i h_lt_s h_len_s p h_p_cp h_p_log_s
    · -- a ≠ i, b ≠ i: both logs unchanged
      rw [lt_ne a h_a, lt_ne b h_b]
      have h_lt_s : lastTerm (s.log a) = (s.commitPoint b).term := by
        rw [h_log_ne a h_a] at h_lt; exact h_lt
      have h_len_s : (s.log a).length ≥ (s.commitPoint b).index := by
        rw [h_log_ne a h_a] at h_len; exact h_len
      have h_p_log_s : p ≤ (s.log b).length := by rw [← h_len_ne b h_b]; exact h_p_log
      exact h_cpa a b h_lt_s h_len_s p h_p_cp h_p_log_s
  -- 13. leaderLastTermGeCommitPointTerm: state/cp unchanged, log i shortened
  -- Proof: for ldr ≠ i, log unchanged → use IH. For ldr = i (leader rolled back):
  -- (a) cpIndex(srv) < len(log i) via same argument as h_lccp case (h_llcp + third cond).
  -- (b) logTerm srv cpIndex = cpTerm: use h_llcp or h_cpa with a cpbq quorum member.
  -- (c) logTerm i cpIndex = cpTerm via h_lccp agreement.
  -- (d) cpIndex ≤ len(dropLast), so monotonicity gives lastTerm(dropLast) ≥ cpTerm.
  · intro ldr srv h_ldr_s
    rw [h_state] at h_ldr_s; rw [h_cp]
    by_cases h_eq : ldr = i
    · -- ldr = i: leader's log shortened to dropLast
      rw [h_eq] at h_ldr_s ⊢
      rw [h_log_i]
      -- Key step (a): cpIndex(srv) < len(log i) — same argument as in h_lccp proof
      have h_cp_strict : (s.commitPoint srv).index < (s.log i).length := by
        by_contra h_not
        push_neg at h_not
        obtain ⟨h_idx, h_agree⟩ := h_lccp i srv h_ldr_s
        have h_eq_len : (s.commitPoint srv).index = (s.log i).length :=
          Nat.le_antisymm h_idx h_not
        obtain ⟨_, h_lt_term, h_third⟩ := h_can
        have h_ge_cp := h_lgt i srv h_ldr_s
        obtain ⟨h_idx_j, h_agree_j⟩ := h_llcp j srv (by omega)
        rcases h_third with h_gt | ⟨h_le, h_ne⟩
        · omega
        · have h1 := h_agree _ (le_refl _) (h_cp_le_srv srv)
          have h2 := h_agree_j _ (le_refl _) (h_cp_le_srv srv)
          rw [h_eq_len] at h1 h2
          exact absurd (h1.trans h2.symm) h_ne
      -- Key step (b): logTerm srv cpIndex = cpTerm
      -- Use logTerm_at_commitPoint_eq_term with cpbq quorum witness.
      have h_srv_eq := logTerm_at_commitPoint_eq_term s srv h_cpbq h_llcp h_cpa (h_cp_le_srv srv)
      -- Key step (c): logTerm i cpIndex = cpTerm via h_lccp
      have h_leader_eq : logTerm s i (s.commitPoint srv).index = (s.commitPoint srv).term := by
        rw [← h_srv_eq]
        exact (h_lccp i srv h_ldr_s).2 _ (le_refl _) (h_cp_le_srv srv)
      -- Key step (d): monotonicity: cpIndex ≤ len(dropLast) and logTerm at cpIndex =
      -- cpTerm, so lastTerm(dropLast) ≥ logTerm at cpIndex = cpTerm.
      rw [← h_leader_eq, h_lastTerm_drop_eq]
      exact h_mono i _ _ (by rw [List.length_dropLast]; omega) (by rw [List.length_dropLast]; omega)
    · -- ldr ≠ i: leader's log unchanged
      rw [h_log_ne ldr h_eq]
      exact h_lgt ldr srv h_ldr_s
  -- 14. uniformLogEntriesInTerm: dropLast preserves the property
  · -- Dropping the last entry only shrinks log i. Other servers' logs unchanged.
    -- If term T first appeared at position p in the shortened log, it also first
    -- appeared at position p in the original log, so the property is inherited.
    -- For any server, logTerm at positions within the new log equals logTerm in s
    have lt_srv : ∀ srv idx, idx ≤ (s'.log srv).length →
        logTerm s' srv idx = logTerm s srv idx := by
      intro srv idx h_idx
      by_cases h : srv = i
      · subst h; exact lt_drop idx (by rw [h_len_i] at h_idx; exact h_idx)
      · exact lt_ne srv h idx
    intro a' b' p q hp hpa hq hqb h_eq' h_ne' h_first'
    have hpa_s : p ≤ (s.log a').length := by
      by_cases h : a' = i
      · subst h; rw [h_len_i, List.length_dropLast] at hpa; omega
      · rw [h_len_ne a' h] at hpa; exact hpa
    have hqb_s : q ≤ (s.log b').length := by
      by_cases h : b' = i
      · subst h; rw [h_len_i, List.length_dropLast] at hqb; omega
      · rw [h_len_ne b' h] at hqb; exact hqb
    exact h_ulet a' b' p q hp hpa_s hq hqb_s
      (by rw [← lt_srv a' p (by omega), ← lt_srv b' q (by omega)]; exact h_eq')
      (by rw [← lt_srv a' p (by omega)]; exact h_ne')
      (fun k hk1 hkp => by
        rw [← lt_srv a' k (by omega), ← lt_srv a' p (by omega)]
        exact h_first' k hk1 hkp)
  -- 15. commitPointWeaklyBelowLogTip: cp unchanged, log i shortened
  -- For srv ≠ i: logs/cp unchanged, use h_cwb directly.
  -- For srv = i: h_rsc gives cp.term ≤ lastTerm(dropLast). If strict, done.
  -- If equal, need cp.index ≤ dropLast.length. Use h_llcp j i (since
  -- lastTerm(s.log j) > cp.term from canRollbackOplog) to get cp.index ≤ len(j)
  -- and agreement. If cp.index = len(i), agreement at len(i) contradicts
  -- canRollbackOplog's third condition.
  · intro srv
    rw [h_cp]
    by_cases h_eq : srv = i
    · subst h_eq
      -- After subst: 'i' eliminated, 'srv' survives. Shared helpers h_log_i,
      -- h_lastTerm_i, h_mono_drop, h_cp_le_srv now speak of 'srv' in place of 'i'.
      rw [h_lastTerm_i]
      have h_rsc_srv := h_rsc srv ⟨j, h_can⟩
      rcases Nat.lt_or_eq_of_le h_rsc_srv with h_lt_rsc | h_eq_rsc
      · left; exact h_lt_rsc
      · right; refine ⟨h_eq_rsc, ?_⟩
        rw [h_log_i, List.length_dropLast]
        -- cp.term < lastTerm(s.log j) via canRollbackOplog + monotonicity
        have h_j_gt : lastTerm (s.log j) > (s.commitPoint srv).term :=
          calc (s.commitPoint srv).term
              = lastTerm (s.log srv).dropLast := h_eq_rsc
            _ ≤ lastTerm (s.log srv) := h_mono_drop
            _ < lastTerm (s.log j) := h_can.2.1
        obtain ⟨_, h_agree_j⟩ := h_llcp j srv h_j_gt
        have h_cpidx_srv := h_cp_le_srv srv
        -- Show cp.index < len(srv), hence ≤ len(srv) - 1
        suffices h_strict : (s.commitPoint srv).index < (s.log srv).length by omega
        by_contra h_not
        push_neg at h_not
        have h_eq_len : (s.commitPoint srv).index = (s.log srv).length := by omega
        -- Agreement: logTerm s j len(srv) = lastTerm(s.log srv)
        have h_agree_at : logTerm s j (s.log srv).length = lastTerm (s.log srv) := by
          unfold lastTerm
          exact h_agree_j _ (by omega) (le_refl _)
        -- canRollbackOplog's third condition gives contradiction
        rcases h_can.2.2 with h_gt_len | ⟨h_le_len, h_ne⟩
        · exact absurd h_gt_len (Nat.not_lt.mpr (by omega))
        · exact absurd h_agree_at (Ne.symm h_ne)
    · rw [h_log_ne srv h_eq]; exact h_cwb srv
  -- 16. commitPointEntryTermsBounded: cp unchanged, log i shortened (prefix preserved)
  · intro b p hp hpl
    rw [h_cp] at hp
    by_cases h_b : b = i
    · subst h_b
      have hpl_old : p ≤ (s.log b).length := by rw [h_len_i, List.length_dropLast] at hpl; omega
      rw [lt_drop p (h_len_i ▸ hpl), h_cp]; exact h_cpetb b p hp hpl_old
    · rw [lt_ne b h_b p, h_cp]; exact h_cpetb b p hp (by rw [h_log_ne b h_b] at hpl; exact hpl)
  -- 17. rollbackSafeCommitPoint: cp unchanged, log i shortened
  -- Proof sketch:
  -- For srv ≠ i: transfer canRollbackOplog witness from s' to s.
  --   If k' ≠ i: both logs unchanged, direct transfer.
  --   If k' = i: use monotonicity (lastTerm(dropLast) ≤ lastTerm) to get
  --     lastTerm(srv) < lastTerm(s.log i), then transfer third condition.
  -- For srv = i: use h_llcp with witness k' to show cp.index < n-1.
  --   Then logTerm(i, cp.index) = cp.term via h_cpbq + h_llcp/h_cpa.
  --   Conclude cp.term ≤ lastTerm(dropLast.dropLast) by monotonicity.
  · intro srv ⟨k', h_can'⟩
    rw [h_cp]
    by_cases h_srv : srv = i
    · -- Case srv = i: need cp.term ≤ lastTerm(dropLast.dropLast)
      rw [h_srv]
      -- k' ≠ i (otherwise lastTerm < lastTerm, contradiction)
      have h_k_ne : k' ≠ i := by
        intro h_eq
        have : srv = k' := h_srv.trans h_eq.symm
        rw [this] at h_can'
        exact absurd h_can'.2.1 (Nat.lt_irrefl _)
      -- cp.term ≤ lastTerm(dropLast) from h_rsc
      have h_rsc_i := h_rsc i ⟨j, h_can⟩
      -- lastTerm(dropLast) < lastTerm(s.log k')
      have h_lt_k : lastTerm (s.log i).dropLast < lastTerm (s.log k') := by
        have := h_can'.2.1; rw [h_srv, h_log_i, h_log_ne k' h_k_ne] at this; exact this
      -- lastTerm(s.log k') > cp.term
      have h_k_gt_cp : lastTerm (s.log k') > (s.commitPoint i).term := by omega
      -- h_llcp k' i: agreement up to cp.index, cp.index ≤ len(k')
      obtain ⟨h_idx_k, h_agree_ki⟩ := h_llcp k' i h_k_gt_cp
      -- (s.log i).length ≥ 2
      have h_len_ge2 : (s.log i).length ≥ 2 := by
        have := h_can'.1; rw [h_srv, h_log_i, List.length_dropLast] at this; omega
      -- cp.index < n - 1 using third condition of canRollbackOplog i k' s'
      have h_cp_strict : (s.commitPoint i).index < (s.log i).length - 1 := by
        by_contra h_not; push_neg at h_not
        obtain ⟨_, _, h_third'⟩ := h_can'
        rw [h_srv, h_log_i, h_log_ne k' h_k_ne] at h_third'
        rcases h_third' with h_gt_len | ⟨h_le_len, h_ne_term⟩
        · -- dropLast.length > len(k'): contradicts cp.index ≤ len(k')
          rw [List.length_dropLast] at h_gt_len; omega
        · -- lastTerm(dropLast) ≠ logTerm s' k' (dropLast.length)
          rw [List.length_dropLast] at h_le_len h_ne_term
          -- From h_agree_ki: logTerm s k' (n-1) = logTerm s i (n-1)
          have h_agree_at :=
            h_agree_ki ((s.log i).length - 1) (by omega) (by omega)
          -- logTerm s i (n-1) = lastTerm(dropLast) by h_lastTerm_drop_eq
          have h_lt_i : logTerm s i ((s.log i).length - 1) =
              lastTerm (s.log i).dropLast := by
            rw [← List.length_dropLast]; exact h_lastTerm_drop_eq.symm
          rw [lt_ne k' h_k_ne, h_agree_at, h_lt_i] at h_ne_term
          exact absurd rfl h_ne_term
      -- logTerm(s, i, cp.index) = cp.term via quorum overlap
      have h_logterm_cp :=
        logTerm_at_commitPoint_eq_term s i h_cpbq h_llcp h_cpa (by omega)
      -- Final: cp.term = logTerm(i, cp.idx) ≤ logTerm(i, n-2) = lastTerm(ddl)
      rw [h_log_i, ← h_logterm_cp]
      -- Goal: logTerm s i cp.idx ≤ lastTerm (s.log i).dropLast.dropLast
      -- Step 1: lastTerm(ddl) = logTerm s i (ddl.length)
      have h_lastTerm_ddl : lastTerm (s.log i).dropLast.dropLast =
          logTerm s i ((s.log i).dropLast.dropLast.length) := by
        unfold lastTerm logTerm getTerm
        rw [List.length_dropLast, List.length_dropLast]
        simp only [Nat.sub_sub]
        split
        · rfl
        · next h_ne =>
          congr 1
          rw [List.getElem?_dropLast, if_pos (by rw [List.length_dropLast]; omega)]
          rw [List.getElem?_dropLast, if_pos (by omega)]
      -- Step 2: logTerm(i, cp.idx) ≤ logTerm(i, ddl.length) by monotonicity
      rw [h_lastTerm_ddl]
      exact h_mono i _ _
        (by rw [List.length_dropLast, List.length_dropLast]; omega)
        (by rw [List.length_dropLast, List.length_dropLast]; omega)
    · -- Case srv ≠ i: transfer canRollbackOplog witness to s
      rw [h_log_ne srv h_srv]
      by_cases h_k_i : k' = i
      · -- k' = i: construct canRollbackOplog srv i s
        rw [h_k_i] at h_can'
        obtain ⟨h_pos', h_lt', h_third'⟩ := h_can'
        rw [h_log_ne srv h_srv] at h_pos'
        rw [h_log_ne srv h_srv, h_log_i] at h_lt' h_third'
        -- lastTerm(dropLast) ≤ lastTerm(s.log i) by shared h_mono_drop
        have h_lt_i : lastTerm (s.log srv) < lastTerm (s.log i) :=
          lt_of_lt_of_le h_lt' h_mono_drop
        have h_third_s :
            (s.log srv).length > (s.log i).length ∨
            ((s.log srv).length ≤ (s.log i).length ∧
              lastTerm (s.log srv) ≠ logTerm s i (s.log srv).length) := by
          rcases h_third' with h_gt | ⟨h_le, h_ne⟩
          · -- len(srv) > len(dropLast) = len(i) - 1
            rw [List.length_dropLast] at h_gt
            rcases Nat.lt_or_ge (s.log i).length (s.log srv).length with h_lt | h_ge
            · exact Or.inl h_lt
            · exact Or.inr ⟨h_ge, by
                have : (s.log srv).length = (s.log i).length := by omega
                rw [this]; exact ne_of_lt h_lt_i⟩
          · -- len(srv) ≤ len(dropLast): logTerm s' i = logTerm s i at this position
            refine Or.inr ⟨by rw [List.length_dropLast] at h_le; omega, ?_⟩
            rwa [lt_drop (s.log srv).length h_le] at h_ne
        exact h_rsc srv ⟨i, h_pos', h_lt_i, h_third_s⟩
      · -- k' ≠ i: both srv and k' logs unchanged
        have h_can_s : canRollbackOplog srv k' s := by
          unfold canRollbackOplog at h_can' ⊢
          rw [h_log_ne srv h_srv, h_log_ne k' h_k_i] at h_can'
          refine ⟨h_can'.1, h_can'.2.1, ?_⟩
          rcases h_can'.2.2 with h_gt | ⟨h_le, h_ne⟩
          · exact Or.inl h_gt
          · refine Or.inr ⟨h_le, ?_⟩
            rwa [lt_ne k' h_k_i] at h_ne
        exact h_rsc srv ⟨k', h_can_s⟩
  -- 18. rollbackWithSyncSourceImpliesCommitPointBelowTip
  -- Proof: case split on a = i and b = i. rollbackOplog only changes server i's log
  -- (dropLast). We transfer appendOplogEnabled and canRollbackOplog between s' and s.
  · intro a b h_aoe h_can_ex h_below
    rw [h_cp] at h_below
    by_cases h_a : a = i <;> by_cases h_b : b = i
    · -- Case a = i, b = i: appendOplogEnabled i i requires len < len, impossible
      subst h_a; subst h_b; exact Nat.lt_irrefl _ h_aoe.1
    · -- Case a = i, b ≠ i: a's log shortened, b's log unchanged.
      -- Strategy: take witness k₀ from h_can_ex (canRollbackOplog i k₀ s').
      -- In both cases of h_below, apply h_llcp k₀ b to get logTerm(k₀, dropLast.length)
      -- = lastTerm(dropLast(i)), then contradict the third condition of canRollbackOplog.
      -- inr case: lastTerm(dropLast) = cp.term < lastTerm(k₀) by h_lt_k₀. Direct.
      -- inl case: derive cp.index > dropLast.length from monotonicity, then same argument
      --           when lastTerm(k₀) > cp.term. (lastTerm(k₀) ≤ cp.term left as sorry.)
      rw [h_a] at h_aoe h_below h_can_ex
      unfold appendOplogEnabled at h_aoe
      rw [h_log_i, h_log_ne b h_b] at h_aoe
      obtain ⟨h_aoe_len, h_aoe_match⟩ := h_aoe
      rw [lt_ne b h_b] at h_aoe_match
      rw [h_log_i] at h_below
      have h_lt_cp : logTerm s b (s.commitPoint b).index = (s.commitPoint b).term :=
        logTerm_at_commitPoint_eq_term s b h_cpbq h_llcp h_cpa (h_cp_le_srv b)
      obtain ⟨k₀, h_can_k₀⟩ := h_can_ex
      have h_k₀_ne_i : k₀ ≠ i := by
        intro heq; subst heq; exact absurd h_can_k₀.2.1 (lt_irrefl _)
      have h_lt_k₀ : lastTerm (s.log i).dropLast < lastTerm (s.log k₀) := by
        have := h_can_k₀.2.1
        rwa [h_lastTerm_i, h_log_ne k₀ h_k₀_ne_i] at this
      -- Shared closing tactic for both cases once we have h_cp_le_k₀, h_k₀_dl
      -- (cp.index ≤ len(k₀) and logTerm(k₀, dropLast.length) = lastTerm(dropLast(i))):
      -- h_gt branch of canRollbackOplog third condition contradicts cp.index ≤ len(k₀)
      --   combined with cp.index ≥ dropLast.length > len(k₀).
      -- h_ne branch contradicts logTerm(k₀, dropLast.length) = lastTerm(dropLast(i)).
      rcases h_below with h_lt | ⟨h_eq, h_le⟩
      · -- inl: lastTerm(dropLast(i)) < cp(b).term
        -- Monotonicity forces cp.index > dropLast.length
        have h_cp_gt : (s.log i).dropLast.length < (s.commitPoint b).index := by
          by_contra h; push_neg at h
          have h_m := h_mono b _ _ h (Nat.le_of_lt h_aoe_len)
          rw [h_lt_cp, ← h_aoe_match] at h_m; omega
        rcases Nat.lt_or_ge (s.commitPoint b).term (lastTerm (s.log k₀)) with h_k₀_gt | h_k₀_le
        · obtain ⟨h_cp_le_k₀, h_agree_k₀⟩ := h_llcp k₀ b h_k₀_gt
          have h_k₀_dl : logTerm s k₀ (s.log i).dropLast.length =
              lastTerm (s.log i).dropLast :=
            (h_agree_k₀ _ (by omega) (Nat.le_of_lt h_aoe_len)).trans h_aoe_match.symm
          rcases h_can_k₀.2.2 with h_gt | ⟨_, h_ne⟩
          · rw [h_len_i, h_len_ne k₀ h_k₀_ne_i] at h_gt; omega
          · rw [h_len_i, h_lastTerm_i, lt_ne k₀ h_k₀_ne_i] at h_ne
            exact h_ne h_k₀_dl.symm
        · -- lastTerm(k₀) ≤ cp(b).term: needs additional invariant structure
          sorry
      · -- inr: lastTerm(dropLast(i)) = cp(b).term, dropLast.length ≤ cp.index
        -- h_lt_k₀ + h_eq give lastTerm(k₀) > cp(b).term directly
        have h_k₀_gt : (s.commitPoint b).term < lastTerm (s.log k₀) := h_eq ▸ h_lt_k₀
        obtain ⟨h_cp_le_k₀, h_agree_k₀⟩ := h_llcp k₀ b h_k₀_gt
        have h_k₀_dl : logTerm s k₀ (s.log i).dropLast.length =
            lastTerm (s.log i).dropLast :=
          (h_agree_k₀ _ h_le (Nat.le_of_lt h_aoe_len)).trans h_aoe_match.symm
        rcases h_can_k₀.2.2 with h_gt | ⟨_, h_ne⟩
        · rw [h_len_i, h_len_ne k₀ h_k₀_ne_i] at h_gt; omega
        · rw [h_len_i, h_lastTerm_i, lt_ne k₀ h_k₀_ne_i] at h_ne
          exact h_ne h_k₀_dl.symm
    · -- Case a ≠ i, b = i: a's log unchanged, b's log shortened
      -- Rewrite b → i everywhere
      rw [h_b] at h_aoe h_below
      -- Unfold appendOplogEnabled to extract length and match conditions
      unfold appendOplogEnabled at h_aoe
      rw [h_log_ne a h_a, h_log_i] at h_aoe
      obtain ⟨h_aoe_len, h_aoe_match⟩ := h_aoe
      -- len(a) < len(dropLast) ≤ len(original)
      have h_aoe_len_s : (s.log a).length < (s.log i).length := by
        rw [List.length_dropLast] at h_aoe_len; omega
      -- logTerm match: len(a) < len(dropLast), so logTerm s' i = logTerm s i
      have h_le_dl : (s.log a).length ≤ (s.log i).dropLast.length := by omega
      have h_aoe_match_s : lastTerm (s.log a) = logTerm s i (s.log a).length := by
        rwa [lt_drop _ h_le_dl] at h_aoe_match
      have h_aoe_s : appendOplogEnabled a i s := ⟨h_aoe_len_s, h_aoe_match_s⟩
      -- Transfer canRollbackOplog from s' to s
      have h_can_s : ∃ k, canRollbackOplog a k s := by
        obtain ⟨k, hk⟩ := h_can_ex
        by_cases h_k : k = i
        · -- k = i: canRollbackOplog a i s' is impossible here.
          -- appendOplogEnabled gives len(a) < len(dropLast) and
          -- lastTerm(a) = logTerm s i len(a). But canRollbackOplog a i s'
          -- requires either len(a) > len(dropLast) (contradicts <) or
          -- lastTerm(a) ≠ logTerm s' i len(a) = logTerm s i len(a) (contradicts =).
          exfalso
          unfold canRollbackOplog at hk
          rw [h_k, h_log_ne a h_a, h_log_i] at hk
          obtain ⟨_, _, h_third⟩ := hk
          rcases h_third with h_gt | ⟨_, h_ne⟩
          · omega
          · rw [lt_drop _ h_le_dl] at h_ne; exact absurd h_aoe_match_s h_ne
        · exact ⟨k, by
            unfold canRollbackOplog at hk ⊢
            rw [h_log_ne a h_a, h_log_ne k h_k, lt_ne k h_k] at hk
            exact hk⟩
      -- Apply h_rwss in state s
      rw [h_log_ne a h_a] at h_below
      exact h_rwss a i h_aoe_s h_can_s h_below
    · -- Case a ≠ i, b ≠ i: both logs unchanged, transfer directly
      have h_aoe_s : appendOplogEnabled a b s := by
        unfold appendOplogEnabled at h_aoe ⊢
        rw [h_log_ne a h_a, h_log_ne b h_b, lt_ne b h_b] at h_aoe
        exact h_aoe
      have h_can_s : ∃ k, canRollbackOplog a k s := by
        obtain ⟨k, hk⟩ := h_can_ex
        by_cases h_k : k = i
        · unfold canRollbackOplog at hk
          rw [h_k, h_log_ne a h_a, h_log_i] at hk
          obtain ⟨h_pos', h_lt', h_third'⟩ := hk
          -- lastTerm(a) < lastTerm(dropLast) ≤ lastTerm(original)
          have h_lt_orig : lastTerm (s.log a) < lastTerm (s.log i) :=
            lt_of_lt_of_le h_lt' h_mono_drop
          have h_third_s : (s.log a).length > (s.log i).length
              ∨ ((s.log a).length ≤ (s.log i).length
                ∧ lastTerm (s.log a) ≠ logTerm s i (s.log a).length) := by
            rcases h_third' with h_gt | ⟨h_le, h_ne⟩
            · -- len(a) > len(dropLast), so len(a) ≥ len(i)
              rw [List.length_dropLast] at h_gt
              rcases Nat.lt_or_ge (s.log i).length (s.log a).length with h_strict | h_le_i
              · exact Or.inl h_strict
              · -- len(a) = len(i): lastTerm(a) ≠ lastTerm(i) since lastTerm(a) < lastTerm(i)
                have h_eq_len : (s.log a).length = (s.log i).length := by omega
                exact Or.inr ⟨le_of_eq h_eq_len, by rw [h_eq_len]; exact ne_of_lt h_lt_orig⟩
            · -- len(a) ≤ len(dropLast) ≤ len(i)
              refine Or.inr ⟨by rw [List.length_dropLast] at h_le; omega, ?_⟩
              have h_le' : (s.log a).length ≤ (s.log i).dropLast.length := by
                rw [List.length_dropLast] at h_le; rw [List.length_dropLast]; omega
              rwa [lt_drop _ h_le'] at h_ne
          exact ⟨i, h_pos', h_lt_orig, h_third_s⟩
        · exact ⟨k, by
            unfold canRollbackOplog at hk ⊢
            rw [h_log_ne a h_a, h_log_ne k h_k, lt_ne k h_k] at hk
            exact hk⟩
      rw [h_log_ne a h_a] at h_below
      exact h_rwss a b h_aoe_s h_can_s h_below

lemma raftInvariant_becomePrimaryByMagic (i : Server) (s s' : RaftState Server) :
    raftInvariant s → becomePrimaryByMagic i s s' → raftInvariant s' := by
  -- becomePrimaryByMagic changes: state (all reset), globalCurrentTerm (+1)
  -- Unchanged: commitPoint, log
  -- Key insight: incrementing globalCurrentTerm only strengthens termsAreBounded
  -- and commitPointBounded. The log-based safety properties only depend on log
  -- and commitPoint, which are unchanged. The only subtlety is that isCommitted
  -- requires logTerm = globalCurrentTerm, which becomes harder to satisfy after
  -- the term increment — but that only makes rollbackCommitted *harder* to trigger.
  intro ⟨h_nrc, h_nrbcp, h_tb, h_cpb, h_mono, h_ctml, h_lu, h_lm,
         h_lccp, h_cpbq, h_llcp, h_cpa, h_lgt, h_ulet, h_cwb, h_cpetb, h_rsc, h_rwss⟩
    ⟨_, h_state, h_term, h_cp, h_log⟩
  have h_tb' := termsAreBounded_of_log_eq_term_ge h_log (by omega) h_tb
  refine ⟨neverRollbackCommitted_of_termsAreBounded h_tb',
    fun srv h => h_nrbcp srv ((rollbackBeforeCommitPoint_of_eq h_log h_cp).mp h),
    h_tb',
    commitPointBounded_of_cp_eq_term_ge h_cp (by omega) h_cpb,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- 5. logTermsMonotonic: log unchanged
  · exact logTermsMonotonic_of_log_eq h_log h_mono
  -- 6. currentTermMatchesLeader: vacuous — gCT' = gCT+1, no entry has term gCT+1
  · intro ldr b p _ h_len h_eq
    have h_eq_lt : logTerm s b p = s.globalCurrentTerm + 1 := by
      unfold logTerm getTerm at h_eq ⊢; rw [h_log] at h_eq; rw [h_term] at h_eq
      exact h_eq
    have h_bound := logTerm_le_globalCurrentTerm h_tb b p
    omega
  -- 7. leaderUnique: becomePrimaryByMagic sets exactly one leader
  · intro a b ha hb
    rw [h_state] at ha hb
    simp only at ha hb
    split_ifs at ha with ha_eq; split_ifs at hb with hb_eq; simp_all
  -- 8. logMatching: log unchanged
  · exact logMatching_of_log_eq h_log h_lm
  -- 9. leaderCompletenessForCommitPoints: new leader elected, log/cp unchanged
  --     Requires quorum overlap argument: the election quorum intersects with
  --     any commit quorum, so the new leader's log contains committed entries.
  · -- 9. leaderCompletenessForCommitPoints
    intro ldr srv h_ldr_s
    rw [h_state] at h_ldr_s
    -- ldr = i (only leader after becomePrimaryByMagic)
    have h_ldr_i : ldr = i := by
      simp only at h_ldr_s
      split_ifs at h_ldr_s with h; simp_all
    rw [h_ldr_i, h_cp, h_log]
    -- Convert logTerm s' to logTerm s (since s'.log = s.log)
    have h_lt_eq : ∀ a b, logTerm s' a b = logTerm s a b := by
      intro a b; simp only [logTerm, h_log]
    simp only [h_lt_eq]
    -- Get witness from commitPointsBackedByQuorums using election quorum
    obtain ⟨w, hw_mem, hw_len, hw_term⟩ :=
      cpbq_witness_in_quorum h_cpbq srv (ayeVoters i s) ‹isQuorum (ayeVoters i s)›
    -- w is an aye voter: extract the disjunction
    simp only [ayeVoters, Finset.mem_filter, Finset.mem_univ, true_and] at hw_mem
    rcases hw_mem with h_gt_w | ⟨h_eq_w, h_ge_w⟩
    · -- Case A: lastTerm(i) > lastTerm(w) ≥ cp.term → use h_llcp
      have h_gt_cp : lastTerm (s.log i) > (s.commitPoint srv).term := by omega
      exact h_llcp i srv h_gt_cp
    · -- Case B: lastTerm(i) = lastTerm(w), len(i) ≥ len(w)
      rcases Nat.lt_or_ge ((s.commitPoint srv).term) (lastTerm (s.log i)) with h_gt_cp | h_le_cp
      · -- Sub-case B1: lastTerm(i) > cp.term → use h_llcp
        exact h_llcp i srv h_gt_cp
      · -- Sub-case B2: lastTerm(i) = cp.term → use h_cpa
        have h_eq_cp : lastTerm (s.log i) = (s.commitPoint srv).term := by omega
        have h_ge_idx : (s.log i).length ≥ (s.commitPoint srv).index := by omega
        exact ⟨h_ge_idx, h_cpa i srv h_eq_cp h_ge_idx⟩
  -- 10. commitPointsBackedByQuorums: log/cp unchanged, gCT increased
  · exact commitPointsBackedByQuorums_of_log_cp_eq h_log h_cp h_cpbq
  -- 11. logsLaterThanCommitPointHaveEntries: log/cp unchanged, gCT increased
  · exact logsLaterThanCommitPointHaveEntries_of_log_cp_eq h_log h_cp h_llcp
  -- 12. commitPointAgreement: log/cp unchanged, gCT increased
  · exact commitPointAgreement_of_log_cp_eq h_log h_cp h_cpa
  -- 13. leaderLastTermGeCommitPointTerm: new leader elected
  · intro ldr srv h_ldr_s
    rw [h_state] at h_ldr_s
    -- ldr = i (only leader after election)
    have h_ldr_i : ldr = i := by
      simp only at h_ldr_s; split_ifs at h_ldr_s with h; simp_all
    rw [h_ldr_i, h_log, h_cp]
    -- From cpbq with ayeVoters quorum: ∃ w with cpTerm ≤ lastTerm(w)
    obtain ⟨w, hw_mem, _, hw_term⟩ :=
      cpbq_witness_in_quorum h_cpbq srv (ayeVoters i s) ‹isQuorum (ayeVoters i s)›
    -- w is an aye voter: lastTerm(i) ≥ lastTerm(w)
    simp only [ayeVoters, Finset.mem_filter, Finset.mem_univ,
      true_and] at hw_mem
    rcases hw_mem with h_gt_w | ⟨h_eq_w, _⟩
    · -- lastTerm(i) > lastTerm(w) ≥ cpTerm
      omega
    · -- lastTerm(i) = lastTerm(w) ≥ cpTerm
      omega
  -- 14. uniformLogEntriesInTerm: log unchanged
  · exact uniformLogEntriesInTerm_of_log_eq h_log h_ulet
  -- 15. commitPointWeaklyBelowLogTip: log/cp unchanged
  · exact commitPointWeaklyBelowLogTip_of_eq h_log h_cp h_cwb
  -- 16. commitPointEntryTermsBounded: log/cp unchanged
  · exact commitPointEntryTermsBounded_of_log_cp_eq h_log h_cp h_cpetb
  -- 17. rollbackSafeCommitPoint: log/cp unchanged
  · exact rollbackSafeCommitPoint_of_log_cp_eq h_log h_cp h_rsc
  -- 18. rollbackWithSyncSourceImpliesCommitPointBelowTip: log/cp unchanged
  · exact rollbackWithSyncSourceImpliesCommitPointBelowTip_of_log_cp_eq h_log h_cp h_rwss

lemma raftInvariant_clientWrite (i : Server) (s s' : RaftState Server) :
    raftInvariant s → clientWrite i s s' → raftInvariant s' := by
  -- clientWrite changes: log (appends entry with term = globalCurrentTerm to server i)
  -- Unchanged: globalCurrentTerm, state, commitPoint
  -- The new entry has term = globalCurrentTerm, so termsAreBounded is preserved.
  -- Safety properties: log grows (append only) for one server. Rolling back requires
  -- a strictly smaller last term — appending an entry at globalCurrentTerm cannot
  -- create new rollback opportunities (the last term can only stay the same or grow).
  intro ⟨h_nrc, h_nrbcp, h_tb, h_cpb, h_mono, h_ctml, h_lu, h_lm,
         h_lccp, h_cpbq, h_llcp, h_cpa, h_lgt, h_ulet, h_cwb, h_cpetb, h_rsc, h_rwss⟩
    ⟨h_leader, h_log, h_term, h_state, h_cp⟩
  have h_tb' : termsAreBounded s' := by
    intro srv e he
    rw [h_log] at he
    simp only [Function.update_apply] at he
    split_ifs at he with h_eq
    · rw [h_term]
      rcases List.mem_append.mp he with h_old | h_new
      · exact h_tb _ e h_old
      · simp only [List.mem_singleton] at h_new; rw [h_new]
    · rw [h_term]; exact h_tb srv e he
  -- Shared helpers: restate the logTerm/lastTerm rewriting lemmas with h_log fixed,
  -- so sub-goal proofs can reference them without re-unfolding definitions.
  -- For clientWrite, the appended entry is ⟨s.globalCurrentTerm⟩.
  have lt_ne : ∀ srv, srv ≠ i → ∀ idx, logTerm s' srv idx = logTerm s srv idx :=
    fun srv h_ne idx => logTerm_update_ne h_log h_ne idx
  have lt_old : ∀ idx, idx ≤ (s.log i).length → logTerm s' i idx = logTerm s i idx :=
    fun idx h_idx => logTerm_update_self_append_old h_log h_idx
  have lt_new : logTerm s' i ((s.log i).length + 1) = s.globalCurrentTerm :=
    logTerm_update_self_append_new h_log
  have h_lastTerm_app : lastTerm (s.log i ++ [⟨s.globalCurrentTerm⟩]) = s.globalCurrentTerm :=
    lastTerm_append_entry (s.log i) ⟨s.globalCurrentTerm⟩
  have h_new_len : (s'.log i).length = (s.log i).length + 1 :=
    length_update_self_append h_log
  have h_len_ne : ∀ srv, srv ≠ i → (s'.log srv).length = (s.log srv).length := by
    intro srv h_ne; exact length_update_ne h_log h_ne
  -- lastTerm of the new log equals globalCurrentTerm (entry term)
  have h_last_gct : lastTerm (s'.log i) = s.globalCurrentTerm := by
    have : s'.log i = s.log i ++ [⟨s.globalCurrentTerm⟩] := by
      have := congr_fun h_log i; simp at this; exact this
    rw [this, h_lastTerm_app]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- 1. neverRollbackCommitted: follows from termsAreBounded
  · exact neverRollbackCommitted_of_termsAreBounded h_tb'
  -- 2. neverRollbackBeforeCommitPoint
  · intro srv h_rbcp
    unfold rollbackBeforeCommitPoint at h_rbcp
    obtain ⟨⟨k, h_can⟩, h_below⟩ := h_rbcp
    by_cases h_srv_i : srv = i
    · -- srv = i: after appending ⟨gCT⟩, lastTerm = gCT ≥ all terms, so no rollback possible
      rw [h_srv_i] at h_can h_below
      unfold canRollbackOplog at h_can
      rw [h_log] at h_can
      simp only [Function.update_apply, ite_true] at h_can
      obtain ⟨_, h_lt, _⟩ := h_can
      by_cases h_k_i : k = i
      · -- k = i: both sides have the same list, so lastTerm X < lastTerm X is absurd
        rw [if_pos h_k_i] at h_lt
        exact absurd h_lt (lt_irrefl _)
      · -- k ≠ i: gCT = lastTerm(appended) < lastTerm(s.log k) ≤ gCT, contradiction
        rw [if_neg h_k_i] at h_lt
        rw [h_lastTerm_app] at h_lt
        have := logTerm_le_globalCurrentTerm h_tb k (s.log k).length
        unfold logTerm at this; unfold lastTerm at h_lt; omega
    · -- srv ≠ i: srv's log/cp unchanged, only i's log grew
      have h_log_srv : s'.log srv = s.log srv := by rw [h_log]; simp [h_srv_i]
      rw [h_log_srv, h_cp] at h_below
      unfold canRollbackOplog at h_can
      rw [h_log] at h_can
      simp only [Function.update_apply, if_neg h_srv_i] at h_can
      by_cases h_k_i : k = i
      · -- k = i: i's log changed to (s.log i) ++ [⟨gCT⟩]
        rw [h_k_i, if_pos rfl] at h_can
        obtain ⟨h_len_pos, h_lt_last, h_disj⟩ := h_can
        rw [h_lastTerm_app] at h_lt_last
        -- Simplify appended list length in h_disj
        simp only [List.length_append, List.length_singleton] at h_disj
        -- So lastTerm(s.log srv) < gCT
        -- Case split on h_below to derive contradiction
        rcases h_below with h_below_lt | ⟨h_below_eq, h_below_len⟩
        · -- lastTerm(s.log srv) < (s.commitPoint srv).term
          -- Try i as canRollbackOplog witness in old state
          by_cases h_lt_i : lastTerm (s.log srv) < lastTerm (s.log i)
          · -- lastTerm(srv) < lastTerm(i): i is a witness in old state
            -- Third condition: need to establish for old state
            have h_third : (s.log srv).length > (s.log i).length
                ∨ ((s.log srv).length ≤ (s.log i).length
                  ∧ lastTerm (s.log srv) ≠ logTerm s i (s.log srv).length) := by
              rcases h_disj with h_left | ⟨h_le, h_ne⟩
              · -- (s.log srv).length > (s.log i).length + 1 implies > (s.log i).length
                left; omega
              · -- (s.log srv).length ≤ (s.log i).length + 1
                rcases Nat.lt_or_ge (s.log srv).length ((s.log i).length + 1) with h_sm | h_bg
                · -- (s.log srv).length ≤ (s.log i).length
                  right
                  refine ⟨by omega, ?_⟩
                  rw [← lt_old (s.log srv).length (by omega)]; exact h_ne
                · -- (s.log srv).length = (s.log i).length + 1
                  left; omega
            exact h_nrbcp srv ⟨⟨i, h_len_pos, h_lt_i, h_third⟩, Or.inl h_below_lt⟩
          · -- lastTerm(i) ≤ lastTerm(srv): contradicts h_lgt
            -- h_lgt gives lastTerm(i) ≥ cpTerm, h_below_lt gives cpTerm > lastTerm(srv)
            have := h_lgt i srv h_leader; omega
        · -- lastTerm(s.log srv) = (s.commitPoint srv).term ∧ len(srv) ≤ cpIdx
          -- By h_lccp: cpIdx ≤ len(i), so len(srv) ≤ len(i)
          obtain ⟨h_idx_le, h_lccp_agree⟩ := h_lccp i srv h_leader
          -- len(srv) ≤ cpIdx ≤ len(i)
          have h_srv_le_i : (s.log srv).length ≤ (s.log i).length := by omega
          -- By h_lccp_agree at p = len(srv):
          -- logTerm s i len(srv) = logTerm s srv len(srv) = lastTerm(srv)
          have h_agree_at : logTerm s i (s.log srv).length = lastTerm (s.log srv) := by
            have := h_lccp_agree (s.log srv).length h_below_len (le_refl _)
            unfold logTerm at this; unfold lastTerm; exact this
          -- The third condition requires lastTerm(srv) ≠ logTerm s' i len(srv)
          -- But logTerm s' i len(srv) = logTerm s i len(srv) = lastTerm(srv). Contradiction!
          rcases h_disj with h_left | ⟨h_le, h_ne⟩
          · -- len(srv) > len(i) + 1, but len(srv) ≤ len(i). Contradiction.
            omega
          · -- lastTerm(srv) ≠ logTerm s' i len(srv)
            rw [lt_old (s.log srv).length h_srv_le_i, h_agree_at] at h_ne
            exact absurd rfl h_ne
      · -- k ≠ i: both logs unchanged, canRollbackOplog transfers directly
        simp only [if_neg h_k_i] at h_can
        simp only [lt_ne k h_k_i] at h_can
        exact h_nrbcp srv ⟨⟨k, h_can⟩, h_below⟩
  -- 3. termsAreBounded
  · exact h_tb'
  -- 4. commitPointBounded: commitPoint unchanged, globalCurrentTerm unchanged
  · intro srv; rw [h_cp, h_term]; exact h_cpb srv
  -- 5. logTermsMonotonic: for server i, the appended entry has term = gCT ≥ all
  --    existing terms (by termsAreBounded). For other servers, log unchanged.
  · exact logTermsMonotonic_append_entry h_log h_mono h_tb
  -- 6. currentTermMatchesLeader: state/gCT unchanged, leader i's log grew by ⟨gCT⟩
  --    By leaderUnique, ldr = i. If b = ldr, h_eq gives the answer directly.
  --    If b ≠ ldr, use old h_ctml + termsAreBounded.
  · intro ldr b p h_ldr h_len h_eq
    rw [h_state] at h_ldr
    -- ldr = i by leader uniqueness; rewrite goal from ldr to i
    have h_li : ldr = i := h_lu ldr i h_ldr h_leader
    rw [h_li]
    by_cases h_b_eq : b = i
    · -- b = i = ldr: h_eq says logTerm s' i p = s'.gCT, which is our goal
      rw [h_b_eq] at h_eq; exact h_eq
    · -- b ≠ i: b's log unchanged
      rw [h_term]
      -- Translate h_eq to old state using shared helpers
      have h_eq_s : logTerm s b p = s.globalCurrentTerm := by
        rw [← lt_ne b h_b_eq, ← h_term]; exact h_eq
      have h_len_s : p ≤ (s.log b).length := by
        rwa [h_len_ne b h_b_eq] at h_len
      -- By old h_ctml: logTerm s i p = gCT
      have h_old := h_ctml i b p h_leader h_len_s h_eq_s
      -- Transfer to new state: case on p vs old log length
      rcases Nat.lt_or_ge p ((s.log i).length + 1) with h_small | h_big
      · -- p ≤ old length: logTerm s' i p = logTerm s i p
        rw [lt_old p (by omega)]; exact h_old
      · -- p > old length: logTerm s i p = 0, so gCT = 0
        have h_oob : logTerm s i p = 0 := by
          unfold logTerm getTerm; split; · omega
          · next h_ne =>
            rw [List.getElem?_eq_none (by omega)]
        rw [h_old] at h_oob
        have := logTerm_le_globalCurrentTerm h_tb' i p
        rw [h_term] at this; omega
  -- 7. leaderUnique: state unchanged
  · exact leaderUnique_of_state_eq h_state h_lu
  -- 8. logMatching: i's log grows by ⟨gCT⟩, all others unchanged.
  --    Hard case: p = oldLen+1 (new entry position) and logTerm s' b p = gCT.
  --    By currentTermMatchesLeader, logTerm s i p = gCT. But p > oldLen so
  --    logTerm s i p = 0, giving gCT = 0. All terms are 0 → trivial agreement.
  · intro a b p h_len_a h_len_b h_eq q h_qp
    -- Case split on whether a or b is i
    by_cases h_a : a = i <;> by_cases h_b : b = i
    · -- a = i, b = i: trivial
      rw [h_a, h_b]
    · -- a = i, b ≠ i
      rw [h_a] at h_len_a h_eq ⊢
      -- Translate b's logTerm to old state
      rw [lt_ne b h_b] at h_eq
      rw [lt_ne b h_b]
      -- Derive old-state length bounds
      have h_len_b_s : p ≤ (s.log b).length := by
        rw [h_len_ne b h_b] at h_len_b; exact h_len_b
      -- Case on p ≤ oldLen vs p = oldLen + 1
      rcases Nat.lt_or_ge p ((s.log i).length + 1) with h_small | h_big
      · -- p ≤ oldLen: logTerm s' i p = logTerm s i p
        rw [lt_old p (by omega)] at h_eq
        rw [lt_old q (by omega)]
        exact h_lm i b p (by omega) h_len_b_s h_eq q h_qp
      · -- p ≥ oldLen + 1, but p ≤ (s'.log i).length = oldLen + 1, so p = oldLen + 1
        have h_p : p = (s.log i).length + 1 := by rw [h_new_len] at h_len_a; omega
        -- logTerm s' i p = gCT (the new entry)
        have h_lt_i : logTerm s' i p = s.globalCurrentTerm := h_p ▸ lt_new
        -- h_eq: gCT = logTerm s b p
        rw [h_lt_i] at h_eq
        -- By currentTermMatchesLeader: logTerm s i p = gCT
        -- But p = oldLen + 1 > (s.log i).length, so logTerm s i p = 0 → gCT = 0
        have h_old_i : logTerm s i p = s.globalCurrentTerm :=
          h_ctml i b p h_leader h_len_b_s h_eq.symm
        have h_oob : logTerm s i p = 0 := by
          unfold logTerm getTerm; rw [h_p]
          simp only [show (s.log i).length + 1 ≠ 0 from by omega, ↓reduceIte]
          rw [List.getElem?_eq_none (by omega)]
        -- gCT = 0
        have h_gct_zero : s.globalCurrentTerm = 0 := by omega
        -- All entry terms are 0, so all logTerm values at valid positions are 0
        have all_zero : ∀ (srv : Server) (idx : Nat),
            idx ≤ (s.log srv).length → logTerm s srv idx = 0 := by
          intro srv idx h_idx
          rcases Nat.eq_zero_or_pos idx with h_z | h_pos
          · rw [h_z]; unfold logTerm getTerm; simp
          · unfold logTerm getTerm
            simp only [show idx ≠ 0 from by omega, ↓reduceIte]
            rcases h_opt : (s.log srv)[idx - 1]? with _ | entry
            · rfl
            · simp only
              have h_mem := List.mem_of_getElem? h_opt
              have := h_tb srv entry h_mem
              omega
        -- Both sides are 0. logTerm s' b q = logTerm s b q = 0.
        -- logTerm s' i q: if q ≤ oldLen, use lt_old + all_zero;
        -- if q = oldLen+1 = p, logTerm s' i q = gCT = 0.
        have h_b_zero : logTerm s b q = 0 :=
          all_zero b q (by omega)
        rcases Nat.lt_or_ge q ((s.log i).length + 1) with h_q_sm | h_q_bg
        · rw [lt_old q (by omega), all_zero i q (by omega), h_b_zero]
        · -- q ≥ oldLen+1 and q ≤ p = oldLen+1, so q = p
          have h_q_p : q = p := by omega
          rw [h_q_p, h_lt_i, h_eq]
    · -- a ≠ i, b = i: symmetric to the previous case
      rw [h_b] at h_len_b h_eq ⊢
      rw [lt_ne a h_a] at h_eq
      rw [lt_ne a h_a]
      -- Derive old-state length bounds
      have h_len_a_s : p ≤ (s.log a).length := by
        rw [h_len_ne a h_a] at h_len_a; exact h_len_a
      rcases Nat.lt_or_ge p ((s.log i).length + 1) with h_small | h_big
      · rw [lt_old p (by omega)] at h_eq
        rw [lt_old q (by omega)]
        exact h_lm a i p h_len_a_s (by omega) h_eq q h_qp
      · have h_p : p = (s.log i).length + 1 := by rw [h_new_len] at h_len_b; omega
        have h_lt_i : logTerm s' i p = s.globalCurrentTerm := h_p ▸ lt_new
        rw [h_lt_i] at h_eq
        have h_old_i : logTerm s i p = s.globalCurrentTerm :=
          h_ctml i a p h_leader h_len_a_s h_eq
        have h_oob : logTerm s i p = 0 := by
          unfold logTerm getTerm; rw [h_p]
          simp only [show (s.log i).length + 1 ≠ 0 from by omega, ↓reduceIte]
          rw [List.getElem?_eq_none (by omega)]
        have h_gct_zero : s.globalCurrentTerm = 0 := by omega
        have all_zero : ∀ (srv : Server) (idx : Nat),
            idx ≤ (s.log srv).length → logTerm s srv idx = 0 := by
          intro srv idx h_idx
          rcases Nat.eq_zero_or_pos idx with h_z | h_pos
          · rw [h_z]; unfold logTerm getTerm; simp
          · unfold logTerm getTerm
            simp only [show idx ≠ 0 from by omega, ↓reduceIte]
            rcases h_opt : (s.log srv)[idx - 1]? with _ | entry
            · rfl
            · simp only
              have h_mem := List.mem_of_getElem? h_opt
              have := h_tb srv entry h_mem
              omega
        have h_a_zero : logTerm s a q = 0 :=
          all_zero a q (by omega)
        rcases Nat.lt_or_ge q ((s.log i).length + 1) with h_q_sm | h_q_bg
        · rw [h_a_zero, lt_old q (by omega), all_zero i q (by omega)]
        · have h_q_p : q = p := by omega
          rw [h_q_p, h_lt_i, h_eq]
    · -- a ≠ i, b ≠ i: both logs unchanged
      rw [lt_ne a h_a] at h_eq ⊢
      rw [lt_ne b h_b] at h_eq ⊢
      have h_len_a_s : p ≤ (s.log a).length := by
        rw [h_len_ne a h_a] at h_len_a; exact h_len_a
      have h_len_b_s : p ≤ (s.log b).length := by
        rw [h_len_ne b h_b] at h_len_b; exact h_len_b
      exact h_lm a b p h_len_a_s h_len_b_s h_eq q h_qp
  -- 9. leaderCompletenessForCommitPoints: log i grew by ⟨gCT⟩, state/cp unchanged
  · intro ldr srv h_ldr_s
    rw [h_state] at h_ldr_s
    have h_li : ldr = i := h_lu ldr i h_ldr_s h_leader
    rw [h_li] at h_ldr_s ⊢
    obtain ⟨h_idx_le, h_agree⟩ := h_lccp i srv h_leader
    have h_cp_eq : s'.commitPoint srv = s.commitPoint srv := by rw [h_cp]
    constructor
    · -- cpIndex(srv) ≤ len(s'.log i) = len(s.log i) + 1
      rw [h_cp_eq]; omega
    · intro p h_p_cp h_p_len
      rw [h_cp_eq] at h_p_cp
      have h_p_old : p ≤ (s.log i).length := by omega
      by_cases h_srv : srv = i
      · subst h_srv; rw [lt_old p h_p_old]
      · rw [lt_old p h_p_old, lt_ne srv h_srv]
        exact h_agree p h_p_cp (by rwa [h_len_ne srv h_srv] at h_p_len)
  -- 10. commitPointsBackedByQuorums: log i grew by ⟨gCT⟩, cp unchanged
  -- Same Q₀: all members have len ≥ cpIdx, so positions ≤ cpIdx are in prefix.
  · intro srv
    obtain ⟨Q₀, hQ₀, hcover₀, hagree₀⟩ := h_cpbq srv
    refine ⟨Q₀, hQ₀, fun n hn => ?_, fun n₁ n₂ hn₁ hn₂ p hp => ?_⟩
    · obtain ⟨hlen, hterm, hlt⟩ := hcover₀ n hn
      rw [h_cp]; refine ⟨?_, ?_, ?_⟩
      · -- cpIdx ≤ len(s'.log n): use h_new_len for n = i, h_len_ne otherwise
        by_cases h_n : n = i
        · subst h_n; rw [h_new_len]; omega
        · rw [h_len_ne n h_n]; exact hlen
      · -- cpTerm ≤ lastTerm(s'.log n): use h_last_gct for n = i, lastTerm_update_ne otherwise
        by_cases h_n : n = i
        · subst h_n; rw [h_last_gct]; exact h_cpb srv
        · rw [lastTerm_update_ne h_log h_n]; exact hterm
      · -- logTerm s' n cp.index = cp.term: in prefix
        have lt_pres_n : logTerm s' n (s.commitPoint srv).index =
            logTerm s n (s.commitPoint srv).index := by
          by_cases h_n : n = i
          · subst h_n; exact lt_old _ hlen
          · exact lt_ne n h_n _
        rw [lt_pres_n]; exact hlt
    · rw [h_cp] at hp
      have lt_pres : ∀ m, m ∈ Q₀ → logTerm s' m p = logTerm s m p := by
        intro m hm
        have hlen_m := (hcover₀ m hm).1
        by_cases h_m : m = i
        · subst h_m; exact lt_old p (by omega)
        · exact lt_ne m h_m p
      rw [lt_pres n₁ hn₁, lt_pres n₂ hn₂]
      exact hagree₀ n₁ n₂ hn₁ hn₂ p hp
  -- 11. logsLaterThanCommitPointHaveEntries: log i grew by ⟨gCT⟩, cp unchanged
  · intro a b h_gt
    rw [h_cp] at h_gt ⊢
    by_cases h_a : a = i
    · -- a = i: lastTerm(s'.log i) = gCT (shared h_last_gct)
      rw [h_a] at h_gt ⊢
      rw [h_last_gct] at h_gt
      -- h_lgt: lastTerm(s.log i) ≥ cpTerm(b)
      have h_ge := h_lgt i b h_leader
      obtain ⟨h_idx_le, _⟩ := h_lccp i b h_leader
      rcases Nat.eq_or_lt_of_le h_ge with h_eq | h_strict
      · -- cpTerm(b) = lastTerm(s.log i): use h_lccp and h_cpa
        constructor
        · -- cpIndex(b) ≤ len(s'.log i)
          omega
        · intro p h_p_cp h_p_log
          rw [lt_old p (by omega)]
          by_cases h_b : b = i
          · -- a = b = i: both sides reduce to logTerm s i p
            rw [h_b, lt_old p (by omega)]
          · rw [lt_ne b h_b]
            exact h_cpa i b h_eq.symm h_idx_le p h_p_cp
              (by rwa [h_len_ne b h_b] at h_p_log)
      · -- cpTerm(b) < lastTerm(s.log i): apply h_llcp directly
        obtain ⟨h_len, h_agree⟩ := h_llcp i b h_strict
        constructor
        · omega
        · intro p h_p_cp h_p_log
          rw [lt_old p (by omega)]
          by_cases h_b : b = i
          · -- a = b = i: both sides reduce to logTerm s i p
            rw [h_b, lt_old p (by omega)]
          · rw [lt_ne b h_b]
            exact h_agree p h_p_cp (by rwa [h_len_ne b h_b] at h_p_log)
    · -- a ≠ i: log a unchanged
      rw [lastTerm_update_ne h_log h_a] at h_gt
      obtain ⟨h_len, h_agree⟩ := h_llcp a b h_gt
      constructor
      · rwa [h_len_ne a h_a]
      · intro p h_p_cp h_p_log
        rw [lt_ne a h_a]
        by_cases h_b : b = i
        · obtain ⟨h_cpb_le_i, _⟩ := h_lccp i b h_leader
          have h_p_old : p ≤ (s.log i).length := by omega
          subst h_b; rw [lt_old p h_p_old]
          exact h_agree p h_p_cp h_p_old
        · rw [lt_ne b h_b]
          exact h_agree p h_p_cp (by rwa [h_len_ne b h_b] at h_p_log)
  -- 12. commitPointAgreement: log i grew by ⟨gCT⟩, cp unchanged
  · intro a b h_lt h_len p h_p_cp h_p_log
    rw [h_cp] at h_p_cp h_lt h_len
    obtain ⟨h_cpb_le, h_lccp_agree⟩ := h_lccp i b h_leader
    have h_p_le_i : p ≤ (s.log i).length := by omega
    -- Both logTerms reduce to s version since p ≤ len(s.log i)
    have lt_eq : ∀ srv, logTerm s' srv p = logTerm s srv p := fun srv => by
      by_cases h : srv = i
      · subst h; exact lt_old p h_p_le_i
      · exact lt_ne srv h p
    rw [lt_eq a, lt_eq b]
    have h_p_log_s : p ≤ (s.log b).length := by
      by_cases h_b : b = i
      · subst h_b; exact h_p_le_i
      · rwa [h_len_ne b h_b] at h_p_log
    by_cases h_a : a = i
    · subst h_a; exact h_lccp_agree p h_p_cp h_p_log_s
    · rw [lastTerm_update_ne h_log h_a] at h_lt
      rw [h_len_ne a h_a] at h_len
      exact h_cpa a b h_lt h_len p h_p_cp h_p_log_s
  -- 13. leaderLastTermGeCommitPointTerm: state/cp unchanged, log i grew
  · intro ldr srv h_ldr_s
    rw [h_state] at h_ldr_s; rw [h_cp]
    have h_ldr_i : ldr = i := h_lu ldr i h_ldr_s h_leader
    -- lastTerm(s'.log i) = gCT (shared h_last_gct) ≥ cpTerm(srv) by commitPointBounded
    rw [h_ldr_i, h_last_gct]; exact h_cpb srv
  -- 14. uniformLogEntriesInTerm: i's log grew by ⟨gCT⟩
  · -- The new entry has term = gCT. By termsAreBounded, no existing entry has
    -- term > gCT. So gCT is either already present or is new. If it's new, its
    -- first occurrence is at len(old)+1 in i's log. No other server can have
    -- gCT at an earlier position (by the old invariant applied to j's log which
    -- also has gCT entries via currentTermMatchesLeader). If gCT already exists
    -- in i's log, the new entry at len+1 is not a "first occurrence" so the
    -- precondition is vacuous.
    intro a b ip j h_ip1 h_ipa h_j1 h_jb h_eq h_ne_zero h_first
    -- Proof: case split on whether a or b is the writing server i.
    -- - If neither: both logs unchanged, apply old invariant.
    -- - If a = i with ip in old prefix: translate to old state, apply old invariant.
    -- - If a = i with ip = len+1 (new entry, term = gCT): by currentTermMatchesLeader,
    --   gCT in any server's log implies gCT in i's old log—contradicting first-occurrence.
    -- - If b = i with j in old prefix: translate to old state, apply old invariant.
    -- - If b = i with j = len+1: by currentTermMatchesLeader, logTerm s i ip = gCT,
    --   so ip ≤ len(old) < j.
    by_cases h_a : a = i <;> by_cases h_b : b = i
    · -- a = i, b = i: both indices in the same extended log
      subst a; subst b
      rcases Nat.lt_or_ge ip ((s.log i).length + 1) with h_ip_old | h_ip_new
      · -- ip within old prefix
        rcases Nat.lt_or_ge j ((s.log i).length + 1) with h_j_old | h_j_new
        · -- j also in old prefix: convert to old state, apply h_ulet
          have h_eq' : logTerm s i ip = logTerm s i j := by
            rwa [lt_old ip (by omega), lt_old j (by omega)] at h_eq
          have h_ne' : logTerm s i ip ≠ 0 := by
            rwa [lt_old ip (by omega)] at h_ne_zero
          have h_first' : ∀ k, 1 ≤ k → k < ip → logTerm s i k ≠ logTerm s i ip := by
            intro k hk1 hki; have := h_first k hk1 hki
            rwa [lt_old k (by omega), lt_old ip (by omega)] at this
          exact h_ulet i i ip j h_ip1 (by omega) h_j1 (by omega) h_eq' h_ne' h_first'
        · -- j at new position (len+1): j > ip since ip ≤ len(old)
          omega
      · -- ip at new position (len+1): first occurrence of gCT at end of i's log
        have h_ip_eq : ip = (s.log i).length + 1 := by omega
        subst h_ip_eq
        -- If j < len+1, then logTerm s' i j = logTerm s' i (len+1) contradicts h_first
        rcases Nat.lt_or_ge j ((s.log i).length + 1) with h_j_old | h_j_new
        · exfalso; exact h_first j h_j1 h_j_old h_eq.symm
        · omega
    · -- a = i, b ≠ i: a's log extended, b's log unchanged
      subst a
      rcases Nat.lt_or_ge ip ((s.log i).length + 1) with h_ip_old | h_ip_new
      · -- ip within old prefix: convert to old state, apply h_ulet
        have h_eq' : logTerm s i ip = logTerm s b j := by
          rwa [lt_old ip (by omega), lt_ne b h_b] at h_eq
        have h_ne' : logTerm s i ip ≠ 0 := by
          rwa [lt_old ip (by omega)] at h_ne_zero
        have h_first' : ∀ k, 1 ≤ k → k < ip → logTerm s i k ≠ logTerm s i ip := by
          intro k hk1 hki; have := h_first k hk1 hki
          rwa [lt_old k (by omega), lt_old ip (by omega)] at this
        exact h_ulet i b ip j h_ip1 (by omega) h_j1
          (by rwa [h_len_ne b h_b] at h_jb) h_eq' h_ne' h_first'
      · -- ip at new position: gCT doesn't appear in any other server's log
        -- (by currentTermMatchesLeader: gCT in b's log → gCT in i's old log,
        -- but h_first says gCT is absent from i's old log)
        have h_ip_eq : ip = (s.log i).length + 1 := by omega
        subst h_ip_eq
        exfalso
        rw [lt_new] at h_eq
        -- h_eq: gCT = logTerm s' b j. Convert to old state.
        have h_eq_b : logTerm s b j = s.globalCurrentTerm := by
          rw [← lt_ne b h_b]; exact h_eq.symm
        have h_jb_s : j ≤ (s.log b).length := by rwa [h_len_ne b h_b] at h_jb
        -- By currentTermMatchesLeader: logTerm s i j = gCT
        have h_ctml_j := h_ctml i b j h_leader h_jb_s h_eq_b
        rcases Nat.lt_or_ge j ((s.log i).length + 1) with h_j_le | h_j_gt
        · -- j ≤ len(old): logTerm s' i j = logTerm s i j = gCT, contradicts h_first
          exact h_first j h_j1 h_j_le
            ((lt_old j (by omega)).trans (h_ctml_j.trans lt_new.symm))
        · -- j > len(old): logTerm s i j = 0 → gCT = 0, contradicts h_ne_zero
          have h_oob : logTerm s i j = 0 := by
            unfold logTerm getTerm
            simp only [show j ≠ 0 from by omega, ↓reduceIte]
            rw [List.getElem?_eq_none (by omega)]
          rw [h_oob] at h_ctml_j
          rw [lt_new] at h_ne_zero
          exact h_ne_zero h_ctml_j.symm
    · -- a ≠ i, b = i: a's log unchanged, b's log extended
      subst b
      rcases Nat.lt_or_ge j ((s.log i).length + 1) with h_j_old | h_j_new
      · -- j within old prefix: convert to old state, apply h_ulet
        have h_eq' : logTerm s a ip = logTerm s i j := by
          rwa [lt_ne a h_a, lt_old j (by omega)] at h_eq
        have h_ne' : logTerm s a ip ≠ 0 := by
          rwa [lt_ne a h_a] at h_ne_zero
        have h_first' : ∀ k, 1 ≤ k → k < ip → logTerm s a k ≠ logTerm s a ip := by
          intro k hk1 hki; have := h_first k hk1 hki
          rwa [lt_ne a h_a, lt_ne a h_a] at this
        exact h_ulet a i ip j h_ip1 (by rwa [h_len_ne a h_a] at h_ipa)
          h_j1 (by omega) h_eq' h_ne' h_first'
      · -- j at new position (len+1): need j ≥ ip
        -- logTerm s a ip = gCT, so by currentTermMatchesLeader, logTerm s i ip = gCT,
        -- hence ip ≤ len(s.log i) < j.
        have h_j_eq : j = (s.log i).length + 1 := by omega
        subst h_j_eq
        rw [lt_new, lt_ne a h_a] at h_eq
        -- h_eq: logTerm s a ip = gCT
        have h_ipa_s : ip ≤ (s.log a).length := by rwa [h_len_ne a h_a] at h_ipa
        have h_ctml_ip := h_ctml i a ip h_leader h_ipa_s h_eq
        -- gCT in i's old log at position ip, so ip ≤ len(s.log i)
        have h_ip_le_i : ip ≤ (s.log i).length := by
          by_contra h_gt; push_neg at h_gt
          have : logTerm s i ip = 0 := by
            unfold logTerm getTerm
            simp only [show ip ≠ 0 from by omega, ↓reduceIte]
            rw [List.getElem?_eq_none (by omega)]
          have := lt_ne a h_a ip; omega
        -- j = len(s.log i) + 1 > ip
        omega
    · -- a ≠ i, b ≠ i: both logs unchanged, apply old invariant directly
      have h_eq' : logTerm s a ip = logTerm s b j := by
        rwa [lt_ne a h_a, lt_ne b h_b] at h_eq
      have h_ne' : logTerm s a ip ≠ 0 := by
        rwa [lt_ne a h_a] at h_ne_zero
      have h_first' : ∀ k, 1 ≤ k → k < ip → logTerm s a k ≠ logTerm s a ip := by
        intro k hk1 hki; have := h_first k hk1 hki
        rwa [lt_ne a h_a, lt_ne a h_a] at this
      exact h_ulet a b ip j h_ip1 (by rwa [h_len_ne a h_a] at h_ipa) h_j1
        (by rwa [h_len_ne b h_b] at h_jb) h_eq' h_ne' h_first'
  -- 15. commitPointWeaklyBelowLogTip: cp unchanged, log i grew by ⟨gCT⟩
  · intro srv
    rw [h_cp]
    by_cases h_eq : srv = i
    · subst h_eq
      -- lastTerm(s'.log srv) = gCT (shared h_last_gct); length grew by 1 (shared h_new_len)
      have h_old_le : lastTerm (s.log srv) ≤ s.globalCurrentTerm := by
        have := logTerm_le_globalCurrentTerm h_tb srv (s.log srv).length
        unfold logTerm at this; exact this
      rcases h_cwb srv with h_lt | ⟨h_eq_t, h_le⟩
      · left; rw [h_last_gct]; omega
      · rcases Nat.lt_or_ge (s.commitPoint srv).term s.globalCurrentTerm with h1 | h2
        · left; rw [h_last_gct]; exact h1
        · right; exact ⟨by rw [h_last_gct]; omega, by rw [h_new_len]; omega⟩
    · have : s'.log srv = s.log srv := by rw [h_log]; simp [h_eq]
      rw [this]; exact h_cwb srv
  -- 16. commitPointEntryTermsBounded: cp unchanged, log i grew by ⟨gCT⟩
  · -- Same pattern as appendOplog: positions ≤ cp.index are in unchanged prefix
    intro b p hp hpl
    rw [h_cp] at hp
    by_cases h_b : b = i
    · subst h_b
      have h_cp_le : (s.commitPoint b).index ≤ (s.log b).length := by
        rcases h_cwb b with h_lt | ⟨_, h_le⟩
        · exact (h_llcp b b h_lt).1
        · exact h_le
      have hpl_old : p ≤ (s.log b).length := by omega
      rw [lt_old p hpl_old, h_cp]; exact h_cpetb b p hp hpl_old
    · rw [lt_ne b h_b, h_cp]
      exact h_cpetb b p hp (by rwa [h_len_ne b h_b] at hpl)
  -- 17. rollbackSafeCommitPoint: cp unchanged, log i grew by ⟨gCT⟩
  --   For srv = i: dropLast of appended log = original log, use h_cwb.
  --   For srv ≠ i, k ≠ i: transfer canRollbackOplog to s, use h_rsc.
  --   For srv ≠ i, k = i: if lastTerm(i) > lastTerm(srv), transfer witness.
  --     Otherwise prove directly: logTerm(srv, cpIdx) = cpTerm via cpbq quorum,
  --     cpIdx < len(srv), then monotonicity gives cpTerm ≤ lastTerm(dropLast).
  · intro srv ⟨k, h_can⟩
    rw [h_cp]
    by_cases h_srv_i : srv = i
    · -- srv = i: (s'.log i).dropLast = s.log i
      subst h_srv_i
      have h_log_srv : s'.log srv = s.log srv ++ [⟨s.globalCurrentTerm⟩] := by rw [h_log]; simp
      rw [h_log_srv]
      simp only [List.dropLast_concat]
      rcases h_cwb srv with h_lt | ⟨h_eq_t, _⟩
      · exact Nat.le_of_lt h_lt
      · exact Nat.le_of_eq h_eq_t
    · -- srv ≠ i: logs unchanged
      have h_log_srv : s'.log srv = s.log srv := by rw [h_log]; simp [h_srv_i]
      rw [h_log_srv]
      by_cases h_k_i : k = i
      · -- k = i: i's log grew by ⟨gCT⟩
        have h_log_i : s'.log i = s.log i ++ [⟨s.globalCurrentTerm⟩] := by rw [h_log]; simp
        unfold canRollbackOplog at h_can
        rw [h_k_i, h_log_srv, h_log_i] at h_can
        obtain ⟨h_pos, h_lt_last, h_div⟩ := h_can
        rw [h_lastTerm_app] at h_lt_last
        simp only [List.length_append, List.length_singleton] at h_div
        -- lastTerm(s.log srv) < gCT
        by_cases h_lt_i : lastTerm (s.log srv) < lastTerm (s.log i)
        · -- Use i as canRollbackOplog witness in state s
          have h_third : (s.log srv).length > (s.log i).length
              ∨ ((s.log srv).length ≤ (s.log i).length
                ∧ lastTerm (s.log srv) ≠ logTerm s i (s.log srv).length) := by
            rcases h_div with h_left | ⟨h_le, h_ne⟩
            · left; omega
            · rcases Nat.lt_or_ge (s.log srv).length ((s.log i).length + 1) with h_sm | h_bg
              · right; refine ⟨by omega, ?_⟩
                rw [← lt_old (s.log srv).length (by omega)]; exact h_ne
              · left; omega
          exact h_rsc srv ⟨i, h_pos, h_lt_i, h_third⟩
        · -- lastTerm(i) ≤ lastTerm(srv): prove cp.term ≤ lastTerm(dropLast) directly
          push_neg at h_lt_i
          -- cpIdx ≤ len(srv)
          have h_cp_le_srv : (s.commitPoint srv).index ≤ (s.log srv).length := by
            rcases h_cwb srv with h_cwb_lt | ⟨_, h_cwb_le⟩
            · exact (h_llcp srv srv h_cwb_lt).1
            · exact h_cwb_le
          -- logTerm(srv, cpIdx) = cp.term via cpbq quorum
          have h_srv_eq := logTerm_at_commitPoint_eq_term s srv h_cpbq h_llcp h_cpa h_cp_le_srv
          -- cpIdx < len(srv)
          have h_cp_strict : (s.commitPoint srv).index < (s.log srv).length := by
            rcases h_cwb srv with h_cwb_lt | ⟨h_cwb_eq, h_cwb_le⟩
            · -- cp.term < lastTerm(srv): cpIdx = len would give lastTerm = cp.term, contradiction
              by_contra h_not
              push_neg at h_not
              have h_eq : (s.commitPoint srv).index = (s.log srv).length :=
                Nat.le_antisymm h_cp_le_srv h_not
              rw [h_eq] at h_srv_eq
              unfold logTerm at h_srv_eq; unfold lastTerm at h_cwb_lt
              omega
            · -- cp.term = lastTerm(srv): cpIdx = len makes canRollbackOplog impossible
              by_contra h_not
              push_neg at h_not
              have h_eq_idx : (s.commitPoint srv).index = (s.log srv).length :=
                Nat.le_antisymm h_cwb_le h_not
              obtain ⟨h_idx_le_i, h_lccp_agree⟩ := h_lccp i srv h_leader
              rw [h_eq_idx] at h_idx_le_i
              rcases h_div with h_left | ⟨h_le_div, h_ne_div⟩
              · omega
              · rcases Nat.lt_or_ge (s.log srv).length ((s.log i).length + 1) with h_sm | h_bg
                · have h_agree_at := h_lccp_agree (s.log srv).length (by omega) (le_refl _)
                  rw [lt_old (s.log srv).length (by omega), h_agree_at] at h_ne_div
                  exact absurd rfl h_ne_div
                · omega
          -- By monotonicity: cp.term ≤ lastTerm(dropLast(srv))
          have h_lastTerm_dl : lastTerm (s.log srv).dropLast =
              logTerm s srv (s.log srv).dropLast.length := by
            unfold lastTerm logTerm getTerm
            split
            · rfl
            · next h_ne =>
              congr 1
              rw [List.getElem?_dropLast]
              rw [if_pos (by rw [List.length_dropLast] at h_ne ⊢; omega)]
          rw [h_lastTerm_dl, ← h_srv_eq]
          exact h_mono srv _ _ (by rw [List.length_dropLast]; omega)
            (by rw [List.length_dropLast]; omega)
      · -- k ≠ i: both logs unchanged, transfer directly
        have h_log_k : s'.log k = s.log k := by rw [h_log]; simp [h_k_i]
        have h_can_s : canRollbackOplog srv k s := by
          unfold canRollbackOplog logTerm getTerm at h_can ⊢
          rw [h_log_srv, h_log_k] at h_can
          exact h_can
        exact h_rsc srv ⟨k, h_can_s⟩
  -- 18. rollbackWithSyncSourceImpliesCommitPointBelowTip
  -- Proof: case split on a = i and b = i. clientWrite appends ⟨gCT⟩ to i's log.
  -- Key insight: i is Leader, so lastTerm(s'.log i) = gCT = max possible term.
  -- Case a=i: canRollbackOplog impossible (gCT can't be < any lastTerm).
  -- Case a≠i,b=i: appendOplogEnabled a i s' contradicts canRollbackOplog a i s',
  --   so witness k ≠ i, transfer to s. Sub-case len(a)=len(i) uses h_nrbcp.
  -- Case a≠i,b≠i: if k=i, either use i as witness in s (lastTerm(a)< lastTerm(i)),
  --   or use h_lgt + h_lccp to contradict h_below directly.
  · intro a b h_aoe h_can_ex h_below
    rw [h_cp] at h_below
    by_cases h_a : a = i <;> by_cases h_b : b = i
    · -- Case a = i, b = i: appendOplogEnabled i i s' requires len < len, impossible
      subst h_a; subst h_b; exact Nat.lt_irrefl _ h_aoe.1
    · -- Case a = i, b ≠ i: canRollbackOplog i k s' impossible
      -- lastTerm(s'.log i) = gCT and all terms ≤ gCT by h_tb'
      subst h_a
      obtain ⟨k, hk⟩ := h_can_ex
      have h_lt_k := hk.2.1
      rw [h_last_gct] at h_lt_k
      have : lastTerm (s'.log k) ≤ s.globalCurrentTerm := by
        have := logTerm_le_globalCurrentTerm h_tb' k (s'.log k).length
        rw [h_term] at this; unfold logTerm at this; exact this
      omega
    · -- Case a ≠ i, b = i: a's log unchanged, b's log grew
      rw [h_b] at h_aoe h_below
      have h_log_a : s'.log a = s.log a := by
        have := congr_fun h_log a; simp only [Function.update_apply, if_neg h_a] at this; exact this
      unfold appendOplogEnabled at h_aoe
      rw [h_log_a, h_new_len] at h_aoe
      obtain ⟨h_aoe_len, h_aoe_match⟩ := h_aoe
      rw [h_log_a] at h_below
      -- appendOplogEnabled a i s' contradicts canRollbackOplog a i s':
      -- aoe: len(a) < len(i)+1, lastTerm(a) = logTerm s' i len(a)
      -- cro: len(a) > len(i)+1 (impossible) or lastTerm(a) ≠ logTerm s' i len(a) (contradicts)
      have h_can_s : ∃ k, canRollbackOplog a k s := by
        obtain ⟨k, hk⟩ := h_can_ex
        have h_k_ne : k ≠ i := by
          intro heq; subst heq
          rcases hk.2.2 with h_gt | ⟨_, h_ne⟩
          · rw [h_log_a, h_new_len] at h_gt; omega
          · rw [h_log_a] at h_ne; exact h_ne h_aoe_match
        exact ⟨k, by
          unfold canRollbackOplog at hk ⊢
          rw [h_log_a, show s'.log k = s.log k from by rw [h_log]; simp [h_k_ne],
              lt_ne k h_k_ne] at hk
          exact hk⟩
      rcases Nat.lt_or_ge (s.log a).length (s.log i).length with h_lt_i | h_ge_i
      · -- len(a) < len(i): transfer appendOplogEnabled to s, apply h_rwss
        exact h_rwss a i ⟨h_lt_i, by rwa [lt_old _ (Nat.le_of_lt h_lt_i)] at h_aoe_match⟩
          h_can_s h_below
      · -- len(a) = len(i): lastTerm(a) = lastTerm(i), transfer canRollbackOplog to i
        have h_eq_len : (s.log a).length = (s.log i).length := by omega
        have h_lt_eq : lastTerm (s.log a) = lastTerm (s.log i) := by
          rw [h_aoe_match, h_eq_len, lt_old _ (le_refl _)]
          unfold logTerm lastTerm; rfl
        obtain ⟨k₀, h_can_k₀⟩ := h_can_s
        have h_can_i : ∃ k, canRollbackOplog i k s := by
          obtain ⟨h1, h2, h3⟩ := h_can_k₀
          refine ⟨k₀, by omega, by omega, ?_⟩
          rcases h3 with h3l | ⟨h3a, h3b⟩
          · exact Or.inl (by omega)
          · exact Or.inr ⟨by omega, by rw [h_eq_len, h_lt_eq] at h3b; exact h3b⟩
        apply h_nrbcp i
        unfold rollbackBeforeCommitPoint
        refine ⟨h_can_i, ?_⟩
        rcases h_cwb i with h_lt_cwb | ⟨h_eq_cwb, h_le_cwb⟩
        · rcases h_below with h1 | ⟨h2, _⟩ <;> omega
        · rcases h_below with h1 | ⟨_, h_le_idx⟩
          · omega
          · exact Or.inr ⟨h_eq_cwb.symm, by omega⟩
    · -- Case a ≠ i, b ≠ i: both logs unchanged
      have h_aoe_s : appendOplogEnabled a b s := by
        unfold appendOplogEnabled at h_aoe ⊢
        rw [h_log] at h_aoe; simp [h_a, h_b, lt_ne b h_b] at h_aoe; exact h_aoe
      have h_log_a : s'.log a = s.log a := by rw [h_log]; simp [h_a]
      rw [h_log_a] at h_below
      obtain ⟨k, hk⟩ := h_can_ex
      by_cases h_k : k = i
      · -- k = i: i's log grew by ⟨gCT⟩
        unfold canRollbackOplog at hk
        rw [h_log_a] at hk
        have h_log_k : s'.log k = s.log i ++ [⟨s.globalCurrentTerm⟩] := by
          rw [h_k]; have := congr_fun h_log i; simp at this; exact this
        rw [h_log_k] at hk
        obtain ⟨h_pos, h_lt_last, h_third⟩ := hk
        rw [h_lastTerm_app] at h_lt_last
        simp only [List.length_append, List.length_singleton] at h_third
        -- lastTerm(a) < gCT. h_lgt: cp(b).term ≤ lastTerm(i).
        by_cases h_lt_i : lastTerm (s.log a) < lastTerm (s.log i)
        · -- Use i as canRollbackOplog witness in state s
          have h_third_s : (s.log a).length > (s.log i).length
              ∨ ((s.log a).length ≤ (s.log i).length
                ∧ lastTerm (s.log a) ≠ logTerm s i (s.log a).length) := by
            rcases h_third with h_left | ⟨h_le, h_ne⟩
            · left; omega
            · rcases Nat.lt_or_ge (s.log a).length ((s.log i).length + 1) with h_sm | h_bg
              · right; refine ⟨by omega, ?_⟩
                rw [h_k] at h_ne; rw [← lt_old (s.log a).length (by omega)]; exact h_ne
              · left; omega
          exact h_rwss a b h_aoe_s ⟨i, h_pos, h_lt_i, h_third_s⟩ h_below
        · -- lastTerm(i) ≤ lastTerm(a): cp(b).term ≤ lastTerm(i) ≤ lastTerm(a)
          push_neg at h_lt_i
          have h_lgt_b := h_lgt i b h_leader
          rcases h_below with h_lt_below | ⟨h_eq_below, h_le_below⟩
          · -- lastTerm(a) < cp(b).term: impossible since cp(b).term ≤ lastTerm(a)
            omega
          · -- lastTerm(a) = cp(b).term ∧ len(a) ≤ cp(b).index
            -- cp(b).term = lastTerm(a) = lastTerm(i) (all equal)
            obtain ⟨h_cp_le_i, h_lccp_agree⟩ := h_lccp i b h_leader
            rcases h_third with h_gt_third | ⟨h_le_third, h_ne_third⟩
            · -- len(a) > len(i)+1: cp(b).index ≤ len(i) < len(a), contradiction
              omega
            · rcases Nat.lt_or_ge (s.log a).length ((s.log i).length + 1) with h_sm | h_bg
              · -- len(a) ≤ len(i): use h_lccp agreement to contradict h_ne_third
                have h_le_i : (s.log a).length ≤ (s.log i).length := by omega
                -- logTerm s' i len(a) = logTerm s i len(a) (in old prefix)
                rw [h_k] at h_ne_third
                have h_lt_old_eq : logTerm s' i (s.log a).length =
                    logTerm s i (s.log a).length := lt_old _ h_le_i
                rw [h_lt_old_eq] at h_ne_third
                -- h_lccp_agree: logTerm i len(a) = logTerm b len(a)
                have h_agree := h_lccp_agree (s.log a).length h_le_below
                  (by have := h_aoe_s.1; omega)
                -- appendOplogEnabled: lastTerm(a) = logTerm b len(a)
                -- So logTerm i len(a) = lastTerm(a), contradicts h_ne_third
                exact absurd (h_aoe_s.2.trans h_agree.symm) h_ne_third
              · -- len(a) = len(i)+1: cp(b).index ≤ len(i) < len(a), contradiction
                omega
      · -- k ≠ i: transfer directly
        exact h_rwss a b h_aoe_s ⟨k, by
          unfold canRollbackOplog at hk ⊢
          rw [h_log_a, show s'.log k = s.log k from by rw [h_log]; simp [h_k],
              lt_ne k h_k] at hk; exact hk⟩ h_below

lemma raftInvariant_advanceCommitPoint (s s' : RaftState Server) :
    raftInvariant s → advanceCommitPoint s s' → raftInvariant s' := by
  -- advanceCommitPoint changes: commitPoint (for one leader)
  -- Unchanged: globalCurrentTerm, state, log
  intro ⟨h_nrc, h_nrbcp, h_tb, h_cpb, h_mono, h_ctml, h_lu, h_lm,
         h_lccp, h_cpbq, h_llcp, h_cpa, h_lgt, h_ulet, h_cwb, h_cpetb, h_rsc, h_rwss⟩
    ⟨leader, h_leader, h_comm, h_cp, h_term, h_state, h_log⟩
  -- logTerm is unchanged since logs are identical
  have lt_eq : ∀ srv p, logTerm s' srv p = logTerm s srv p :=
    fun srv p => by unfold logTerm getTerm; rw [h_log]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- 1. neverRollbackCommitted: log and globalCurrentTerm unchanged
  · exact neverRollbackCommitted_of_termsAreBounded
      (termsAreBounded_of_log_eq_term_ge h_log (by omega) h_tb)
  -- 2. neverRollbackBeforeCommitPoint: log unchanged, commitPoint changed.
  --    Key insight: advanceCommitPoint requires isCommitted, which means
  --    logTerm(leader, len(log[leader])) = globalCurrentTerm.
  --    For any server whose commit point changed (only the leader):
  --    canRollbackOplog requires lastTerm < some other lastTerm, but the leader's
  --    lastTerm = globalCurrentTerm (from isCommitted), and termsAreBounded says
  --    all terms ≤ globalCurrentTerm. So canRollbackOplog is false for the leader.
  --    For all other servers, commitPoint unchanged, so use IH.
  · intro srv h_rbcp
    unfold rollbackBeforeCommitPoint at h_rbcp
    obtain ⟨⟨j_rb, h_can_rb⟩, h_below⟩ := h_rbcp
    -- canRollbackOplog uses only log, which is unchanged
    rw [canRollbackOplog_of_log_eq h_log] at h_can_rb
    -- Check if srv = leader or not
    by_cases h_eq : srv = leader
    · -- srv = leader: the commit point changed to (lastTerm(log[leader]), len(log[leader]))
      -- canRollbackOplog leader j_rb s requires lastTerm(log[leader]) < lastTerm(log[j_rb])
      -- But isCommitted requires logTerm(leader, len(log[leader])) = globalCurrentTerm
      -- i.e., lastTerm(log[leader]) = globalCurrentTerm.
      -- And termsAreBounded gives lastTerm(log[j_rb]) ≤ globalCurrentTerm.
      -- So lastTerm(log[leader]) < lastTerm(log[j_rb]) is impossible.
      subst h_eq
      unfold canRollbackOplog at h_can_rb
      obtain ⟨_, h_lt, _⟩ := h_can_rb
      -- From isCommitted: logTerm = globalCurrentTerm, i.e., lastTerm = globalCurrentTerm
      unfold isCommitted at h_comm
      obtain ⟨_, h_eq_term⟩ := h_comm
      -- h_eq_term : logTerm s leader (s.log leader).length = s.globalCurrentTerm
      -- logTerm at length = lastTerm
      unfold logTerm at h_eq_term
      -- h_lt : lastTerm (s.log leader) < lastTerm (s.log j_rb)
      -- lastTerm (s.log j_rb) ≤ globalCurrentTerm by termsAreBounded
      have h_bound := logTerm_le_globalCurrentTerm h_tb j_rb (s.log j_rb).length
      unfold logTerm at h_bound
      -- lastTerm = getTerm at length, and h_eq_term says getTerm = globalCurrentTerm
      unfold lastTerm at h_lt
      omega
    · -- srv ≠ leader: commitPoint unchanged
      have h_cp_srv : s'.commitPoint srv = s.commitPoint srv := by
        rw [h_cp]; simp [h_eq]
      -- Reconstruct rollbackBeforeCommitPoint for the old state
      have : rollbackBeforeCommitPoint s srv := by
        unfold rollbackBeforeCommitPoint
        exact ⟨⟨j_rb, h_can_rb⟩, by rwa [h_log, h_cp_srv] at h_below⟩
      exact h_nrbcp srv this
  -- 3. termsAreBounded: log and globalCurrentTerm unchanged
  · exact termsAreBounded_of_log_eq_term_ge h_log (by omega) h_tb
  -- 4. commitPointBounded: the new commit point has term = lastTerm(log[leader])
  --    which is ≤ globalCurrentTerm by termsAreBounded.
  · intro srv
    rw [h_cp]
    simp only [Function.update_apply]
    split
    · -- srv = leader: new commit point term = lastTerm(s.log leader)
      -- lastTerm is logTerm at length, which is ≤ globalCurrentTerm
      rw [h_term]
      exact logTerm_le_globalCurrentTerm h_tb leader (s.log leader).length
    · -- srv ≠ leader: commitPoint unchanged
      rw [h_term]
      exact h_cpb srv
  -- 5. logTermsMonotonic: log unchanged
  · exact logTermsMonotonic_of_log_eq h_log h_mono
  -- 6. currentTermMatchesLeader: log, state, gCT unchanged
  · exact currentTermMatchesLeader_of_log_state_eq h_log h_state h_term h_ctml
  -- 7. leaderUnique: state unchanged
  · exact leaderUnique_of_state_eq h_state h_lu
  -- 8. logMatching: log unchanged
  · exact logMatching_of_log_eq h_log h_lm
  -- 9. leaderCompletenessForCommitPoints: log/state unchanged, commitPoint changed
  · intro ldr srv h_ldr_s
    rw [h_state] at h_ldr_s
    -- By leaderUnique, ldr = leader
    have h_ll : ldr = leader := h_lu ldr leader h_ldr_s h_leader
    rw [h_ll]
    by_cases h_srv : srv = leader
    · -- srv = leader: new cp = (lastTerm(log leader), len(log leader))
      rw [h_srv]
      have h_cp_eq : s'.commitPoint leader = ⟨lastTerm (s.log leader), (s.log leader).length⟩ := by
        rw [h_cp]; simp
      rw [h_cp_eq]
      exact ⟨by rw [congr_fun h_log], fun _ _ _ => rfl⟩
    · -- srv ≠ leader: cp unchanged
      have h_cp_eq : s'.commitPoint srv = s.commitPoint srv := by rw [h_cp]; simp [h_srv]
      obtain ⟨h_idx, h_agree⟩ := h_lccp leader srv h_leader
      rw [h_cp_eq]
      refine ⟨by rw [congr_fun h_log]; exact h_idx, ?_⟩
      intro p h_p_cp h_p_len
      rw [lt_eq, lt_eq]
      exact h_agree p h_p_cp (by rw [congr_fun h_log] at h_p_len; exact h_p_len)
  -- 10. commitPointsBackedByQuorums: log unchanged, cp changed for leader
  · intro srv
    by_cases h_srv : srv = leader
    · -- srv = leader: new cp = (lastTerm(log leader), len(log leader))
      -- Use agree set as Q₀: all members have len ≥ len(leader) and agree pairwise
      rw [h_srv]
      have h_cp_eq : s'.commitPoint leader =
          ⟨lastTerm (s.log leader), (s.log leader).length⟩ := by
        rw [h_cp]; simp
      rw [h_cp_eq]
      obtain ⟨h_agree_q, h_gct⟩ := h_comm
      refine ⟨agree s leader (s.log leader).length, h_agree_q,
        fun n hn => ?_, fun n₁ n₂ hn₁ hn₂ p hp => ?_⟩
      · -- Coverage: every agree member has len ≥ len(leader) and lastTerm ≥ lastTerm(leader)
        simp only [agree, Finset.mem_filter, Finset.mem_univ, true_and] at hn
        obtain ⟨hn_len, hn_eq⟩ := hn
        refine ⟨?_, ?_, ?_⟩
        · rw [h_log]; dsimp only; exact hn_len
        · rw [h_log]; dsimp only
          -- logTerm leader len = logTerm n len (by hn_eq), and
          -- lastTerm(leader) = logTerm leader len, logTerm n len ≤ lastTerm(n)
          have h1 : logTerm s n (s.log leader).length = lastTerm (s.log leader) :=
            hn_eq.symm
          have h2 := h_mono n (s.log leader).length (s.log n).length hn_len (le_refl _)
          have h3 : logTerm s n (s.log n).length = lastTerm (s.log n) := rfl
          omega
        · -- logTerm s' n len(leader) = lastTerm(leader)
          -- By hn_eq: logTerm s leader len = logTerm s n len
          -- By lt_eq: logTerm s' n len = logTerm s n len
          rw [lt_eq]; exact hn_eq.symm
      · -- Pairwise agreement: all agree members agree with leader at ≤ len(leader),
        -- hence agree pairwise via logMatching
        dsimp only at hp
        simp only [agree, Finset.mem_filter, Finset.mem_univ, true_and] at hn₁ hn₂
        obtain ⟨hn₁_len, hn₁_eq⟩ := hn₁
        obtain ⟨hn₂_len, hn₂_eq⟩ := hn₂
        rw [lt_eq, lt_eq]
        have h1 := h_lm leader n₁ (s.log leader).length (le_refl _) hn₁_len hn₁_eq p hp
        have h2 := h_lm leader n₂ (s.log leader).length (le_refl _) hn₂_len hn₂_eq p hp
        exact h1.symm.trans h2
    · -- srv ≠ leader: cp unchanged, logs unchanged → old Q₀ works
      have h_cp_eq : s'.commitPoint srv = s.commitPoint srv := by
        rw [h_cp]; simp [h_srv]
      obtain ⟨Q₀, hQ₀, hcover₀, hagree₀⟩ := h_cpbq srv
      refine ⟨Q₀, hQ₀, fun n hn => ?_, fun n₁ n₂ hn₁ hn₂ p hp => ?_⟩
      · obtain ⟨hlen, hterm, hlt⟩ := hcover₀ n hn
        exact ⟨by rw [h_cp_eq, h_log]; exact hlen,
          by rw [h_cp_eq, h_log]; exact hterm,
          by rw [h_cp_eq, lt_eq]; exact hlt⟩
      · rw [lt_eq, lt_eq]
        exact hagree₀ n₁ n₂ hn₁ hn₂ p (by rw [h_cp_eq] at hp; exact hp)
  -- 11. logsLaterThanCommitPointHaveEntries: log unchanged, cp changed for leader
  · intro a b h_gt
    by_cases h_b : b = leader
    · -- b = leader: new cp.term = lastTerm(log leader) = gCT (by isCommitted)
      -- But h_gt says lastTerm(log a) > cp.term, i.e., lastTerm(log a) > gCT.
      -- This contradicts termsAreBounded: lastTerm(log a) ≤ gCT.
      rw [h_b] at h_gt ⊢
      have h_cp_eq : s'.commitPoint leader =
          ⟨lastTerm (s.log leader), (s.log leader).length⟩ := by
        rw [h_cp]; simp
      rw [h_cp_eq] at h_gt ⊢; dsimp only at h_gt ⊢; rw [h_log] at h_gt
      obtain ⟨_, h_eq_gct⟩ := h_comm
      have h_bound := logTerm_le_globalCurrentTerm h_tb a (s.log a).length
      unfold logTerm at h_eq_gct h_bound; unfold lastTerm at h_gt
      omega
    · -- b ≠ leader: cp unchanged
      have h_cp_eq : s'.commitPoint b = s.commitPoint b := by
        rw [h_cp]; simp [h_b]
      rw [h_cp_eq] at h_gt ⊢; rw [h_log] at h_gt
      obtain ⟨hlen, hagree⟩ := h_llcp a b h_gt
      refine ⟨by rw [h_log]; exact hlen, fun p hp hpl => ?_⟩
      rw [lt_eq, lt_eq]
      exact hagree p hp (by rw [h_log] at hpl; exact hpl)
  -- 12. commitPointAgreement: log unchanged, cp changed for leader
  · intro a b h_lt h_len p hp hpl
    rw [lt_eq, lt_eq]
    by_cases h_b : b = leader
    · -- b = leader: new cp = (lastTerm(log leader), len(log leader))
      subst h_b
      rw [h_cp] at h_lt h_len hp
      simp only [Function.update_apply, ite_true] at h_lt h_len hp
      rw [h_log] at h_lt h_len hpl
      obtain ⟨_, h_gct⟩ := h_comm
      -- lastTerm(a) = gCT
      have h_lt_a : lastTerm (s.log a) = s.globalCurrentTerm := by
        unfold logTerm at h_gct; rw [← h_gct]; exact h_lt
      -- Case split on gCT = 0 vs gCT > 0
      by_cases h_gct_zero : s.globalCurrentTerm = 0
      · -- gCT = 0: all logTerms ≤ 0 (by termsAreBounded), so both sides are 0
        have h1 := logTerm_le_globalCurrentTerm h_tb a p
        have h2 := logTerm_le_globalCurrentTerm h_tb b p
        omega
      · -- gCT > 0: show len(a) = len(b), then use logMatching
        -- logTerm a (len a) = lastTerm(a) = gCT
        have h_lt_at_len : logTerm s a (s.log a).length = s.globalCurrentTerm := by
          unfold logTerm lastTerm at h_lt_a; exact h_lt_a
        -- len(a) ≤ len(b): by contradiction, if len(a) > len(b),
        -- currentTermMatchesLeader gives logTerm(b, len(a)) = gCT,
        -- but len(a) > len(b) means logTerm is out of bounds = 0,
        -- contradicting gCT > 0.
        have h_len_le : (s.log a).length ≤ (s.log b).length := by
          by_contra h_gt
          push_neg at h_gt
          have h_ctml_app := h_ctml b a (s.log a).length h_leader (le_refl _) h_lt_at_len
          have : logTerm s b (s.log a).length = 0 := by
            unfold logTerm getTerm
            split
            · omega
            · next h_ne => rw [List.getElem?_eq_none (by omega)]
          omega
        -- len(a) ≥ len(b) from h_len, combined with h_len_le gives equality
        have h_len_eq : (s.log a).length = (s.log b).length := by omega
        -- logTerm a (len b) = logTerm a (len a) = gCT = logTerm b (len b)
        -- So logMatching at len(b) gives agreement at all p ≤ len(b)
        have h_lt_match : logTerm s a (s.log b).length = logTerm s b (s.log b).length := by
          have h_a_eq : logTerm s a (s.log b).length = s.globalCurrentTerm := by
            rw [← h_len_eq]; exact h_lt_at_len
          have h_b_eq : logTerm s b (s.log b).length = s.globalCurrentTerm := by
            unfold logTerm; exact h_gct
          omega
        exact h_lm a b (s.log b).length (by omega) (le_refl _) h_lt_match p hp
    · -- b ≠ leader: cp unchanged
      rw [h_cp] at h_lt h_len hp
      simp only [Function.update_apply, if_neg h_b] at h_lt h_len hp
      rw [h_log] at h_lt h_len hpl
      exact h_cpa a b h_lt h_len p hp hpl
  -- 13. leaderLastTermGeCommitPointTerm: log/state unchanged, cp changed for leader
  · intro ldr srv h_ldr_s
    rw [h_state] at h_ldr_s; rw [h_log, h_cp]
    simp only [Function.update_apply]
    split
    · -- srv = leader: new cp = (lastTerm(log leader), len(log leader))
      -- Need lastTerm(ldr) ≥ lastTerm(log leader).
      -- But ldr is Leader, and leader is Leader, so ldr = leader by leaderUnique.
      have h_eq : ldr = leader := h_lu ldr leader h_ldr_s h_leader
      subst h_eq; simp
    · -- srv ≠ leader: cp unchanged
      exact h_lgt ldr srv h_ldr_s
  -- 14. uniformLogEntriesInTerm: log unchanged
  · exact uniformLogEntriesInTerm_of_log_eq h_log h_ulet
  -- 15. commitPointWeaklyBelowLogTip: log unchanged, cp changed for leader
  · intro srv
    rw [h_cp, h_log]
    simp only [Function.update_apply]
    by_cases h_srv : srv = leader
    · -- srv = leader: new cp = (lastTerm(log leader), len(log leader))
      -- Right disjunct: term = lastTerm and index ≤ length
      simp [h_srv]
    · -- srv ≠ leader: cp unchanged
      simp [h_srv]
      exact h_cwb srv
  -- 16. commitPointEntryTermsBounded: log unchanged, cp changed for leader
  · -- For b = leader: new cp = (lastTerm(log leader), len(log leader)).
    --   logTerm(b, p) ≤ lastTerm(log b) = cp'.term by monotonicity.
    -- For b ≠ leader: cp and log unchanged, use h_cpetb.
    intro b p hp hpl
    by_cases h_b : b = leader
    · subst h_b
      have h_cp_eq : s'.commitPoint b =
          ⟨lastTerm (s.log b), (s.log b).length⟩ := by
        rw [h_cp]; simp
      rw [h_cp_eq] at hp ⊢; dsimp only at hp ⊢
      rw [h_log] at hpl
      -- logTerm s b p ≤ lastTerm(s.log b) by monotonicity
      unfold logTerm getTerm lastTerm at *; rw [h_log]
      exact h_mono b p (s.log b).length (by omega) (by omega)
    · have h_cp_eq : s'.commitPoint b = s.commitPoint b := by
        rw [h_cp]; simp [h_b]
      rw [h_cp_eq] at hp; rw [h_log] at hpl
      rw [lt_eq, h_cp_eq]; exact h_cpetb b p hp hpl
  -- 17. rollbackSafeCommitPoint: log unchanged, cp changed for leader
  · intro srv ⟨k, h_can⟩
    rw [h_cp, h_log]
    simp only [Function.update_apply]
    split_ifs with h_eq
    · -- srv = leader: canRollbackOplog requires lastTerm(log_srv) < lastTerm(log_k).
      -- But leader's lastTerm ≥ all cp terms (h_lgt), and from h_tb all lastTerms
      -- ≤ gCT. Actually, the leader can't be rolled back: its lastTerm = gCT
      -- (from h_ctml), so no server has a strictly higher lastTerm.
      subst h_eq
      exfalso
      have h_can_s := (canRollbackOplog_of_log_eq h_log).mp h_can
      obtain ⟨_, h_lt_term, _⟩ := h_can_s
      have := logTerm_le_globalCurrentTerm h_tb k (s.log k).length
      unfold lastTerm at h_lt_term
      -- leader's lastTerm = gCT from h_comm, contradicting h_lt_term and this
      have h_comm_term := h_comm.2
      unfold logTerm at h_comm_term this
      omega
    · -- srv ≠ leader: cp unchanged
      exact h_rsc srv ⟨k, (canRollbackOplog_of_log_eq h_log).mp h_can⟩
  -- 18. rollbackWithSyncSourceImpliesCommitPointBelowTip
  -- Proof: logs unchanged, only leader's cp changes to ⟨lastTerm(log leader), len(log leader)⟩.
  -- Case b ≠ leader: cp unchanged, transfer from h_rwss.
  -- Case b = leader: leader's lastTerm = gCT (from h_comm), so canRollbackOplog a k
  --   gives lastTerm(log a) < lastTerm(log k) ≤ gCT = lastTerm(log leader).
  --   The new cp.term = lastTerm(log leader) > lastTerm(log a), so the "below"
  --   condition holds — we must derive contradiction.
  · intro a b h_aoe h_can_ex h_below
    rw [h_cp] at h_below
    have h_aoe_s : appendOplogEnabled a b s :=
      (appendOplogEnabled_of_log_eq h_log).mp h_aoe
    have h_can_s : ∃ k, canRollbackOplog a k s := by
      obtain ⟨k, hk⟩ := h_can_ex
      exact ⟨k, (canRollbackOplog_of_log_eq h_log).mp hk⟩
    rw [h_log] at h_below
    by_cases h_b : b = leader
    · -- Case b = leader: new cp = ⟨lastTerm(log leader), len(log leader)⟩
      subst h_b
      simp at h_below
      -- Strategy: show canRollbackOplog is impossible when syncing from a leader
      -- whose lastTerm = gCT. The leader can't be rolled back (lastTerm = gCT = max),
      -- so we use h_rwss on the old state to get the contradiction.
      --
      -- Step 1: leader's lastTerm = gCT
      have h_comm_term : logTerm s b (s.log b).length = s.globalCurrentTerm := h_comm.2
      -- Step 2: from canRollbackOplog a k s, get lastTerm(a) < lastTerm(k)
      obtain ⟨k, h_can_k⟩ := h_can_s
      obtain ⟨h_pos, h_lt_term, h_third⟩ := h_can_k
      -- Step 3: lastTerm(k) ≤ gCT
      have h_k_bound := logTerm_le_globalCurrentTerm h_tb k (s.log k).length
      -- Step 4: so lastTerm(a) < gCT = lastTerm(b)
      have h_lt_gct : lastTerm (s.log a) < s.globalCurrentTerm := by
        unfold lastTerm at h_lt_term ⊢; unfold logTerm at h_k_bound h_comm_term; omega
      -- Step 5: appendOplogEnabled gives lastTerm(a) = logTerm b (len a)
      have ⟨h_aoe_len, h_aoe_match⟩ := h_aoe_s
      -- Step 6: case split on third condition of canRollbackOplog
      rcases h_third with h_len_gt | ⟨h_len_le, h_ne⟩
      · -- len(a) > len(k): use h_rwss with original cp
        -- UNPROVABLE: the h1 subcase below requires proving the OLD cp(b) is
        -- "above" a's log tip, but nothing in the current invariant guarantees
        -- that. The old cp can be vacuously low (e.g. ⟨0, 0⟩), making h_rwss
        -- trivially true in the old state but useless for deriving False.
        --
        -- Counterexample (5 servers {a, b, k, c, d}, gCT = 3):
        --   b (leader): log = [1, 1, 1, 3], cp = ⟨0, 0⟩
        --   a:          log = [1, 1],        cp = ⟨0, 0⟩
        --   k:          log = [2],           cp = ⟨0, 0⟩
        --   c, d:       log = [1, 1, 1, 3], cp = ⟨0, 0⟩
        -- All 18 invariant components hold. advanceCommitPoint sets cp(b) = ⟨3, 4⟩.
        -- New h_rwss asks ¬(1 < 3 ∨ ...) = False. Invariant violated.
        -- The old h_rwss held vacuously: ¬(1 < 0 ∨ ...) = ¬False = True.
        --
        -- Root cause: advanceCommitPoint can jump the leader's cp from a
        -- vacuously low value to its log tip in one step, but h_rwss for
        -- the old state has no "teeth" when the old cp is below all log tips.
        --
        -- Fix: strengthen the invariant so the old cp(leader) is already high
        -- enough. Two options:
        --   (1) New invariant: appendOplogEnabled a b ∧ state(b) = Leader →
        --       ¬∃k, canRollbackOplog a k. This makes the b = leader case
        --       contradictory before reaching this point.
        --   (2) Strengthen existing: when state(b) = Leader, ensure
        --       cp(b).term = lastTerm(b). Then h_rwss on the old state would
        --       have lastTerm(a) < cp(b).term = lastTerm(b), giving the left
        --       disjunct directly.
        exact h_rwss a b h_aoe_s ⟨k, h_pos, h_lt_term, Or.inl h_len_gt⟩
          (by rcases h_below with h1 | ⟨h2, h3⟩
              · sorry -- BLOCKED: see counterexample above
              · -- lastTerm(a) = lastTerm(b) contradicts h_lt_gct since lastTerm(b) = gCT
                exfalso; unfold lastTerm at h2 h_lt_gct; unfold logTerm at h_comm_term; omega
          )
      · -- len(a) ≤ len(k) and lastTerm(a) ≠ logTerm k (len(a))
        -- UNPROVABLE: same root cause as the Or.inl case above.
        -- Counterexample: same as above but k's log = [2, 2] (len=2 ≥ 2=len(a)),
        -- so Or.inr fires: len(a)=2 ≤ 2=len(k) and lastTerm(a)=1 ≠ 2=logTerm(k,2).
        -- Sorry goal is still 1 < 0 ∨ (1 = 0 ∧ 2 ≤ 0) = False.
        exact h_rwss a b h_aoe_s ⟨k, h_pos, h_lt_term, Or.inr ⟨h_len_le, h_ne⟩⟩
          (by rcases h_below with h1 | ⟨h2, h3⟩
              · sorry -- BLOCKED: see counterexample above and in this branch
              · -- lastTerm(a) = lastTerm(b) contradicts h_lt_gct since lastTerm(b) = gCT
                exfalso; unfold lastTerm at h2 h_lt_gct; unfold logTerm at h_comm_term; omega
          )
    · -- Case b ≠ leader: cp unchanged
      simp [h_b] at h_below
      exact h_rwss a b h_aoe_s h_can_s h_below

/- ----------------------------------------------------------------
   Helper lemmas for learnCommitPointFromSyncSource (sorry'd)
   ---------------------------------------------------------------- -/

-- When j's commit point term strictly exceeds i's last term (the "clamped" branch of
-- learnCommitPointFromSyncSource), the clamped commit point ⟨lastTerm(log i), len(log i)⟩
-- is backed by a quorum. The quorum backing j's CP (cpbq j) is the witness: every member n
-- has lastTerm(log n) ≥ cp(j).term > lastTerm(log i), and from logsLaterThanCommitPointHaveEntries
-- and logMatching we get len(log i) ≤ len(log n) and logTerm n len(log i) = lastTerm(log i).
lemma clampedCommitPointBackedByQuorum
    {Server : Type} [Fintype Server] [DecidableEq Server]
    (s : RaftState Server) (i j : Server)
    (_h_lm : logMatching s)
    (h_cpbq : commitPointsBackedByQuorums s)
    (h_llcp : logsLaterThanCommitPointHaveEntries s)
    (h_cwb : commitPointWeaklyBelowLogTip s)
    (h_mono : logTermsMonotonic s)
    (h_cpa : commitPointAgreement s)
    (h_len : (s.log i).length < (s.log j).length)
    (h_match : lastTerm (s.log i) = logTerm s j (s.log i).length)
    (h_cp_higher : lastTerm (s.log i) < (s.commitPoint j).term) :
    ∃ Q : Finset Server, isQuorum Q ∧
      (∀ n, n ∈ Q →
        (s.log i).length ≤ (s.log n).length ∧
        lastTerm (s.log i) ≤ lastTerm (s.log n) ∧
        logTerm s n (s.log i).length = lastTerm (s.log i)) ∧
      (∀ n₁ n₂, n₁ ∈ Q → n₂ ∈ Q →
        ∀ p, p ≤ (s.log i).length → logTerm s n₁ p = logTerm s n₂ p) := by
  -- Witness: the quorum Q from cpbq(j).
  obtain ⟨Q, hQ, hcover_j, hagree_j⟩ := h_cpbq j
  -- Step 1: cp(j).index ≤ len(log j)
  have h_cp_le_j : (s.commitPoint j).index ≤ (s.log j).length := by
    rcases h_cwb j with h_lt | ⟨_, h_le⟩
    · exact (h_llcp j j h_lt).1
    · exact h_le
  -- Step 2: logTerm j cp(j).index = cp(j).term
  have h_j_at_cp : logTerm s j (s.commitPoint j).index = (s.commitPoint j).term :=
    logTerm_at_commitPoint_eq_term s j h_cpbq h_llcp h_cpa h_cp_le_j
  -- Step 3: len(log i) ≤ cp(j).index (by contradiction using monotonicity)
  -- If len(log i) > cp(j).index, then by logTermsMonotonic on j:
  --   cp(j).term = logTerm j cp(j).index ≤ logTerm j len(log i) = lastTerm(log i)
  -- contradicting h_cp_higher.
  have h_len_le_cp : (s.log i).length ≤ (s.commitPoint j).index := by
    by_contra h_neg
    push_neg at h_neg
    have := h_mono j (s.commitPoint j).index (s.log i).length (by omega) (by omega)
    rw [h_j_at_cp, ← h_match] at this; omega
  -- Step 4: every Q member agrees with j at positions ≤ cp(j).index
  have h_n_agrees_j : ∀ n, n ∈ Q →
      ∀ p, p ≤ (s.commitPoint j).index → logTerm s n p = logTerm s j p := by
    intro n hn p hp
    obtain ⟨hlen_n, hterm_n, hlt_n⟩ := hcover_j n hn
    rcases Nat.lt_or_ge (s.commitPoint j).term (lastTerm (s.log n)) with h_gt | h_le
    · -- lastTerm(log n) > cp(j).term: use h_llcp
      exact (h_llcp n j h_gt).2 p hp (by omega)
    · -- lastTerm(log n) = cp(j).term: use commitPointAgreement
      have h_eq : lastTerm (s.log n) = (s.commitPoint j).term := Nat.le_antisymm h_le hterm_n
      exact h_cpa n j h_eq (by omega) p hp (by omega)
  -- Construct the witness
  refine ⟨Q, hQ, fun n hn => ?_, fun n₁ n₂ hn₁ hn₂ p hp => ?_⟩
  · obtain ⟨hlen_n, hterm_n, _⟩ := hcover_j n hn
    refine ⟨by omega, by omega, ?_⟩
    rw [h_n_agrees_j n hn _ h_len_le_cp]
    exact h_match.symm
  · -- Q members agree up to cp(j).index ≥ len(log i)
    exact hagree_j n₁ n₂ hn₁ hn₂ p (by omega)

-- When the clamped CP ⟨lastTerm(log i), len(log i)⟩ is valid (cp(j).term > lastTerm(log i))
-- and server a has lastTerm(log a) > lastTerm(log i), then a's log covers all of i's entries.
-- Proof sketch: clampedCommitPointBackedByQuorum gives a quorum Q where every member n has
-- logTerm n len(log i) = lastTerm(log i). Since lastTerm(log a) > lastTerm(log i), a has
-- entries in a later term; by log matching against a quorum member, a agrees with i up to
-- len(log i).
lemma logCoverageWhenLastTermExceedsClampedCP
    {Server : Type} [Fintype Server] [DecidableEq Server]
    (s : RaftState Server) (a i j : Server)
    (h_lm : logMatching s)
    (h_cpbq : commitPointsBackedByQuorums s)
    (h_llcp : logsLaterThanCommitPointHaveEntries s)
    (h_cwb : commitPointWeaklyBelowLogTip s)
    (h_mono : logTermsMonotonic s)
    (h_cpa : commitPointAgreement s)
    (h_len : (s.log i).length < (s.log j).length)
    (h_match : lastTerm (s.log i) = logTerm s j (s.log i).length)
    (h_cp_higher : lastTerm (s.log i) < (s.commitPoint j).term)
    (h_gt : lastTerm (s.log a) > lastTerm (s.log i))
    (h_no_rollback : ¬canRollbackOplog i a s) :
    (s.log i).length ≤ (s.log a).length ∧
    ∀ p, p ≤ (s.log i).length → logTerm s a p = logTerm s i p := by
  -- Step 1: i agrees with j up to len(log i) via logMatching + h_match
  have h_ij : ∀ p, p ≤ (s.log i).length → logTerm s i p = logTerm s j p :=
    h_lm i j _ (le_refl _) (by omega) h_match
  -- Step 2: cp(j).idx ≤ len(log j)
  have h_cp_le_j : (s.commitPoint j).index ≤ (s.log j).length := by
    rcases h_cwb j with h_lt | ⟨_, h_le⟩
    · exact (h_llcp j j h_lt).1
    · exact h_le
  -- Step 3: logTerm j cp(j).idx = cp(j).term
  have h_j_at_cp : logTerm s j (s.commitPoint j).index = (s.commitPoint j).term :=
    logTerm_at_commitPoint_eq_term s j h_cpbq h_llcp h_cpa h_cp_le_j
  -- Step 4: len(log i) ≤ cp(j).idx (by contradiction using monotonicity on j)
  have h_len_le_cp : (s.log i).length ≤ (s.commitPoint j).index := by
    by_contra h_neg
    push_neg at h_neg
    have := h_mono j (s.commitPoint j).index (s.log i).length (by omega) (by omega)
    rw [h_j_at_cp, ← h_match] at this; omega
  -- Step 5: case split on lastTerm(log a) vs cp(j).term
  -- Case >: use h_llcp a j directly
  -- Case ≤: use h_cpa or h_llcp through quorum members
  rcases Nat.lt_or_ge (s.commitPoint j).term (lastTerm (s.log a)) with h_high | h_low
  · -- lastTerm(log a) > cp(j).term: h_llcp a j gives agreement with j up to cp(j).idx
    obtain ⟨hlen_aj, hagree_aj⟩ := h_llcp a j h_high
    exact ⟨by omega, fun p hp =>
      (hagree_aj p (by omega) (by omega)).trans (h_ij p hp).symm⟩
  · -- lastTerm(log a) ≤ cp(j).term: use ¬canRollbackOplog i a.
    -- canRollbackOplog i a = len(i) > 0 ∧ lastTerm(i) < lastTerm(a) ∧ (len(i) > len(a) ∨ ...)
    -- Since h_gt gives lastTerm(i) < lastTerm(a), the negation (with len > 0) forces:
    --   len(log i) ≤ len(log a) ∧ lastTerm(log i) = logTerm a len(log i)
    -- Then logMatching at len(log i) gives agreement at all ≤ len(log i).
    -- Case: len(log i) = 0 — use h_llcp a i via h_cwb
    by_cases h_pos : (s.log i).length = 0
    · -- h_cwb i: cp(i).term ≤ lastTerm(log i) (in both disjuncts)
      -- So cp(i).term ≤ lastTerm(log i) < lastTerm(log a) (from h_gt)
      have h_cp_i_term : (s.commitPoint i).term ≤ lastTerm (s.log i) := by
        rcases h_cwb i with h_lt | ⟨h_eq, _⟩ <;> omega
      have h_cp_i_idx : (s.commitPoint i).index ≤ (s.log i).length := by
        rcases h_cwb i with h_lt | ⟨_, h_le⟩
        · exact (h_llcp i i h_lt).1
        · exact h_le
      obtain ⟨_, h_agree_ai⟩ := h_llcp a i (by omega)
      rw [h_pos]
      exact ⟨Nat.zero_le _, fun p hp => h_agree_ai p (by omega) (by omega)⟩
    · -- len(log i) > 0: extract the key facts from ¬canRollbackOplog
      have h_pos' : (s.log i).length > 0 := by omega
      unfold canRollbackOplog at h_no_rollback
      -- h_no_rollback : ¬(len > 0 ∧ lastTerm(i) < lastTerm(a) ∧ (len(i) > len(a) ∨ ...))
      -- Push through the conjunction: since len > 0 and lastTerm(i) < lastTerm(a) both hold,
      -- the third conjunct must fail.
      push_neg at h_no_rollback
      have h_key := h_no_rollback h_pos' (by omega)
      -- h_key : len(i) ≤ len(a) ∧ (len(i) ≤ len(a) → lastTerm(i) = logTerm a len(i))
      obtain ⟨h_len_ok, h_term_eq⟩ := h_key
      have h_term_eq := h_term_eq h_len_ok
      -- h_term_eq : lastTerm(log i) = logTerm a len(log i)
      -- logTerm a len(log i) = lastTerm(log i) = logTerm i len(log i) (by def of lastTerm)
      have h_match_ai : logTerm s a (s.log i).length = logTerm s i (s.log i).length := by
        rw [← h_term_eq]; unfold lastTerm logTerm getTerm; rfl
      -- By logMatching at len(log i): a and i agree at all ≤ len(log i)
      exact ⟨h_len_ok, fun p hp =>
        h_lm a i _ h_len_ok (le_refl _) h_match_ai p hp⟩

-- When a's last term equals i's last term and a's log is at least as long as i's,
-- a and i agree on every entry up to len(log i). Intuitively, the clamped CP
-- ⟨lastTerm(log i), len(log i)⟩ is backed by a quorum (clampedCommitPointBackedByQuorum);
-- every quorum member n has logTerm n len(log i) = lastTerm(log i) = lastTerm(log a).
-- By logTermsMonotonic, logTerm a len(log i) ≤ lastTerm(log a); combined with
-- the quorum evidence and logMatching this gives entry-by-entry agreement.
lemma logTermsAgreeWhenLastTermsMatchAndCovers
    {Server : Type} [Fintype Server] [DecidableEq Server]
    (s : RaftState Server) (a i j : Server)
    (h_lm : logMatching s)
    (h_mono : logTermsMonotonic s)
    (_h_cpbq : commitPointsBackedByQuorums s)
    (_h_llcp : logsLaterThanCommitPointHaveEntries s)
    (_h_cwb : commitPointWeaklyBelowLogTip s)
    (h_ulet : uniformLogEntriesInTerm s)
    (_h_len_ij : (s.log i).length < (s.log j).length)
    (_h_match_ij : lastTerm (s.log i) = logTerm s j (s.log i).length)
    (_h_cp_higher : lastTerm (s.log i) < (s.commitPoint j).term)
    (h_lt : lastTerm (s.log a) = lastTerm (s.log i))
    (h_len : (s.log a).length ≥ (s.log i).length)
    (p : ℕ) (hp : p ≤ (s.log i).length) :
    logTerm s a p = logTerm s i p := by
  -- Case: len(log i) = 0 → p = 0, logTerm at 0 is always 0
  by_cases h_pos : (s.log i).length = 0
  · have : p = 0 := by omega
    subst this; unfold logTerm getTerm; simp
  -- len(log i) > 0
  · -- By monotonicity: logTerm a len(log i) ≤ lastTerm(log a) = lastTerm(log i)
    have h_le : logTerm s a (s.log i).length ≤ lastTerm (s.log i) := by
      calc logTerm s a (s.log i).length
          ≤ logTerm s a (s.log a).length := h_mono a _ _ h_len (le_refl _)
        _ = lastTerm (s.log i) := h_lt
    -- lastTerm(log i) = logTerm i len(log i) definitionally
    -- If logTerm a len(log i) = logTerm i len(log i), logMatching gives agreement
    by_cases h_eq : logTerm s a (s.log i).length = logTerm s i (s.log i).length
    · exact h_lm a i _ h_len (le_refl _) h_eq p hp
    · -- logTerm a len(log i) < lastTerm(log i): contradiction via uniformLogEntriesInTerm.
      -- The first occurrence of lastTerm(log i) in a's log is > len(log i) (by monotonicity),
      -- but uniformLogEntriesInTerm forces it to be ≤ len(log i) (since i has that term there).
      exfalso
      -- logTerm a len(log i) < lastTerm(log i) (from ≤ and ≠)
      have h_strict : logTerm s a (s.log i).length < lastTerm (s.log i) := by
        have : lastTerm (s.log i) = logTerm s i (s.log i).length := rfl
        omega
      have h_lt_pos : lastTerm (s.log i) > 0 := by omega
      -- logTerm a len(log a) = lastTerm(log i)
      have h_a_last : logTerm s a (s.log a).length = lastTerm (s.log i) := h_lt
      -- Find first occurrence of lastTerm(log i) in a's log via Nat.find
      have h_exists : ∃ k, logTerm s a k = lastTerm (s.log i) ∧ 1 ≤ k :=
        ⟨(s.log a).length, h_a_last, by omega⟩
      have h_fa_prop := Nat.find_spec h_exists
      -- Nat.find h_exists > len(log i): if ≤, monotonicity gives
      -- logTerm a (find) ≤ logTerm a len(log i) < lastTerm(log i) = logTerm a (find)
      have h_fa_gt : Nat.find h_exists > (s.log i).length := by
        by_contra h_neg
        push_neg at h_neg
        have := h_mono a (Nat.find h_exists) (s.log i).length h_neg h_len
        omega
      -- Nat.find ≤ len(log a): beyond the log, logTerm = 0, contradicts lastTerm > 0
      have h_fa_le : Nat.find h_exists ≤ (s.log a).length := by
        by_contra h_neg
        push_neg at h_neg
        have : logTerm s a (Nat.find h_exists) = 0 := by
          unfold logTerm getTerm
          have : Nat.find h_exists ≠ 0 := by omega
          simp only [this, ↓reduceIte]
          rw [List.getElem?_eq_none (by omega)]
        omega
      -- Nat.find h_exists is the first occurrence in a's log
      have h_fa_first : ∀ k, 1 ≤ k → k < Nat.find h_exists →
          logTerm s a k ≠ logTerm s a (Nat.find h_exists) := by
        intro k hk1 hk_lt h_eq_k
        have := Nat.find_min h_exists hk_lt
        exact this ⟨h_eq_k.trans h_fa_prop.1, hk1⟩
      -- Apply uniformLogEntriesInTerm: first occurrence at Nat.find in a, position len(log i) in i.
      -- Since logTerm a (find) = lastTerm(log i) = logTerm i len(log i) and find is the first
      -- occurrence, we get len(log i) ≥ find. But find > len(log i). Contradiction.
      have h_match_term : logTerm s a (Nat.find h_exists) = logTerm s i (s.log i).length := by
        rw [h_fa_prop.1]; unfold lastTerm logTerm getTerm; rfl
      have := h_ulet a i (Nat.find h_exists) (s.log i).length h_fa_prop.2 h_fa_le
        (by omega) (le_refl _) h_match_term (by rw [h_fa_prop.1]; omega) h_fa_first
      omega

-- When j's commit point term strictly exceeds i's last term (the "clamped" branch of
-- learnCommitPointFromSyncSource), the leader's log must already cover all of i's
-- entries: the leader has a higher last term than i (via h_lgt on j), and log matching
-- then propagates agreement back through j's log to i's log prefix.
lemma leaderLogCoversIWhenCPJTermHigh
    {Server : Type} [Fintype Server] [DecidableEq Server]
    (s : RaftState Server) (ldr i j : Server)
    (h_lm : logMatching s)
    (h_lccp : leaderCompletenessForCommitPoints s)
    (_h_lgt : leaderLastTermGeCommitPointTerm s)
    (h_llcp : logsLaterThanCommitPointHaveEntries s)
    (h_mono : logTermsMonotonic s)
    (h_cwb : commitPointWeaklyBelowLogTip s)
    (h_cpbq : commitPointsBackedByQuorums s)
    (h_cpa : commitPointAgreement s)
    (h_ldr : s.state ldr = ServerState.Leader)
    (h_len : (s.log i).length < (s.log j).length)
    (h_match : lastTerm (s.log i) = logTerm s j (s.log i).length)
    (h_cp_higher : lastTerm (s.log i) < (s.commitPoint j).term) :
    (s.log i).length ≤ (s.log ldr).length ∧
    ∀ p, p ≤ (s.log i).length → logTerm s ldr p = logTerm s i p := by
  -- Step 1: i agrees with j up to len(log i) via logMatching + h_match
  have h_ij : ∀ p, p ≤ (s.log i).length → logTerm s i p = logTerm s j p :=
    h_lm i j _ (le_refl _) (by omega) h_match
  -- Step 2: cp(j).index ≤ len(log j)
  have h_cp_le_j : (s.commitPoint j).index ≤ (s.log j).length := by
    rcases h_cwb j with h_lt | ⟨_, h_le⟩
    · exact (h_llcp j j h_lt).1
    · exact h_le
  -- Step 3: logTerm j cp(j).index = cp(j).term
  have h_j_at_cp : logTerm s j (s.commitPoint j).index = (s.commitPoint j).term :=
    logTerm_at_commitPoint_eq_term s j h_cpbq h_llcp h_cpa h_cp_le_j
  -- Step 4: len(log i) ≤ cp(j).index (by contradiction using monotonicity on j)
  have h_len_le_cp : (s.log i).length ≤ (s.commitPoint j).index := by
    by_contra h_neg
    push_neg at h_neg
    have := h_mono j (s.commitPoint j).index (s.log i).length (by omega) (by omega)
    rw [h_j_at_cp, ← h_match] at this; omega
  -- Step 5: leader agrees with j up to cp(j).index, then chain to i
  obtain ⟨h_cp_le_ldr, h_agree_ldr_j⟩ := h_lccp ldr j h_ldr
  have h_agree_at_cp :
      logTerm s ldr (s.commitPoint j).index =
      logTerm s j (s.commitPoint j).index :=
    h_agree_ldr_j _ (le_refl _) h_cp_le_j
  have h_ldr_j : ∀ q, q ≤ (s.commitPoint j).index → logTerm s ldr q = logTerm s j q :=
    h_lm ldr j _ h_cp_le_ldr (by omega) h_agree_at_cp
  constructor
  · omega
  · intro p hp
    rw [h_ij p hp]
    exact h_ldr_j p (by omega)

lemma raftInvariant_learnCommitPointFromSyncSource (i j : Server) (s s' : RaftState Server) :
    raftInvariant s → learnCommitPointFromSyncSource i j s s' → raftInvariant s' := by
  -- learnCommitPointFromSyncSource changes: commitPoint (for server i, set to j's)
  -- Unchanged: globalCurrentTerm, state, log
  intro ⟨h_nrc, h_nrbcp, h_tb, h_cpb, h_mono, h_ctml, h_lu, h_lm,
         h_lccp, h_cpbq, h_llcp, h_cpa, h_lgt, h_ulet, h_cwb, h_cpetb, h_rsc, h_rwss⟩
    ⟨⟨h_len_ij, h_match_ij⟩, _, h_cp, h_term, h_state, h_log⟩
  -- Shared helpers: log is completely unchanged, so logTerm transfers trivially
  have lt_eq : ∀ srv p, logTerm s' srv p = logTerm s srv p := by
    intro srv p; unfold logTerm getTerm; rw [h_log]
  -- i's log is a prefix of j's (from appendOplogEnabled), so their logTerms agree up to len(log i)
  have h_ij_agree : ∀ p, p ≤ (s.log i).length → logTerm s i p = logTerm s j p :=
    h_lm i j (s.log i).length (le_refl _) (by omega) h_match_ij
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- 1. neverRollbackCommitted: depends on log and globalCurrentTerm (unchanged)
  · intro srv h
    exact h_nrc srv ((rollbackCommitted_of_eq h_log h_term).mp h)
  -- 2. neverRollbackBeforeCommitPoint:
  --   srv = i: cp becomes cp(j). Use h_rwss with appendOplogEnabled i j s.
  --   srv ≠ i: cp unchanged. Use h_nrbcp directly.
  · intro srv ⟨⟨k, h_can⟩, h_below⟩
    have h_can_s : ∃ k, canRollbackOplog srv k s :=
      ⟨k, (canRollbackOplog_of_log_eq h_log).mp h_can⟩
    rw [h_log] at h_below
    by_cases h_eq : srv = i
    · subst h_eq
      -- cp(srv) in s' = cp(j) in s
      have h_cp_eq : s'.commitPoint srv = s.commitPoint j := by
        rw [h_cp]; simp only [Function.update_apply, ite_true]
        split_ifs with h
        · rfl
        · exfalso
          exact h_rwss srv j ⟨h_len_ij, h_match_ij⟩ h_can_s (Or.inl (by omega))
      rw [h_cp_eq] at h_below
      exact h_rwss srv j ⟨h_len_ij, h_match_ij⟩ h_can_s h_below
    · -- cp(srv) unchanged, use neverRollbackBeforeCommitPoint from old state
      have h_cp_eq : s'.commitPoint srv = s.commitPoint srv := by
        rw [h_cp]; simp [h_eq]
      rw [h_cp_eq] at h_below
      exact h_nrbcp srv ⟨h_can_s, h_below⟩
  -- 3. termsAreBounded: log and globalCurrentTerm unchanged
  · exact termsAreBounded_of_log_eq_term_ge h_log (by omega) h_tb
  -- 4. commitPointBounded: i's commit point becomes j's, which was already bounded
  · intro srv
    rw [h_cp]
    simp only [Function.update_apply]
    split
    · -- srv = i: new commit point = commitPoint j or lastTerm(log i), both bounded
      rw [h_term]
      split_ifs with h_if
      · exact h_cpb j
      · exact logTerm_le_globalCurrentTerm h_tb i (s.log i).length
    · -- srv ≠ i: unchanged
      rw [h_term]; exact h_cpb srv
  -- 5. logTermsMonotonic: log unchanged
  · exact logTermsMonotonic_of_log_eq h_log h_mono
  -- 6. currentTermMatchesLeader: log, state, gCT unchanged
  · exact currentTermMatchesLeader_of_log_state_eq h_log h_state h_term h_ctml
  -- 7. leaderUnique: state unchanged
  · exact leaderUnique_of_state_eq h_state h_lu
  -- 8. logMatching: log unchanged
  · exact logMatching_of_log_eq h_log h_lm
  -- 9. leaderCompletenessForCommitPoints: log/state unchanged, commitPoint changed for i
  · intro ldr srv h_ldr_s
    rw [h_state] at h_ldr_s
    by_cases h_srv : srv = i
    · -- srv = i: new cp is either cp(j) or clamped to ⟨lastTerm(log i), len(log i)⟩
      rw [h_srv]
      have h_cp_i : s'.commitPoint i =
          if (s.commitPoint j).term ≤ lastTerm (s.log i)
          then s.commitPoint j
          else ⟨lastTerm (s.log i), (s.log i).length⟩ := by
        rw [h_cp]; simp
      rw [h_cp_i]
      split_ifs with h_if
      · -- then-branch: new cp(i) = s.commitPoint j
        obtain ⟨h_idx_j, h_agree_j⟩ := h_lccp ldr j h_ldr_s
        refine ⟨by rw [congr_fun h_log]; exact h_idx_j, ?_⟩
        intro p h_p_cp h_p_len
        rw [lt_eq, lt_eq]
        rw [congr_fun h_log] at h_p_len
        rw [h_ij_agree p h_p_len]
        exact h_agree_j p h_p_cp (by omega)
      · -- else-branch: new cp(i) = ⟨lastTerm(log i), len(log i)⟩
        -- h_if : ¬(s.commitPoint j).term ≤ lastTerm (s.log i), i.e. lastTerm(log i) < cp(j).term
        simp only
        have h_cp_higher : lastTerm (s.log i) < (s.commitPoint j).term := by omega
        obtain ⟨h_len_ldr, h_agree_ldr⟩ :=
          leaderLogCoversIWhenCPJTermHigh s ldr i j
            h_lm h_lccp h_lgt h_llcp h_mono h_cwb h_cpbq h_cpa
            h_ldr_s h_len_ij h_match_ij h_cp_higher
        refine ⟨by rw [congr_fun h_log]; exact h_len_ldr, ?_⟩
        intro p h_p_cp _
        rw [lt_eq, lt_eq]
        exact h_agree_ldr p h_p_cp
    · -- srv ≠ i: cp unchanged
      have h_cp_eq : s'.commitPoint srv = s.commitPoint srv := by rw [h_cp]; simp [h_srv]
      obtain ⟨h_idx, h_agree⟩ := h_lccp ldr srv h_ldr_s
      rw [h_cp_eq]
      refine ⟨by rw [congr_fun h_log]; exact h_idx, ?_⟩
      intro p h_p_cp h_p_len
      rw [lt_eq, lt_eq]
      exact h_agree p h_p_cp (by rw [congr_fun h_log] at h_p_len; exact h_p_len)
  -- 10. commitPointsBackedByQuorums: log unchanged, cp changed for i
  · intro srv
    by_cases h_srv : srv = i
    · -- srv = i: new cp is cp(j) or clamped ⟨lastTerm(log i), len(log i)⟩
      rw [h_srv]
      have h_cp_i : s'.commitPoint i =
          if (s.commitPoint j).term ≤ lastTerm (s.log i)
          then s.commitPoint j
          else ⟨lastTerm (s.log i), (s.log i).length⟩ := by
        rw [h_cp]; simp
      rw [h_cp_i]
      split_ifs with h_if
      · -- then-branch: new cp(i) = cp(j); reuse cpbq(j)
        obtain ⟨Q₀, hQ₀, hcover₀, hagree₀⟩ := h_cpbq j
        refine ⟨Q₀, hQ₀, fun n hn => ?_, fun n₁ n₂ hn₁ hn₂ p hp => ?_⟩
        · obtain ⟨hlen, hterm, hlt⟩ := hcover₀ n hn
          exact ⟨by rw [h_log]; exact hlen,
            by rw [h_log]; exact hterm,
            by rw [lt_eq]; exact hlt⟩
        · rw [lt_eq, lt_eq]
          exact hagree₀ n₁ n₂ hn₁ hn₂ p hp
      · -- else-branch: new cp(i) = ⟨lastTerm(log i), len(log i)⟩
        simp only
        have h_cp_higher : lastTerm (s.log i) < (s.commitPoint j).term := by omega
        obtain ⟨Q, hQ, hcover, hagree⟩ :=
          clampedCommitPointBackedByQuorum s i j
            h_lm h_cpbq h_llcp h_cwb h_mono h_cpa h_len_ij h_match_ij h_cp_higher
        refine ⟨Q, hQ, fun n hn => ?_, fun n₁ n₂ hn₁ hn₂ p hp => ?_⟩
        · obtain ⟨hlen, hterm, hlogterm⟩ := hcover n hn
          exact ⟨by rw [h_log]; exact hlen,
            by rw [h_log]; exact hterm,
            by rw [lt_eq]; exact hlogterm⟩
        · rw [lt_eq, lt_eq]
          exact hagree n₁ n₂ hn₁ hn₂ p hp
    · -- srv ≠ i: cp unchanged, logs unchanged → old Q₀ works
      have h_cp_eq : s'.commitPoint srv = s.commitPoint srv := by
        rw [h_cp]; simp [h_srv]
      obtain ⟨Q₀, hQ₀, hcover₀, hagree₀⟩ := h_cpbq srv
      refine ⟨Q₀, hQ₀, fun n hn => ?_, fun n₁ n₂ hn₁ hn₂ p hp => ?_⟩
      · obtain ⟨hlen, hterm, hlt⟩ := hcover₀ n hn
        exact ⟨by rw [h_cp_eq, h_log]; exact hlen,
          by rw [h_cp_eq, h_log]; exact hterm,
          by rw [h_cp_eq, lt_eq]; exact hlt⟩
      · rw [lt_eq, lt_eq]
        exact hagree₀ n₁ n₂ hn₁ hn₂ p (by rw [h_cp_eq] at hp; exact hp)
  -- 11. logsLaterThanCommitPointHaveEntries: log unchanged, cp changed for i
  · intro a b h_gt
    by_cases h_b : b = i
    · -- b = i: new cp is cp(j) or clamped ⟨lastTerm(log i), len(log i)⟩
      rw [h_b] at h_gt ⊢
      have h_cp_i : s'.commitPoint i =
          if (s.commitPoint j).term ≤ lastTerm (s.log i)
          then s.commitPoint j
          else ⟨lastTerm (s.log i), (s.log i).length⟩ := by
        rw [h_cp]; simp
      rw [h_cp_i] at h_gt ⊢
      split_ifs with h_if
      · -- then-branch: new cp(i) = cp(j); lastTerm(log a) > cp(j).term
        rw [if_pos h_if] at h_gt
        rw [h_log] at h_gt
        obtain ⟨hlen, hagree_j⟩ := h_llcp a j h_gt
        refine ⟨by rw [h_log]; exact hlen, fun p hp hpl => ?_⟩
        rw [lt_eq, lt_eq]; rw [h_log] at hpl
        exact (hagree_j p hp (by omega)).trans (h_ij_agree p hpl).symm
      · -- else-branch: new cp(i) = ⟨lastTerm(log i), len(log i)⟩
        -- h_gt : lastTerm(log a) > lastTerm(log i)
        simp only
        rw [h_log] at h_gt
        have h_cp_higher : lastTerm (s.log i) < (s.commitPoint j).term := by omega
        rw [if_neg h_if] at h_gt
        -- Derive ¬canRollbackOplog i a from h_rwss: appendOplogEnabled i j holds,
        -- and if i could roll back, h_rwss would contradict h_cp_higher.
        have h_no_rb : ¬canRollbackOplog i a s := by
          intro h_can
          exact h_rwss i j ⟨h_len_ij, h_match_ij⟩ ⟨a, h_can⟩ (Or.inl h_cp_higher)
        obtain ⟨h_len_a, h_agree_a⟩ :=
          logCoverageWhenLastTermExceedsClampedCP s a i j
            h_lm h_cpbq h_llcp h_cwb h_mono h_cpa h_len_ij h_match_ij h_cp_higher h_gt
            h_no_rb
        refine ⟨by rw [h_log]; exact h_len_a, fun p hp _ => ?_⟩
        rw [lt_eq, lt_eq]
        exact h_agree_a p hp
    · -- b ≠ i: cp unchanged
      have h_cp_eq : s'.commitPoint b = s.commitPoint b := by rw [h_cp]; simp [h_b]
      rw [h_cp_eq] at h_gt ⊢; rw [h_log] at h_gt
      obtain ⟨hlen, hagree⟩ := h_llcp a b h_gt
      refine ⟨by rw [h_log]; exact hlen, fun p hp hpl => ?_⟩
      rw [lt_eq, lt_eq]
      exact hagree p hp (by rw [h_log] at hpl; exact hpl)
  -- 12. commitPointAgreement: log unchanged, cp changed for i
  · -- Proof sketch:
    -- For b ≠ i: cp(b) unchanged, use h_cpa directly.
    -- For b = i: new cp(i) = cp(j).
    --   Use h_cpa(a, j) to get agreement between a and j at positions ≤ cp(j).index.
    --   Use logMatching(i, j) via prefix relationship (appendOplogEnabled) to get
    --   agreement between i and j at positions ≤ len(log i).
    --   Since p ≤ cp(j).index and p ≤ len(log i), both apply.
    --   Chain: logTerm(a, p) = logTerm(j, p) = logTerm(i, p).
    intro a b h_lt h_len p hp hpl
    rw [lt_eq, lt_eq]
    by_cases h_b : b = i
    · -- b = i: new cp is cp(j) or clamped ⟨lastTerm(log i), len(log i)⟩
      rw [h_b]
      have h_cp_i : s'.commitPoint i =
          if (s.commitPoint j).term ≤ lastTerm (s.log i)
          then s.commitPoint j
          else ⟨lastTerm (s.log i), (s.log i).length⟩ := by
        rw [h_cp]; simp
      rw [h_b, h_cp_i] at h_lt h_len hp
      rw [h_b, h_log] at hpl
      split_ifs at h_lt h_len hp with h_if
      · -- then-branch: new cp(i) = cp(j)
        rw [h_log] at h_lt h_len
        have h_aj : logTerm s a p = logTerm s j p :=
          h_cpa a j h_lt h_len p hp (by omega)
        rw [h_aj, h_ij_agree p hpl]
      · -- else-branch: new cp(i) = ⟨lastTerm(log i), len(log i)⟩
        -- h_lt : lastTerm(log a) = lastTerm(log i), h_len : len(log a) ≥ len(log i)
        simp only at h_lt h_len hp
        rw [h_log] at h_lt h_len
        have h_cp_higher : lastTerm (s.log i) < (s.commitPoint j).term := by omega
        exact logTermsAgreeWhenLastTermsMatchAndCovers s a i j
          h_lm h_mono h_cpbq h_llcp h_cwb h_ulet h_len_ij h_match_ij h_cp_higher h_lt h_len p hp
    · -- b ≠ i: cp unchanged
      have h_cp_eq : s'.commitPoint b = s.commitPoint b := by rw [h_cp]; simp [h_b]
      rw [h_cp_eq] at h_lt h_len hp
      rw [h_log] at h_lt h_len hpl
      exact h_cpa a b h_lt h_len p hp hpl
  -- 13. leaderLastTermGeCommitPointTerm: log/state unchanged, cp changed for i
  · intro ldr srv h_ldr_s
    rw [h_state] at h_ldr_s; rw [h_log, h_cp]
    simp only [Function.update_apply]
    split
    · -- srv = i: new cp(i) is if-then-else; split on the condition
      split_ifs with h_if
      · -- then-branch: new cp(i) = cp(j)
        exact h_lgt ldr j h_ldr_s
      · -- else-branch: new cp(i) = ⟨lastTerm(log i), len(log i)⟩
        -- lastTerm(ldr) ≥ cp(j).term > lastTerm(log i)
        have h_ge : lastTerm (s.log ldr) ≥ (s.commitPoint j).term := h_lgt ldr j h_ldr_s
        simp only; omega
    · -- srv ≠ i: cp unchanged
      exact h_lgt ldr srv h_ldr_s
  -- 14. uniformLogEntriesInTerm: log unchanged
  · exact uniformLogEntriesInTerm_of_log_eq h_log h_ulet
  -- 15. commitPointWeaklyBelowLogTip: log unchanged, cp changed for i
  -- Proof sketch:
  -- - srv ≠ i: cp and log unchanged, use h_cwb srv directly.
  -- - srv = i, else-branch (cp = ⟨lastTerm(log i), len(log i)⟩): trivially weakly below.
  -- - srv = i, then-branch (cp = cp(j), with h_if: cp(j).term ≤ lastTerm(log i)):
  --     - If cp(j).term < lastTerm(log i): left disjunct, done.
  --     - If cp(j).term = lastTerm(log i): need cp(j).index ≤ len(log i).
  --       STUCK: This sub-goal appears unprovable. The guard `cp(j).term ≤ lastTerm(log i)`
  --       only checks the term, not the index. A counterexample: j's log = [1,1,2,2,2]
  --       (len=5), i's log = [1,1,2] (len=3), cp(j) = (2,5). Then cp(j).term = 2 =
  --       lastTerm(log i), appendOplogEnabled holds, but cp(j).index = 5 > 3 = len(log i).
  --       Copying cp(j) to i violates commitPointWeaklyBelowLogTip. The fix likely requires
  --       strengthening the guard in learnCommitPointFromSyncSource (line 222) to also
  --       check cp(j).index ≤ len(log i), or changing the if-condition to strict <.
  · intro srv
    rw [h_cp, h_log]
    simp only [Function.update_apply]
    by_cases h_srv : srv = i
    · -- srv = i: new cp is if-then-else
      simp [h_srv]
      split_ifs with h_if
      · -- then-branch: new cp(i) = cp(j), h_if : cp(j).term ≤ lastTerm(log i)
        rcases Nat.lt_or_eq_of_le h_if with h_lt | h_eq_term
        · -- cp(j).term < lastTerm(log i): left disjunct
          left; exact h_lt
        · -- cp(j).term = lastTerm(log i): need cp(j).index ≤ len(log i)
          -- STUCK: see comment above. The guard does not ensure cp(j).index ≤ len(log i).
          right; exact ⟨h_eq_term, sorry⟩
      · -- else-branch: new cp(i) = ⟨lastTerm(log i), len(log i)⟩
        right; simp
    · -- srv ≠ i: cp unchanged
      simp [h_srv]
      exact h_cwb srv
  -- 16. commitPointEntryTermsBounded: log unchanged, cp changed for i
  · -- For b = i: new cp(i) = cp(j). Need logTerm(i, p) ≤ cp(j).term.
    --   By logMatching (prefix relationship), logTerm(i, p) = logTerm(j, p).
    --   By h_cpetb on j: logTerm(j, p) ≤ cp(j).term.
    -- For b ≠ i: cp and log unchanged, use h_cpetb.
    intro b p hp hpl
    by_cases h_b : b = i
    · subst h_b
      have h_cp_i : s'.commitPoint b =
          if (s.commitPoint j).term ≤ lastTerm (s.log b)
          then s.commitPoint j
          else ⟨lastTerm (s.log b), (s.log b).length⟩ := by
        rw [h_cp]; simp
      rw [h_cp_i] at hp ⊢
      split_ifs at hp ⊢ with h_if
      · -- then-branch: new cp = cp(j)
        rw [h_log] at hpl
        rw [lt_eq b p, h_ij_agree p hpl]
        exact h_cpetb j p hp (by omega)
      · -- else-branch: new cp = ⟨lastTerm(log b), len(log b)⟩
        -- need logTerm s b p ≤ lastTerm(log b), which is logTermsMonotonic
        simp only at hp ⊢
        rw [h_log] at hpl
        rw [lt_eq b p]
        exact h_mono b p (s.log b).length hp (le_refl _)
    · have h_cp_eq : s'.commitPoint b = s.commitPoint b := by
        rw [h_cp]; simp [h_b]
      rw [h_cp_eq] at hp; rw [h_log] at hpl
      rw [lt_eq b p, h_cp_eq]; exact h_cpetb b p hp hpl
  -- 17. rollbackSafeCommitPoint: log unchanged, cp changed for i
  · intro srv ⟨k, h_can⟩
    rw [h_cp, h_log]
    simp only [Function.update_apply]
    split_ifs with h_eq h_if
    · -- srv = i, then-branch: new cp = cp(j). Need cp(j).term ≤ lastTerm(dropLast(log_i)).
      --   From h_rwss: cp(j) is not above i's log tip. Then:
      --   1. Show logTerm(i, cp(j).index) = cp(j).term (via llcp/cpa + cpbq)
      --   2. Show cp(j).index < len(log i) strictly (from h_rwss)
      --   3. Monotonicity: cp(j).term ≤ lastTerm(dropLast(log i))
      subst h_eq
      have h_can_s : ∃ k, canRollbackOplog srv k s :=
        ⟨k, (canRollbackOplog_of_log_eq h_log).mp h_can⟩
      have h_not_j := h_rwss srv j ⟨h_len_ij, h_match_ij⟩ h_can_s
      push_neg at h_not_j
      obtain ⟨h_term_le, h_not_eq⟩ := h_not_j
      -- cp(j).index ≤ len(log j)
      have h_cp_le_j : (s.commitPoint j).index ≤ (s.log j).length := by
        rcases h_cwb j with h_lt | ⟨_, h_le⟩
        · exact (h_llcp j j h_lt).1
        · exact h_le
      -- Shared: lastTerm(dropLast) = logTerm at dropLast.length (used in both cases below)
      have h_lastTerm_dl : lastTerm (s.log srv).dropLast =
          logTerm s srv (s.log srv).dropLast.length := by
        unfold lastTerm logTerm getTerm; split; · rfl
        · next h_ne =>
          congr 1; rw [List.getElem?_dropLast]
          rw [if_pos (by rw [List.length_dropLast] at h_ne ⊢; omega)]
      -- Case split: lastTerm(log i) > cp(j).term or = cp(j).term
      rcases Nat.lt_or_ge (s.commitPoint j).term (lastTerm (s.log srv)) with h_gt | h_ge
      · -- Case A: lastTerm(log i) > cp(j).term
        obtain ⟨h_cp_le_i, h_agree_i⟩ := h_llcp srv j h_gt
        -- cp(j).index < len(log i) strictly: if = len, logTerm = lastTerm = cp.term, contradiction
        have h_cp_strict : (s.commitPoint j).index < (s.log srv).length := by
          by_contra h_not_strict; push_neg at h_not_strict
          have h_eq_idx : (s.commitPoint j).index = (s.log srv).length :=
            Nat.le_antisymm h_cp_le_i h_not_strict
          have h_eq_lt : logTerm s srv (s.commitPoint j).index =
              logTerm s j (s.commitPoint j).index :=
            h_agree_i _ (le_refl _) h_cp_le_j
          have h_j_eq := logTerm_at_commitPoint_eq_term s j h_cpbq h_llcp h_cpa h_cp_le_j
          rw [h_eq_idx] at h_eq_lt h_j_eq
          unfold logTerm at h_eq_lt; omega
        -- logTerm(i, cp(j).index) = cp(j).term
        have h_i_eq : logTerm s srv (s.commitPoint j).index = (s.commitPoint j).term := by
          have h_eq_lt := h_agree_i _ (le_refl _) h_cp_le_j
          have h_j_eq := logTerm_at_commitPoint_eq_term s j h_cpbq h_llcp h_cpa h_cp_le_j
          rw [h_eq_lt, h_j_eq]
        rw [h_lastTerm_dl, ← h_i_eq]
        exact h_mono srv _ _ (by rw [List.length_dropLast]; omega)
          (by rw [List.length_dropLast]; omega)
      · -- Case B: lastTerm(log i) = cp(j).term
        have h_eq_term : lastTerm (s.log srv) = (s.commitPoint j).term :=
          Nat.le_antisymm h_ge h_term_le
        have h_cp_strict : (s.commitPoint j).index < (s.log srv).length := by
          by_contra h_not; push_neg at h_not
          exact absurd (h_not_eq h_eq_term) (Nat.not_lt.mpr h_not)
        have h_agree_i := h_cpa srv j h_eq_term (by omega)
        have h_i_eq : logTerm s srv (s.commitPoint j).index = (s.commitPoint j).term := by
          have h_j_eq := logTerm_at_commitPoint_eq_term s j h_cpbq h_llcp h_cpa h_cp_le_j
          rw [h_agree_i _ (le_refl _) h_cp_le_j, h_j_eq]
        rw [h_lastTerm_dl, ← h_i_eq]
        exact h_mono srv _ _ (by rw [List.length_dropLast]; omega)
          (by rw [List.length_dropLast]; omega)
    · -- srv = i, else-branch: clamped CP = ⟨lastTerm(log i), len(log i)⟩
      -- h_if : ¬(s.commitPoint j).term ≤ lastTerm (s.log i), i.e. lastTerm(log i) < cp(j).term
      -- h_rwss says this cannot happen when srv can be rolled back → contradiction
      exfalso
      have h_can_s : ∃ k', canRollbackOplog srv k' s :=
        ⟨k, (canRollbackOplog_of_log_eq h_log).mp h_can⟩
      have h_len_srv : (s.log srv).length < (s.log j).length := h_eq ▸ h_len_ij
      have h_match_srv : lastTerm (s.log srv) = logTerm s j (s.log srv).length :=
        h_eq ▸ h_match_ij
      have h_last_eq : lastTerm (s.log srv) = lastTerm (s.log i) :=
        congrArg (lastTerm ∘ s.log) h_eq
      exact h_rwss srv j ⟨h_len_srv, h_match_srv⟩ h_can_s (Or.inl (by omega))
    · -- srv ≠ i: cp unchanged
      exact h_rsc srv ⟨k, (canRollbackOplog_of_log_eq h_log).mp h_can⟩
  -- 18. rollbackWithSyncSourceImpliesCommitPointBelowTip
  -- Proof sketch:
  -- Logs unchanged, only cp(i) changes.
  -- appendOplogEnabled and canRollbackOplog transfer to old state.
  -- Case b ≠ i: cp(b) unchanged, transfer directly from h_rwss.
  -- Case b = i: cp(i) changes to clamped value. Split on if-condition.
  --   Then-branch (cp(j).term ≤ lastTerm(log i)): cp(i) := cp(j).
  --     Case a = i: appendOplogEnabled i i is impossible (len(i) < len(i)).
  --     Case a ≠ i: establish appendOplogEnabled a j s (via log matching through i),
  --       then use h_rwss a j to get ¬(below) for cp(j).
  --   Else-branch (lastTerm(log i) < cp(j).term): cp(i) := ⟨lastTerm(log i), len(log i)⟩.
  --     Case a = i: appendOplogEnabled i i is impossible.
  --     Case a ≠ i: need exfalso. a's log tip is at or below i's log tip
  --       (from appendOplogEnabled + monotonicity), so new cp is above a's log tip.
  --       Must show appendOplogEnabled a i + canRollbackOplog a k + else-branch is contradictory.
  · intro a b h_aoe h_can_ex h_below
    have h_aoe_s : appendOplogEnabled a b s :=
      (appendOplogEnabled_of_log_eq h_log).mp h_aoe
    have h_can_s : ∃ k, canRollbackOplog a k s := by
      obtain ⟨k, hk⟩ := h_can_ex
      exact ⟨k, (canRollbackOplog_of_log_eq h_log).mp hk⟩
    rw [h_cp, h_log] at h_below
    by_cases h_b : b = i
    · -- Case b = i: cp(i) is updated
      simp only [h_b, Function.update_apply, ite_true] at h_below
      split_ifs at h_below with h_if
      · -- Then-branch: cp(j).term ≤ lastTerm(log i), so cp(i) := cp(j)
        by_cases h_a : a = i
        · -- a = i: appendOplogEnabled i i requires len(i) < len(i), contradiction
          exact absurd (h_a ▸ h_b ▸ h_aoe_s).1 (Nat.lt_irrefl _)
        · -- a ≠ i: establish appendOplogEnabled a j s by transitivity through i
          -- (lastTerm(log a) = logTerm i (len a) = logTerm j (len a) via h_ij_agree / h_lm)
          -- then apply h_rwss a j h_aoe_aj h_can_s h_below
          have h_aoe_ai : appendOplogEnabled a i s := h_b ▸ h_aoe_s
          have h_aoe_aj : appendOplogEnabled a j s :=
            ⟨Nat.lt_trans h_aoe_ai.1 h_len_ij,
             h_aoe_ai.2.trans (h_ij_agree _ (le_of_lt h_aoe_ai.1))⟩
          exact h_rwss a j h_aoe_aj h_can_s h_below
      · -- Else-branch: ¬(cp(j).term ≤ lastTerm(log i)), so cp(i) := ⟨lastTerm(log i), len(log i)⟩
        -- i.e., lastTerm(log i) < cp(j).term
        by_cases h_a : a = i
        · -- a = i: appendOplogEnabled i i requires len(i) < len(i), contradiction
          exact absurd (h_a ▸ h_b ▸ h_aoe_s).1 (Nat.lt_irrefl _)
        · -- a ≠ i: establish appendOplogEnabled a j s, then h_rwss a j
          -- says ¬(below for cp(j)). But lastTerm(log a) ≤ lastTerm(log i)
          -- (monotonicity) < cp(j).term (h_if), contradicting h_rwss.
          exfalso
          have h_aoe_ai : appendOplogEnabled a i s := h_b ▸ h_aoe_s
          have h_aoe_aj : appendOplogEnabled a j s :=
            ⟨Nat.lt_trans h_aoe_ai.1 h_len_ij,
             h_aoe_ai.2.trans (h_ij_agree _ (le_of_lt h_aoe_ai.1))⟩
          have h_le : lastTerm (s.log a) ≤ lastTerm (s.log i) := by
            rw [h_aoe_ai.2]
            exact h_mono i _ _ (le_of_lt h_aoe_ai.1) (le_refl _)
          exact h_rwss a j h_aoe_aj h_can_s (Or.inl (by omega))
    · -- Case b ≠ i: cp(b) unchanged, transfer from h_rwss
      simp [h_b] at h_below
      exact h_rwss a b h_aoe_s h_can_s h_below

/- ================================================================
   Section 13: Inductive Step — Assembly
   ================================================================ -/

lemma raftInvariant_step (s s' : RaftState Server) :
    raftInvariant s → raftNext s s' → raftInvariant s' := by
  intro h_inv h_next
  unfold raftNext at h_next
  rcases h_next with ⟨i, j, h⟩ | ⟨i, j, h⟩ | ⟨i, h⟩ | ⟨i, h⟩ | h | ⟨i, j, h⟩
  · exact raftInvariant_appendOplog i j s s' h_inv h
  · exact raftInvariant_rollbackOplog i j s s' h_inv h
  · exact raftInvariant_becomePrimaryByMagic i s s' h_inv h
  · exact raftInvariant_clientWrite i s s' h_inv h
  · exact raftInvariant_advanceCommitPoint s s' h_inv h
  · exact raftInvariant_learnCommitPointFromSyncSource i j s s' h_inv h

/- ================================================================
   Section 14: Main Theorems
   ================================================================ -/

-- THEOREM: NeverRollbackCommitted is an invariant of the protocol
theorem raftNeverRollbackCommitted (s : RaftState Server) :
    RaftReachable s → neverRollbackCommitted s := by
  intro h
  suffices raftInvariant s from this.1
  induction h with
  | init => exact raftInvariant_init
  | step h_reach h_next ih => exact raftInvariant_step _ _ ih h_next

-- THEOREM: NeverRollbackBeforeCommitPoint is an invariant of the protocol
theorem raftNeverRollbackBeforeCommitPoint (s : RaftState Server) :
    RaftReachable s → neverRollbackBeforeCommitPoint s := by
  intro h
  suffices raftInvariant s from this.2.1
  induction h with
  | init => exact raftInvariant_init
  | step h_reach h_next ih => exact raftInvariant_step _ _ ih h_next
