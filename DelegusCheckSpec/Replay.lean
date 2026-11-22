/-
Copyright 2026 Inam Haq. Licensed under the Apache License, Version 2.0.

The replay store and the one-time-use theorem (§5.3 T5, §7, erratum 5).
The store is modelled as the erratum states it: the set of writes it holds,
each a key with an absolute expiry `E`, a key being present at store instant
`s` iff some write of it has `s ≤ E`, and the store's own clock check in the
same atomic operation. Histories are one sequence of atomic operations.
Every assumption is a hypothesis of the theorems below, never an axiom. Attribution for restated spec text:
"Delegus Specification v0.2, © Delegus (delegus.ai)", CC BY 4.0.
-/
import DelegusCheckSpec.Revocation

namespace DelegusCheck

/-! ## The store -/

abbrev ReplayKey := Did × String

structure ReplayStore where
  writes : List (ReplayKey × Int)

def ReplayStore.empty : ReplayStore := ⟨[]⟩

/-- Present at store instant `s`, up to and including the expiry instant. -/
def ReplayStore.present (st : ReplayStore) (k : ReplayKey) (s : Int) : Bool :=
  st.writes.any fun w => w.1 == k && decide (s ≤ w.2)

/-- The absolute expiry of a write made at store instant `s`. -/
def expiryAt (x : Expiry) (s : Int) : Int :=
  match x with
  | .pxat ms => ms
  | .px ms => s + ms

/-- One atomic store operation at store instant `s` (erratum 5): if the
    store's clock reads more than 4 000 ms ahead of the verifier's `now`, it
    refuses and writes nothing; otherwise `SET key 1 NX PXAT E`. -/
def setNX (st : ReplayStore) (q : ReplayQuery) (s : Int) : ReplayAnswer × ReplayStore :=
  if s - q.nowMs > replayMaxStoreAheadMs then (.unavailable, st)
  else if st.present (q.rp, q.jti) s then (.replayed, st)
  else (.ok, ⟨((q.rp, q.jti), expiryAt q.expiry s) :: st.writes⟩)

/-! ## One verification against the store -/

/-- A verification: its inputs other than the replay store, plus when its
    replay write reaches the store (store clock), how long the store takes
    to acknowledge it, and whether the store is down. -/
structure RVerify where
  π : Prims
  req : Request
  s : Snapshots
  tc : TrustConfig
  clk : Clock
  storeAt : Int
  delayMs : Nat
  down : Bool

/-- What the verifier hears back from its write. Down, or not acknowledged
    within the timeout, is `SERVICE_UNAVAILABLE` (erratum 5). -/
def respond (st : ReplayStore) (v : RVerify) (q : ReplayQuery) : ReplayAnswer :=
  if v.down then .unavailable
  else if v.delayMs > replayWriteTimeoutMs then .unavailable
  else (setNX st q v.storeAt).1

def RVerify.env (v : RVerify) (st : ReplayStore) : Env :=
  ⟨v.π, v.req, v.s, v.tc, v.clk, respond st v⟩

/-- The replay write this evaluation performs, if any. -/
def writeOf (e : Env) : Option ReplayQuery :=
  (opsOf e).findSome? fun o => match o with
    | .replay q => some q
    | _ => none

/-- The store after the verification. A write that reaches the store stays,
    even if its acknowledgement came too late. -/
def RVerify.after (v : RVerify) (st : ReplayStore) : ReplayStore :=
  match writeOf (v.env st) with
  | some q => if v.down then st else (setNX st q v.storeAt).2
  | none => st

def RVerify.eval (v : RVerify) (st : ReplayStore) : Evaluation := evaluateWith staged (v.env st)

/-- The store after a sequence of verifications. -/
def storeAfter : ReplayStore → List RVerify → ReplayStore
  | st, [] => st
  | st, v :: vs => storeAfter (v.after st) vs

/-! ## Facts -/

theorem opsOf_replay_query {e : Env} {q : ReplayQuery} (h : Op.replay q ∈ opsOf e) :
    ∃ p, e.proof = some p ∧ q = e.query p := by
  unfold opsOf at h
  repeat' split at h
  all_goals simp_all

theorem writeOf_of_mem {e : Env} {q : ReplayQuery} (h : Op.replay q ∈ opsOf e) : writeOf e = some q := by
  unfold writeOf
  rcases trace_shape e with hs | ⟨d, hs⟩ | ⟨d, u, hs⟩ | ⟨d, u, q', hs⟩ <;> rw [hs] at h ⊢ <;> simp_all

/-- If T5 passed, the evaluation wrote `e.query p` for its Proof and the
    store answered OK. -/
theorem t5_pass_write {e : Env} (h : (staged e).get .T5 = .pass) :
    ∃ p, e.proof = some p ∧ writeOf e = some (e.query p) ∧ e.ρ (e.query p) = .ok := by
  have hb := base_of_pass h
  have hall : ∀ k ∈ p1ToP14, (staged e).get k = .pass := by
    intro k hk
    exact prereq_of_pass h k (by simp [enginePrereq]; simp [p1ToP14] at hk; exact hk)
  obtain ⟨q, hq⟩ := (replay_write_iff e).mpr hall
  obtain ⟨p, hp, rfl⟩ := opsOf_replay_query hq
  refine ⟨p, hp, writeOf_of_mem hq, ?_⟩
  simp only [base, hp] at hb
  revert hb
  cases e.ρ (e.query p) <;> simp [replayOutcome]

theorem present_mono {st : ReplayStore} {k : ReplayKey} {s : Int} (h : st.present k s = true)
    (q : ReplayQuery) (s' : Int) : (setNX st q s').2.present k s = true := by
  unfold setNX
  split
  · exact h
  · split
    · exact h
    · simp only [ReplayStore.present] at h ⊢
      simp [h]

theorem present_after {st : ReplayStore} {k : ReplayKey} {s : Int} (h : st.present k s = true)
    (v : RVerify) : (v.after st).present k s = true := by
  unfold RVerify.after
  split
  · split
    · exact h
    · exact present_mono h _ _
  · exact h

theorem present_storeAfter {k : ReplayKey} {s : Int} :
    ∀ (vs : List RVerify) (st : ReplayStore), st.present k s = true → (storeAfter st vs).present k s = true
  | [], _, h => h
  | v :: vs, _, h => present_storeAfter vs _ (present_after h v)

/-- An ALLOW leaves its key in the store with expiry
    `iat·1000 + window_ms + 5000`. -/
theorem allow_writes {v : RVerify} {st : ReplayStore}
    (h : (v.eval st).result.decision = .allow) :
    ∃ p, parseProof v.π v.req.proof = some p ∧
      ∀ s, s ≤ p.iat * 1000 + (v.req.windowS : Int) * 1000 + replayMarginMs →
        (v.after st).present (v.req.rp, p.jti) s = true := by
  have h5 := (allow_iff_every_check _).mp h .T5
  obtain ⟨p, hp, hw, hok⟩ := t5_pass_write h5
  refine ⟨p, hp, fun s hs => ?_⟩
  unfold RVerify.after
  rw [hw]
  have hok' : respond st v ((v.env st).query p) = .ok := hok
  unfold respond at hok'
  split at hok'
  · cases hok'
  · split at hok'
    · cases hok'
    · rename_i hdown _
      simp only [hdown, Bool.false_eq_true, ite_false]
      unfold setNX at hok' ⊢
      split at hok'
      · cases hok'
      · rename_i hskew
        split at hok'
        · cases hok'
        · rename_i hnp
          simp only [RVerify.env, Env.query, replayQuery, ReplayStore.present] at hskew hnp ⊢
          simp only [hskew, hnp, ite_false, Bool.false_eq_true, List.any_cons, expiryAt]
          simp [hs]

/-! ## The theorem -/

/-- **Erratum 5's replay statement.** Suppose the store holds the key
    `(rp_did, jti)` at every store instant up to `E = iat·1000 + w1 + 5000`,
    as an earlier ALLOW of the Proof left it. A later verification of a
    Proof with the same `(rp_did, jti)` and `iat`, under a window `w2 ≤ w1`,
    is DENY. Two branches: if its write reaches the store at most 4 000 ms
    (store clock) after its `now`, the key is still present and T5 is
    `PROOF_REPLAYED`; otherwise the store refuses the write and T5 is
    `SERVICE_UNAVAILABLE`. -/
theorem replay_denied {v : RVerify} {st : ReplayStore} {p : ProofF} {w1 : Nat}
    (hp : parseProof v.π v.req.proof = some p) (hw : v.req.windowS ≤ w1)
    (hkey : ∀ s, s ≤ p.iat * 1000 + (w1 : Int) * 1000 + replayMarginMs →
      st.present (v.req.rp, p.jti) s = true) :
    (v.eval st).result.decision = .deny := by
  cases hd : (v.eval st).result.decision with
  | deny => rfl
  | allow =>
    exfalso
    have hall := (allow_iff_every_check _).mp hd
    -- P13 passed: |now − iat·1000| ≤ w2·1000
    have h13 := base_of_pass (hall .P13)
    obtain ⟨p', hp', -, hok⟩ := t5_pass_write (hall .T5)
    have hpp : p' = p := by
      have : (v.env st).proof = some p := hp
      rw [this] at hp'; exact (Option.some.inj hp').symm
    subst hpp
    simp only [base, show (v.env st).proof = some p' from hp, p13Of, ok_pass, decide_eq_true_eq] at h13
    have hwin : v.clk.nowMs ≤ p'.iat * 1000 + (w1 : Int) * 1000 := by
      have h' : (v.clk.nowMs - p'.iat * 1000).natAbs ≤ v.req.windowS * 1000 := h13
      omega
    -- T5 answered OK, so the store did not refuse and did not find the key
    have hok' : respond st v ((v.env st).query p') = .ok := hok
    unfold respond at hok'
    split at hok'
    · cases hok'
    · split at hok'
      · cases hok'
      · unfold setNX at hok'
        split at hok'
        · cases hok'
        · rename_i hskew
          -- the store's check passed: s2 − t2 ≤ 4 000, so s2 < E and the key is present
          have hpres : st.present (v.req.rp, p'.jti) v.storeAt = true := by
            apply hkey
            simp only [RVerify.env, Env.query, replayQuery, replayMaxStoreAheadMs, replayMarginMs,
              replayWriteTimeoutMs] at hskew ⊢
            omega
          simp only [RVerify.env, Env.query, replayQuery, hpres, ite_true] at hok'
          cases hok'

/-- **At most one ALLOW per `(rp_did, jti)`** (§5.3 T5, erratum 5). In any
    history of verifications through one replay store (one sequence of
    atomic operations), take an earlier verification `v1` and a later one
    `v2`, with any verifications `mid` between them, whose Proofs have the
    same relying party, `jti` and `iat`, and where `v2`'s Proof window is no
    larger than `v1`'s. They are not both ALLOW. -/
theorem at_most_one_allow (st0 : ReplayStore) (v1 : RVerify) (mid : List RVerify) (v2 : RVerify)
    {p1 p2 : ProofF}
    (hp1 : parseProof v1.π v1.req.proof = some p1) (hp2 : parseProof v2.π v2.req.proof = some p2)
    (hrp : v1.req.rp = v2.req.rp) (hjti : p1.jti = p2.jti) (hiat : p1.iat = p2.iat)
    (hw : v2.req.windowS ≤ v1.req.windowS) :
    ¬ ((v1.eval st0).result.decision = .allow ∧
       (v2.eval (storeAfter (v1.after st0) mid)).result.decision = .allow) := by
  rintro ⟨h1, h2⟩
  obtain ⟨p, hp, hpres⟩ := allow_writes h1
  rw [hp1] at hp; cases hp
  have hden := replay_denied (st := storeAfter (v1.after st0) mid) (w1 := v1.req.windowS) hp2 hw
    (fun s hs => by
      rw [← hrp, ← hjti]
      apply present_storeAfter mid
      apply hpres
      rw [hiat]; exact hs)
  rw [hden] at h2
  cases h2

end DelegusCheck
