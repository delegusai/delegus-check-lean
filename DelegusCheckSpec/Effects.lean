/-
Copyright 2026 Inam Haq. Licensed under the Apache License, Version 2.0.

Phase 4 (the parts that do not depend on replay-window semantics): the
evaluator written against the three internal operations the hot path may
perform (§5.5, §7), a recording run that yields the trace of operations,
and the erratum 1 ordering. Attribution for restated spec text: "Delegus
Specification v0.2, © Delegus (delegus.ai)", CC BY 4.0.
-/
import DelegusCheckSpec.Historical

namespace DelegusCheck

/-- The internal operations `/verify` may perform (§5.5): the issuer
    registry read (after P1), the revocation read `[read status_ver; refresh
    cached status credential]` (before P6), and the replay write `[atomic
    replay SET NX]` (before T5). -/
inductive Op
  | issuer (principal : Did)
  | status (url : String)
  | replay (q : ReplayQuery)
  deriving DecidableEq

/-- An implementation of the three operations in some monad. -/
structure Seams (m : Type → Type) where
  issuer : Did → m IssuerLookup
  statusRead : String → m StatusLookup
  replaySetNX : ReplayQuery → m ReplayAnswer

/-- The pure parts of an evaluation: everything except the store answers. -/
def pureEnv (π : Prims) (req : Request) (tc : TrustConfig) (clk : Clock) : Env :=
  ⟨π, req, ⟨fun _ => .unavailable, fun _ => .unavailable⟩, tc, clk, fun _ => .unavailable⟩

/-- The evaluator with effects. Each operation happens at exactly the place
    §5.4 gives it; nothing else touches a store. -/
def evaluateM {m : Type → Type} [Monad m] (S : Seams m) (π : Prims) (req : Request) (tc : TrustConfig)
    (clk : Clock) : m Row := do
  let e := pureEnv π req tc clk
  match e.grant with
  | .error r => pure { p1 := .fail r }
  | .ok g =>
    let iss ← S.issuer g.issuer
    match iss with
    | .unavailable => pure { p1 := .pass, t1 := .fail .SERVICE_UNAVAILABLE }
    | .unknown => pure { p1 := .pass, t1 := .fail .ISSUER_UNKNOWN }
    | .registered dv comp doc =>
      let t2 := ok dv .ISSUER_UNVERIFIED
      let t3 := ok (!comp.contains g.kid) .ISSUER_KEY_COMPROMISED
      match findKey π doc g.issuer g.kid with
      | none => pure { p1 := .pass, t1 := .pass, t2, t3, p2 := .fail .ISSUER_KEY_NOT_FOUND }
      | some key =>
        if π.sigOk key g.signingInput g.signature then
          let p4 := p4Of e g
          let p5 := p5Of e g
          let st ← S.statusRead g.statusUrl
          let p6 := p6From π tc clk st g
          let p7 := p7Of e g
          match e.proof with
          | none => pure { p1 := .pass, t1 := .pass, t2, t3, p2 := .pass, p3 := .pass, p4, p5, p6, p7,
                           p8 := .fail .PROOF_MALFORMED }
          | some p =>
            let t5 ← if earlyPass e g p4 p5 p6 p7 p then
                do let a ← S.replaySetNX (e.query p); pure (replayOutcome a)
              else pure .skipped
            pure (proofRow e g t2 t3 p4 p5 p6 p7 p t5)
        else
          pure { p1 := .pass, t1 := .pass, t2, t3, p2 := .pass, p3 := .fail .GRANT_SIGNATURE_INVALID }

/-! ## A recording run -/

abbrev Rec := StateM (List Op)

/-- Answer from the snapshots and the replay store, and record each
    operation performed. -/
def recSeams (s : Snapshots) (ρ : ReplayQuery → ReplayAnswer) : Seams Rec where
  issuer d := do modify (· ++ [.issuer d]); pure (s.issuer d)
  statusRead u := do modify (· ++ [.status u]); pure (s.status u)
  replaySetNX q := do modify (· ++ [.replay q]); pure (ρ q)

/-- The operations one evaluation performs, in order. -/
def traceOf (π : Prims) (req : Request) (s : Snapshots) (tc : TrustConfig) (clk : Clock)
    (ρ : ReplayQuery → ReplayAnswer) : List Op :=
  ((evaluateM (recSeams s ρ) π req tc clk).run []).2

/-- The same, written out. -/
def opsOf (e : Env) : List Op :=
  match e.grant with
  | .error _ => []
  | .ok g =>
    .issuer g.issuer ::
    match e.s.issuer g.issuer with
    | .registered _ _ doc =>
      match findKey e.π doc g.issuer g.kid with
      | some key =>
        if e.π.sigOk key g.signingInput g.signature then
          .status g.statusUrl ::
          match e.proof with
          | some p => if earlyPass e g (p4Of e g) (p5Of e g) (p6Of e g) (p7Of e g) p then [.replay (e.query p)] else []
          | none => []
        else []
      | none => []
    | _ => []

theorem pureEnv_grant (π : Prims) (req : Request) (s : Snapshots) (tc : TrustConfig) (clk : Clock)
    (ρ : ReplayQuery → ReplayAnswer) : (pureEnv π req tc clk).grant = (envOf π req s tc clk ρ).grant := rfl

/-- **The effectful evaluator, answered from the snapshots, is the pure
    one**, and its trace is `opsOf`. -/
theorem run_eq (π : Prims) (req : Request) (s : Snapshots) (tc : TrustConfig) (clk : Clock)
    (ρ : ReplayQuery → ReplayAnswer) :
    (evaluateM (recSeams s ρ) π req tc clk).run [] = (stagedRow (envOf π req s tc clk ρ), opsOf (envOf π req s tc clk ρ)) := by
  unfold evaluateM stagedRow opsOf
  simp only [pureEnv_grant π req s tc clk ρ]
  rcases hg : (envOf π req s tc clk ρ).grant with r | g
  · rfl
  · rcases hi : s.issuer g.issuer with _ | _ | ⟨dv, comp, doc⟩
    · simp [recSeams, hi] <;> try rfl
    · simp [recSeams, hi] <;> try rfl
    · rcases hk : findKey π doc g.issuer g.kid with _ | key
      · simp [recSeams, hi, hk] <;> try rfl
      · by_cases hs : π.sigOk key g.signingInput g.signature = true
        · rcases hp : (envOf π req s tc clk ρ).proof with _ | p
          · have : (pureEnv π req tc clk).proof = none := hp
            simp [recSeams, hi, hk, hs, this] <;> try rfl
          · have : (pureEnv π req tc clk).proof = some p := hp
            by_cases he : earlyPass (envOf π req s tc clk ρ) g (p4Of (envOf π req s tc clk ρ) g)
                (p5Of (envOf π req s tc clk ρ) g) (p6Of (envOf π req s tc clk ρ) g) (p7Of (envOf π req s tc clk ρ) g) p = true
            · have he' : earlyPass (pureEnv π req tc clk) g (p4Of (pureEnv π req tc clk) g)
                  (p5Of (pureEnv π req tc clk) g) (p6From π tc clk (s.status g.statusUrl) g)
                  (p7Of (pureEnv π req tc clk) g) p = true := he
              simp [recSeams, hi, hk, hs, this, proofStage, he, he'] <;> try rfl
            · have he' : ¬ earlyPass (pureEnv π req tc clk) g (p4Of (pureEnv π req tc clk) g)
                  (p5Of (pureEnv π req tc clk) g) (p6From π tc clk (s.status g.statusUrl) g)
                  (p7Of (pureEnv π req tc clk) g) p = true := he
              simp [recSeams, hi, hk, hs, this, proofStage, he, he'] <;> try rfl
        · simp [recSeams, hi, hk, hs] <;> try rfl

/-- The recorded trace is `opsOf`. -/
theorem trace_eq (π : Prims) (req : Request) (s : Snapshots) (tc : TrustConfig) (clk : Clock)
    (ρ : ReplayQuery → ReplayAnswer) :
    traceOf π req s tc clk ρ = opsOf (envOf π req s tc clk ρ) := by
  unfold traceOf; rw [run_eq]

/-- The effectful evaluator's result is `evaluate`'s. -/
theorem evaluateM_result (π : Prims) (req : Request) (s : Snapshots) (tc : TrustConfig) (clk : Clock)
    (ρ : ReplayQuery → ReplayAnswer) :
    ((evaluateM (recSeams s ρ) π req tc clk).run []).1.toChecks = (evaluate π req s tc clk ρ).result.checks := by
  rw [run_eq]; rfl

/-- **Hot-path shape** (§5.5, §7): an evaluation performs only the three
    internal operations, each at most once, in the order issuer read,
    revocation read, replay write. -/
theorem trace_shape (e : Env) :
    opsOf e = [] ∨ (∃ d, opsOf e = [.issuer d]) ∨ (∃ d u, opsOf e = [.issuer d, .status u]) ∨
      (∃ d u q, opsOf e = [.issuer d, .status u, .replay q]) := by
  unfold opsOf
  repeat' split
  all_goals simp

/-- The issuer registry is read exactly when P1 passed. -/
theorem issuer_read_iff_p1 (e : Env) : (∃ d, Op.issuer d ∈ opsOf e) ↔ (staged e).get .P1 = .pass := by
  rw [staged_get]
  simp only [enginePrereq, List.all_nil, ite_true, base]
  unfold opsOf
  split <;> simp_all

/-- The revocation state is read exactly when P3 passed: after the Grant is
    authentic, before P6. -/
theorem status_read_iff_p3 (e : Env) : (∃ u, Op.status u ∈ opsOf e) ↔ (staged e).get .P3 = .pass := by
  unfold opsOf staged Row.toChecks Row.get stagedRow
  repeat' split
  all_goals simp_all [proofStage, proofRow, earlyRow, actionStage]
  all_goals (try ((repeat' split) <;> simp_all))

def p1ToP14 : List Check :=
  [.P1, .P2, .P3, .P4, .P5, .P6, .P7, .P8, .P9, .P10, .P11, .P12, .P13, .P14]

theorem actionStage_early (e : Env) (g : GrantF) (r : Row) :
    ∀ k ∈ p1ToP14, (actionStage e g r).get k = r.get k := by
  intro k hk
  unfold actionStage
  simp only [p1ToP14, List.mem_cons, List.not_mem_nil, or_false] at hk
  split <;> rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem proofStage_early_iff (e : Env) (g : GrantF) (t2 t3 p4 p5 p6 p7 : Outcome) (p : ProofF) :
    (∀ k ∈ p1ToP14, (proofStage e g t2 t3 p4 p5 p6 p7 p).get k = .pass) ↔ earlyPass e g p4 p5 p6 p7 p = true := by
  unfold proofStage
  generalize (if earlyPass e g p4 p5 p6 p7 p then replayOutcome (e.ρ (e.query p)) else Outcome.skipped) = t5
  have base : ∀ k ∈ p1ToP14, (proofRow e g t2 t3 p4 p5 p6 p7 p t5).get k =
      (earlyRow e g t2 t3 p4 p5 p6 p7 p t5).get k := by
    intro k hk
    unfold proofRow
    split
    · exact actionStage_early e g _ k hk
    · rfl
  constructor
  · intro h
    have hk : ∀ k ∈ p1ToP14, (earlyRow e g t2 t3 p4 p5 p6 p7 p t5).get k = .pass :=
      fun k hk => (base k hk).symm.trans (h k hk)
    simp only [p1ToP14, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      earlyRow, Row.get] at hk
    simp [earlyPass, hk]
  · intro h k hk
    rw [base k hk]
    simp only [earlyPass, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at h
    simp only [p1ToP14, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [earlyRow, Row.get]

/-- **Erratum 1, the replay write:** the `jti` is consumed exactly when P1
    to P14 all passed (§5.3, §7). -/
theorem replay_write_iff (e : Env) :
    (∃ q, Op.replay q ∈ opsOf e) ↔ ∀ k ∈ p1ToP14, (staged e).get k = .pass := by
  have hs : ∀ k, (staged e).get k = (stagedRow e).get k := fun _ => rfl
  simp only [hs]
  unfold opsOf stagedRow
  rcases hg : e.grant with r | g
  · simp [p1ToP14, Row.get]
  · rcases hi : e.s.issuer g.issuer with _ | _ | ⟨dv, comp, doc⟩
    · simp [hi, p1ToP14, Row.get]
    · simp [hi, p1ToP14, Row.get]
    · rcases hk : findKey e.π doc g.issuer g.kid with _ | key
      · simp [hi, hk, p1ToP14, Row.get]
      · by_cases hsig : e.π.sigOk key g.signingInput g.signature = true
        · rcases hp : e.proof with _ | p
          · simp [hi, hk, hsig, p1ToP14, Row.get]
          · simp only [hi, hk, hsig, ite_true]
            rw [proofStage_early_iff]
            by_cases he : earlyPass e g (p4Of e g) (p5Of e g) (p6Of e g) (p7Of e g) p = true <;> simp [he]
        · simp [hi, hk, hsig, p1ToP14, Row.get]

/-- The replay write happens only after P1–P14 pass. -/
theorem setnx_only_after_p14 (e : Env) (q : ReplayQuery) (h : Op.replay q ∈ opsOf e) :
    ∀ k ∈ p1ToP14, (staged e).get k = .pass :=
  (replay_write_iff e).mp ⟨q, h⟩

/-- **A revoked, forged or expired request never burns the `jti`:** if P6
    (or any of P1–P14) is not `true`, no replay write happens. -/
theorem revoked_never_burns_jti (e : Env) (h : (staged e).get .P6 ≠ .pass) :
    ∀ q, Op.replay q ∉ opsOf e :=
  fun q hq => h (setnx_only_after_p14 e q hq .P6 (by simp [p1ToP14]))

/-- The revocation read comes before the replay write (erratum 1): when
    both happen, the read is first. -/
theorem status_read_before_replay_write (e : Env) {u : String} {q : ReplayQuery}
    (hu : Op.status u ∈ opsOf e) (hq : Op.replay q ∈ opsOf e) :
    (opsOf e).idxOf (Op.status u) < (opsOf e).idxOf (Op.replay q) := by
  rcases trace_shape e with h | ⟨d, h⟩ | ⟨d, u', h⟩ | ⟨d, u', q', h⟩ <;> rw [h] at hu hq ⊢ <;> simp_all
  simp [List.idxOf, List.findIdx_cons]

/-- **Revoked and replayed at once: revocation wins.** If everything before
    P6 passed and P6 is `AUTHORITY_REVOKED`, that is the reason, whatever the
    replay store answers, because P6 precedes T5 (§5.4, §7). -/
theorem revoked_beats_replayed (e : Env)
    (hpre : ∀ k ∈ [Check.P1, .T1, .T2, .T3, .P2, .P3, .P4, .P5], (staged e).get k = .pass)
    (h6 : (staged e).get .P6 = .fail .AUTHORITY_REVOKED) :
    (kernel (staged e)).reason = some .AUTHORITY_REVOKED := by
  refine (reason_first_fail _ _).mpr ⟨[.P1, .T1, .T2, .T3, .P2, .P3, .P4, .P5], .P6,
    [.P7, .P8, .P9, .P10, .P11, .P12, .P13, .P14, .T5, .P15, .P16, .P17, .P18, .P19, .P20], rfl, h6, ?_⟩
  intro k hk
  simp [hpre k hk, Outcome.isFail]

/-- The answers two service states give to one operation agree. -/
def AgreeOn (s₁ s₂ : Snapshots) (ρ₁ ρ₂ : ReplayQuery → ReplayAnswer) : Op → Prop
  | .issuer d => s₁.issuer d = s₂.issuer d
  | .status u => s₁.status u = s₂.status u
  | .replay q => ρ₁ q = ρ₂ q

/-- **Only the answers to the operations actually performed matter**
    (plan §2.3, `seams_congr`): two service states that answer every
    operation of the first evaluation's trace the same way give the same
    result and the same trace. -/
theorem seams_congr {π : Prims} {req : Request} {tc : TrustConfig} {clk : Clock}
    {s₁ s₂ : Snapshots} {ρ₁ ρ₂ : ReplayQuery → ReplayAnswer}
    (h : ∀ o ∈ opsOf (envOf π req s₁ tc clk ρ₁), AgreeOn s₁ s₂ ρ₁ ρ₂ o) :
    stagedRow (envOf π req s₁ tc clk ρ₁) = stagedRow (envOf π req s₂ tc clk ρ₂) ∧
      opsOf (envOf π req s₁ tc clk ρ₁) = opsOf (envOf π req s₂ tc clk ρ₂) := by
  have hg2 : (envOf π req s₂ tc clk ρ₂).grant = (envOf π req s₁ tc clk ρ₁).grant := rfl
  have hp2 : (envOf π req s₂ tc clk ρ₂).proof = (envOf π req s₁ tc clk ρ₁).proof := rfl
  unfold opsOf at h
  unfold stagedRow opsOf
  rw [hg2, hp2]
  rcases hg : (envOf π req s₁ tc clk ρ₁).grant with r | g
  · constructor <;> first | rfl | trivial
  · simp only [hg] at h
    have hi : s₁.issuer g.issuer = s₂.issuer g.issuer := h (.issuer g.issuer) (List.mem_cons_self ..)
    simp only [envOf] at hi ⊢
    rw [← hi]
    rcases hi1 : s₁.issuer g.issuer with _ | _ | ⟨dv, comp, doc⟩
    · constructor <;> first | rfl | trivial
    · constructor <;> first | rfl | trivial
    · simp only [hi1] at h ⊢
      rcases hk : findKey π doc g.issuer g.kid with _ | key
      · constructor <;> first | rfl | trivial
      · simp only [hk] at h ⊢
        by_cases hs : π.sigOk key g.signingInput g.signature = true
        · simp only [hs, ite_true] at h ⊢
          have hst : s₁.status g.statusUrl = s₂.status g.statusUrl := h (.status g.statusUrl) (by simp)
          have h6 : p6Of (envOf π req s₂ tc clk ρ₂) g = p6Of (envOf π req s₁ tc clk ρ₁) g := by
            simp only [p6Of, hst]
          simp only [envOf] at h6
          rcases hp : (envOf π req s₁ tc clk ρ₁).proof with _ | p
          · simp only [envOf] at hp
            simp only [h6]
            constructor <;> first | rfl | trivial
          · simp only [envOf] at hp
            simp only [hp] at h ⊢
            by_cases he : earlyPass (envOf π req s₁ tc clk ρ₁) g (p4Of (envOf π req s₁ tc clk ρ₁) g)
                (p5Of (envOf π req s₁ tc clk ρ₁) g) (p6Of (envOf π req s₁ tc clk ρ₁) g)
                (p7Of (envOf π req s₁ tc clk ρ₁) g) p = true
            · simp only [envOf] at he
              simp only [he, ite_true] at h
              have hr : ρ₁ (Env.query ⟨π, req, s₁, tc, clk, ρ₁⟩ p) = ρ₂ (Env.query ⟨π, req, s₁, tc, clk, ρ₁⟩ p) :=
                h (.replay _) (by simp)
              constructor
              · simp only [proofStage, h6, he]
                have he2 : earlyPass ⟨π, req, s₂, tc, clk, ρ₂⟩ g (p4Of ⟨π, req, s₂, tc, clk, ρ₂⟩ g)
                    (p5Of ⟨π, req, s₂, tc, clk, ρ₂⟩ g) (p6Of ⟨π, req, s₁, tc, clk, ρ₁⟩ g)
                    (p7Of ⟨π, req, s₂, tc, clk, ρ₂⟩ g) p = true := he
                simp only [he2, ite_true]
                exact congrArg _ (congrArg replayOutcome hr)
              · simp only [h6]
                have he2 : earlyPass ⟨π, req, s₂, tc, clk, ρ₂⟩ g (p4Of ⟨π, req, s₂, tc, clk, ρ₂⟩ g)
                    (p5Of ⟨π, req, s₂, tc, clk, ρ₂⟩ g) (p6Of ⟨π, req, s₁, tc, clk, ρ₁⟩ g)
                    (p7Of ⟨π, req, s₂, tc, clk, ρ₂⟩ g) p = true := he
                simp only [he, he2, ite_true]
                rfl
            · simp only [envOf] at he
              have he2 : ¬ earlyPass ⟨π, req, s₂, tc, clk, ρ₂⟩ g (p4Of ⟨π, req, s₂, tc, clk, ρ₂⟩ g)
                  (p5Of ⟨π, req, s₂, tc, clk, ρ₂⟩ g) (p6Of ⟨π, req, s₁, tc, clk, ρ₁⟩ g)
                  (p7Of ⟨π, req, s₂, tc, clk, ρ₂⟩ g) p = true := he
              simp only [proofStage, h6, he, he2, ite_false, Bool.false_eq_true]
              constructor <;> first | rfl | trivial
        · simp only [hs, Bool.false_eq_true, ite_false]
          constructor <;> first | rfl | trivial

end DelegusCheck
