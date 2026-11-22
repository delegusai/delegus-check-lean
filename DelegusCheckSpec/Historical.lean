/-
Copyright 2026 Inam Haq. Licensed under the Apache License, Version 2.0.

Phase 3: offline re-verification of a receipt (§6.4) and the historical
verification clock (erratum 2). Attribution for restated spec text:
"Delegus Specification v0.2, © Delegus (delegus.ai)", CC BY 4.0.
-/
import DelegusCheckSpec.Phase1Rows

namespace DelegusCheck

open Lean (Json)

/-! ## The receipt, as far as re-verification uses it (§6.2, §6.3) -/

structure Receipt where
  /-- `evaluated_at`: the `now` of the decision, inside the signed payload. -/
  evaluatedAt : Clock
  relyingParty : Did
  /-- The Delegus DID (from the receipt key's `kid`), the status-list issuer. -/
  serviceDid : Did
  /-- `protocol.checks` and `trust.checks`. -/
  checks : Checks
  decision : Decision
  reason : Option Reason
  grantHash : String
  proofHash : String
  requestHash : Option String
  /-- `evidence.issuer_resolution.did_document_hash`, present when the
      Principal was registered (T1 passed). -/
  didDocumentHash : Option String
  /-- `evidence.status.credential_hash`, present when the status credential
      was read (after P3) and was available. -/
  credentialHash : Option String

/-- The receipt of an evaluation. -/
def receiptOf (π : Prims) (req : Request) (s : Snapshots) (tc : TrustConfig) (clk : Clock)
    (ρ : ReplayQuery → ReplayAnswer) : Receipt :=
  let e := envOf π req s tc clk ρ
  let c := staged e
  { evaluatedAt := clk, relyingParty := req.rp, serviceDid := tc.serviceDid, checks := c,
    decision := (kernel c).decision, reason := (kernel c).reason,
    grantHash := π.sha256 req.grant, proofHash := π.sha256 req.proof, requestHash := e.requestHash,
    didDocumentHash := match e.grant with
      | .ok g => match s.issuer g.issuer with
        | .registered _ _ doc => some (π.sha256 doc)
        | _ => none
      | .error _ => none,
    credentialHash := match e.grant with
      | .ok g => if c.get .P3 = .pass then
          (match s.status g.statusUrl with
           | .snapshot cr => some (π.sha256 cr)
           | .unavailable => none)
        else none
      | .error _ => none }

/-! ## Offline re-verification (§6.4) -/

/-- What a third party holds besides the receipt: the Grant, Proof and Action
    the RP presented, the artifacts retrieved by hash (§8), the Delegus
    status-list keys, and the RP's Proof window. -/
structure Artifacts where
  grant : String
  proof : String
  action : Json
  didDocument : Option String
  credential : Option String
  statusKeys : List (String × PubKey)
  /-- The RP's Proof window at the time. It is not recorded in the receipt
      (§6.2), so the verifier must know it from elsewhere; see the README. -/
  windowS : Nat

/-- The service state as the receipt and artifacts show it. The trust block
    is replayed from the receipt, not recomputed (§6.4). -/
def replayedSnapshots (rc : Receipt) (art : Artifacts) : Snapshots where
  issuer _ := match rc.didDocumentHash, art.didDocument with
    | some _, some d => .registered (rc.checks.get .T2 == .pass) [] d
    | _, _ => if rc.checks.get .T1 = .fail .SERVICE_UNAVAILABLE then .unavailable else .unknown
  status _ := match rc.credentialHash, art.credential with
    | some _, some c => .snapshot c
    | _, _ => .unavailable

def replayedRequest (rc : Receipt) (art : Artifacts) : Request :=
  { grant := art.grant, proof := art.proof, action := art.action, rp := rc.relyingParty, windowS := art.windowS }

def replayedTrust (rc : Receipt) (art : Artifacts) : TrustConfig :=
  { serviceDid := rc.serviceDid, statusKeys := art.statusKeys }

def replayedReplay (rc : Receipt) : ReplayQuery → ReplayAnswer :=
  fun _ => if rc.checks.get .T5 = .pass then .ok else .replayed

/-- Re-run the evaluation for a receipt. **Erratum 2:** `now` is the
    receipt's `evaluated_at`; the verifier's own wall clock `_wall` is an
    argument only to show that it is not used. -/
def reverify (π : Prims) (rc : Receipt) (art : Artifacts) (_wall : Clock) : Checks :=
  staged (envOf π (replayedRequest rc art) (replayedSnapshots rc art) (replayedTrust rc art)
    rc.evaluatedAt (replayedReplay rc))

/-- The artifacts are the ones the receipt pins by hash (§6.3). -/
def ArtifactsMatch (π : Prims) (rc : Receipt) (art : Artifacts) : Prop :=
  π.sha256 art.grant = rc.grantHash ∧ π.sha256 art.proof = rc.proofHash ∧
  (∀ h, rc.didDocumentHash = some h → ∃ d, art.didDocument = some d ∧ π.sha256 d = h) ∧
  (∀ h, rc.credentialHash = some h → ∃ c, art.credential = some c ∧ π.sha256 c = h)

/-! ## Theorems -/

/-- **Erratum 2, "MUST NOT use its own wall-clock time":** re-verification
    does not depend on the verifier's clock. -/
theorem reverify_ignores_wall (π : Prims) (rc : Receipt) (art : Artifacts) (w₁ w₂ : Clock) :
    reverify π rc art w₁ = reverify π rc art w₂ := rfl

/-- Re-verification evaluates at the receipt's `evaluated_at`. -/
theorem reverify_clock (π : Prims) (rc : Receipt) (art : Artifacts) (w : Clock) :
    reverify π rc art w = staged (envOf π (replayedRequest rc art) (replayedSnapshots rc art)
      (replayedTrust rc art) rc.evaluatedAt (replayedReplay rc)) := rfl

/-- T1 of an evaluation whose Grant parsed is the issuer answer's own rule. -/
theorem t1_of_grant {e : Env} {g : GrantF} (hg : e.grant = .ok g) :
    (staged e).get .T1 = t1Of (e.s.issuer g.issuer) := by
  rw [staged_eq_table]
  simp [table, tableRow, Row.toChecks, Row.get, base, hg, gate]

/-- **Offline re-verification reproduces the decision's protocol layer**
    (§6.4 with erratum 2). Given the receipt of any evaluation, artifacts
    that match its pinned hashes, the same Action and the RP's Proof window,
    and the Delegus status-list keys, re-running at the receipt's
    `evaluated_at` gives the same 20 protocol checks, whatever the wall
    clock. Assumes SHA-256 is injective (a hypothesis, not an axiom). -/
theorem reverify_reproduces {π : Prims} {req : Request} {s : Snapshots} {tc : TrustConfig} {clk : Clock}
    {ρ : ReplayQuery → ReplayAnswer} {art : Artifacts}
    (hinj : Function.Injective π.sha256)
    (hm : ArtifactsMatch π (receiptOf π req s tc clk ρ) art)
    (ha : art.action = req.action) (hw : art.windowS = req.windowS) (hk : art.statusKeys = tc.statusKeys)
    (wall : Clock) :
    ∀ k ∈ protocolChecks,
      (reverify π (receiptOf π req s tc clk ρ) art wall).get k = (evaluate π req s tc clk ρ).result.checks.get k := by
  obtain ⟨hgr, hpr, hdoc, hcred⟩ := hm
  have hg : art.grant = req.grant := hinj hgr
  have hp : art.proof = req.proof := hinj hpr
  have hreq : replayedRequest (receiptOf π req s tc clk ρ) art = req := by
    cases req; simp_all [replayedRequest, receiptOf]
  have htc : replayedTrust (receiptOf π req s tc clk ρ) art = tc := by
    cases tc; simp_all [replayedTrust, receiptOf]
  rw [reverify_clock, hreq, htc]
  intro k hk
  refine (protocol_local (s₁ := s) (ρ₁ := ρ) ?_ ?_ k hk).symm
  · intro g hgo
    have hT1 := t1_of_grant (e := envOf π req s tc clk ρ) hgo
    rcases hiss : s.issuer g.issuer with _ | _ | ⟨dv, comp, doc⟩
    · have : (receiptOf π req s tc clk ρ).didDocumentHash = none := by
        simp [receiptOf, Env.grant, hgo, hiss]
      have hc : (receiptOf π req s tc clk ρ).checks = staged (envOf π req s tc clk ρ) := rfl
      simp only [replayedSnapshots, this, hc, hT1]
      simp [hiss, t1Of, IssuerLookup.view]
    · have : (receiptOf π req s tc clk ρ).didDocumentHash = none := by
        simp [receiptOf, Env.grant, hgo, hiss]
      have hc : (receiptOf π req s tc clk ρ).checks = staged (envOf π req s tc clk ρ) := rfl
      simp only [replayedSnapshots, this, hc, hT1]
      simp [hiss, t1Of, IssuerLookup.view]
    · have hh : (receiptOf π req s tc clk ρ).didDocumentHash = some (π.sha256 doc) := by
        simp [receiptOf, Env.grant, hgo, hiss]
      obtain ⟨d, hd, hdh⟩ := hdoc _ hh
      have : d = doc := hinj hdh
      subst this
      simp [replayedSnapshots, hh, hd, IssuerLookup.view]
  · intro g hgo h3
    rcases hst : s.status g.statusUrl with _ | cr
    · have : (receiptOf π req s tc clk ρ).credentialHash = none := by
        simp [receiptOf, Env.grant, hgo, hst]
      simp [replayedSnapshots, this]
    · have hh : (receiptOf π req s tc clk ρ).credentialHash = some (π.sha256 cr) := by
        have h3' : (staged (envOf π req s tc clk ρ)).get .P3 = .pass := h3
        simp [receiptOf, Env.grant, hgo, hst, h3']
      obtain ⟨c, hc, hch⟩ := hcred _ hh
      have : c = cr := hinj hch
      subst this
      simp [replayedSnapshots, hh, hc]

/-- **Why erratum 2 is needed:** re-checking an ALLOW with the wall clock
    breaks as soon as the Grant expires. If a decision was ALLOW at time `t`,
    the same inputs evaluated at any `w` at or after the Grant's
    `validUntil` give `GRANT_EXPIRED`. -/
theorem wall_clock_breaks {π : Prims} {req : Request} {s : Snapshots} {tc : TrustConfig} {t : Int}
    {ρ : ReplayQuery → ReplayAnswer} (h : (evaluate π req s tc ⟨t⟩ ρ).result.decision = .allow) :
    ∃ g, parseGrant π req.grant = .ok g ∧
      ∀ w, g.validUntilMs ≤ w → (evaluate π req s tc ⟨w⟩ ρ).result.reason = some .GRANT_EXPIRED := by
  obtain ⟨g, hg, hvf, hvu, -⟩ := grant_window h
  refine ⟨g, hg, fun w hw => ?_⟩
  have hall := (allow_iff_every_check _).mp h
  -- P1, T1, T2, T3, P2, P3 do not read the clock
  have same : ∀ k ∈ [Check.P1, .T1, .T2, .T3, .P2, .P3],
      (staged (envOf π req s tc ⟨w⟩ ρ)).get k = (staged (envOf π req s tc ⟨t⟩ ρ)).get k := by
    intro k hk
    rw [staged_eq_table, staged_eq_table]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have pass_w : ∀ k ∈ [Check.P1, .T1, .T2, .T3, .P2, .P3], (staged (envOf π req s tc ⟨w⟩ ρ)).get k = .pass :=
    fun k hk => (same k hk).trans (hall k)
  have p3w := pass_w .P3 (by simp)
  have p4w : (staged (envOf π req s tc ⟨w⟩ ρ)).get .P4 = .pass := by
    rw [staged_get]
    simp [enginePrereq, p3w, base, Env.grant, hg, p4Of, ok]
    omega
  have p5w : (staged (envOf π req s tc ⟨w⟩ ρ)).get .P5 = .fail .GRANT_EXPIRED := by
    rw [staged_get]
    simp [enginePrereq, p3w, base, Env.grant, hg, p5Of, ok]
    omega
  simp only [evaluate_result]
  refine (reason_first_fail _ _).mpr ⟨[.P1, .T1, .T2, .T3, .P2, .P3, .P4], .P5,
    [.P6, .P7, .P8, .P9, .P10, .P11, .P12, .P13, .P14, .T5, .P15, .P16, .P17, .P18, .P19, .P20],
    rfl, p5w, ?_⟩
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [pass_w .P1 (by simp), Outcome.isFail]
  · simp [pass_w .T1 (by simp), Outcome.isFail]
  · simp [pass_w .T2 (by simp), Outcome.isFail]
  · simp [pass_w .T3 (by simp), Outcome.isFail]
  · simp [pass_w .P2 (by simp), Outcome.isFail]
  · simp [pass_w .P3 (by simp), Outcome.isFail]
  · simp [p4w, Outcome.isFail]

/-- **`evaluated_at` is bound by the Delegus signature** (§6.4), as a
    statement about the hypotheses it rests on: if a verifying signature
    under Delegus's receipt key means Delegus signed (`hsig`), Delegus signs
    only encodings of receipts it issued (`honly`), and the encoding is
    injective (`henc`), then a receipt that verifies is one Delegus issued,
    so its `evaluated_at` is the one Delegus recorded. -/
theorem evaluated_at_bound {π : Prims} (dk : PubKey) (SignedBy : PubKey → String → Prop)
    (encode : Receipt → String) (issued : Receipt → Prop)
    (hsig : ∀ m σ, π.sigOk dk m σ = true → SignedBy dk m)
    (honly : ∀ m, SignedBy dk m → ∃ rc, issued rc ∧ encode rc = m)
    (henc : Function.Injective encode) {rc' : Receipt} {σ : String}
    (hv : π.sigOk dk (encode rc') σ = true) :
    ∃ rc, issued rc ∧ rc = rc' ∧ rc.evaluatedAt = rc'.evaluatedAt := by
  obtain ⟨rc, hi, he⟩ := honly _ (hsig _ _ hv)
  exact ⟨rc, hi, henc he, by rw [henc he]⟩

end DelegusCheck
