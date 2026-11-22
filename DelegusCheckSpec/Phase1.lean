/-
Copyright 2026 Inam Haq. Licensed under the Apache License, Version 2.0.

Phase 1 theorems about the full evaluator `evaluate` (§5): how each check
relates to its rule and prerequisites, fail closed, determinism, and the
plan's §2.7 rows. Every statement is for every input and every `Prims`.
-/
import DelegusCheckSpec.Facts
import DelegusCheckSpec.Theorems

namespace DelegusCheck

open Lean (Json)

/-! ## Each evaluated check follows the table -/

/-- Check `k` is its own rule when every prerequisite is `true`, and
    `skipped` otherwise. -/
theorem staged_get (e : Env) (k : Check) :
    (staged e).get k =
      if (enginePrereq k).all (fun p => (staged e).get p == .pass) then base e k else .skipped := by
  rw [staged_eq_table]
  cases k <;> rfl

theorem not_pass_of_base {e : Env} {k : Check} (h : base e k ≠ .pass) : (staged e).get k ≠ .pass := by
  rw [staged_get]
  split <;> simp_all

theorem base_of_pass {e : Env} {k : Check} (h : (staged e).get k = .pass) : base e k = .pass := by
  rw [staged_get] at h
  split at h <;> simp_all

theorem prereq_of_pass {e : Env} {k : Check} (h : (staged e).get k = .pass) :
    ∀ p ∈ enginePrereq k, (staged e).get p = .pass := by
  rw [staged_get] at h
  split at h
  · rename_i hall
    intro p hp
    have := List.all_eq_true.mp hall p hp
    simpa using this
  · cases h

/-- The evaluator's environment for these inputs. -/
abbrev envOf (π : Prims) (req : Request) (s : Snapshots) (tc : TrustConfig) (clk : Clock)
    (ρ : ReplayQuery → ReplayAnswer) : Env := ⟨π, req, s, tc, clk, ρ⟩

theorem evaluate_result (π : Prims) (req : Request) (s : Snapshots) (tc : TrustConfig) (clk : Clock)
    (ρ : ReplayQuery → ReplayAnswer) :
    (evaluate π req s tc clk ρ).result = kernel (staged (envOf π req s tc clk ρ)) := rfl

section
variable {π : Prims} {req : Request} {s : Snapshots} {tc : TrustConfig} {clk : Clock}
  {ρ : ReplayQuery → ReplayAnswer}

theorem deny_of_base (k : Check) (h : base (envOf π req s tc clk ρ) k ≠ .pass) :
    (evaluate π req s tc clk ρ).result.decision = .deny :=
  deny_of_not_pass _ k (not_pass_of_base h)

theorem base_of_allow (h : (evaluate π req s tc clk ρ).result.decision = .allow) (k : Check) :
    base (envOf π req s tc clk ρ) k = .pass :=
  base_of_pass ((allow_iff_every_check _).mp h k)

theorem ok_pass {b : Bool} {r : Reason} : ok b r = .pass ↔ b = true := by
  cases b <;> simp [ok]

theorem ok_ne_skipped (b : Bool) (r : Reason) : ok b r ≠ .skipped := by
  cases b <;> simp [ok]

/-! ## Fail closed (§0 constraint 3) -/

/-- An unreadable issuer registry is DENY (§0.3; T1). -/
theorem issuer_unavailable_denies (h : ∀ d, s.issuer d = .unavailable) :
    (evaluate π req s tc clk ρ).result.decision = .deny := by
  rcases hg : parseGrant π req.grant with r | g
  · exact deny_of_base .P1 (by simp [base, Env.grant, hg])
  · exact deny_of_base .T1 (by simp [base, Env.grant, hg, h, t1Of])

/-- Unavailable revocation state is DENY (§7; P6). -/
theorem status_unavailable_denies (h : ∀ u, s.status u = .unavailable) :
    (evaluate π req s tc clk ρ).result.decision = .deny := by
  rcases hg : parseGrant π req.grant with r | g
  · exact deny_of_base .P1 (by simp [base, Env.grant, hg])
  · exact deny_of_base .P6 (by simp [base, Env.grant, hg, p6Of, p6From, h])

/-- An unavailable replay store is DENY (§5.3; T5). -/
theorem replay_unavailable_denies (h : ∀ q, ρ q = .unavailable) :
    (evaluate π req s tc clk ρ).result.decision = .deny := by
  rcases hp : parseProof π req.proof with _ | p
  · exact deny_of_base .P8 (by simp [base, Env.proof, hp, ok])
  · exact deny_of_base .T5 (by simp [base, Env.proof, hp, h, replayOutcome])

theorem exactKeys_has {j : Json} {ks : List String} {k : String} (h : exactKeys j ks = true)
    (hk : k ∈ ks) : has j k = true := by
  simp only [exactKeys, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1.2 k hk

/-- A Grant without `credentialStatus` is DENY (§3.2 row 14; P1). -/
theorem no_status_entry_denies
    (h : ∀ j, π.decodeJws req.grant = some j → has j.payload "credentialStatus" = false) :
    (evaluate π req s tc clk ρ).result.decision = .deny := by
  apply deny_of_base .P1
  rcases hg : parseGrant π req.grant with r | g
  · simp [base, Env.grant, hg]
  · obtain ⟨j, hj, -, -, hp⟩ := parseGrant_ok hg
    have := exactKeys_has (grantPayload_sound hp).1 (k := "credentialStatus") (by simp [grantTop])
    simp [h j hj] at this

/-- A Grant whose JOSE header does not name EdDSA is DENY (§3.1; P1). -/
theorem grant_non_eddsa_denies
    (h : ∀ j, π.decodeJws req.grant = some j → fieldIs j.header "alg" "EdDSA" = false) :
    (evaluate π req s tc clk ρ).result.decision = .deny := by
  apply deny_of_base .P1
  rcases hg : parseGrant π req.grant with r | g
  · simp [base, Env.grant, hg]
  · obtain ⟨j, hj, hh, -, -⟩ := parseGrant_ok hg
    exact absurd (grantHeaderOk_alg hh) (by simp [h j hj])

/-- A Proof whose JOSE header does not name EdDSA is DENY (§4.1; P8). -/
theorem proof_non_eddsa_denies
    (h : ∀ j, π.decodeJws req.proof = some j → fieldIs j.header "alg" "EdDSA" = false) :
    (evaluate π req s tc clk ρ).result.decision = .deny := by
  apply deny_of_base .P8
  rcases hp : parseProof π req.proof with _ | p
  · simp [base, Env.proof, hp, ok]
  · obtain ⟨j, hj, ha, -⟩ := parseProof_sound hp
    simp [h j hj] at ha

/-- A Grant that does not decode (including duplicate members or unsafe
    integers, which the strict decoder rejects) is DENY (P1). -/
theorem grant_undecodable_denies (h : π.decodeJws req.grant = none) :
    (evaluate π req s tc clk ρ).result.decision = .deny := by
  apply deny_of_base .P1
  obtain ⟨r, hr⟩ := parseGrant_undecodable (π := π) h
  simp [base, Env.grant, hr]

/-- A Proof that does not decode is DENY (P8). -/
theorem proof_undecodable_denies (h : π.decodeJws req.proof = none) :
    (evaluate π req s tc clk ρ).result.decision = .deny := by
  apply deny_of_base .P8
  simp [base, Env.proof, parseProof, h, ok]

/-- The reason is P1's code whenever P1 is false: P1 comes first. -/
theorem reason_of_p1 {e : Env} {r : Reason} (h : (staged e).get .P1 = .fail r) :
    (kernel (staged e)).reason = some r :=
  (reason_first_fail _ r).mpr ⟨[], .P1, order.tail, rfl, h, by simp⟩

/-- A Grant carrying `parentGrant` (with a well-formed header and within the
    size limit) is DENY with `UNSUPPORTED_FEATURE` (§3.2 row 15). The header
    condition comes from the pending P1-precedence reading (`p1Code`). -/
theorem parent_grant_denies {j : Jws} (hs : req.grant.length ≤ grantMaxBytes)
    (hj : π.decodeJws req.grant = some j) (hh : grantHeaderOk j.header = true)
    (hp : has j.payload "parentGrant" = true) :
    (evaluate π req s tc clk ρ).result.reason = some .UNSUPPORTED_FEATURE := by
  apply reason_of_p1
  rw [staged_get]
  simp [enginePrereq, base, Env.grant, parseGrant_parent hs hj hh hp]

theorem authorize_p17_pass {caps : List Capability} {a : Action} (h : (authorize caps a).p17 = .pass) :
    ∀ c ∈ caps, c.action = a.type → allKeysKnown c = true := by
  revert h
  cases a <;> simp only [authorize] <;> (repeat' split) <;> simp_all

/-- A Grant carrying `parentGrant` is DENY, whatever else is wrong with it
    (§3.2 row 15; P1 is false with `UNSUPPORTED_FEATURE` or
    `GRANT_MALFORMED`, by the pending P1-precedence reading). -/
theorem parent_grant_denies_any {j : Jws} (hj : π.decodeJws req.grant = some j)
    (hp : has j.payload "parentGrant" = true) :
    (evaluate π req s tc clk ρ).result.decision = .deny := by
  apply deny_of_base .P1
  rcases hg : parseGrant π req.grant with r | g
  · simp [base, Env.grant, hg]
  · obtain ⟨j', hj', -, hnp, -⟩ := parseGrant_ok hg
    rw [hj] at hj'; cases hj'
    simp [hp] at hnp

/-- A candidate Capability with a constraint key this version does not
    evaluate is DENY (§3.3; P17). -/
theorem unknown_constraint_denies {g : GrantF} {a : Action} {c : Capability}
    (hg : parseGrant π req.grant = .ok g) (ha : validateAction req.action = some a)
    (hc : c ∈ g.authority) (hca : c.action = a.type) (hk : allKeysKnown c = false) :
    (evaluate π req s tc clk ρ).result.decision = .deny := by
  apply deny_of_base .P17
  simp only [base, Env.grant, Env.action, hg, ha]
  intro h17
  simp [authorize_p17_pass h17 c hc hca] at hk

theorem validateAction_fields {a : Json} {x : Action} (h : validateAction a = some x) :
    ∃ t fs, fieldStr? a "type" = some t ∧ actionFields t = some fs ∧ exactKeys a fs = true := by
  unfold validateAction at h
  peel h
  exact ⟨_, _, ‹_›, ‹_›, ‹_›⟩

/-- An Action whose members are not exactly its type's fields (an unknown
    field, a missing one, or an unknown type) is DENY (§5.1; P15). -/
theorem unknown_action_field_denies
    (h : ∀ t fs, fieldStr? req.action "type" = some t → actionFields t = some fs →
      exactKeys req.action fs = false) :
    (evaluate π req s tc clk ρ).result.decision = .deny := by
  apply deny_of_base .P15
  rcases hv : validateAction req.action with _ | x
  · simp [base, Env.action, hv, ok]
  · obtain ⟨t, fs, ht, hf, he⟩ := validateAction_fields hv
    simp [h t fs ht hf] at he

/-! ## Determinism (§0 constraint 2) -/

/-- Lean functions are deterministic, so this is `rfl`; the content is the
    signature of `evaluate`: it reads exactly the request, the snapshots, the
    trust configuration, the clock and the replay answer, and nothing else. -/
theorem deterministic :
    evaluate π req s tc clk ρ = evaluate π req s tc clk ρ := rfl

end

theorem t1Of_view {x y : IssuerLookup} (h : x.view = y.view) : t1Of x = t1Of y := by
  cases x <;> cases y <;> simp_all [IssuerLookup.view, t1Of]

theorem p2Of_view {π : Prims} {g : GrantF} {x y : IssuerLookup} (h : x.view = y.view) :
    p2Of π g x = p2Of π g y := by
  cases x <;> cases y <;> simp_all [IssuerLookup.view, p2Of]

theorem p3Of_view {π : Prims} {g : GrantF} {x y : IssuerLookup} (h : x.view = y.view) :
    p3Of π g x = p3Of π g y := by
  cases x <;> cases y <;> simp_all [IssuerLookup.view, p3Of]

theorem gate_congr {xs : List Outcome} {o₁ o₂ : Outcome} (h : (∀ x ∈ xs, x = .pass) → o₁ = o₂) :
    gate xs o₁ = gate xs o₂ := by
  unfold gate
  split
  · rename_i hall
    apply h
    intro x hx
    simpa using List.all_eq_true.mp hall x hx
  · rfl

/-- **The protocol layer depends only on what it reads** (§0 constraint 2,
    §5.2). Two evaluations of the same request with the same clock and trust
    configuration give the same 20 protocol checks when, for the Grant as
    parsed, the issuer registry gives the same registration answer and DID
    document for its Principal, and, once P3 has passed, the status-list
    snapshot for its URL is the same. Domain verification, compromised keys
    (T2, T3), the replay store (T5) and every other Principal or URL may
    differ freely. -/
theorem protocol_local {π : Prims} {req : Request} {clk : Clock} {tc : TrustConfig}
    {s₁ s₂ : Snapshots} {ρ₁ ρ₂ : ReplayQuery → ReplayAnswer}
    (hi : ∀ g, parseGrant π req.grant = .ok g → (s₁.issuer g.issuer).view = (s₂.issuer g.issuer).view)
    (hs : ∀ g, parseGrant π req.grant = .ok g →
      (staged (envOf π req s₁ tc clk ρ₁)).get .P3 = .pass → s₁.status g.statusUrl = s₂.status g.statusUrl) :
    ∀ k ∈ protocolChecks,
      (evaluate π req s₁ tc clk ρ₁).result.checks.get k = (evaluate π req s₂ tc clk ρ₂).result.checks.get k := by
  have hb : ∀ k, k ≠ .T2 → k ≠ .T3 → k ≠ .T5 → k ≠ .P6 →
      base (envOf π req s₁ tc clk ρ₁) k = base (envOf π req s₂ tc clk ρ₂) k := by
    intro k h2 h3 h5 h6
    cases k <;> simp_all [base, Env.grant, Env.proof, Env.action, Env.requestHash, p4Of, p5Of,
      p7Of, p9Of, p12Of, p13Of, p14Of]
    all_goals split
    all_goals first
      | exact t1Of_view (hi _ ‹_›) | exact p2Of_view (hi _ ‹_›) | exact p3Of_view (hi _ ‹_›) | rfl
  have h6 : (staged (envOf π req s₁ tc clk ρ₁)).get .P3 = .pass →
      base (envOf π req s₁ tc clk ρ₁) .P6 = base (envOf π req s₂ tc clk ρ₂) .P6 := by
    intro h3
    simp only [base, Env.grant]
    split
    · rename_i g hg
      simp only [p6Of, p6From, hs g hg h3]
    · rfl
  have bP1 := hb .P1 (by decide) (by decide) (by decide) (by decide)
  have bT1 := hb .T1 (by decide) (by decide) (by decide) (by decide)
  have bP2 := hb .P2 (by decide) (by decide) (by decide) (by decide)
  have bP3 := hb .P3 (by decide) (by decide) (by decide) (by decide)
  have bP4 := hb .P4 (by decide) (by decide) (by decide) (by decide)
  have bP5 := hb .P5 (by decide) (by decide) (by decide) (by decide)
  have bP7 := hb .P7 (by decide) (by decide) (by decide) (by decide)
  have bP8 := hb .P8 (by decide) (by decide) (by decide) (by decide)
  have bP9 := hb .P9 (by decide) (by decide) (by decide) (by decide)
  have bP10 := hb .P10 (by decide) (by decide) (by decide) (by decide)
  have bP11 := hb .P11 (by decide) (by decide) (by decide) (by decide)
  have bP12 := hb .P12 (by decide) (by decide) (by decide) (by decide)
  have bP13 := hb .P13 (by decide) (by decide) (by decide) (by decide)
  have bP14 := hb .P14 (by decide) (by decide) (by decide) (by decide)
  have bP15 := hb .P15 (by decide) (by decide) (by decide) (by decide)
  have bP16 := hb .P16 (by decide) (by decide) (by decide) (by decide)
  have bP17 := hb .P17 (by decide) (by decide) (by decide) (by decide)
  have bP18 := hb .P18 (by decide) (by decide) (by decide) (by decide)
  have bP19 := hb .P19 (by decide) (by decide) (by decide) (by decide)
  have bP20 := hb .P20 (by decide) (by decide) (by decide) (by decide)
  have hX : (staged (envOf π req s₁ tc clk ρ₁)).get .P3 =
      (table (base (envOf π req s₂ tc clk ρ₂))).get .P3 := by
    rw [staged_eq_table]
    simp only [table, tableRow, Row.toChecks, Row.get, bP1, bT1, bP2, bP3]
  intro k hk
  simp only [evaluate_result, kernel]
  rw [staged_eq_table, staged_eq_table]
  simp only [protocolChecks, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  case inr.inr.inr.inr.inr.inl =>
    simp only [table, Row.toChecks] at hX ⊢
    simp only [tableRow, Row.get, bP1, bT1, bP2, bP3, bP4, bP5, bP7, bP8, bP9, bP10, bP11, bP12, bP13, bP14, bP15, bP16, bP17, bP18, bP19, bP20] at hX ⊢
    apply gate_congr
    intro hall
    apply h6
    rw [hX]
    exact hall _ (List.mem_singleton_self _)
  all_goals simp only [table, tableRow, Row.toChecks, Row.get, bP1, bT1, bP2, bP3, bP4, bP5, bP7, bP8, bP9, bP10, bP11, bP12, bP13, bP14, bP15, bP16, bP17, bP18, bP19, bP20]

/-- **The protocol layer is reproducible** (§0 constraint 2, §5.2): with the
    same request (Grant, Proof, Action, RP DID, window), clock, status-list
    snapshot, trust configuration (Delegus DID and status-list keys), and the
    same registration answer and DID document for every Principal, all 20
    protocol checks come out the same. Domain verification, compromised keys
    (T2, T3) and the replay store (T5) may differ freely. -/
theorem protocol_reproducible {π : Prims} {req : Request} {clk : Clock} {tc : TrustConfig}
    {s₁ s₂ : Snapshots} {ρ₁ ρ₂ : ReplayQuery → ReplayAnswer}
    (hi : ∀ d, (s₁.issuer d).view = (s₂.issuer d).view) (hs : s₁.status = s₂.status) :
    ∀ k ∈ protocolChecks,
      (evaluate π req s₁ tc clk ρ₁).result.checks.get k = (evaluate π req s₂ tc clk ρ₂).result.checks.get k :=
  protocol_local (fun g _ => hi g.issuer) (fun _ _ _ => by rw [hs])

end DelegusCheck
