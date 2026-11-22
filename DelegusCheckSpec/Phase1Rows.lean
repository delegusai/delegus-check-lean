/-
Copyright 2026 Inam Haq. Licensed under the Apache License, Version 2.0.

Phase 1: the evaluator's outcomes are well formed (so the Phase 0 kernel
theorems apply to it), and the plan's §2.7 rows, including the threat-model
rows of §13.1 that this model can state.
-/
import DelegusCheckSpec.Phase1

namespace DelegusCheck

open Lean (Json)

/-! ## Chains of prerequisites -/

theorem pass_prereq {e : Env} {k p : Check} (h : (staged e).get k = .pass) (hp : p ∈ enginePrereq k) :
    (staged e).get p = .pass := prereq_of_pass h p hp

theorem grant_of_p3 {e : Env} (h : (staged e).get .P3 = .pass) : ∃ g, e.grant = .ok g := by
  have hb := base_of_pass h
  revert hb
  simp only [base]
  split
  · exact fun _ => ⟨_, ‹_›⟩
  · simp

theorem proof_of_p8 {e : Env} (h : (staged e).get .P8 = .pass) : ∃ p, e.proof = some p := by
  have hb := base_of_pass h
  simp only [base, ok_pass, Option.isSome_iff_exists] at hb
  exact hb

theorem action_of_p15 {e : Env} (h : (staged e).get .P15 = .pass) : ∃ a, e.action = some a := by
  have hb := base_of_pass h
  simp only [base, ok_pass, Option.isSome_iff_exists] at hb
  exact hb

theorem p3_of_p8 {e : Env} (h : (staged e).get .P8 = .pass) : (staged e).get .P3 = .pass :=
  pass_prereq h (by simp [enginePrereq])
theorem p8_of_p14 {e : Env} (h : (staged e).get .P14 = .pass) : (staged e).get .P8 = .pass :=
  pass_prereq h (by simp [enginePrereq])
theorem p14_of_p15 {e : Env} (h : (staged e).get .P15 = .pass) : (staged e).get .P14 = .pass :=
  pass_prereq h (by simp [enginePrereq])
theorem p15_of_p16 {e : Env} (h : (staged e).get .P16 = .pass) : (staged e).get .P15 = .pass :=
  pass_prereq h (by simp [enginePrereq])
theorem p16_of_p17 {e : Env} (h : (staged e).get .P17 = .pass) : (staged e).get .P16 = .pass :=
  pass_prereq h (by simp [enginePrereq])
theorem p17_of_p18 {e : Env} (h : (staged e).get .P18 = .pass) : (staged e).get .P17 = .pass :=
  pass_prereq h (by simp [enginePrereq])
theorem p18_of_p19 {e : Env} (h : (staged e).get .P19 = .pass) : (staged e).get .P18 = .pass :=
  pass_prereq h (by simp [enginePrereq])
theorem p19_of_p20 {e : Env} (h : (staged e).get .P20 = .pass) : (staged e).get .P19 = .pass :=
  pass_prereq h (by simp [enginePrereq])

theorem authorize_next (caps : List Capability) (a : Action) :
    ((authorize caps a).p16 = .pass → (authorize caps a).p17 ≠ .skipped) ∧
    ((authorize caps a).p17 = .pass → (authorize caps a).p18 ≠ .skipped) ∧
    ((authorize caps a).p18 = .pass → (authorize caps a).p19 ≠ .skipped) ∧
    ((authorize caps a).p19 = .pass → (authorize caps a).p20 ≠ .skipped) := by
  cases a <;> simp only [authorize] <;> (repeat' split) <;> simp_all [nonempty] <;> split <;> simp

theorem t1Of_ne_skipped (x : IssuerLookup) : t1Of x ≠ .skipped := by cases x <;> simp [t1Of]
theorem replayOutcome_ne_skipped (x : ReplayAnswer) : replayOutcome x ≠ .skipped := by
  cases x <;> simp [replayOutcome]
theorem p6Of_ne_skipped (e : Env) (g : GrantF) : p6Of e g ≠ .skipped := by
  unfold p6Of p6From; split <;> simp; split <;> simp

/-- With every prerequisite `true`, a check's rule always has the data it
    needs: it is `true` or `false`, never skipped. -/
theorem base_ne_skipped (e : Env) (k : Check) (hall : ∀ p ∈ enginePrereq k, (staged e).get p = .pass) :
    base e k ≠ .skipped := by
  have pre : ∀ p, p ∈ enginePrereq k → (staged e).get p = .pass := hall
  cases k
  case P1 => simp only [base]; split <;> simp
  case T1 =>
    have h1 := base_of_pass (pre .P1 (by simp [enginePrereq]))
    simp only [base] at h1 ⊢; split <;> simp_all [t1Of_ne_skipped]
  case T2 | T3 | P2 =>
    have h1 := base_of_pass (pre .T1 (by simp [enginePrereq]))
    simp only [base] at h1 ⊢
    split <;> simp_all
    rename_i g _
    revert h1; cases e.s.issuer g.issuer <;> simp [t1Of, t2Of, t3Of, p2Of, ok_ne_skipped]
  case P3 =>
    have h2 := base_of_pass (pre .P2 (by simp [enginePrereq]))
    simp only [base] at h2 ⊢
    split <;> simp_all
    rename_i g _
    revert h2; cases e.s.issuer g.issuer <;> simp [p2Of, p3Of, ok_pass]
    intro h; obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp h; simp [hk, ok_ne_skipped]
  case P4 | P5 | P6 | P7 | P8 =>
    obtain ⟨g, hg⟩ := grant_of_p3 (pre .P3 (by simp [enginePrereq]))
    simp [base, hg, p4Of, p5Of, p7Of, ok_ne_skipped, p6Of_ne_skipped]
  case P9 | P12 | P13 | P14 | T5 =>
    obtain ⟨p, hp⟩ := proof_of_p8 (pre .P8 (by simp [enginePrereq]))
    simp [base, hp, p9Of, p12Of, p13Of, p14Of, ok_ne_skipped, replayOutcome_ne_skipped]
  case P10 | P11 =>
    have h8 := pre .P8 (by simp [enginePrereq])
    obtain ⟨p, hp⟩ := proof_of_p8 h8
    obtain ⟨g, hg⟩ := grant_of_p3 (p3_of_p8 h8)
    simp [base, hp, hg, p10Of, p11Of, ok_ne_skipped]
  case P15 => simp [base, ok_ne_skipped]
  case P16 =>
    have h15 := pre .P15 (by simp [enginePrereq])
    obtain ⟨a, ha⟩ := action_of_p15 h15
    obtain ⟨g, hg⟩ := grant_of_p3 (p3_of_p8 (p8_of_p14 (p14_of_p15 h15)))
    simp only [base, hg, ha]
    rcases authorize_p16 g.authority a with h | h <;> simp [h]
  case P17 =>
    have hprev := pre .P16 (by simp [enginePrereq])
    have h15 : (staged e).get .P15 = .pass := p15_of_p16 hprev
    obtain ⟨a, ha⟩ := action_of_p15 h15
    obtain ⟨g, hg⟩ := grant_of_p3 (p3_of_p8 (p8_of_p14 (p14_of_p15 h15)))
    have hb := base_of_pass hprev
    simp only [base, hg, ha] at hb ⊢
    exact (authorize_next g.authority a).1 hb
  case P18 =>
    have hprev := pre .P17 (by simp [enginePrereq])
    have h15 : (staged e).get .P15 = .pass := p15_of_p16 (p16_of_p17 hprev)
    obtain ⟨a, ha⟩ := action_of_p15 h15
    obtain ⟨g, hg⟩ := grant_of_p3 (p3_of_p8 (p8_of_p14 (p14_of_p15 h15)))
    have hb := base_of_pass hprev
    simp only [base, hg, ha] at hb ⊢
    exact (authorize_next g.authority a).2.1 hb
  case P19 =>
    have hprev := pre .P18 (by simp [enginePrereq])
    have h15 : (staged e).get .P15 = .pass := p15_of_p16 (p16_of_p17 (p17_of_p18 hprev))
    obtain ⟨a, ha⟩ := action_of_p15 h15
    obtain ⟨g, hg⟩ := grant_of_p3 (p3_of_p8 (p8_of_p14 (p14_of_p15 h15)))
    have hb := base_of_pass hprev
    simp only [base, hg, ha] at hb ⊢
    exact (authorize_next g.authority a).2.2.1 hb
  case P20 =>
    have hprev := pre .P19 (by simp [enginePrereq])
    have h15 : (staged e).get .P15 = .pass := p15_of_p16 (p16_of_p17 (p17_of_p18 (p18_of_p19 hprev)))
    obtain ⟨a, ha⟩ := action_of_p15 h15
    obtain ⟨g, hg⟩ := grant_of_p3 (p3_of_p8 (p8_of_p14 (p14_of_p15 h15)))
    have hb := base_of_pass hprev
    simp only [base, hg, ha] at hb ⊢
    exact (authorize_next g.authority a).2.2.2 hb

/-! ## The evaluator's outcomes are well formed -/

/-- Every skipped check has a prerequisite that is not `true`. -/
theorem evaluate_respects (e : Env) : Respects enginePrereq (staged e) := by
  intro k hk
  rw [staged_get] at hk
  split at hk
  · exact absurd hk (base_ne_skipped e k (by
      rename_i hall
      intro p hp; have := List.all_eq_true.mp hall p hp; simpa using this))
  · rename_i hall
    simp only [Bool.not_eq_true, List.all_eq_false] at hall
    obtain ⟨p, hp, hnp⟩ := hall
    exact ⟨p, hp, by simpa using hnp⟩

theorem ok_fail {b : Bool} {r r' : Reason} (h : ok b r = .fail r') : r' = r := by
  cases b <;> simp [ok] at h; exact h.symm

theorem parseGrant_error {π : Prims} {t : String} {r : Reason} (h : parseGrant π t = .error r) :
    r = .GRANT_MALFORMED ∨ r = .UNSUPPORTED_FEATURE := by
  unfold parseGrant p1Code at h
  split at h
  · cases h; simp
  · split at h
    · cases h; simp
    · split at h
      · cases h; simp
      · split at h
        · cases h; simp
        · split at h
          · cases h
          · cases h; simp

theorem authorize_codes (caps : List Capability) (a : Action) (r : Reason) :
    ((authorize caps a).p16 = .fail r → r = .ACTION_NOT_AUTHORIZED) ∧
    ((authorize caps a).p17 = .fail r → r = .UNKNOWN_CONSTRAINT) ∧
    ((authorize caps a).p18 = .fail r → r = .CURRENCY_NOT_AUTHORIZED) ∧
    ((authorize caps a).p19 = .fail r → r = .AMOUNT_EXCEEDS_AUTHORITY) ∧
    ((authorize caps a).p20 = .fail r → r = .RESOURCE_NOT_AUTHORIZED) := by
  cases a <;> simp only [authorize] <;> (repeat' split) <;> simp_all [nonempty] <;>
    (split <;> simp) <;> (intro h; exact h.symm)

/-- Every rule's `false` carries one of its check's codes. -/
theorem base_codes (e : Env) (k : Check) (r : Reason) (h : base e k = .fail r) : r ∈ codes k := by
  cases k <;> simp only [base] at h <;> (repeat' split at h) <;>
    simp_all [ok, codes, t1Of, t2Of, t3Of, p2Of, p3Of, p4Of, p5Of, p6Of, p6From, p7Of, p9Of, p10Of, p11Of,
      p12Of, p13Of, p14Of, replayOutcome, unusableStatusCode]
  all_goals (try (repeat' split at h) <;> simp_all)
  all_goals first
    | (subst_vars; exact parseGrant_error ‹_›)
    | exact (authorize_codes _ _ _).1 h
    | exact (authorize_codes _ _ _).2.1 h
    | exact (authorize_codes _ _ _).2.2.1 h
    | exact (authorize_codes _ _ _).2.2.2.1 h
    | exact (authorize_codes _ _ _).2.2.2.2 h

/-- Every `false` the evaluator reports carries one of its check's codes. -/
theorem evaluate_wellCoded (e : Env) : WellCoded (staged e) := by
  intro k r h
  rw [staged_get] at h
  split at h
  · exact base_codes e k r h
  · cases h

section
variable {π : Prims} {req : Request} {s : Snapshots} {tc : TrustConfig} {clk : Clock}
  {ρ : ReplayQuery → ReplayAnswer}

/-! ## The Phase 0 kernel theorems hold for the evaluator -/

/-- Every DENY names a reason, and only ALLOW has none. -/
theorem evaluate_reason_none_iff_allow :
    (evaluate π req s tc clk ρ).result.reason = none ↔ (evaluate π req s tc clk ρ).result.decision = .allow :=
  reason_none_iff_allow enginePrereq _ enginePrereq_backward (evaluate_respects _)

/-- A skipped check always has a `false` check earlier in §5.4 order. -/
theorem evaluate_skipped_has_earlier_fail (k : Check)
    (h : (evaluate π req s tc clk ρ).result.checks.get k = .skipped) :
    ∃ k', order.idxOf k' < order.idxOf k ∧ ((evaluate π req s tc clk ρ).result.checks.get k').isFail = true :=
  skipped_has_earlier_fail enginePrereq _ enginePrereq_backward (evaluate_respects _) k h

/-- The reserved `ISSUER_NOT_TRUSTED` is never the reason (§5.3). -/
theorem evaluate_reason_never_reserved :
    (evaluate π req s tc clk ρ).result.reason ≠ some .ISSUER_NOT_TRUSTED :=
  reason_never_reserved _ (evaluate_wellCoded _)

/-! ## §2.7 rows -/

/-- §6.4: no attribution unless the Grant signature verified (P3). -/
theorem no_unauthenticated_attribution
    (h : (evaluate π req s tc clk ρ).result.checks.get .P3 ≠ .pass) :
    (evaluate π req s tc clk ρ).attribution = none := by
  simp only [evaluate, evaluateWith, attributionOf]
  split
  · rename_i hp _; exact absurd hp h
  · rfl

/-- §6.3: when P14 passes, `request_hash` is the Proof's `action_hash`. -/
theorem request_hash_eq_action_hash
    (h : (evaluate π req s tc clk ρ).result.checks.get .P14 = .pass) :
    ∃ p, parseProof π req.proof = some p ∧ (evaluate π req s tc clk ρ).requestHash = some p.actionHash := by
  have hb := base_of_pass h
  simp only [base] at hb
  split at hb
  · rename_i p hp
    refine ⟨p, hp, ?_⟩
    simp only [p14Of, ok_pass, beq_iff_eq] at hb
    exact hb
  · cases hb

/-- §3.2, TM-07: ALLOW only inside the Grant's validity window, and that
    window is at most 90 days. -/
theorem grant_window (h : (evaluate π req s tc clk ρ).result.decision = .allow) :
    ∃ g, parseGrant π req.grant = .ok g ∧ g.validFromMs ≤ clk.nowMs ∧ clk.nowMs < g.validUntilMs ∧
      g.validUntilMs - g.validFromMs ≤ grantMaxLifetimeMs := by
  have h4 := base_of_allow h .P4
  have h5 := base_of_allow h .P5
  simp only [base, Env.grant] at h4 h5
  split at h4
  · rename_i g hg
    simp only [hg, p4Of, p5Of, ok_pass, decide_eq_true_eq] at h4 h5
    obtain ⟨j, -, -, -, hp⟩ := parseGrant_ok hg
    exact ⟨g, hg, h4, h5, (grantPayload_sound hp).2.1⟩
  · cases h4

/-- The constraints of a Capability, for an Action (§3.3). -/
def constraintsHold (c : Capability) : Action → Bool
  | .purchase _ amount cur => currencyMatches c cur && amountWithin c amount
  | .apiCall m _ => methodAllowed c m

theorem exists_find {α : Type} {P : α → Bool} {l : List α} {R : α → Prop} (x : α) (hx : x ∈ l)
    (hpx : P x = true) (hR : ∀ c, c ∈ l → P c = true → R c) : ∃ c, l.find? P = some c ∧ R c := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨x, hx, hpx⟩)
  exact ⟨c, hc, hR c (List.mem_of_find?_eq_some hc) (List.find?_some hc)⟩

theorem authorize_sound {caps : List Capability} {a : Action} (h : (authorize caps a).p20 = .pass) :
    ∃ c, (authorize caps a).matched = some c ∧ c ∈ caps ∧ c.action = a.type ∧ allKeysKnown c = true ∧
      constraintsHold c a = true ∧ resourceMatches c a.resource = true := by
  revert h
  cases a <;> simp only [authorize] <;> (repeat' split) <;> simp_all [nonempty]
  all_goals
    intro x hx
    intros
    refine exists_find x hx ?_ ?_
    · simp_all [p20Keep]
    · intro c hm hp
      simp_all [constraintsHold, p20Keep]

/-- §3.3 authorization soundness: ALLOW only when some Capability in the
    Grant names the action type, carries only keys this version evaluates,
    satisfies every constraint, matches the resource, and is the one the
    receipt reports as `authority`. (One direction only: see the
    `merchantCategory` reading.) -/
theorem authorization_sound (h : (evaluate π req s tc clk ρ).result.decision = .allow) :
    ∃ g a c, parseGrant π req.grant = .ok g ∧ validateAction req.action = some a ∧ c ∈ g.authority ∧
      c.action = a.type ∧ allKeysKnown c = true ∧ constraintsHold c a = true ∧
      resourceMatches c a.resource = true ∧ (authorize g.authority a).matched = some c := by
  have h20 := base_of_allow h .P20
  simp only [base, Env.grant, Env.action] at h20
  split at h20
  · rename_i g a hg ha
    obtain ⟨c, hm, hc, hca, hk, hcon, hr⟩ := authorize_sound h20
    exact ⟨g, a, c, hg, ha, hc, hca, hk, hcon, hr, hm⟩
  · cases h20

theorem validateAction_values {a : Json} {x : Action} (h : validateAction a = some x) :
    ∀ k v, field? a k = some v → (k = "amount" ∧ (safeInt? v).isSome) ∨ (str? v).isSome := by
  intro k v hv
  have hk : k ∈ keysOf a := by
    simp only [field?, Option.map_eq_some_iff] at hv
    obtain ⟨m, hm, rfl⟩ := hv
    have := List.find?_some hm
    simp only [beq_iff_eq] at this
    simp only [keysOf, List.mem_map]
    exact ⟨m, List.mem_of_find?_eq_some hm, this⟩
  have str_of : ∀ s, fieldStr? a k = some s → (str? v).isSome := by
    intro s hs
    simp only [fieldStr?, hv, Option.bind_some] at hs
    simp [hs]
  obtain ⟨t, fs, ht, hfs, hex⟩ := validateAction_fields h
  have hkf : k ∈ fs := by
    simp only [exactKeys, Bool.and_eq_true, List.all_eq_true] at hex
    simpa using hex.2 k hk
  unfold validateAction at h
  simp only [ht, hfs, hex, Option.bind_eq_bind, Option.bind_some, req, ite_true] at h
  unfold actionFields at hfs
  split at hfs
  · simp only [Option.some.injEq] at hfs
    subst hfs
    simp only [beq_self_eq_true, ite_true] at h
    peel h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hkf
    rcases hkf with rfl | rfl | rfl | rfl
    · exact .inr (str_of _ ht)
    · exact .inr (str_of _ ‹fieldStr? a "resource" = some _›)
    · left; refine ⟨rfl, ?_⟩
      obtain ⟨v', hv', hs⟩ := ‹∃ b, field? a "amount" = some b ∧ safeInt? b = some _›
      rw [hv] at hv'; cases hv'
      simp [hs]
    · exact .inr (str_of _ ‹fieldStr? a "currency" = some _›)
  · simp only [Option.some.injEq] at hfs
    subst hfs
    split at h
    · rename_i hc; exact absurd hc (by decide)
    peel h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hkf
    rcases hkf with rfl | rfl | rfl
    · exact .inr (str_of _ ht)
    · exact .inr (str_of _ ‹fieldStr? a "method" = some _›)
    · exact .inr (str_of _ ‹fieldStr? a "resource" = some _›)
  · cases hfs

/-- §3.3, §4.3 integers only: on ALLOW, every number in the Action is an
    integer (the only numeric member of a v0 Action is `amount`, a safe
    integer in minor units). -/
theorem integers_only (h : (evaluate π req s tc clk ρ).result.decision = .allow) :
    ∀ k n, field? req.action k = some (.num n) → (int? (.num n)).isSome := by
  intro k n hv
  have h15 := base_of_allow h .P15
  simp only [base, Env.action, ok_pass, Option.isSome_iff_exists] at h15
  obtain ⟨x, hx⟩ := h15
  rcases validateAction_values hx k _ hv with ⟨-, hs⟩ | hs
  · simp only [safeInt?] at hs
    split at hs
    · simp_all
    · simp at hs
  · simp [str?] at hs

/-- §11 key rotation: with the Grant parsed and its Principal registered, T3
    fails exactly for a `kid` marked compromised; a key that is only retired
    (not compromised) passes. -/
theorem key_rotation {g : GrantF} {dv : Bool} {comp : List String} {doc : String}
    (hg : parseGrant π req.grant = .ok g) (hi : s.issuer g.issuer = .registered dv comp doc) :
    (evaluate π req s tc clk ρ).result.checks.get .T3 =
      (if g.kid ∈ comp then .fail .ISSUER_KEY_COMPROMISED else .pass) := by
  simp only [evaluate_result, kernel]
  rw [staged_eq_table]
  simp [table, tableRow, Row.toChecks, Row.get, base, Env.grant, hg, hi, t1Of, t3Of, ok, gate]

/-- §4.2 `jti` format, as the checker accepts it. -/
theorem isJti_iff (t : String) :
    isJti t = true ↔ 22 ≤ t.length ∧ t.length ≤ 64 ∧ ∀ c ∈ t.toList, isBase64UrlChar c = true := by
  simp [isJti, List.all_eq_true, and_assoc]

/-- P8 passes only for a Proof whose `jti` has the §4.2 format. -/
theorem p8_jti (h : (evaluate π req s tc clk ρ).result.checks.get .P8 = .pass) :
    ∃ p, parseProof π req.proof = some p ∧ isJti p.jti = true := by
  obtain ⟨p, hp⟩ := proof_of_p8 h
  obtain ⟨_, _, _, _, _, hj, _⟩ := parseProof_sound hp
  exact ⟨p, hp, hj⟩

/-- The `htu` rule is the model's own (§4.3): canonical means a fixed point
    of `normalizeHtu`. -/
theorem isCanonicalHtu_iff (t : String) : isCanonicalHtu t = true ↔ normalizeHtu t = some t := by
  simp [isCanonicalHtu]

theorem parseProof_htu {π : Prims} {t : String} {p : ProofF} (h : parseProof π t = some p) :
    isCanonicalHtu p.htu = true := by
  unfold parseProof at h
  peel h
  assumption

/-- P8 passes only for a Proof whose `htu` is already in the §4.3 canonical
    form, as the model itself computes it. -/
theorem p8_htu (h : (evaluate π req s tc clk ρ).result.checks.get .P8 = .pass) :
    ∃ p, parseProof π req.proof = some p ∧ normalizeHtu p.htu = some p.htu := by
  obtain ⟨p, hp⟩ := proof_of_p8 h
  exact ⟨p, hp, (isCanonicalHtu_iff _).mp (parseProof_htu hp)⟩

/-! ## Threat model rows (§13.1) -/

/-- TM-05: a Proof addressed to another RP is DENY (P12). -/
theorem tm05_other_rp_denies {p : ProofF} (hp : parseProof π req.proof = some p) (h : p.aud ≠ req.rp) :
    (evaluate π req s tc clk ρ).result.decision = .deny :=
  deny_of_base .P12 (by simp [base, Env.proof, hp, p12Of, ok, h])

/-- TM-06: on ALLOW, the submitted Action has the hash the Agent signed. If
    SHA-256 is injective and JCS is a canonical form (both hypotheses), any
    action the Agent hashed is the submitted one up to that canonical form. -/
theorem tm06_action_bound (R : Json → Json → Prop)
    (hinj : Function.Injective π.sha256) (hcanon : ∀ a b t, jcs a = some t → jcs b = some t → R a b)
    (h : (evaluate π req s tc clk ρ).result.decision = .allow) :
    ∃ p, parseProof π req.proof = some p ∧
      ∀ b tb, jcs b = some tb → p.actionHash = π.sha256 tb → R req.action b := by
  obtain ⟨p, hp, hr⟩ := request_hash_eq_action_hash ((allow_iff_every_check _).mp h .P14)
  refine ⟨p, hp, fun b tb hb hab => ?_⟩
  simp only [evaluate, evaluateWith, Env.requestHash, Option.map_eq_some_iff] at hr
  obtain ⟨ta, hta, hsa⟩ := hr
  have : ta = tb := hinj (hsa.trans hab)
  subst this
  exact hcanon _ _ _ hta hb

/-- TM-07: a Grant not yet valid, or expired, is DENY (P4, P5). -/
theorem tm07_outside_window_denies {g : GrantF} (hg : parseGrant π req.grant = .ok g)
    (h : clk.nowMs < g.validFromMs ∨ g.validUntilMs ≤ clk.nowMs) :
    (evaluate π req s tc clk ρ).result.decision = .deny := by
  rcases h with h | h
  · exact deny_of_base .P4 (by simp [base, Env.grant, hg, p4Of, ok]; omega)
  · exact deny_of_base .P5 (by simp [base, Env.grant, hg, p5Of, ok]; omega)

/-- TM-08: a status credential that does not show the Grant as unrevoked is
    DENY (P6). -/
theorem tm08_revoked_denies {g : GrantF} {cred : String} (hg : parseGrant π req.grant = .ok g)
    (hs : s.status g.statusUrl = .snapshot cred)
    (hr : statusOk π tc clk.nowMs cred g.statusUrl g.statusIndex = false) :
    (evaluate π req s tc clk ρ).result.decision = .deny := by
  apply deny_of_base .P6
  simp only [statusOk, beq_eq_false_iff_ne, ne_eq] at hr
  simp only [base, Env.grant, hg, p6Of, p6From, hs]
  split <;> simp_all

/-- **Erratum 6: only a set bit is a revocation.** P6's rule reports
    `AUTHORITY_REVOKED` exactly when the status store returned a credential
    that verifies, is valid at `now` and has the Grant's bit set. -/
theorem p6_revoked_iff {e : Env} {g : GrantF} (hg : e.grant = .ok g) :
    base e .P6 = .fail .AUTHORITY_REVOKED ↔
      ∃ cred, e.s.status g.statusUrl = .snapshot cred ∧
        statusBit e.π e.tc e.clk.nowMs cred g.statusUrl g.statusIndex = some true := by
  simp only [base, hg, p6Of, p6From]
  split
  · simp_all
  · rename_i cred hst
    split <;> simp_all [unusableStatusCode]

/-- A usable credential, an unusable one, or no credential: P6 fails with
    `AUTHORITY_REVOKED` or `SERVICE_UNAVAILABLE`, and nothing else. -/
theorem p6_codes {e : Env} {r : Reason} (h : base e .P6 = .fail r) :
    r = .AUTHORITY_REVOKED ∨ r = .SERVICE_UNAVAILABLE := by
  have := base_codes e .P6 r h
  simpa [codes] using this

/-- TM-09: a `kid` marked compromised is DENY (T3). -/
theorem tm09_compromised_denies {g : GrantF} {dv : Bool} {comp : List String} {doc : String}
    (hg : parseGrant π req.grant = .ok g) (hi : s.issuer g.issuer = .registered dv comp doc)
    (hk : g.kid ∈ comp) : (evaluate π req s tc clk ρ).result.decision = .deny :=
  deny_of_base .T3 (by simp [base, Env.grant, hg, hi, t3Of, ok, hk])

/-- TM-11: an unknown or unverified issuer is DENY (T1, T2). -/
theorem tm11_unknown_issuer_denies {g : GrantF} (hg : parseGrant π req.grant = .ok g)
    (hi : s.issuer g.issuer = .unknown) : (evaluate π req s tc clk ρ).result.decision = .deny :=
  deny_of_base .T1 (by simp [base, Env.grant, hg, hi, t1Of])

theorem tm11_unverified_issuer_denies {g : GrantF} {comp : List String} {doc : String}
    (hg : parseGrant π req.grant = .ok g) (hi : s.issuer g.issuer = .registered false comp doc) :
    (evaluate π req s tc clk ρ).result.decision = .deny :=
  deny_of_base .T2 (by simp [base, Env.grant, hg, hi, t2Of, ok])

/-- TM-12: a status credential not signed by a trusted Delegus status-list
    key is DENY (P6). -/
theorem tm12_unsigned_status_denies {g : GrantF} {cred : String} (hg : parseGrant π req.grant = .ok g)
    (hs : s.status g.statusUrl = .snapshot cred)
    (hu : ∀ j kid key, π.decodeJws cred = some j → (kid, key) ∈ tc.statusKeys →
      π.sigOk key j.signingInput j.signature = false) :
    (evaluate π req s tc clk ρ).result.decision = .deny := by
  apply tm08_revoked_denies hg hs
  cases hso : statusOk π tc clk.nowMs cred g.statusUrl g.statusIndex
  · rfl
  · simp only [statusOk, beq_iff_eq] at hso
    obtain ⟨j, kid, key, hj, hk, hsig⟩ := statusBit_signed hso
    simp [hu j kid key hj hk] at hsig

/-- TM-13: a Grant whose audience excludes the RP is DENY (P7). -/
theorem tm13_excluded_rp_denies {g : GrantF} {auds : List Did} (hg : parseGrant π req.grant = .ok g)
    (ha : g.audience = some auds) (hn : req.rp ∉ auds) :
    (evaluate π req s tc clk ρ).result.decision = .deny :=
  deny_of_base .P7 (by simp [base, Env.grant, hg, p7Of, audienceOk, ha, hn, ok])

theorem findKey_safe {π : Prims} {doc iss kid : String} {k : PubKey} (h : findKey π doc iss kid = some k) :
    π.keyOk k = true := by
  unfold findKey at h
  peel h
  split at h
  · peel h
    simp_all
  · cases h

/-- TM-01, TM-02: on ALLOW, the Grant's signing input verifies under a safe
    key named by `kid` in the Principal's DID document snapshot. With the
    signature hypothesis (`hsig`: a verifying signature under a safe key
    means the key's holder signed), the Principal's key holder signed the
    Grant exactly as received. -/
theorem tm01_grant_signed (SignedBy : PubKey → String → Prop)
    (hsig : ∀ k m σ, π.keyOk k = true → π.sigOk k m σ = true → SignedBy k m)
    (h : (evaluate π req s tc clk ρ).result.decision = .allow) :
    ∃ g dv comp doc key, parseGrant π req.grant = .ok g ∧ s.issuer g.issuer = .registered dv comp doc ∧
      findKey π doc g.issuer g.kid = some key ∧ SignedBy key g.signingInput := by
  have h3 := base_of_allow h .P3
  simp only [base, Env.grant] at h3
  split at h3
  · rename_i g hg
    revert h3
    unfold p3Of
    split
    · rename_i dv comp doc hi
      split
      · rename_i key hk
        intro hs
        exact ⟨g, dv, comp, doc, key, hg, hi, hk, hsig _ _ _ (findKey_safe hk) (ok_pass.mp hs)⟩
      · simp
    · simp
  · cases h3

/-- TM-03: on ALLOW, the Proof is signed under the Grant's own Agent key
    (`credentialSubject.id`), so a stolen Grant is useless without that
    key. With the signature hypothesis, the Agent's key holder signed it. -/
theorem tm03_proof_signed_by_agent (SignedBy : PubKey → String → Prop)
    (hsig : ∀ k m σ, π.keyOk k = true → π.sigOk k m σ = true → SignedBy k m)
    (h : (evaluate π req s tc clk ρ).result.decision = .allow) :
    ∃ g p, parseGrant π req.grant = .ok g ∧ parseProof π req.proof = some p ∧ p.iss = g.agent ∧
      SignedBy g.agentKey p.signingInput := by
  have h9 := base_of_allow h .P9
  have h10 := base_of_allow h .P10
  simp only [base, Env.grant, Env.proof] at h9 h10
  split at h10
  · rename_i g p hg hp
    simp only [hp, p9Of, p10Of, ok_pass, beq_iff_eq] at h9 h10
    obtain ⟨_, _, _, hpk, hpok, _⟩ := parseProof_sound hp
    obtain ⟨j, -, -, -, hgp⟩ := parseGrant_ok hg
    obtain ⟨-, -, hgk, -⟩ := grantPayload_sound hgp
    have : p.agentKey = g.agentKey := by
      rw [h10] at hpk; rw [hpk] at hgk; exact Option.some.inj hgk
    exact ⟨g, p, hg, hp, h10, this ▸ hsig _ _ _ hpok h9⟩
  · cases h10

end

end DelegusCheck
