/-
Copyright 2026 Inam Haq. Licensed under the Apache License, Version 2.0.

What a passing parser guarantees, and how each evaluated check relates to
its rule and its prerequisites. Used by the Phase 1 theorems.
-/
import DelegusCheckSpec.Staged

namespace DelegusCheck

open Lean (Json)

@[simp] theorem req_eq_some (b : Bool) (u : Unit) : req b = some u ↔ b = true := by
  cases b <;> simp [req]

/-- Peel a passing `Option` parser into its conditions. -/
macro "peel" h:ident : tactic =>
  `(tactic| (
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, req_eq_some,
      Option.some.injEq, Option.map_eq_some_iff] at $h:ident
    repeat obtain ⟨_, $h:ident⟩ := $h:ident))

/-! ## P1 -/

theorem grantPayload_sound {π : Prims} {j : Jws} {g : GrantF} (h : grantPayload π j = some g) :
    exactKeys j.payload grantTop = true ∧
    g.validUntilMs - g.validFromMs ≤ grantMaxLifetimeMs ∧
    π.didKeyPub g.agent = some g.agentKey ∧ π.keyOk g.agentKey = true ∧
    g.signingInput = j.signingInput ∧ g.signature = j.signature := by
  unfold grantPayload at h
  peel h
  refine ⟨‹_›, ?_, ‹_›, ‹_›, rfl, rfl⟩
  simp_all

theorem parseGrant_ok {π : Prims} {t : String} {g : GrantF} (h : parseGrant π t = .ok g) :
    ∃ j, π.decodeJws t = some j ∧ grantHeaderOk j.header = true ∧
      has j.payload "parentGrant" = false ∧ grantPayload π j = some g := by
  unfold parseGrant p1Code at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i j hj
      refine ⟨j, hj, ?_⟩
      by_cases hh : grantHeaderOk j.header = true
      · by_cases hp : has j.payload "parentGrant" = true
        · simp [hh, hp] at h
        · simp only [hh, hp, Bool.not_true, Bool.false_eq_true, ite_false] at h
          split at h
          · cases h; simp_all
          · cases h
      · simp [hh] at h

/-- The Grant's header names EdDSA (§3.1). -/
theorem grantHeaderOk_alg {h : Json} (hh : grantHeaderOk h = true) : fieldIs h "alg" "EdDSA" = true := by
  simp only [grantHeaderOk, Bool.and_eq_true] at hh
  exact hh.1.1.2

theorem parseGrant_parent {π : Prims} {t : String} {j : Jws} (hs : t.length ≤ grantMaxBytes)
    (hj : π.decodeJws t = some j) (hh : grantHeaderOk j.header = true)
    (hp : has j.payload "parentGrant" = true) : parseGrant π t = .error .UNSUPPORTED_FEATURE := by
  unfold parseGrant p1Code
  have : ¬ t.length > grantMaxBytes := by omega
  simp [this, hj, hh, hp]

theorem parseGrant_undecodable {π : Prims} {t : String} (hj : π.decodeJws t = none) :
    ∃ r, parseGrant π t = .error r := by
  unfold parseGrant
  split
  · exact ⟨_, rfl⟩
  · simp [hj]

/-! ## P8 -/

theorem parseProof_sound {π : Prims} {t : String} {p : ProofF} (h : parseProof π t = some p) :
    ∃ j, π.decodeJws t = some j ∧ fieldIs j.header "alg" "EdDSA" = true ∧
      π.didKeyPub p.iss = some p.agentKey ∧ π.keyOk p.agentKey = true ∧ isJti p.jti = true ∧
      p.signingInput = j.signingInput ∧ p.signature = j.signature := by
  unfold parseProof at h
  peel h
  exact ⟨_, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, rfl, rfl⟩

/-! ## P6 -/

/-- A usable credential (any bit) was signed by a trusted Delegus
    status-list key. -/
theorem statusBit_signed {π : Prims} {tc : TrustConfig} {now : Int} {cred url idx : String} {b : Bool}
    (h : statusBit π tc now cred url idx = some b) :
    ∃ j kid key, π.decodeJws cred = some j ∧ (kid, key) ∈ tc.statusKeys ∧
      π.sigOk key j.signingInput j.signature = true := by
  unfold statusBit at h
  peel h
  obtain ⟨kv, hf, rfl⟩ := Option.map_eq_some_iff.mp ‹statusKey tc _ = some _›
  exact ⟨_, kv.1, kv.2, ‹_›, List.mem_of_find?_eq_some hf, ‹_›⟩

end DelegusCheck
