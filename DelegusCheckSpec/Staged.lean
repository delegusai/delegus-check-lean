/-
Copyright 2026 Inam Haq. Licensed under the Apache License, Version 2.0.

The staged evaluator equals the declarative table.
-/
import DelegusCheckSpec.Evaluate

namespace DelegusCheck

/-! ## Gate facts -/

@[simp] theorem gate_nil (o : Outcome) : gate [] o = o := rfl

theorem gate_cons (x : Outcome) (xs : List Outcome) (o : Outcome) :
    gate (x :: xs) o = if x = .pass then gate xs o else .skipped := by
  unfold gate
  by_cases h : x = .pass <;> simp [h, List.all_cons]

@[simp] theorem gate_pass (xs : List Outcome) (o : Outcome) : gate (.pass :: xs) o = gate xs o := by
  simp [gate_cons]

@[simp] theorem gate_skipped (xs : List Outcome) (o : Outcome) : gate (.skipped :: xs) o = .skipped := by
  simp [gate_cons]

@[simp] theorem gate_fail (r : Reason) (xs : List Outcome) (o : Outcome) :
    gate (.fail r :: xs) o = .skipped := by
  simp [gate_cons]

@[simp] theorem gate_of_skipped (xs : List Outcome) : gate xs .skipped = .skipped := by
  unfold gate; split <;> rfl

theorem ite_chain (x y : Outcome) (h : x = .pass ∨ y = .skipped) :
    (if x = .pass then y else .skipped) = y := by
  rcases h with h | h <;> simp [h]

/-! ## Authorization is a chain: a later check is skipped unless the one
before it passed. -/

theorem authorize_chain (caps : List Capability) (a : Action) :
    ((authorize caps a).p16 = .pass ∨ (authorize caps a).p17 = .skipped) ∧
    ((authorize caps a).p17 = .pass ∨ (authorize caps a).p18 = .skipped) ∧
    ((authorize caps a).p18 = .pass ∨ (authorize caps a).p19 = .skipped) ∧
    ((authorize caps a).p19 = .pass ∨ (authorize caps a).p20 = .skipped) := by
  unfold authorize
  cases a <;> simp only <;> (repeat' split) <;> simp_all

/-- P16 is never skipped: once the Action is valid, authorization runs. -/
theorem authorize_p16 (caps : List Capability) (a : Action) :
    (authorize caps a).p16 = .pass ∨ (authorize caps a).p16 = .fail .ACTION_NOT_AUTHORIZED := by
  unfold authorize
  cases a <;> simp only <;> (repeat' split) <;> simp_all

/-! ## The equality -/

theorem stagedRow_eq_tableRow (e : Env) : stagedRow e = tableRow (base e) := by
  unfold stagedRow tableRow base
  rcases hg : e.grant with r | g
  · simp
  · rcases hi : e.s.issuer g.issuer with _ | _ | ⟨dv, comp, doc⟩
    · simp [hi, t1Of]
    · simp [hi, t1Of]
    · simp only [hi, t1Of, t2Of, t3Of, p2Of, p3Of]
      rcases hk : findKey e.π doc g.issuer g.kid with _ | key
      · simp [ok]
      · by_cases hs : e.π.sigOk key g.signingInput g.signature = true
        · rcases hp : e.proof with _ | p
          · simp [ok, hs, gate]
          · simp only [hs, ite_true, ok, Option.isSome_some, proofStage, proofRow, earlyRow, earlyPass]
            by_cases h14 : p14Of e p = .pass
            · rcases ha : e.action with _ | a
              · simp [h14, actionStage, ha, gate]
              · obtain ⟨c17, c18, c19, c20⟩ := authorize_chain g.authority a
                simp [h14, actionStage, ha, gate, ite_chain _ _ c17, ite_chain _ _ c18,
                  ite_chain _ _ c19, ite_chain _ _ c20]
            · simp [h14, gate]
        · simp [ok, hs]

/-- **`staged_eq_table`**: the step-by-step evaluator, written the way the
    engine runs, equals the declarative table of §5.4 with the engine's
    prerequisites. -/
theorem staged_eq_table (e : Env) : staged e = table (base e) := by
  unfold staged table
  rw [stagedRow_eq_tableRow]

theorem evaluate_eq_evalTable (π : Prims) (req : Request) (s : Snapshots) (tc : TrustConfig)
    (clk : Clock) (ρ : ReplayQuery → ReplayAnswer) :
    evaluate π req s tc clk ρ = evalTable π req s tc clk ρ := by
  unfold evaluate evalTable evaluateWith
  rw [staged_eq_table]

end DelegusCheck
