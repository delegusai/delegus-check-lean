/-
Copyright 2026 Inam Haq. Licensed under the Apache License, Version 2.0.

Phase 0 theorems. scripts/check-axioms.sh audits what each one rests on.
-/
import DelegusCheckSpec.Kernel

namespace DelegusCheck

/-! ## The order (§5.4) -/

/-- The model's order is, symbol for symbol, the §5.4 order. -/
theorem order_is_spec :
    order = [.P1, .T1, .T2, .T3, .P2, .P3, .P4, .P5, .P6, .P7, .P8,
      .P9, .P10, .P11, .P12, .P13, .P14, .T5, .P15, .P16, .P17, .P18, .P19, .P20] :=
  rfl

/-- 24 checks, each exactly once, and every check is in the order. -/
theorem order_length : order.length = 24 := rfl
theorem order_nodup : order.Nodup := by decide
theorem order_complete : ∀ k : Check, k ∈ order := by
  intro k; cases k <;> decide

/-- §7: implementations MUST NOT reorder P6 after T5. -/
theorem p6_before_t5 : order.idxOf .P6 < order.idxOf .T5 := by decide

/-- §5.3, §7: T5 executes only after P1–P14; it comes after P14 in the order. -/
theorem p14_before_t5 : order.idxOf .P14 < order.idxOf .T5 := by decide

/-- Every protocol check before P14 also precedes T5. -/
theorem p1_to_p14_before_t5 :
    ∀ k ∈ [Check.P1, .P2, .P3, .P4, .P5, .P6, .P7, .P8, .P9, .P10, .P11, .P12, .P13, .P14],
      order.idxOf k < order.idxOf .T5 := by
  decide

/-- The two layers split the 24 checks: every check is in exactly one. -/
theorem layers_partition :
    ∀ k : Check, (k ∈ protocolChecks ∨ k ∈ trustChecks) ∧ ¬ (k ∈ protocolChecks ∧ k ∈ trustChecks) := by
  intro k; cases k <;> decide

/-! ## Helper facts about outcomes -/

theorem Outcome.isPass_iff (o : Outcome) : o.isPass = true ↔ o = .pass := by
  cases o <;> simp [Outcome.isPass]

theorem Outcome.failReason_eq_none_iff (o : Outcome) : o.failReason = none ↔ o.isFail = false := by
  cases o <;> simp [Outcome.failReason, Outcome.isFail]

theorem Outcome.failReason_eq_some_iff (o : Outcome) (r : Reason) : o.failReason = some r ↔ o = .fail r := by
  cases o <;> simp [Outcome.failReason]

theorem allPass_iff (c : Checks) (l : List Check) : allPass c l = true ↔ ∀ k ∈ l, c.get k = .pass := by
  simp [allPass, List.all_eq_true, Outcome.isPass_iff]

/-! ## Fail closed: the core (§0 constraint 3, §5.4) -/

/-- The master statement: ALLOW if and only if every one of the 24 checks in
    §5.4 order is `true`. There is no other path to ALLOW. -/
theorem allow_iff_all_pass (c : Checks) :
    (kernel c).decision = .allow ↔ ∀ k ∈ order, c.get k = .pass := by
  simp only [kernel, decisionOf]
  rw [← allPass_iff]
  cases allPass c order <;> simp

/-- The same statement over the type of checks itself. -/
theorem allow_iff_every_check (c : Checks) :
    (kernel c).decision = .allow ↔ ∀ k : Check, c.get k = .pass := by
  rw [allow_iff_all_pass]
  exact ⟨fun h k => h k (order_complete k), fun h k _ => h k⟩

/-- Any check that is not `true` (whether `false` or skipped) forces DENY. -/
theorem deny_of_not_pass (c : Checks) (k : Check) (h : c.get k ≠ .pass) :
    (kernel c).decision = .deny := by
  cases hd : (kernel c).decision with
  | deny => rfl
  | allow => exact absurd ((allow_iff_every_check c).mp hd k) h

/-- A `false` check forces DENY. -/
theorem deny_of_fail (c : Checks) (k : Check) (r : Reason) (h : c.get k = .fail r) :
    (kernel c).decision = .deny :=
  deny_of_not_pass c k (by rw [h]; exact Outcome.noConfusion)

/-! ## Layer results (§5.4) -/

theorem protocolPass_iff (c : Checks) :
    (kernel c).protocolPass = true ↔ ∀ k ∈ protocolChecks, c.get k = .pass :=
  allPass_iff c protocolChecks

theorem trustPass_iff (c : Checks) :
    (kernel c).trustPass = true ↔ ∀ k ∈ trustChecks, c.get k = .pass :=
  allPass_iff c trustChecks

/-- ALLOW if and only if both layers PASS. -/
theorem allow_iff_layers (c : Checks) :
    (kernel c).decision = .allow ↔ (kernel c).protocolPass = true ∧ (kernel c).trustPass = true := by
  rw [allow_iff_every_check, protocolPass_iff, trustPass_iff]
  constructor
  · intro h; exact ⟨fun k _ => h k, fun k _ => h k⟩
  · intro ⟨hp, ht⟩ k
    rcases (layers_partition k).1 with hk | hk
    · exact hp k hk
    · exact ht k hk

/-! ## The reason is the first `false` in §5.4 order -/

/-- `reason = x` exactly when §5.4 order splits as `before ++ k :: after`,
    check `k` is `false` with reason `x`, and no check in `before` is `false`. -/
theorem reason_first_fail (c : Checks) (x : Reason) :
    (kernel c).reason = some x ↔
      ∃ before k after, order = before ++ k :: after ∧ c.get k = .fail x ∧
        ∀ k' ∈ before, (c.get k').isFail = false := by
  simp only [kernel, firstFail, List.findSome?_eq_some_iff, Outcome.failReason_eq_some_iff,
    Outcome.failReason_eq_none_iff]

/-- The same, as indices: the reason comes from position `i`, and no
    position before `i` is `false`. -/
theorem reason_first_fail_idx (c : Checks) (x : Reason) :
    (kernel c).reason = some x ↔
      ∃ i, ∃ h : i < order.length, c.get order[i] = .fail x ∧
        ∀ j, ∀ hj : j < i, (c.get (order[j]'(Nat.lt_trans hj h))).isFail = false := by
  rw [reason_first_fail]
  constructor
  · rintro ⟨before, k, after, ho, hk, hb⟩
    have hlen : before.length < order.length := by rw [ho]; simp
    refine ⟨before.length, hlen, ?_, ?_⟩
    · have : order[before.length] = k := by simp [ho]
      rw [this]; exact hk
    · intro j hj
      have hjb : order[j]'(Nat.lt_trans hj hlen) = before[j] := by
        simp [ho, List.getElem_append_left hj]
      rw [hjb]; exact hb _ (List.getElem_mem hj)
  · rintro ⟨i, hi, hk, hb⟩
    refine ⟨order.take i, order[i], order.drop (i + 1), ?_, hk, ?_⟩
    · simp
    · intro k' hk'
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hk'
      have hji : j < i := by simp at hj; omega
      simpa using hb j hji

/-- The reason is the outcome of the first failing check, if any. -/
theorem reason_eq_firstFailCheck (c : Checks) :
    (kernel c).reason = (firstFailCheck c).bind fun k => (c.get k).failReason := by
  simp only [kernel, firstFail, firstFailCheck]
  induction order with
  | nil => rfl
  | cons a t ih =>
    rw [List.findSome?_cons, List.find?_cons]
    cases h : c.get a with
    | pass => exact ih
    | skipped => exact ih
    | fail r => simp [h, Outcome.failReason, Outcome.isFail]

/-! ## Skipped checks (§5.4) -/

private theorem skipped_aux (pr : Prereq) (c : Checks) (hb : Backward pr) (hr : Respects pr c) :
    ∀ n, ∀ k, order.idxOf k < n → c.get k = .skipped →
      ∃ k', order.idxOf k' < order.idxOf k ∧ (c.get k').isFail = true := by
  intro n
  induction n with
  | zero => intro k h; omega
  | succ n ih =>
    intro k hn hs
    obtain ⟨p, hp, hnp⟩ := hr k hs
    have hlt := hb k p hp
    cases hcp : c.get p with
    | pass => exact absurd hcp hnp
    | fail r => exact ⟨p, hlt, by simp [hcp, Outcome.isFail]⟩
    | skipped =>
      obtain ⟨k', h1, h2⟩ := ih p (by omega) hcp
      exact ⟨k', by omega, h2⟩

/-- For any backward-pointing prerequisite table: if the outcomes respect it,
    every skipped check has a `false` check strictly earlier in §5.4 order.
    (The engine throws if this is ever violated; here it cannot happen.) -/
theorem skipped_has_earlier_fail (pr : Prereq) (c : Checks) (hb : Backward pr) (hr : Respects pr c)
    (k : Check) (hs : c.get k = .skipped) :
    ∃ k', order.idxOf k' < order.idxOf k ∧ (c.get k').isFail = true :=
  skipped_aux pr c hb hr (order.idxOf k + 1) k (Nat.lt_succ_self _) hs

/-- Fail closed, completed: for outcomes that respect a backward table, the
    reason is `null` exactly when the decision is ALLOW. Every DENY names a
    reason. -/
theorem reason_none_iff_allow (pr : Prereq) (c : Checks) (hb : Backward pr) (hr : Respects pr c) :
    (kernel c).reason = none ↔ (kernel c).decision = .allow := by
  simp only [kernel, firstFail, List.findSome?_eq_none_iff, Outcome.failReason_eq_none_iff]
  rw [show decisionOf c = (kernel c).decision from rfl, allow_iff_all_pass]
  constructor
  · intro hnf k hk
    cases hck : c.get k with
    | pass => rfl
    | fail r => have := hnf k hk; simp [hck, Outcome.isFail] at this
    | skipped =>
      obtain ⟨k', _, hf⟩ := skipped_has_earlier_fail pr c hb hr k hck
      have := hnf k' (order_complete k'); simp [this] at hf
  · intro hp k hk
    simp [hp k hk, Outcome.isFail]

/-- Every reason given is a code that the failing check may carry, and so the
    reserved `ISSUER_NOT_TRUSTED` is never given (§5.3). -/
theorem reason_mem_codes (c : Checks) (hw : WellCoded c) (r : Reason) (h : (kernel c).reason = some r) :
    ∃ k, c.get k = .fail r ∧ r ∈ codes k := by
  obtain ⟨_, k, _, _, hk, _⟩ := (reason_first_fail c r).mp h
  exact ⟨k, hk, hw k r hk⟩

theorem reason_never_reserved (c : Checks) (hw : WellCoded c) :
    (kernel c).reason ≠ some .ISSUER_NOT_TRUSTED := by
  intro h
  obtain ⟨k, _, hm⟩ := reason_mem_codes c hw _ h
  cases k <;> simp [codes] at hm

/-! ## The engine's prerequisite table -/

theorem backwardB_sound (pr : Prereq) (h : backwardB pr = true) : Backward pr := by
  intro k p hp
  simp only [backwardB, List.all_eq_true, decide_eq_true_eq] at h
  exact h k (order_complete k) p hp

/-- The engine's table points backward, so every theorem above that takes a
    table applies to it. -/
theorem enginePrereq_backward : Backward enginePrereq :=
  backwardB_sound enginePrereq (by decide)

/-- If a case passes the executable table check, it respects the table. -/
theorem exactB_sound (pr : Prereq) (c : Checks) (h : exactB pr c = true) : Respects pr c := by
  intro k hs
  simp only [exactB, List.all_eq_true] at h
  have hk := h k (order_complete k)
  rw [hs] at hk
  have hany : ((pr k).any fun p => !(c.get p).isPass) = true := by
    simpa using hk.symm
  obtain ⟨p, hp, hnp⟩ := List.any_eq_true.mp hany
  refine ⟨p, hp, fun he => ?_⟩
  simp [he, Outcome.isPass] at hnp

theorem wellCodedB_sound (c : Checks) (h : wellCodedB c = true) : WellCoded c := by
  intro k r hk
  simp only [wellCodedB, List.all_eq_true] at h
  have := h k (order_complete k)
  simp only [hk, List.contains_iff_mem] at this
  simpa using this

end DelegusCheck
