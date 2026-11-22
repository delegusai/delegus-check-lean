/-
Copyright 2026 Inam Haq. Licensed under the Apache License, Version 2.0.

Phase 0 kernel: from the 24 check outcomes to the decision, the reason and
the two layer results (§5.4). Attribution for restated spec text:
"Delegus Specification v0.2, © Delegus (delegus.ai)", CC BY 4.0.
-/
import DelegusCheckSpec.Basic

namespace DelegusCheck

/-- The reason: the first `false` in §5.4 order. -/
def firstFail (c : Checks) : Option Reason :=
  order.findSome? fun k => (c.get k).failReason

/-- The check that supplies the reason. -/
def firstFailCheck (c : Checks) : Option Check :=
  order.find? fun k => (c.get k).isFail

/-- Every check in `l` is `true`. -/
def allPass (c : Checks) (l : List Check) : Bool :=
  l.all fun k => (c.get k).isPass

/-- §5.4: DENY if any check is `false`. The model is stricter in form and
    equal in effect for well-formed outcomes: ALLOW only if every one of the
    24 checks is `true` (a `"skipped"` check is not `true`). -/
def decisionOf (c : Checks) : Decision :=
  if allPass c order then .allow else .deny

/-- What the Phase 0 kernel reports for one evaluation. -/
structure Result where
  decision : Decision
  /-- `none` is the receipt's `reason: null`. -/
  reason : Option Reason
  /-- `protocol.result` is PASS (§5.4). -/
  protocolPass : Bool
  /-- `trust.result` is PASS (§5.4). -/
  trustPass : Bool
  checks : Checks

/-- The Phase 0 evaluator: pure, total, no effects. Store answers and
    cryptographic results reach it only through the check outcomes. -/
def kernel (c : Checks) : Result where
  decision := decisionOf c
  reason := firstFail c
  protocolPass := allPass c protocolChecks
  trustPass := allPass c trustChecks
  checks := c

/-! ## Prerequisites

§5.4 says checks "whose prerequisites failed are skipped" but does not list
the prerequisites. A table is a function from a check to the checks it needs.
The theorems hold for every table in which each prerequisite comes earlier in
§5.4 order (`Backward`). -/

abbrev Prereq := Check → List Check

/-- The engine's table (`packages/core/src/evaluate.ts`, header comment):
    T1 needs P1; T2, T3, P2 need T1; P3 needs P2; P4–P8 need P3; P9–P14 need
    P8; T5 needs all of P1–P14; P15 needs P14; P16–P20 each need the one
    before. (The engine also states "P4–P20 need P3"; for P9–P20 that follows
    through P8 and P14.) -/
def enginePrereq : Prereq
  | .P1 => []
  | .T1 => [.P1]
  | .T2 => [.T1]
  | .T3 => [.T1]
  | .P2 => [.T1]
  | .P3 => [.P2]
  | .P4 => [.P3]
  | .P5 => [.P3]
  | .P6 => [.P3]
  | .P7 => [.P3]
  | .P8 => [.P3]
  | .P9 => [.P8]
  | .P10 => [.P8]
  | .P11 => [.P8]
  | .P12 => [.P8]
  | .P13 => [.P8]
  | .P14 => [.P8]
  | .T5 => [.P1, .P2, .P3, .P4, .P5, .P6, .P7, .P8, .P9, .P10, .P11, .P12, .P13, .P14]
  | .P15 => [.P14]
  | .P16 => [.P15]
  | .P17 => [.P16]
  | .P18 => [.P17]
  | .P19 => [.P18]
  | .P20 => [.P19]

/-- Every prerequisite comes strictly earlier in §5.4 order. -/
def Backward (pr : Prereq) : Prop :=
  ∀ k, ∀ p ∈ pr k, order.idxOf p < order.idxOf k

/-- A skipped check has a prerequisite that is not `true`. -/
def Respects (pr : Prereq) (c : Checks) : Prop :=
  ∀ k, c.get k = .skipped → ∃ p ∈ pr k, c.get p ≠ .pass

/-- Every `false` carries one of its check's codes (§5.2, §5.3). -/
def WellCoded (c : Checks) : Prop :=
  ∀ k r, c.get k = .fail r → r ∈ codes k

/-! Executable versions, used on the conformance cases. -/

def backwardB (pr : Prereq) : Bool :=
  order.all fun k => (pr k).all fun p => decide (order.idxOf p < order.idxOf k)

/-- The table is followed exactly: a check is skipped if and only if one of
    its prerequisites is not `true`. -/
def exactB (pr : Prereq) (c : Checks) : Bool :=
  order.all fun k => (c.get k == .skipped) == (pr k).any fun p => !(c.get p).isPass

def wellCodedB (c : Checks) : Bool :=
  order.all fun k => match c.get k with
    | .fail r => (codes k).contains r
    | _ => true

end DelegusCheck
