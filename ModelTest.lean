/-
Copyright 2026 Inam Haq. Licensed under the Apache License, Version 2.0.

`lake test`: runs the 40 conformance cases through the Lean model and fails
on any difference from the case's expected decision, reason, layer results
or any of the 24 check outcomes, or if an outcome breaks the prerequisite
table or carries a code its check cannot carry.
-/
import DelegusCheckVectors

open Lean (Json)
open DelegusCheck DelegusCheck.Vectors

def expectedCount : Nat := 40

def main (args : List String) : IO UInt32 := do
  let cases : System.FilePath := args.getD 0 "vectors/cases"
  let lowered : System.FilePath := args.getD 1 "vectors/lowered"
  let files ← caseFiles cases
  let mut bad := 0
  for f in files do
    match ← loadFile f lowered with
    | .error e =>
      IO.println s!"FAIL {f}: cannot read case: {e}"
      bad := bad + 1
    | .ok l =>
      let ev := runLoaded l
      let got := resultJson l.id ev
      let mut problems : List String := []
      for k in ["decision", "reason", "protocol_result", "trust_result", "protocol_checks", "trust_checks"] do
        let g := got.getObjValD k
        let w := l.expected.getObjValD k
        if g.compress != w.compress then
          problems := problems ++ [s!"{k}: model {g.compress}, case {w.compress}"]
      if !exactB enginePrereq ev.result.checks then
        problems := problems ++ ["outcomes do not follow the prerequisite table"]
      if !wellCodedB ev.result.checks then
        problems := problems ++ ["a false check carries a code its check cannot carry"]
      if problems.isEmpty then
        IO.println s!"ok   {l.id}  {ev.result.decision.name} {(ev.result.reason.map (·.name)).getD "null"}"
      else
        IO.println s!"FAIL {l.id}: {String.intercalate "; " problems}"
        bad := bad + 1
  if files.size != expectedCount then
    IO.println s!"FAIL expected {expectedCount} cases in {cases}, found {files.size}"
    bad := bad + 1
  IO.println s!"{files.size - min bad files.size} of {files.size} cases match on decision, reason, both layers and all 24 checks; {bad} failure(s)"
  return if bad == 0 then 0 else 1
