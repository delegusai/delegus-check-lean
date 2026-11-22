/-
Copyright 2026 Inam Haq. Licensed under the Apache License, Version 2.0.

`lake test`: runs the 40 conformance cases through the Phase 0 kernel and
fails on any difference from the case's expected decision, reason and layer
results, or if a case does not follow the engine's prerequisite table or
carries a code its check cannot carry.
-/
import DelegusCheckVectors

open DelegusCheck DelegusCheck.Vectors

def expectedCount : Nat := 40

def main (args : List String) : IO UInt32 := do
  let dir : System.FilePath := args.headD "vectors/cases"
  let files ← caseFiles dir
  let mut bad := 0
  for f in files do
    match parseCase (← IO.FS.readFile f) with
    | .error e =>
      IO.eprintln s!"FAIL {f}: cannot read case: {e}"
      bad := bad + 1
    | .ok c =>
      let ch := c.checks
      let r := kernel ch
      let got := (r.decision.name, r.reason.map (·.name), layerName r.protocolPass, layerName r.trustPass)
      let want := (c.expDecision, c.expReason, c.expProtocol, c.expTrust)
      let mut problems : List String := []
      if got != want then
        problems := problems ++ [s!"kernel {repr got} but case expects {repr want}"]
      if !exactB enginePrereq ch then
        problems := problems ++ ["outcomes do not follow the prerequisite table"]
      if !wellCodedB ch then
        problems := problems ++ ["a false check carries a code its check cannot carry"]
      if problems.isEmpty then
        IO.println s!"ok   {c.id}  {r.decision.name} {(r.reason.map (·.name)).getD "null"}"
      else
        IO.println s!"FAIL {c.id}: {String.intercalate "; " problems}"
        bad := bad + 1
  if files.size != expectedCount then
    IO.println s!"FAIL expected {expectedCount} cases in {dir}, found {files.size}"
    bad := bad + 1
  IO.println s!"{files.size - min bad files.size} of {files.size} cases match; {bad} failure(s)"
  return if bad == 0 then 0 else 1
