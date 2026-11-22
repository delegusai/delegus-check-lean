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

def expectedCount : Nat := 52

/-- The three normalization sets, run on the model's own `normalizeHtu`,
    `jcs` and `isJti`. Returns the number of failures. -/
def runSets (dir : System.FilePath) : IO Nat := do
  let mut bad := 0
  let mut checked := 0
  let read (n : String) : IO Json := do
    match Json.parse (← IO.FS.readFile (dir / n)) with
    | .ok j => pure j
    | .error e => throw (IO.userError s!"{n}: {e}")
  let htu ← read "htu.json"
  for c in ((htu.getObjValD "normalize").getArr?.toOption.getD #[]) do
    let input := (c.getObjValAs? String "input").toOption.getD ""
    let want := (c.getObjValAs? String "canonical").toOption
    checked := checked + 1
    if normalizeHtu input != want then
      IO.println s!"FAIL set htu {input}: model {repr (normalizeHtu input)}, set {repr want}"
      bad := bad + 1
  for c in ((htu.getObjValD "malformed").getArr?.toOption.getD #[]) do
    let input := (c.getStr?).toOption.getD ""
    checked := checked + 1
    if (normalizeHtu input).isSome then
      IO.println s!"FAIL set htu {input}: model accepts a malformed value"
      bad := bad + 1
  let jcsSet ← read "jcs.json"
  for c in ((jcsSet.getObjValD "cases").getArr?.toOption.getD #[]) do
    let input := (c.getObjValAs? String "input").toOption.getD ""
    let want := (c.getObjValAs? String "canonical").toOption
    let got := match Json.parse input with
      | .ok j => jcs j
      | .error _ => none
    checked := checked + 1
    if got != want then
      IO.println s!"FAIL set jcs {input}: model {repr got}, set {repr want}"
      bad := bad + 1
  let jti ← read "jti.json"
  for (k, expect) in [("valid", true), ("invalid", false)] do
    for v in ((jti.getObjValD k).getArr?.toOption.getD #[]) do
      let s := (v.getStr?).toOption.getD ""
      checked := checked + 1
      if isJti s != expect then
        IO.println s!"FAIL set jti {s}: model {isJti s}, set {expect}"
        bad := bad + 1
  IO.println s!"sets: {checked - bad} of {checked} htu, JCS and jti checks pass on the model's own rules; {bad} failure(s)"
  return bad

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
  bad := bad + (← runSets "vectors/sets")
  if files.size != expectedCount then
    IO.println s!"FAIL expected {expectedCount} cases in {cases}, found {files.size}"
    bad := bad + 1
  IO.println s!"{files.size - min bad files.size} of {files.size} cases match on decision, reason, both layers and all 24 checks; {bad} failure(s)"
  return if bad == 0 then 0 else 1
