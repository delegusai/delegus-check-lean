/-
Copyright 2026 Inam Haq. Licensed under the Apache License, Version 2.0.

`delegus-check-model [cases-dir [lowered-dir]]`: runs the Lean model of
Delegus Check on each conformance case and prints one JSON object per case
(JSON Lines). Defaults: `vectors/cases`, `vectors/lowered`.
-/
import DelegusCheckVectors

open DelegusCheck DelegusCheck.Vectors

def main (args : List String) : IO UInt32 := do
  let cases : System.FilePath := args.getD 0 "vectors/cases"
  let lowered : System.FilePath := args.getD 1 "vectors/lowered"
  let mut failed := false
  for f in ← caseFiles cases do
    match ← loadFile f lowered with
    | .ok l => IO.println (resultJson l.id (runLoaded l)).compress
    | .error e =>
      IO.eprintln s!"{f}: cannot read case: {e}"
      failed := true
  return if failed then 1 else 0
