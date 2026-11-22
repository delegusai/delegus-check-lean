/-
Copyright 2026 Inam Haq. Licensed under the Apache License, Version 2.0.

`delegus-check-model [cases-dir [lowered-dir]]`: runs the Lean model of
Delegus Check on each conformance case and prints one JSON object per case
(JSON Lines). Defaults: `vectors/cases`, `vectors/lowered`.

`delegus-check-model --is-jti <value>...`: prints `true` or `false` per
value, the model's own §4.2 `jti` rule (`isJti`), for the conformance
runner's `jti` set.
-/
import DelegusCheckVectors

open DelegusCheck DelegusCheck.Vectors

def main (args : List String) : IO UInt32 := do
  if args.head? == some "--is-jti" then
    for v in args.drop 1 do
      IO.println (if isJti v then "true" else "false")
    return 0
  let cases : System.FilePath := args.getD 0 "vectors/cases"
  let lowered : System.FilePath := args.getD 1 "vectors/lowered"
  let mut failed := false
  for f in ← caseFiles cases do
    match ← loadFile f lowered with
    | .ok l => IO.println (resultJson l.id (runLoaded l) (traceLoaded l)).compress
    | .error e =>
      IO.eprintln s!"{f}: cannot read case: {e}"
      failed := true
  return if failed then 1 else 0
