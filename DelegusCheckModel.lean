/-
Copyright 2026 Inam Haq. Licensed under the Apache License, Version 2.0.

`delegus-check-model [cases-dir [lowered-dir]]`: runs the Lean model of
Delegus Check on each conformance case and prints one JSON object per case
(JSON Lines). Defaults: `vectors/cases`, `vectors/lowered`.

`delegus-check-model --is-jti <value>...`: prints `true` or `false` per
value, the model's own §4.2 `jti` rule (`isJti`).

`delegus-check-model --htu`: reads one JSON string per line on standard
input and prints the model's `htu` canonical form of each (`normalizeHtu`)
as a JSON string, or `null`.

`delegus-check-model --jcs`: reads one JSON text per line on standard input
and prints the model's RFC 8785 canonical text of each (`jcs`) as a JSON
string, or `null` (also for a line that is not JSON).
-/
import DelegusCheckVectors

open DelegusCheck DelegusCheck.Vectors

def main (args : List String) : IO UInt32 := do
  if args.head? == some "--is-jti" then
    for v in args.drop 1 do
      IO.println (if isJti v then "true" else "false")
    return 0
  if args.head? == some "--htu" || args.head? == some "--jcs" then
    let stdin ← IO.getStdin
    let mut out : Array String := #[]
    repeat
      let line ← stdin.getLine
      if line.isEmpty then break
      let l : String := String.ofList (line.toList.filter (· != '\n'))
      let r : Option String :=
        if args.head? == some "--htu" then
          match Lean.Json.parse l with
          | .ok (.str s) => normalizeHtu s
          | _ => none
        else
          match Lean.Json.parse l with
          | .ok j => jcs j
          | .error _ => none
      out := out.push (match r with | some t => (Lean.Json.str t).compress | none => "null")
    IO.println (String.intercalate "\n" out.toList)
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
