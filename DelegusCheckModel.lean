/-
Copyright 2026 Inam Haq. Licensed under the Apache License, Version 2.0.

`delegus-check-model [path ...]`: runs each conformance case through the Phase 0
kernel and prints one JSON object per case (JSON Lines). A path may be a
case file or a directory of them; the default is `vectors/cases`.
-/
import DelegusCheckVectors

open DelegusCheck DelegusCheck.Vectors

def collect (paths : List String) : IO (Array System.FilePath) := do
  let mut out := #[]
  for p in (if paths.isEmpty then ["vectors/cases"] else paths) do
    let fp : System.FilePath := p
    if ← fp.isDir then out := out ++ (← caseFiles fp) else out := out.push fp
  return out

def main (args : List String) : IO UInt32 := do
  let files ← collect args
  let mut failed := false
  for f in files do
    match parseCase (← IO.FS.readFile f) with
    | .ok c => IO.println (resultJson c.id c.checks).compress
    | .error e =>
      IO.eprintln s!"{f}: cannot read case: {e}"
      failed := true
  return if failed then 1 else 0
