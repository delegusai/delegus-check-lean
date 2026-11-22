#!/bin/sh
# Copyright 2026 Inam Haq. Licensed under the Apache License, Version 2.0.
#
# Prints `#print axioms` for every public theorem in DelegusCheckSpec/ and fails if
# any depends on anything other than Lean's standard axioms (propext,
# Classical.choice, Quot.sound), or if the sources contain `sorry`, an
# `axiom` declaration or `native_decide`.
set -eu
cd "$(dirname "$0")/.."

if grep -nE '\bsorry\b|^\s*axiom\b|native_decide' DelegusCheckSpec/*.lean DelegusCheckSpec.lean; then
  echo "FAIL: sorry, axiom or native_decide found in the model sources"
  exit 1
fi

gen=.lake/axioms-check.lean
mkdir -p .lake
{
  echo "import DelegusCheckSpec"
  grep -hoE '^(@\[simp\] )?theorem [A-Za-z0-9_.]+' DelegusCheckSpec/*.lean | awk '{print "#print axioms DelegusCheck." $NF}'
} > "$gen"
count=$(grep -c '^#print' "$gen")
out=$(lake env lean "$gen" 2>&1) || { echo "$out"; echo "FAIL: the axiom report did not compile"; exit 1; }
echo "$out"

lines=$(printf '%s\n' "$out" | grep -c "^'DelegusCheck\." || true)
if [ "$lines" -ne "$count" ]; then
  echo "FAIL: expected $count axiom reports, got $lines"
  exit 1
fi
if printf '%s\n' "$out" | grep -q 'depends on axioms' && \
   printf '%s\n' "$out" | grep 'depends on axioms' | sed 's/.*\[\(.*\)\]/\1/' | tr ',' '\n' | tr -d ' ' | grep -vxE 'propext|Classical\.choice|Quot\.sound' | grep -q .; then
  echo "FAIL: a theorem depends on a non-standard axiom"
  exit 1
fi
echo "OK: $count theorems, standard axioms only"
