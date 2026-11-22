#!/bin/sh
# Copyright 2026 Inam Haq. Licensed under the Apache License, Version 2.0.
#
# Re-checks the proofs with independent tools, on an inert export.
#
#   ./scripts/check-independently.sh [WORK_DIR]
#
# WORK_DIR (default: a new temporary directory) receives the exports and every
# tool's output; it should be outside the repository.
#
# Bundled with the Lean toolchain (lean-toolchain), so nothing to install:
#   leanexport, leanchecker, leanchecker-paranoid, nanoda_bin, con-leche, con-ron
# Built from their official repositories, into $DELEGUS_CHECK_TOOLS
# (default: ../delegus-check-tools), when present:
#   lean4lean   https://github.com/digama0/lean4lean      (lake build lean4lean)
#   con-leche   https://github.com/leanprover/con-leche   branch `compare` (lake build con-leche)
# A tool that is not present is reported as not run, never as passed.
#
# `lake comparator` and `lake check --paranoid` need Linux and bwrap:
# see scripts/check-in-linux.sh.
set -u
cd "$(dirname "$0")/.."
ROOT=$(pwd)
W=${1:-$(mktemp -d)}
mkdir -p "$W"
TOOLS=${DELEGUS_CHECK_TOOLS:-$ROOT/../delegus-check-tools}
BIN=$(lake env sh -c 'dirname "$(command -v lean)"')
fail=0
step() { printf '\n== %s\n' "$1"; }
result() { if [ "$1" -eq 0 ]; then echo "PASS ($2)"; else echo "FAIL ($2, exit $1)"; fail=1; fi; }
# run NAME CMD...: run CMD with its output in $W/NAME.txt, show the last lines, record its own exit code
run() { name=$1; shift; "$@" > "$W/$name.txt" 2>&1; rc=$?; grep -v "stats:\|Unable to print\|^\]" "$W/$name.txt" | tail -2; result $rc "$name"; }

step "toolchain"
cat lean-toolchain
lake env lean --version

step "build"
lake build >/dev/null 2>&1; result $? "lake build"
python3 scripts/make-challenge.py --check; result $? "challenge current"
lake build DelegusCheckChallenge >/dev/null 2>&1; result $? "lake build DelegusCheckChallenge"

step "export (lean4export, bundled as leanexport)"
lake env leanexport DelegusCheckSpec > "$W/solution.ndjson"; result $? "export DelegusCheckSpec"
lake env leanexport DelegusCheckSpec > "$W/solution-again.ndjson"
lake env leanexport DelegusCheckChallenge > "$W/challenge.ndjson"; result $? "export DelegusCheckChallenge"
head -c 200 "$W/solution.ndjson"; echo
shasum -a 256 "$W/solution.ndjson" "$W/solution-again.ndjson" "$W/challenge.ndjson" 2>/dev/null || sha256sum "$W/solution.ndjson" "$W/solution-again.ndjson" "$W/challenge.ndjson"
cmp -s "$W/solution.ndjson" "$W/solution-again.ndjson"; result $? "export reproduces byte for byte"

step "Lean's kernel on the export (leanchecker --from-export)"
run leanchecker lake env leanchecker --from-export "$W/solution.ndjson"

step "Lean's kernel, paranoid build (leanchecker-paranoid --from-export)"
run leanchecker-paranoid lake env leanchecker-paranoid --from-export "$W/solution.ndjson"

step "Lean's kernel, every constant replayed into a fresh environment (leanchecker --fresh)"
run leanchecker-fresh lake env leanchecker --fresh DelegusCheckSpec

step "nanoda (nanoda_bin) on the export"
cat > "$W/nanoda.json" <<EOF
{
  "export_file_path": "$W/solution.ndjson",
  "use_stdin": false,
  "permitted_axioms": ["propext", "Classical.choice", "Quot.sound", "Lean.trustCompiler"],
  "unpermitted_axiom_hard_error": false,
  "nat_extension": true,
  "string_extension": true,
  "print_success_message": true
}
EOF
run nanoda "$BIN/nanoda_bin" "$W/nanoda.json"

step "con-leche --verified on the export"
run con-leche "$BIN/con-leche" --verified "$W/solution.ndjson"

step "con-ron --verified on the export"
run con-ron "$BIN/con-ron" --verified "$W/solution.ndjson"

step "lean4lean, every constant replayed into a fresh environment"
L4L="$TOOLS/lean4lean/.lake/build/bin/lean4lean"
if [ -x "$L4L" ]; then
  git -C "$TOOLS/lean4lean" log --oneline -1
  # DelegusCheckSpec.Replay imports every other module of the development.
  run lean4lean lake env "$L4L" --fresh DelegusCheckSpec.Replay
else
  echo "NOT RUN: $L4L not found (build it from https://github.com/digama0/lean4lean)"
fi

step "statement comparison: con-leche --compare (challenge vs solution)"
CLC="$TOOLS/con-leche-compare/.lake/build/bin/con-leche"
if [ -x "$CLC" ]; then
  git -C "$TOOLS/con-leche-compare" log --oneline -1
  "$CLC" --compare "$W/challenge.ndjson" "$W/solution.ndjson" > "$W/compare.txt" 2>&1
  rc=$?
  grep -c "^con-leche: theorem .* justified by the solution$" "$W/compare.txt" | sed "s/^/theorems justified by the solution: /"
  grep -v "stats:\|justified by the solution$\|^con-leche: theorem" "$W/compare.txt" | tail -2
  result $rc "con-leche --compare"
else
  echo "NOT RUN: $CLC not found (build branch compare of https://github.com/leanprover/con-leche)"
fi

printf '\noutputs in %s\n' "$W"
[ $fail -eq 0 ] && echo "ALL RUN CHECKS PASSED" || echo "SOME CHECKS FAILED"
exit $fail
