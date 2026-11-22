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
# (default: ../delegus-check-tools):
#   lean4lean   https://github.com/digama0/lean4lean      (lake build lean4lean)
#   con-leche   https://github.com/leanprover/con-leche   branch `compare` (lake build con-leche)
#
# Fails closed: it stops at once if a tool is missing; a step passes only on
# exit code 0 AND the tool's own success message; the export must be
# non-empty, identical across runs and equal to the expected hash; the
# comparison must justify exactly the theorems in comparator.json; and the
# script exits 1 if any step failed (2 if it could not start).
# `lake comparator` and `lake check --paranoid` need Linux and bwrap: see
# scripts/check-in-linux.sh.
set -u
cd "$(dirname "$0")/.."
ROOT=$(pwd)

# The export of DelegusCheckSpec these sources produce. Update it (and the
# README) whenever the model changes.
EXPECTED_EXPORT_SHA256=851daa2df04359703592e9fa7c0bb4acba4d456a742997e4bacddf7c9f02ca23

fail=0
pass=0
step() { printf '\n== %s\n' "$1"; }
ok() { echo "PASS ($1)"; pass=$((pass + 1)); }
bad() { echo "FAIL ($1)"; fail=$((fail + 1)); }
die() { echo "FAIL: $1"; echo "SOME CHECKS FAILED (stopped before checking)"; exit 2; }
sha() { if command -v shasum >/dev/null 2>&1; then shasum -a 256 "$1" | cut -d' ' -f1; else sha256sum "$1" | cut -d' ' -f1; fi; }

# run NAME PATTERN CMD...: CMD's output goes to $W/NAME.txt. PASS only when CMD
# exits 0 AND its output matches PATTERN (the tool's own success message).
run() {
  name=$1; pattern=$2; shift 2
  "$@" > "$W/$name.txt" 2>&1
  rc=$?
  grep -v "stats:\|Unable to print\|^\]" "$W/$name.txt" | tail -2
  if [ $rc -ne 0 ]; then bad "$name: exit $rc"
  elif ! grep -q -- "$pattern" "$W/$name.txt"; then bad "$name: no '$pattern' in its output"
  else ok "$name"; fi
}

step "preflight: every tool present"
command -v lake >/dev/null 2>&1 || die "lake is not on PATH (install elan from https://github.com/leanprover/elan and add ~/.elan/bin to PATH)"
command -v python3 >/dev/null 2>&1 || die "python3 is not on PATH"
LEANV=$(lake env lean --version 2>&1) || die "lake env lean --version failed: $LEANV"
echo "$LEANV"
WANT=$(sed 's/.*:v//' lean-toolchain)
case "$LEANV" in *"version $WANT,"*) ;; *) die "lean is not version $WANT (lean-toolchain)";; esac
BIN=$(lake env sh -c 'dirname "$(command -v lean)"' 2>/dev/null) || die "cannot locate the toolchain's bin directory"
for t in leanexport leanchecker leanchecker-paranoid nanoda_bin con-leche con-ron; do
  [ -x "$BIN/$t" ] || die "$t is missing from the Lean toolchain at $BIN"
done
TOOLS=${DELEGUS_CHECK_TOOLS:-$ROOT/../delegus-check-tools}
L4L="$TOOLS/lean4lean/.lake/build/bin/lean4lean"
CLC="$TOOLS/con-leche-compare/.lake/build/bin/con-leche"
[ -x "$L4L" ] || die "lean4lean not found at $L4L (git clone https://github.com/digama0/lean4lean $TOOLS/lean4lean, then lake build lean4lean there)"
[ -x "$CLC" ] || die "con-leche (compare branch) not found at $CLC (git clone -b compare https://github.com/leanprover/con-leche $TOOLS/con-leche-compare, then lake build con-leche there)"
EXPECTED_THEOREMS=$(python3 -c 'import json; print(len(json.load(open("comparator.json"))["theorem_names"]))' 2>/dev/null) || die "cannot read comparator.json"
[ "$EXPECTED_THEOREMS" -gt 0 ] 2>/dev/null || die "comparator.json lists no theorems"
W=${1:-$(mktemp -d)}
mkdir -p "$W" || die "cannot create $W"
echo "all tools present; $EXPECTED_THEOREMS theorems to compare; outputs in $W"
echo "lean4lean: $(git -C "$TOOLS/lean4lean" log --oneline -1)"
echo "con-leche compare: $(git -C "$TOOLS/con-leche-compare" log --oneline -1)"

step "build"
if lake build > "$W/build.txt" 2>&1; then ok "lake build"; else bad "lake build"; fi
if python3 scripts/make-challenge.py --check; then ok "challenge current"; else bad "challenge out of date"; fi
if lake build DelegusCheckChallenge > "$W/build-challenge.txt" 2>&1; then ok "lake build DelegusCheckChallenge"; else bad "lake build DelegusCheckChallenge"; fi

step "export (lean4export, bundled as leanexport)"
rm -f "$W/solution.ndjson" "$W/solution-again.ndjson" "$W/challenge.ndjson"
if lake env leanexport DelegusCheckSpec > "$W/solution.ndjson" 2> "$W/export.err" && [ -s "$W/solution.ndjson" ]; then ok "export DelegusCheckSpec"; else bad "export DelegusCheckSpec"; fi
lake env leanexport DelegusCheckSpec > "$W/solution-again.ndjson" 2>> "$W/export.err"
if lake env leanexport DelegusCheckChallenge > "$W/challenge.ndjson" 2>> "$W/export.err" && [ -s "$W/challenge.ndjson" ]; then ok "export DelegusCheckChallenge"; else bad "export DelegusCheckChallenge"; fi
head -c 200 "$W/solution.ndjson"; echo
H1=$(sha "$W/solution.ndjson"); H2=$(sha "$W/solution-again.ndjson")
echo "solution export sha256 $H1 (second run: $H2; expected: $EXPECTED_EXPORT_SHA256)"
if [ ! -s "$W/solution.ndjson" ] || [ ! -s "$W/solution-again.ndjson" ]; then bad "export reproduces: an export is empty or missing"
elif [ "$H1" != "$H2" ]; then bad "export reproduces: two runs differ"
elif [ "$H1" != "$EXPECTED_EXPORT_SHA256" ]; then bad "export reproduces: not the expected hash"
else ok "export reproduces byte for byte, with the expected hash"; fi

step "Lean's kernel on the export (leanchecker --from-export)"
run leanchecker "Lean default kernel accepts the solution" lake env leanchecker --from-export "$W/solution.ndjson"

step "Lean's kernel, paranoid build (leanchecker-paranoid --from-export)"
run leanchecker-paranoid "kernel accepts the solution" lake env leanchecker-paranoid --from-export "$W/solution.ndjson"

step "Lean's kernel, every constant replayed into a fresh environment (leanchecker --fresh)"
# leanchecker --fresh prints nothing on success and fails with a non-zero exit;
# --verbose makes it name the module, so an empty run cannot pass.
run leanchecker-fresh "replaying DelegusCheckSpec with --fresh" lake env leanchecker --fresh --verbose DelegusCheckSpec

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
run nanoda "^Checked [1-9][0-9]* declarations with no typechecker errors" "$BIN/nanoda_bin" "$W/nanoda.json"

step "con-leche --verified on the export"
run con-leche "accepted [1-9][0-9]* declarations (--verified)" "$BIN/con-leche" --verified "$W/solution.ndjson"

step "con-ron --verified on the export"
run con-ron "accepted [1-9][0-9]* declarations (--verified)" "$BIN/con-ron" --verified "$W/solution.ndjson"

step "lean4lean, every constant replayed into a fresh environment"
# DelegusCheckSpec.Replay imports every other module of the development.
run lean4lean "checked [1-9][0-9]* declarations" lake env "$L4L" --fresh DelegusCheckSpec.Replay

step "statement comparison: con-leche --compare (challenge vs solution)"
"$CLC" --compare "$W/challenge.ndjson" "$W/solution.ndjson" > "$W/compare.txt" 2>&1
rc=$?
summary=$(grep "axioms justified by the solution" "$W/compare.txt" | tail -1)
echo "$summary"
decls=$(echo "$summary" | sed -n 's/.*accepted \([0-9]*\) declarations, \([0-9]*\) axioms justified.*/\1/p')
just=$(echo "$summary" | sed -n 's/.*accepted \([0-9]*\) declarations, \([0-9]*\) axioms justified.*/\2/p')
if [ $rc -ne 0 ]; then bad "con-leche --compare: exit $rc"
elif [ -z "$decls" ] || [ "$decls" -eq 0 ]; then bad "con-leche --compare: no declarations accepted"
elif [ "$just" != "$EXPECTED_THEOREMS" ]; then bad "con-leche --compare: ${just:-no} theorems justified, expected $EXPECTED_THEOREMS"
else ok "con-leche --compare: $just of $EXPECTED_THEOREMS theorems justified, $decls declarations accepted"; fi

printf '\noutputs in %s\n' "$W"
if [ $fail -eq 0 ] && [ $pass -gt 0 ]; then
  echo "ALL CHECKS PASSED ($pass)"
  exit 0
fi
echo "SOME CHECKS FAILED ($fail failed, $pass passed)"
exit 1
