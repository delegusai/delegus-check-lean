#!/bin/sh
# Copyright 2026 Inam Haq. Licensed under the Apache License, Version 2.0.
#
# Runs Lean's sandboxed judges, which need Linux and `bwrap`, in a Linux
# container: `lake comparator` (the statements-only challenge against the
# proved development) and `lake check --paranoid` (build, export, and replay
# through Lean's kernel and every external checker bundled with Lean).
#
#   ./scripts/check-in-linux.sh            (needs Docker)
#
# Everything is fetched from its official source inside the container: the
# Ubuntu image, bubblewrap from Ubuntu's archive, elan from
# github.com/leanprover/elan, and the Lean toolchain named in lean-toolchain.
#
# Fails closed: every step must exit 0 and print its success message, the
# export must have the expected hash, and the script exits non-zero if any
# step failed.
set -u
cd "$(dirname "$0")/.."
EXPECTED_EXPORT_SHA256=$(sed -n 's/^EXPECTED_EXPORT_SHA256=//p' scripts/check-independently.sh)
[ -n "$EXPECTED_EXPORT_SHA256" ] || { echo "FAIL: no expected export hash in scripts/check-independently.sh"; exit 2; }
command -v docker >/dev/null 2>&1 || { echo "FAIL: docker is not on PATH"; exit 2; }
docker info >/dev/null 2>&1 || { echo "FAIL: the Docker daemon is not reachable"; exit 2; }
docker run --rm --privileged -e EXPECTED_EXPORT_SHA256="$EXPECTED_EXPORT_SHA256" -v "$PWD":/src:ro ubuntu:24.04 bash -c '
set -u
fail=0; pass=0
ok() { echo "PASS ($1)"; pass=$((pass + 1)); }
bad() { echo "FAIL ($1)"; fail=$((fail + 1)); }
die() { echo "FAIL: $1"; echo "SOME CHECKS FAILED (stopped before checking)"; exit 2; }
export DEBIAN_FRONTEND=noninteractive
apt-get update -qq >/dev/null 2>&1 && apt-get install -y -qq curl git ca-certificates bubblewrap >/dev/null 2>&1 || die "apt-get could not install curl, git and bubblewrap"
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.sh || die "could not fetch elan-init.sh"
sh /tmp/elan-init.sh -y --default-toolchain none >/dev/null 2>&1 || die "elan install failed"
export PATH=$HOME/.elan/bin:$PATH
mkdir -p /run/user/$(id -u) /work
cd /src && tar --exclude=./.lake --exclude=./node_modules --exclude=./.git -cf - . | tar -xf - -C /work
cd /work
command -v lake >/dev/null 2>&1 || die "lake is not on PATH after installing elan"
command -v bwrap >/dev/null 2>&1 || die "bwrap is not installed"
lake env true >/dev/null 2>&1 || die "the Lean toolchain could not be installed"
# the toolchain directory, so the judges find the bundled external kernels (nanoda_bin)
BIN=$(lake env sh -c "dirname \$(command -v lean)") || die "cannot locate the toolchain"
export PATH="$BIN:$PATH"
for t in leanexport nanoda_bin lean4lean con-leche con-ron leanchecker-paranoid; do [ -x "$BIN/$t" ] || die "$t missing from the toolchain"; done
echo "== $(lake env lean --version); bwrap: $(bwrap --version)"
if lake build >/tmp/build.txt 2>&1; then ok "lake build"; else bad "lake build"; fi
if lake build DelegusCheckChallenge >/tmp/build-challenge.txt 2>&1; then ok "lake build DelegusCheckChallenge"; else bad "lake build DelegusCheckChallenge"; fi
lake env leanexport DelegusCheckSpec > /tmp/spec.ndjson 2>/tmp/export.err
H=$(sha256sum /tmp/spec.ndjson | cut -d" " -f1)
echo "export sha256 $H (expected $EXPECTED_EXPORT_SHA256)"
if [ -s /tmp/spec.ndjson ] && [ "$H" = "$EXPECTED_EXPORT_SHA256" ]; then ok "export reproduces, expected hash"; else bad "export reproduces: empty or not the expected hash"; fi
echo "== lake comparator --config comparator.json"
lake comparator --config comparator.json > /tmp/comparator.txt 2>&1
rc=$?
grep -v "^Exporting #\[\|declaration uses .sorry." /tmp/comparator.txt | tail -8
if [ $rc -eq 0 ] && grep -q "Your solution is okay!" /tmp/comparator.txt; then ok "lake comparator"; else bad "lake comparator: exit $rc"; fi
echo "== lake check --paranoid"
lake check --paranoid > /tmp/check.txt 2>&1
rc=$?
grep -v "^Exporting #\[" /tmp/check.txt | tail -24
if [ $rc -eq 0 ] && grep -q "^Uses axioms: propext, Quot.sound, Classical.choice$" /tmp/check.txt \
   && [ "$(grep -c "kernel accepts the solution" /tmp/check.txt)" -ge 6 ]; then ok "lake check --paranoid (six kernels accept)"; else bad "lake check --paranoid: exit $rc"; fi
if [ $fail -eq 0 ] && [ $pass -gt 0 ]; then echo "ALL CHECKS PASSED ($pass)"; exit 0; fi
echo "SOME CHECKS FAILED ($fail failed, $pass passed)"; exit 1
'
