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
set -eu
cd "$(dirname "$0")/.."
docker run --rm --privileged -v "$PWD":/src:ro ubuntu:24.04 bash -c '
set -eu
export DEBIAN_FRONTEND=noninteractive
apt-get update -qq >/dev/null
apt-get install -y -qq curl git ca-certificates bubblewrap >/dev/null
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.sh
sh /tmp/elan-init.sh -y --default-toolchain none >/dev/null 2>&1
export PATH=$HOME/.elan/bin:$PATH
mkdir -p /run/user/$(id -u)
mkdir /work && cd /src && tar --exclude=./.lake --exclude=./node_modules --exclude=./.git -cf - . | tar -xf - -C /work
cd /work
echo "== toolchain: $(cat lean-toolchain); bwrap $(bwrap --version)"
# the toolchain directory, so the judges find the bundled external kernels (nanoda_bin)
lake env true
export PATH="$(lake env sh -c "dirname \$(command -v lean)"):$PATH"
lake env sh -c "ls \$(dirname \$(command -v lean))" | tr "\n" " "; echo
lake build >/dev/null 2>&1 && echo "== lake build: ok"
lake build DelegusCheckChallenge >/dev/null 2>&1 && echo "== lake build DelegusCheckChallenge: ok"
lake env leanexport DelegusCheckSpec > /tmp/spec.ndjson
echo "== export sha256: $(sha256sum /tmp/spec.ndjson | cut -d" " -f1)"
echo "== lake comparator --config comparator.json"
set +e
lake comparator --config comparator.json > /tmp/comparator.txt 2>&1
rc=$?
grep -v "^Exporting #\[\|declaration uses .sorry." /tmp/comparator.txt | tail -12
echo "comparator exit=$rc"
echo "== lake check --paranoid"
lake check --paranoid > /tmp/check.txt 2>&1
rc=$?
tail -40 /tmp/check.txt
echo "check exit=$rc"
'
