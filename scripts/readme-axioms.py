# Copyright 2026 Inam Haq. Licensed under the Apache License, Version 2.0.
#
# Replaces the axiom-audit block in README.md with the output of
# scripts/check-axioms.sh, read from stdin.
#   ./scripts/check-axioms.sh | python3 scripts/readme-axioms.py
import sys
ax = sys.stdin.read().strip()
s = open("README.md").read()
k = "with Lean 4.36.0, every theorem in\n`DelegusCheckSpec/`:\n\n```\n"
a = s.index(k) + len(k)
b = s.index("```", a)
open("README.md", "w").write(s[:a] + ax + "\n" + s[b:])
