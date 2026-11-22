// Copyright 2026 Inam Haq. Licensed under the Apache License, Version 2.0.
//
// The Lean model of Delegus Check as an `Implementation` for the
// @delegus/conformance runner:
//
//   npx delegus-conformance --impl ./bridge/lean-impl.mjs
//
// `evaluate(input)` lowers the input to its primitive facts
// (scripts/lowering.mjs), runs the Lean executable
// (.lake/build/bin/delegus-check-model) on it and returns the model's
// decision, reason, layer results and 24 check outcomes. The model never
// sees the case's expected values. `isJti`, `normalizeHtu` and
// `canonicalize` are the model's own rules (Syntax.lean, Htu.lean,
// Jcs.lean); `sha256` is a primitive of the model, supplied here from
// @delegus/core. No receipt is returned, so receipts are not compared.

import { execFileSync } from "node:child_process";
import { mkdtempSync, mkdirSync, writeFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve, dirname } from "node:path";
import { fileURLToPath } from "node:url";
import { lower } from "../scripts/lowering.mjs";
import { sha256Utf8 } from "@delegus/core";

const root = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const exe = join(root, ".lake", "build", "bin", "delegus-check-model");

/** Run one of the model's line-oriented modes (--htu, --jcs) on many inputs. */
export function runLines(mode, lines) {
  const out = execFileSync(exe, [mode], { input: `${lines.join("\n")}\n`, encoding: "utf8", maxBuffer: 1 << 28 });
  return out.trim().split("\n").map((l) => JSON.parse(l));
}

/** Run the model on one input. */
export function runModel(input, vector = "case") {
  const dir = mkdtempSync(join(tmpdir(), "delegus-check-lean-"));
  try {
    mkdirSync(join(dir, "cases"));
    mkdirSync(join(dir, "lowered"));
    writeFileSync(join(dir, "cases", "case.json"), JSON.stringify({ vector, input }));
    writeFileSync(join(dir, "lowered", "case.json"), JSON.stringify(lower({ vector, input })));
    const out = execFileSync(exe, [join(dir, "cases"), join(dir, "lowered")], { encoding: "utf8" }).trim();
    return JSON.parse(out);
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

export const implementation = {
  name: "delegus-check-lean (Lean 4 model)",
  async evaluate(input) {
    const m = runModel(input);
    return {
      decision: m.decision,
      reason: m.reason,
      protocol_result: m.protocol_result,
      trust_result: m.trust_result,
      protocol_checks: m.protocol_checks,
      trust_checks: m.trust_checks,
    };
  },
  isJti(value) {
    return execFileSync(exe, ["--is-jti", value], { encoding: "utf8" }).trim() === "true";
  },
  normalizeHtu(value) {
    return runLines("--htu", [JSON.stringify(value)])[0];
  },
  canonicalize(value) {
    const r = runLines("--jcs", [JSON.stringify(value)])[0];
    if (r === null) throw new Error("not canonicalizable");
    return r;
  },
  sha256: sha256Utf8,
};

export default implementation;
