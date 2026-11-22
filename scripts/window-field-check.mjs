// Copyright 2026 Inam Haq. Licensed under the Apache License, Version 2.0.
//
// v0.3 erratum 1: checks the model's encoding of the Proof window in a
// receipt (`encodeWindow`) against every v0.3 conformance case: the
// receipt's `proof_window_ms` must be the model's encoding of the case's
// window. Only that field is checked; the model does not evaluate v0.3.
//
//   DELEGUS_ENGINE_DIR=/path/to/delegus node --import ./scripts/engine-hook.mjs scripts/window-field-check.mjs

import { execFileSync } from "node:child_process";
import { readFileSync, readdirSync, existsSync } from "node:fs";
import { join, resolve, dirname } from "node:path";
import { fileURLToPath } from "node:url";

const root = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const exe = join(root, ".lake", "build", "bin", "delegus-check-model");
const mod = await import("@delegus/conformance");
const dir = join(mod.VECTORS_DIR, "..", "vectors-v3", "cases");
if (!existsSync(dir)) throw new Error(`no v0.3 cases at ${dir}`);
const names = readdirSync(dir).filter((f) => f.endsWith(".json")).sort();
const cases = names.map((n) => JSON.parse(readFileSync(join(dir, n), "utf8")));
const windows = cases.map((c) => c.input.proof_window_seconds ?? 60);
const model = execFileSync(exe, ["--encode-window", ...windows.map(String)], { encoding: "utf8" }).trim().split("\n")
  .map((l) => (l === "null" ? undefined : Number(l)));
let bad = 0;
let carrying = 0;
cases.forEach((c, i) => {
  const field = c.receipt?.proof_window_ms;
  if (field !== undefined) carrying++;
  if (field !== model[i]) { bad++; console.log(`DISAGREE ${c.vector}: window ${windows[i]} s, receipt ${field}, model ${model[i]}`); }
});
console.log(`${cases.length - bad} of ${cases.length} v0.3 receipts carry exactly the model's proof_window_ms encoding (${carrying} carry the field); ${bad} disagreement(s)`);
process.exitCode = bad === 0 ? 0 : 1;
