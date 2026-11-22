// Copyright 2026 Inam Haq. Licensed under the Apache License, Version 2.0.
//
// Compares the Lean model with the reference engine on every conformance case.
//
//   node scripts/compare.mjs [--engine <module>]
//
// 1. Checks that vectors/cases/ and vectors/sets/ are byte-identical to the
//    cases and sets shipped in the pinned @delegus/conformance package.
// 2. Checks that vectors/lowered/ is what scripts/lower.mjs produces, then runs
//    the Lean model (.lake/build/bin/delegus-check-model) on the cases and
//    their lowered primitive facts. The model computes every check itself.
// 3. Runs the reference engine (@delegus/core, through the package's
//    `coreImplementation`) live on each case's input.
// 4. Compares decision, reason, both layer results, all 24 check outcomes,
//    request_hash and the attributed principal.
//
// `--engine <module>` loads `coreImplementation` from another module instead,
// for example a local checkout's packages/conformance/src/index.ts.
// Exits 1 on any mismatch.

import { execFileSync } from "node:child_process";
import { readFileSync, readdirSync } from "node:fs";
import { join, resolve, dirname } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";

const root = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const casesDir = join(root, "vectors", "cases");
const PROTOCOL = Array.from({ length: 20 }, (_, i) => `P${i + 1}`);
const TRUST = ["T1", "T2", "T3", "T5"];

const args = process.argv.slice(2);
const engineIdx = args.indexOf("--engine");
const engineModule = engineIdx >= 0 ? args[engineIdx + 1] : "@delegus/conformance";
const mod = await import(engineIdx >= 0 ? pathToFileURL(resolve(engineModule)).href : engineModule);
const engine = mod.coreImplementation;
if (engine === undefined) throw new Error(`${engineModule} does not export coreImplementation`);

let failures = 0;
const fail = (msg) => {
  failures++;
  console.log(`MISMATCH ${msg}`);
};

// 1. The repository's cases are the pinned package's cases, byte for byte.
const pkgDir = dirname(fileURLToPath(import.meta.resolve("@delegus/conformance")));
const pkgCases = join(pkgDir, "vectors", "cases");
const pkgVersion = JSON.parse(readFileSync(join(pkgDir, "package.json"), "utf8")).version;
const names = readdirSync(casesDir).filter((f) => f.endsWith(".json")).sort();
const pkgNames = readdirSync(pkgCases).filter((f) => f.endsWith(".json")).sort();
if (JSON.stringify(names) !== JSON.stringify(pkgNames)) fail(`case file list differs from @delegus/conformance@${pkgVersion}`);
for (const n of names) {
  if (!readFileSync(join(casesDir, n)).equals(readFileSync(join(pkgCases, n)))) fail(`${n} differs from @delegus/conformance@${pkgVersion}`);
}

// 1b. The normalization sets too.
const pkgSets = join(pkgDir, "vectors", "sets");
for (const n of ["htu.json", "jcs.json", "jti.json"]) {
  if (!readFileSync(join(root, "vectors", "sets", n)).equals(readFileSync(join(pkgSets, n)))) fail(`sets/${n} differs from @delegus/conformance@${pkgVersion}`);
}

// 2. The lowered facts are current, and the Lean model.
try {
  execFileSync(process.execPath, [join(root, "scripts", "lower.mjs"), "--check"], { stdio: "inherit" });
} catch {
  fail("vectors/lowered/ is out of date");
}
const exe = join(root, ".lake", "build", "bin", "delegus-check-model");
const lean = new Map();
for (const line of execFileSync(exe, [casesDir, join(root, "vectors", "lowered")], { encoding: "utf8" }).split("\n")) {
  if (line.trim() === "") continue;
  const r = JSON.parse(line);
  lean.set(r.vector, r);
}

// 3 and 4. The engine, live, and the comparison.
const same = (a, b) => JSON.stringify(a) === JSON.stringify(b);
let matched = 0;
for (const n of names) {
  const file = JSON.parse(readFileSync(join(casesDir, n), "utf8"));
  const id = file.vector;
  const m = lean.get(id);
  if (m === undefined) {
    fail(`${id}: no output from the Lean model`);
    continue;
  }
  const e = await engine.evaluate(file.input);
  const diffs = [];
  for (const f of ["decision", "reason", "protocol_result", "trust_result"]) {
    if (!same(m[f], e[f])) diffs.push(`${f}: lean=${JSON.stringify(m[f])} engine=${JSON.stringify(e[f])}`);
  }
  for (const k of PROTOCOL) {
    if (!same(m.protocol_checks[k], e.protocol_checks[k])) diffs.push(`${k}: lean=${JSON.stringify(m.protocol_checks[k])} engine=${JSON.stringify(e.protocol_checks[k])}`);
  }
  for (const k of TRUST) {
    if (!same(m.trust_checks[k], e.trust_checks[k])) diffs.push(`${k}: lean=${JSON.stringify(m.trust_checks[k])} engine=${JSON.stringify(e.trust_checks[k])}`);
  }
  const rh = e.receipt?.request_hash ?? null;
  if (m.request_hash !== rh) diffs.push(`request_hash: lean=${m.request_hash} engine=${rh}`);
  const pr = e.receipt?.principal?.id ?? null;
  if (m.principal !== pr) diffs.push(`principal: lean=${m.principal} engine=${pr}`);
  if (Object.keys(e.protocol_checks).length !== 20 || Object.keys(e.trust_checks).length !== 4) diffs.push("engine did not report exactly 20 + 4 checks");
  if (!m.prerequisite_table_followed) diffs.push("lean: outcomes do not follow the prerequisite table");
  if (!m.reason_codes_well_formed) diffs.push("lean: a false check carries a code its check cannot carry");
  if (diffs.length === 0) {
    matched++;
    console.log(`match    ${id}  ${e.decision} ${e.reason ?? "null"}`);
  } else {
    fail(`${id}: ${diffs.join("; ")}`);
  }
}
if (names.length !== 40) fail(`expected 40 cases, found ${names.length}`);

console.log(`\nengine: ${engineIdx >= 0 ? engineModule : `@delegus/conformance@${pkgVersion}`} (coreImplementation)`);
console.log(`${matched} of ${names.length} cases match on decision, reason, both layer results, all 24 checks, request_hash and principal; ${failures} mismatch(es)`);
process.exit(failures === 0 ? 0 : 1);
