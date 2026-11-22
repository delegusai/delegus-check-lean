// Copyright 2026 Inam Haq. Licensed under the Apache License, Version 2.0.
//
// The lowering: for each conformance case, compute only the primitive facts
// the Lean model takes as parameters (`Prims` in DelegusCheckSpec/Inputs.lean)
// and write them to vectors/lowered/<id>.json.
//
//   node scripts/lower.mjs [--check]
//
// It uses only the primitive functions of @delegus/core: strict JWS and JSON
// decoding, base58 and base64url, Ed25519 verification and key safety,
// SHA-256, RFC 8785 JCS, the htu canonical form, RFC 3339 parsing and GZIP.
// It never imports the evaluator, the Grant or Proof parsers or the
// capability rules, so every decision is made by the Lean model.
//
// The facts are tables over every value the model could ask about: every
// string inside the decoded Grant, Proof, status credential and DID
// document, every candidate key, and every key × JWS pair. Anything not in a
// table is answered "no" by the model (fail closed): the signature table
// lists only the key × JWS pairs that verify, the htu table only the
// strings already in canonical form, the time table only the strings that
// parse.
//
// --check: regenerate in memory and fail if the committed files differ.

import { readFileSync, readdirSync, writeFileSync, mkdirSync, existsSync } from "node:fs";
import { join, resolve, dirname } from "node:path";
import { fileURLToPath } from "node:url";
import { lower } from "./lowering.mjs";

const root = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const casesDir = join(root, "vectors", "cases");
const outDir = join(root, "vectors", "lowered");
const check = process.argv.includes("--check");

const names = readdirSync(casesDir).filter((f) => f.endsWith(".json")).sort();
if (!check) mkdirSync(outDir, { recursive: true });
let stale = 0;
for (const n of names) {
  const file = JSON.parse(readFileSync(join(casesDir, n), "utf8"));
  const text = `${JSON.stringify(lower(file))}\n`;
  const path = join(outDir, n);
  if (check) {
    if (!existsSync(path) || readFileSync(path, "utf8") !== text) {
      stale++;
      console.log(`STALE ${n}`);
    }
  } else {
    writeFileSync(path, text);
  }
}
if (check && stale > 0) {
  console.log(`${stale} lowered file(s) out of date; run node scripts/lower.mjs`);
  process.exit(1);
}
console.log(`${check ? "checked" : "wrote"} ${names.length} lowered cases`);
