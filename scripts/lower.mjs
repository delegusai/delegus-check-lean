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
import { gunzipSync } from "node:zlib";
import {
  parseCompactJws, parseJson, decodeBase58, encodeBase58, decodeBase64Url, isUsableEd25519PublicKey,
  verifyEd25519, sha256Utf8, canonicalize, isCanonicalHtu, parseRfc3339Utc,
} from "@delegus/core";

const root = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const casesDir = join(root, "vectors", "cases");
const outDir = join(root, "vectors", "lowered");
const check = process.argv.includes("--check");

const hex = (b) => Buffer.from(b).toString("hex");
const fromHex = (h) => Uint8Array.from(Buffer.from(h, "hex"));

/** Multibase base58btc Ed25519 key, decoded without the key-safety check (that is `keyOk`). */
function rawMultibase(s) {
  if (typeof s !== "string" || !s.startsWith("z")) return null;
  const b = decodeBase58(s.slice(1));
  if (b === null || b.length !== 34 || b[0] !== 0xed || b[1] !== 0x01) return null;
  if (`z${encodeBase58(b)}` !== s) return null;
  return hex(b.slice(2));
}

function rawDidKey(s) {
  const m = /^did:key:z([1-9A-HJ-NP-Za-km-z]+)$/.exec(s);
  return m ? rawMultibase(`z${m[1]}`) : null;
}

function strings(v, out = new Set()) {
  if (typeof v === "string") out.add(v);
  else if (Array.isArray(v)) v.forEach((x) => strings(x, out));
  else if (v !== null && typeof v === "object") Object.entries(v).forEach(([k, x]) => { out.add(k); strings(x, out); });
  return out;
}

function lower(file) {
  const input = file.input;
  const st = input.state;
  const jwsTexts = [input.grant, input.proof];
  if (st.status_list !== "unavailable") jwsTexts.push(st.status_list.credential);
  const jws = [];
  for (const text of jwsTexts) {
    const j = parseCompactJws(text);
    if (j === null) continue;
    const [h, p, s] = text.split(".");
    jws.push({ text, header: j.header, payload: j.payload, signingInput: `${h}.${p}`, signature: s });
  }

  const json = [];
  let docValue = null;
  if (typeof st.issuer === "object" && st.issuer.registered && typeof st.issuer.did_document === "string") {
    try {
      docValue = parseJson(st.issuer.did_document);
      json.push({ text: st.issuer.did_document, value: docValue });
    } catch { /* not strict JSON: absent from the table */ }
  }

  const all = new Set();
  for (const j of jws) { strings(j.header, all); strings(j.payload, all); }
  if (docValue !== null) strings(docValue, all);
  all.add(input.evaluated_at);

  const didKey = [];
  const multibase = [];
  const pubs = new Set();
  for (const s of all) {
    const k = rawDidKey(s);
    if (k !== null) { didKey.push({ s, pub: k }); pubs.add(k); }
    const m = rawMultibase(s);
    if (m !== null) { multibase.push({ s, pub: m }); pubs.add(m); }
  }
  const statusKeys = [];
  for (const [kid, b64] of Object.entries(input.service.status_list_keys)) {
    const raw = decodeBase64Url(b64);
    if (raw === null) continue;
    statusKeys.push([kid, hex(raw)]);
    pubs.add(hex(raw));
  }
  const keyOk = [...pubs].map((pub) => ({ pub, ok: isUsableEd25519PublicKey(fromHex(pub)) }));
  const sig = [];
  for (const pub of pubs) {
    jws.forEach((j, i) => {
      const signature = decodeBase64Url(j.signature);
      const ok = signature !== null && verifyEd25519(fromHex(pub), new TextEncoder().encode(j.signingInput), signature);
      if (ok) sig.push({ pub, jws: i });
    });
  }

  let jcs = null;
  try { jcs = canonicalize(input.action); } catch { jcs = null; }
  const sha256 = jcs === null ? [] : [{ text: jcs, hash: sha256Utf8(jcs) }];

  const htu = [];
  const time = [];
  const list = [];
  for (const s of all) {
    if (isCanonicalHtu(s)) htu.push(s);
    const ms = parseRfc3339Utc(s);
    if (ms !== null) time.push({ s, ms });
    if (s.startsWith("u")) {
      const b = decodeBase64Url(s.slice(1));
      if (b !== null) {
        let bits = null;
        try { bits = gunzipSync(b, { maxOutputLength: 16 * 1024 * 1024 }); } catch { /* not GZIP */ }
        if (bits !== null) {
          // the decoded bitstring, sparsely: its length in bytes and the set bits (most significant first)
          const set = [];
          for (let i = 0; i < bits.length * 8; i++) if ((bits[i >> 3] >> (7 - (i & 7))) & 1) set.push(i);
          list.push({ s: s.slice(1), bytes: bits.length, set });
        }
      }
    }
  }

  return {
    vector: file.vector,
    lowering: "delegus-check-lean lowering v1",
    statusKeys,
    prims: { jws, json, didKey, multibase, keyOk, sig, jcs, sha256, htu, time, list },
  };
}

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
