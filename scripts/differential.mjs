// Copyright 2026 Inam Haq. Licensed under the Apache License, Version 2.0.
//
// The mutation differential: change each conformance case's input in many
// small ways (clock, Proof window, relying party, Action fields, service
// state, keys, tampered bytes) and run every mutant through both the
// reference engine and the Lean model. There is no expected value: the two
// must simply agree on the decision, the reason, both layer results, all 24
// check outcomes, request_hash, the attributed principal, and the service
// operations performed (issuer read, revocation read, replay write: which,
// in which order, with which arguments), taken from the engine's in-memory
// service call log and the model's recording run of `evaluateM`.
//
//   node scripts/differential.mjs [--engine <module>] [--show <n>]
//
// Action and `iat` mutants are also re-signed with the cases' published test
// Agent keys, so they reach the authorization checks and the window check.
//
// Exits 1 on any disagreement. A mutant the engine rejects as invalid
// service input (it throws, by design, rather than deciding) is counted
// and skipped.

import { execFileSync } from "node:child_process";
import { mkdtempSync, mkdirSync, readFileSync, readdirSync, writeFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve, dirname } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import { lower } from "./lowering.mjs";
import {
  createCompactJws, signEd25519, ed25519PrivateKeyFromSeed, ed25519RawPublicKey, didKeyFromEd25519,
  canonicalize, sha256Utf8, evaluate as coreEvaluate,
} from "@delegus/core";

const root = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const casesDir = join(root, "vectors", "cases");
const exe = join(root, ".lake", "build", "bin", "delegus-check-model");
const args = process.argv.slice(2);
const engineIdx = args.indexOf("--engine");
const showIdx = args.indexOf("--show");
const show = showIdx >= 0 ? Number(args[showIdx + 1]) : 20;
const mod = await import(engineIdx >= 0 ? pathToFileURL(resolve(args[engineIdx + 1])).href : "@delegus/conformance");
const engine = mod.coreImplementation;

/** The service operations the engine performed, from the in-memory service's call log. */
async function engineTrace(input) {
  if (typeof mod.serviceFromState !== "function" || typeof mod.evaluateInputFromVector !== "function") return null;
  const svc = mod.serviceFromState(input, Date.parse(input.evaluated_at));
  await coreEvaluate(mod.evaluateInputFromVector(input, svc));
  return svc.calls.map((c) => c.hook === "issuer" ? ["issuer", c.args[0]]
    : c.hook === "statusList" ? ["status", c.args[1]]
    : ["replay", c.args[0], c.args[1], "PXAT", c.args[2]]);
}

const PROTOCOL = Array.from({ length: 20 }, (_, i) => `P${i + 1}`);
const TRUST = ["T1", "T2", "T3", "T5"];

const b64json = (seg) => { try { return JSON.parse(Buffer.from(seg, "base64url").toString("utf8")); } catch { return null; } };
const segs = (jws) => (typeof jws === "string" ? jws.split(".") : []);
const iso = (ms) => new Date(ms).toISOString();
// The conformance cases sign with fixed, published test keys (Ed25519 seeds
// 0x01…0x07, see the vectors README). Re-signing a Proof with the Agent's
// test key lets a changed Action or `iat` reach P15–P20 and P13 instead of
// stopping at P14 or P9.
const testKeys = Array.from({ length: 7 }, (_, i) => {
  const key = ed25519PrivateKeyFromSeed(new Uint8Array(32).fill(i + 1));
  return { key, did: didKeyFromEd25519(ed25519RawPublicKey(key)) };
});

async function resignProof(input, edit) {
  const [h] = segs(input.proof);
  const header = b64json(h);
  const payload = b64json(segs(input.proof)[1]);
  if (header === null || payload === null) return null;
  const agent = testKeys.find((k) => k.did === payload.iss);
  if (agent === undefined) return null;
  edit(payload);
  return createCompactJws(header, payload, (data) => signEd25519(agent.key, data));
}

const flipLast = (s) => s.slice(0, -1) + (s.at(-1) === "A" ? "B" : "A");

/** Named mutations of one input. Each returns a new input, or null when it does not apply. */
function mutations(input) {
  const now = Date.parse(input.evaluated_at);
  const grantHeader = b64json(segs(input.grant)[0]);
  const proofPayload = b64json(segs(input.proof)[1]);
  const action = input.action;
  const m = [];
  const add = (name, f) => {
    const x = structuredClone(input);
    const r = f(x);
    if (r !== false) m.push([name, x]);
  };
  for (const d of [-86_400_000 * 60, -86_400_000, -301_000, -61_000, -60_000, -1_000, 1_000, 59_000, 60_000, 60_001, 61_000, 300_000, 86_400_000, 86_400_000 * 30, 86_400_000 * 60]) {
    add(`clock${d >= 0 ? "+" : ""}${d}ms`, (x) => { x.evaluated_at = iso(now + d); });
  }
  for (const w of [1, 30, 59, 60, 61, 120, 300]) add(`window=${w}`, (x) => { x.proof_window_seconds = w; });
  add("window+clock-edge", (x) => { x.proof_window_seconds = 1; x.evaluated_at = iso(now + 1_000); });
  add("rp=other", (x) => { x.relying_party = "did:web:other.example"; });
  add("rp=sub-path", (x) => { x.relying_party = `${input.relying_party}:sub`; });
  if (action && typeof action === "object" && !Array.isArray(action)) {
    if (typeof action.amount === "number") {
      for (const a of [0, action.amount + 1, action.amount - 1, 49_999, 50_000, 50_001, 1e12, -1, 1.5]) add(`amount=${a}`, (x) => { x.action.amount = a; });
      add("amount=string", (x) => { x.action.amount = String(action.amount); });
    }
    if (typeof action.currency === "string") for (const c of ["EUR", "usd", "US", "USDX"]) add(`currency=${c}`, (x) => { x.action.currency = c; });
    if (typeof action.resource === "string") {
      for (const r of ["", "other", "https://api.example.com/v1/other", "https://api.example.com/v1/orders/1/items", `${action.resource}/x`]) add(`resource=${r || "empty"}`, (x) => { x.action.resource = r; });
    }
    if (typeof action.method === "string") for (const me of ["DELETE", "get", "POST", "PUT"]) add(`method=${me}`, (x) => { x.action.method = me; });
    add("action+extra", (x) => { x.action.note = "x"; });
    add("action-type", (x) => { delete x.action.type; });
    add("action.type=unknown", (x) => { x.action.type = "commerce:refund"; });
    add("action.type=swap", (x) => { x.action.type = action.type === "api:call" ? "commerce:purchase" : "api:call"; });
  }
  const st = input.state;
  add("issuer=unavailable", (x) => { x.state.issuer = "unavailable"; });
  add("issuer=unregistered", (x) => { x.state.issuer = { did: "did:web:acme.example", registered: false }; });
  if (typeof st.issuer === "object" && st.issuer.registered) {
    add("issuer.unverified", (x) => { x.state.issuer.domain_verified = false; });
    add("issuer.verified", (x) => { x.state.issuer.domain_verified = true; });
    if (grantHeader && typeof grantHeader.kid === "string") add("kid=compromised", (x) => { x.state.issuer.compromised_kids = [grantHeader.kid]; });
    add("kid=retired-only", (x) => { x.state.issuer.compromised_kids = ["did:web:acme.example#key-9"]; });
    add("issuer.other-did", (x) => { x.state.issuer.did = "did:web:other.example"; });
    add("diddoc=empty", (x) => { x.state.issuer.did_document = "{}"; });
    add("diddoc=garbage", (x) => { x.state.issuer.did_document = "not json"; });
  }
  add("status=unavailable", (x) => { x.state.status_list = "unavailable"; });
  if (typeof st.status_list === "object") {
    add("status.url=other", (x) => { x.state.status_list.url = "https://status.test.delegus.example/other/1"; });
    add("status.credential=tampered", (x) => { x.state.status_list.credential = flipLast(st.status_list.credential); });
    add("status.credential=garbage", (x) => { x.state.status_list.credential = "a.b.c"; });
  }
  add("service.did=other", (x) => { x.service.did = "did:web:other.delegus.example"; });
  add("service.status-keys=none", (x) => { x.service.status_list_keys = {}; });
  add("service.status-key=swapped", (x) => {
    const kid = Object.keys(input.service.status_list_keys)[0];
    if (kid === undefined) return false;
    x.service.status_list_keys = { [kid]: Object.values(input.service.receipt_keys)[0] ?? "AAAA" };
  });
  add("replay=unavailable", (x) => { x.state.replay.unavailable = true; });
  // Erratum 5: earlier uses of the same request through the same store, store lag and store clock.
  const w = (input.proof_window_seconds ?? 60) * 1000;
  const iatMs = proofPayload && typeof proofPayload.iat === "number" ? proofPayload.iat * 1000 : now;
  const earlier = [[], [now], [now - 1_000], [now - 60_000], [iatMs - w], [iatMs - w, iatMs], [iatMs + w + 5_001]];
  const lags = [0, 999, 1_018, 3_999, 4_000, 4_001, 5_000, -5_000, -100_000];
  for (const e of earlier) {
    for (const lag of lags) {
      add(`earlier=${e.map((t) => t - now).join("/")}+lag=${lag}`, (x) => {
        if (e.length > 0) x.state.replay.earlier_uses = e.map(iso);
        x.state.replay.store_lag_ms = lag;
      });
    }
  }
  for (const final of [iatMs - w, iatMs + w, iatMs + w + 1]) {
    for (const lag of [0, 1_018, 4_000, 4_001]) {
      add(`edge:first=iat-w,final=${final - iatMs},lag=${lag}`, (x) => {
        x.evaluated_at = iso(final);
        x.state.replay.earlier_uses = [iso(iatMs - w)];
        x.state.replay.store_lag_ms = lag;
      });
    }
  }
  if (proofPayload && typeof proofPayload.jti === "string") add("replay=consumed", (x) => { x.state.replay.consumed = [proofPayload.jti]; });
  add("replay=other-consumed", (x) => { x.state.replay.consumed = ["AAAAAAAAAAAAAAAAAAAAAA"]; });
  add("grant=tampered-sig", (x) => { x.grant = flipLast(input.grant); });
  add("proof=tampered-sig", (x) => { x.proof = flipLast(input.proof); });
  add("grant=proof", (x) => { x.grant = input.proof; });
  add("proof=grant", (x) => { x.proof = input.grant; });
  add("grant=empty", (x) => { x.grant = ""; });
  add("proof=garbage", (x) => { x.proof = "x.y.z"; });
  return m;
}

/** Action and `iat` mutations with the Proof re-signed by the Agent's test key. */
async function resigned(input) {
  const out = [];
  for (const [name, x] of mutations(input)) {
    if (!name.startsWith("amount=") && !name.startsWith("currency=") && !name.startsWith("resource=") &&
        !name.startsWith("method=") && !name.startsWith("action")) continue;
    let text;
    try { text = canonicalize(x.action); } catch { continue; }
    const proof = await resignProof(input, (p) => { p.action_hash = sha256Utf8(text); });
    if (proof === null) continue;
    x.proof = proof;
    out.push([`${name}+resigned`, x]);
  }
  const p = b64json(segs(input.proof)[1]);
  const w = input.proof_window_seconds ?? 60;
  if (p !== null && typeof p.iat === "number") {
    for (const d of [-w - 1, -w, -w + 1, 0, w - 1, w, w + 1, 3600]) {
      const proof = await resignProof(input, (q) => { q.iat = p.iat + d; });
      if (proof === null) continue;
      const x = structuredClone(input);
      x.proof = proof;
      out.push([`iat${d >= 0 ? "+" : ""}${d}s+resigned`, x]);
    }
    for (const [field, v] of [["aud", "did:web:other.example"], ["grant", "urn:delegus:grant:01J9X4QK7M3Y2Z8N6P5R4T3V2X"],
        ["jti", "short"], ["jti", "a".repeat(65)], ["jti", "has space in it 1234567890"], ["htm", "get"],
        ["htu", "HTTPS://Api.Example.com/x"], ["action_hash", "sha256:00"], ["extra", 1]]) {
      const proof = await resignProof(input, (q) => { q[field] = v; });
      if (proof === null) continue;
      const x = structuredClone(input);
      x.proof = proof;
      out.push([`proof.${field}=${String(v).slice(0, 12)}+resigned`, x]);
    }
  }
  return out;
}

const names = readdirSync(casesDir).filter((f) => f.endsWith(".json")).sort();
const dir = mkdtempSync(join(tmpdir(), "delegus-check-diff-"));
mkdirSync(join(dir, "cases"));
mkdirSync(join(dir, "lowered"));
const mutants = [];
let rejected = 0;
try {
  for (const n of names) {
    const file = JSON.parse(readFileSync(join(casesDir, n), "utf8"));
    for (const [name, input] of [...mutations(file.input), ...(await resigned(file.input))]) {
      let e;
      try {
        e = await engine.evaluate(input);
      } catch {
        rejected++;
        continue;
      }
      const trace = await engineTrace(input);
      const id = `${file.vector}~${name}`;
      const fname = `m${String(mutants.length).padStart(5, "0")}.json`;
      writeFileSync(join(dir, "cases", fname), JSON.stringify({ vector: id, input }));
      writeFileSync(join(dir, "lowered", fname), JSON.stringify(lower({ vector: id, input })));
      mutants.push({ id, e, trace });
    }
  }
  const model = new Map();
  const out = execFileSync(exe, [join(dir, "cases"), join(dir, "lowered")], { encoding: "utf8", maxBuffer: 1 << 28 });
  for (const line of out.split("\n")) if (line.trim() !== "") { const r = JSON.parse(line); model.set(r.vector, r); }

  const same = (a, b) => JSON.stringify(a) === JSON.stringify(b);
  const disagreements = [];
  const decisions = { ALLOW: 0, DENY: 0 };
  const reasons = new Map();
  let traced = 0;
  for (const { id, e, trace } of mutants) {
    const m = model.get(id);
    decisions[e.decision]++;
    reasons.set(e.reason ?? "null", (reasons.get(e.reason ?? "null") ?? 0) + 1);
    if (m === undefined) { disagreements.push(`${id}: no model output`); continue; }
    const diffs = [];
    for (const f of ["decision", "reason", "protocol_result", "trust_result"]) if (!same(m[f], e[f])) diffs.push(`${f}: lean=${JSON.stringify(m[f])} engine=${JSON.stringify(e[f])}`);
    for (const k of PROTOCOL) if (!same(m.protocol_checks[k], e.protocol_checks[k])) diffs.push(`${k}: lean=${JSON.stringify(m.protocol_checks[k])} engine=${JSON.stringify(e.protocol_checks[k])}`);
    for (const k of TRUST) if (!same(m.trust_checks[k], e.trust_checks[k])) diffs.push(`${k}: lean=${JSON.stringify(m.trust_checks[k])} engine=${JSON.stringify(e.trust_checks[k])}`);
    const rh = e.receipt?.request_hash ?? null;
    if (m.request_hash !== rh) diffs.push(`request_hash: lean=${m.request_hash} engine=${rh}`);
    const pr = e.receipt?.principal?.id ?? null;
    if (m.principal !== pr) diffs.push(`principal: lean=${m.principal} engine=${pr}`);
    if (trace !== null) {
      traced++;
      if (!same(m.trace, trace)) diffs.push(`trace: lean=${JSON.stringify(m.trace)} engine=${JSON.stringify(trace)}`);
    }
    if (diffs.length > 0) disagreements.push(`${id}: ${diffs.join("; ")}`);
  }
  for (const d of disagreements.slice(0, show)) console.log(`DISAGREE ${d}`);
  if (disagreements.length > show) console.log(`... and ${disagreements.length - show} more`);
  const reasonList = [...reasons.entries()].sort((a, b) => b[1] - a[1]).map(([r, c]) => `${r} ${c}`).join(", ");
  console.log(`mutants: ${mutants.length} evaluated (${decisions.ALLOW} ALLOW, ${decisions.DENY} DENY), ${rejected} rejected by the engine as invalid input`);
  console.log(`engine reasons: ${reasonList}`);
  console.log(`service operations compared on ${traced} mutants (which operations, in which order, with which arguments)`);
  console.log(`${mutants.length - disagreements.length} of ${mutants.length} mutants agree on decision, reason, both layer results, all 24 checks, request_hash, principal and the operation trace; ${disagreements.length} disagreement(s)`);
  process.exitCode = disagreements.length === 0 ? 0 : 1;
} finally {
  rmSync(dir, { recursive: true, force: true });
}
