// Copyright 2026 Inam Haq. Licensed under the Apache License, Version 2.0.
//
// The model's own htu canonical form (Htu.lean) and RFC 8785 JCS (Jcs.lean)
// against @delegus/core's `normalizeHtu` and `canonicalize`, on many
// generated inputs. Deterministic (a fixed-seed generator), no expected
// values: the two must agree exactly.
//
//   node scripts/primitives-differential.mjs [--count <n>]
//
// Exits 1 on any disagreement.

import { normalizeHtu, canonicalize } from "@delegus/core";
import { runLines } from "../bridge/lean-impl.mjs";

const args = process.argv.slice(2);
const countIdx = args.indexOf("--count");
const N = countIdx >= 0 ? Number(args[countIdx + 1]) : 20000;

// mulberry32, fixed seed
let seed = 0x5eed2026;
const rand = () => {
  seed |= 0; seed = (seed + 0x6d2b79f5) | 0;
  let t = Math.imul(seed ^ (seed >>> 15), 1 | seed);
  t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
  return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
};
const pick = (xs) => xs[Math.floor(rand() * xs.length)];
const many = (f, max) => Array.from({ length: Math.floor(rand() * (max + 1)) }, f).join("");

// ---- htu -------------------------------------------------------------------
const schemes = ["http", "https", "HTTP", "HttpS", "ftp", "h", "http:", "https:/", ""];
const hostChars = ["a", "Z", "0", "-", ".", "_", "~", "%41", "%7e", "%7E", "%2f", "%2F", "%zz", "%4", "!", "$", "'", "*", "+", ",", ";", "=", "@", ":", "[", "]", " ", "é"];
const hosts = () => pick([
  () => many(() => pick(hostChars), 8),
  () => "api.example.com",
  () => "API.Example.COM",
  () => `[${many(() => pick(["0", "1", "a", "F", ":", ".", "g"]), 6)}]`,
  () => "[::1]",
  () => "",
]) ();
const ports = ["", ":", ":80", ":443", ":080", ":0443", ":8080", ":65535", ":65536", ":123456", ":abc", ":0"];
const pathChars = ["/", "a", "B", "%41", "%2f", "%2F", "%7e", "%zz", "%", ":", "@", "!", "~", ".", "..", "-", " ", "?", "#", "[", "%c3%a9"];
const goodHostChars = ["a", "b", "Z", "0", "-", ".", "_", "~", "%41", "%7e", "%7E", "%2f", "%2F", "%2d", "!", "$", "+", "="];
const goodPathChars = ["/", "a", "B", "%41", "%2f", "%2F", "%7e", "%7E", ":", "@", "!", "~", ".", "..", "-", "%c3%a9", "%20", "_"];
const htuInputs = [];
for (let i = 0; i < N; i++) {
  if (rand() < 0.3) {
    // anything goes
    htuInputs.push(`${pick(schemes)}${pick(["://", "//", ":/", "://"])}${hosts()}${pick(ports)}${many(() => pick(pathChars), 10)}`);
  } else {
    // mostly well formed, to exercise the normalization itself
    const host = rand() < 0.15 ? pick(["[::1]", "[FE80::1]", "[1.2.3.4]"]) : `${many(() => pick(goodHostChars), 6)}x`;
    const tail = rand() < 0.2 ? `?${many(() => pick(["a", "=", "&", "%41", "/", "?"]), 4)}` : "";
    const frag = rand() < 0.2 ? `#${many(() => pick(["a", "%2F", "/", "?"]), 3)}` : "";
    htuInputs.push(`${pick(["http", "https", "HTTP", "HttpS"])}://${host}${pick(["", "", ":80", ":443", ":080", ":8080", ":65535", ":0"])}/${many(() => pick(goodPathChars), 8)}${tail}${frag}`);
  }
}

// ---- JCS -------------------------------------------------------------------
const numberTexts = [
  "0", "-0", "1", "-1", "0.1", "1.5", "42700", "1e21", "1e20", "123456789012345678901", "1e-7", "1e-6",
  "0.000001", "0.0000001", "5e-324", "2.4703282292062327e-324", "2.4703282292062328e-324", "1e-400",
  "2.2250738585072011e-308", "2.2250738585072014e-308", "1.7976931348623157e308", "1.7976931348623159e308",
  "9007199254740991", "9007199254740993", "0.30000000000000004", "0.1000000000000000055511151231257827",
  "100", "1E2", "1.0", "1.50", "-123.456e-7", "4.35", "0.5e-6", "123e18", "123e19",
];
const randomNumberText = () => pick([
  () => pick(numberTexts),
  () => String(Math.floor(rand() * 1e6)),
  () => String((rand() - 0.5) * 10 ** Math.floor(rand() * 40 - 20)),
  () => String(rand() * 10 ** Math.floor(rand() * 600 - 300)),
  () => `${Math.floor(rand() * 1e9)}e${Math.floor(rand() * 60 - 30)}`,
  () => `0.${many(() => String(Math.floor(rand() * 10)), 25)}1`,
])();
const strChars = ["a", "\"", "\\", "\n", "\t", "\b", "\f", "\r", "\u0001", "\u001f", "\u007f", "é", " ", "€", "", "😀", "𝄞", "/", " "];
const randomString = () => many(() => pick(strChars), 6);
function randomValueText(depth) {
  const r = rand();
  if (depth > 3 || r < 0.4) {
    return pick([() => randomNumberText(), () => JSON.stringify(randomString()), () => "true", () => "false", () => "null"])();
  }
  if (r < 0.7) return `[${Array.from({ length: Math.floor(rand() * 4) }, () => randomValueText(depth + 1)).join(",")}]`;
  const keys = new Set();
  const n = Math.floor(rand() * 5);
  for (let i = 0; i < n; i++) keys.add(randomString());
  return `{${[...keys].map((k) => `${JSON.stringify(k)}:${randomValueText(depth + 1)}`).join(",")}}`;
}
const jcsInputs = [];
for (let i = 0; i < N; i++) jcsInputs.push(randomValueText(0));
for (const t of numberTexts) jcsInputs.push(t, `[${t}]`, `{"x":${t}}`);

// ---- run ---------------------------------------------------------------------
let failures = 0;
const show = (msg) => { if (failures++ < 20) console.log(`DISAGREE ${msg}`); };

const leanHtu = runLines("--htu", htuInputs.map((s) => JSON.stringify(s)));
let htuCanonical = 0;
htuInputs.forEach((s, i) => {
  const e = normalizeHtu(s);
  if (e !== null) htuCanonical++;
  if (e !== leanHtu[i]) show(`htu ${JSON.stringify(s)}: lean=${JSON.stringify(leanHtu[i])} engine=${JSON.stringify(e)}`);
});

const leanJcs = runLines("--jcs", jcsInputs);
let jcsOk = 0;
jcsInputs.forEach((t, i) => {
  let e;
  try { e = canonicalize(JSON.parse(t)); jcsOk++; } catch { e = null; }
  if (e !== leanJcs[i]) show(`jcs ${t}: lean=${JSON.stringify(leanJcs[i])} engine=${JSON.stringify(e)}`);
});

// Properties of the model's own functions (tested here, not proven): the
// canonical form is a fixed point, and JCS output re-canonicalizes to itself.
const htuOut = leanHtu.filter((x) => x !== null);
const again = runLines("--htu", htuOut.map((s) => JSON.stringify(s)));
htuOut.forEach((s, i) => { if (again[i] !== s) show(`htu not idempotent: ${s} -> ${again[i]}`); });
const jcsOut = leanJcs.filter((x) => x !== null);
const jcsAgain = runLines("--jcs", jcsOut);
jcsOut.forEach((t, i) => { if (jcsAgain[i] !== t) show(`jcs not idempotent: ${t} -> ${jcsAgain[i]}`); });
console.log(`properties: normalizeHtu idempotent on ${htuOut.length} outputs, jcs idempotent on ${jcsOut.length} outputs`);

// Erratum 7: inputs whose host carries '%' (found the way the engine finds it).
const hostOf = (u) => {
  const m = /^[A-Za-z][A-Za-z0-9+.-]*:\/\/([^/?#]*)/.exec(u);
  if (!m) return null;
  const a = m[1];
  return a.startsWith("[") ? a.slice(0, a.indexOf("]") + 1) : a.split(":")[0];
};
const percentHosts = htuInputs.filter((u) => (hostOf(u) ?? "").includes("%"));
const percentAccepted = percentHosts.filter((u, i) => leanHtu[htuInputs.indexOf(u)] !== null).length;
console.log(`erratum 7: ${percentHosts.length} generated URIs have '%' in the host; the model accepts ${percentAccepted} of them`);
console.log(`htu: ${htuInputs.length} inputs (${htuCanonical} valid URIs); jcs: ${jcsInputs.length} JSON values (${jcsOk} canonicalizable)`);
console.log(`${htuInputs.length + jcsInputs.length - failures} of ${htuInputs.length + jcsInputs.length} agree with @delegus/core; ${failures} disagreement(s)`);
process.exitCode = failures === 0 ? 0 : 1;
