# Delegus Check decision rules in Lean 4

By Inam Haq

Delegus Check by Delegus answers one question for a business: is this AI
agent really allowed to do this, right now, for this company? The answer
comes from a fixed list of 24 checks, run in a fixed order, written down in
the Delegus Check v0.2 specification. This repository writes those rules as
a precise model in Lean 4, a tool that checks mathematical proofs by
machine, and proves properties of them that hold for every possible input,
not only the cases we happened to test.

Phases 0 to 6 of the plan are done, with errata 5, 6 and 7 applied. Phase 0 proved the order of the checks, the yes-or-no answer and the reason given for a no. Phase 1 writes every one of
the 24 checks as a real rule, field by field, and proves what the
specification promises about the whole decision. Phase 2 ties the model to
the real engine: the published conformance runner runs the model as an
implementation, and thousands of altered cases go through both. Phase 3
proves that an old decision re-checks the same, years later. Phase 4 (the
parts that do not depend on the replay window) proves where the service
reads and writes its stores during a decision. Phase 5 proves that a
cancelled Grant stays cancelled: once a revocation has been confirmed,
every later check of that Grant, on any server, is a no, and that a
Proof is accepted at most once. Phase 6 writes two of
the building blocks the model used to take on trust, the address
clean-up for the Proof's target URL and the canonical form of the Action
before it is fingerprinted, in Lean as well, and checks them against the
engine on tens of thousands of inputs.

## What is proven

Lean has checked each of these for every possible request, every possible
state of the service, and every possible answer from the cryptography:

1. **The order is the specification's order.** The 24 checks run in exactly
   the §5.4 order. The revocation check (P6) comes before the replay check
   (T5), and every check from P1 to P14 comes before T5, as §7 requires.
2. **There is no path to yes except every check passing.** The answer is
   ALLOW if and only if all 24 checks are true.
3. **The reason given is the first check that failed**, and every no comes
   with a reason. A check is skipped only when something before it failed.
   The reserved reason `ISSUER_NOT_TRUSTED` is never given.
4. **The step-by-step evaluator is the table.** The model's evaluator is
   written the way the engine runs, stage by stage. It is proven equal to
   the plain table "each check runs only if the checks it depends on
   passed".
5. **Anything missing, unknown or unavailable is refused.** If the issuer
   registry, the revocation state or the replay store cannot be read, the
   answer is no. So it is for a Grant or a Proof that does not decode, a
   signature scheme other than EdDSA, a Grant with no revocation entry, a
   Grant that claims a parent Grant, an Action with an unknown or missing
   field, and a permission with a condition this version cannot evaluate.
6. **The open part of the answer can be reproduced by anyone.** With the
   same request, clock, documents and keys, the 20 protocol checks come out
   the same, whatever the service's own trust answers were.
7. **A yes means what it should.** On ALLOW: the Grant is inside its
   validity window, which is at most 90 days; some permission in the Grant
   names the action, satisfies every condition and matches the resource;
   every number in the Action is a whole number; the Proof's `jti` has the
   required format; the Proof's target URL is already in canonical form,
   with no escape in its host (erratum 7); and the receipt never names a Principal or Agent unless
   the Grant's signature checked out.
8. **An old decision re-checks the same.** Anyone holding a receipt and the
   documents it names by fingerprint can re-run the open part of the
   decision at the time recorded in the receipt and get the same 20 protocol
   checks, whatever their own clock says (erratum 2). A v0.2 receipt does
   not record the relying party's Proof window, so for v0.2 the person
   re-checking must also be given that window; with it, the result is
   exact. With the window signed in the receipt, as v0.3 erratum 1 does it,
   the same v0.2 rules re-check with no outside window at all. With today's
   clock instead of the recorded one, every yes would turn into "expired"
   once the Grant ran out; that is proven too.
9. **The service touches its stores only where the specification says.**
   A decision reads the issuer registry once, then the revocation state
   once, then writes the one-time-use record once, in that order and
   nothing else. The revocation state is read only after the Grant's
   signature checked out. The one-time-use record is written only when the
   first fourteen checks all passed, so a cancelled, forged or expired
   request never uses up a Proof. A request that is both cancelled and
   replayed is refused as cancelled (erratum 1).
10. **A Proof is accepted at most once** (§5.3 T5, erratum 5). However many
    times the same Proof is presented to a service, through one replay
    store, at most one of those checks says yes. A second use is refused
    either because the first use's record is still there, or because the
    store's clock is too far ahead of the verifier's and the store refuses
    to record anything (fail closed). This assumes the store behaves as one
    ordered ledger and that the second use's Proof window is no larger
    than the first's.
11. **"Revoked" means revoked** (erratum 6). The reason `AUTHORITY_REVOKED`
    is given only for a status list that checks out, is valid at the time
    of the decision and has the Grant's entry set. A status list that is
    missing, unreadable, unsigned, out of date or otherwise unusable gives
    `SERVICE_UNAVAILABLE`: still a no, with the true reason.
12. **A cancelled Grant stays cancelled** (§7). Once Delegus has confirmed a
    revocation, every verification of that Grant that starts afterwards, on
    any server, with any cache, is refused; if nothing else was wrong, the
    reason given is "revoked", even when the same Proof is also being
    replayed. Revoking twice changes nothing, and nothing un-revokes. This
    assumes the stores behave as one ordered ledger (the model is one
    sequence of operations) and that Delegus's status-list signer publishes
    correct, current lists.
13. **The protections the specification lists (§13.1) hold in the model.**
   A Proof sent to a different service, an expired or not-yet-valid Grant, a
   cancelled Grant, a compromised key, an unknown or unverified issuer, a
   status list not signed by Delegus, and a service the Grant excludes are
   all refused. If signatures cannot be forged and fingerprints (hashes) do
   not collide, a yes also means the Principal signed the Grant, the Agent
   signed the Proof, and the action is the one the Agent signed.

The proofs use no unproven steps (no `sorry`) and add no assumptions of
their own (no `axiom`). Each theorem rests only on Lean's standard
foundations; the full audit is under [Axiom audit](#axiom-audit).

## What is not proven

- **Cryptography and decoding.** Signatures, fingerprints (hashes), key
  checks and decoding (of the signed artifacts, keys, timestamps and the
  compressed status lists) are inputs to the model, not part of it. The
  target-URL clean-up (`htu`), the canonical JSON of the Action (JCS) and
  the `jti` rule are written in Lean. Where a theorem needs
  "signatures cannot be forged" or "hashes do not collide", it says so as an
  explicit assumption.
- **The live databases.** The revocation proof assumes the stores behave
  like one ordered ledger and that the status-list signer is correct; it
  does not prove that the hosted Redis and Postgres behave that way, and a
  verification already in flight when a revocation completes is not
  covered (the specification does not claim it is).
- **The replay store and its clock.** The one-time-use proof assumes the
  replay store behaves like one ordered ledger and keeps every record until
  its stated expiry. It does not prove that the hosted Redis does, or that
  its clock check runs atomically with the write, as erratum 5 requires.
- **Delegus Check v0.3.** The model is of v0.2. v0.3's added checks (P21,
  D1–D7 and T7) are not modelled, and the v0.3 conformance cases are not
  run through the model. The one v0.3 rule it does cover is how the Proof
  window is recorded in a v0.3 receipt (v0.3 erratum 1): that encoding is
  proven, used in a re-verification theorem over the v0.2 rules, and checked
  against the receipts of all 53 v0.3 cases.
- **That the real engine equals the model.** The engine is TypeScript. The
  two are tied together by running the 52 published test cases, and over
  nine thousand altered versions of them, through both and failing if they
  differ in any way. That is strong testing, not a proof that the code
  equals the model.

## The 52 published test cases

The 52 conformance cases of `@delegus/conformance` 0.7.0 (vector-set hash
`sha256:e4ed80177c231a7b36e37d0690879a11715c3f11ce647a35d0e9daf33e023ce7`:
ALLOW cases, one DENY case for every reason code, cases that pin
particular readings, and the cases errata 5, 6 and 7 added, including
repeated uses of one Proof through one replay store) run through both the model and the reference engine. The model
computes every check itself, from the case's inputs and a small set of
cryptographic and decoding facts. On every case the two agree:

```
52 of 52 cases match on decision, reason, both layer results, all 24 checks, request_hash and principal; 0 mismatch(es)
```

The same 52 cases run inside `lake test`, against each case's expected
result:

```
52 of 52 cases match on decision, reason, both layers and all 24 checks; 0 failure(s)
```

The published conformance runner, with the model plugged in as the
implementation under test:

```
PASS: 52/52 vectors (0 receipts byte-identical), 3 sets passed, 0 skipped, 52/52 committed receipts re-verify offline
```

(The model signs no receipts, so none are compared. The three sets are
the `htu`, JCS and `jti` sets, run on the model's own rules; `lake test`
runs them too: `sets: 55 of 55 htu, JCS and jti checks pass on the model's
own rules`.)

## Altered cases

Fifty-two cases are fifty-two points. The mutation differential changes each case
in about a hundred small ways (the clock, the Proof window, the relying
party, every Action field, the service state, the trusted keys, tampered
bytes, and Proofs re-signed with the cases' published test keys so a
changed Action or time reaches the later checks, and earlier uses of the
same Proof at the window's edges with the store's clock from far behind
to 5 seconds ahead) and runs every version
through both the model and the engine. There is no expected answer; the
two must simply agree:

```
9546 of 9546 mutants agree on decision, reason, both layer results, all 24 checks, request_hash, principal and the operation trace; 0 disagreement(s)
```

The operation trace is the list of service operations each side performed
(issuer read, revocation read, replay write: which ones, in which order,
with which arguments). The engine's comes from its in-memory service's call
log; the model's from a recording run of its effectful evaluator.

The mutants cover every reason code and both answers.

The model's own `htu` clean-up and JCS are also compared with the engine's
on generated inputs (a fixed-seed generator: URIs with every kind of case,
escape, port, query and fragment; JSON values with doubles at every scale,
subnormals, overflow, long decimals, control characters, astral-plane
characters and keys that sort differently by UTF-16):

```
40105 of 40105 agree with @delegus/core; 0 disagreement(s)
```

That run covers 20,000 URIs (6,955 valid; 7,370 of the others have a `%`
in the host, which erratum 7 refuses, and the model and the engine refuse
every one of them) and 20,105 JSON values. It also
checks, without proving it, that both functions are idempotent on their own
output.

## How to re-run it

You need [elan](https://github.com/leanprover/elan) (the Lean version
manager) and, for the engine comparison, Node.js 22 or later.

```sh
git clone https://github.com/delegusai/delegus-check-lean.git
cd delegus-check-lean
lake build                      # the model, the proofs and the case runner
lake test                       # the 52 cases through the model, against each case's expected result
./scripts/check-axioms.sh       # what every theorem rests on
npm ci --ignore-scripts         # the lowering's primitives: @delegus/core, via @delegus/conformance
node scripts/compare.mjs        # model and engine, case by case
npx --no-install delegus-conformance --impl ./bridge/lean-impl.mjs   # the published runner, with the model plugged in
node scripts/differential.mjs   # model and engine on about 9,500 altered cases
node scripts/primitives-differential.mjs   # the model's htu and JCS against the engine's
```

The cases are those of `@delegus/conformance` 0.7.0 (0.8.0 leaves its
v0.2 set unchanged and adds two v0.3 cases). Until those releases are on
npm (the pinned npm release is 0.4.0, with 40 cases), run the engine
commands against a source checkout of the engine with
`scripts/engine-hook.mjs`:

```sh
export DELEGUS_ENGINE_DIR=/path/to/delegus     # a checkout with packages/core and packages/conformance
node --import ./scripts/engine-hook.mjs scripts/compare.mjs
node --import ./scripts/engine-hook.mjs "$DELEGUS_ENGINE_DIR/packages/conformance/src/cli.ts" --impl ./bridge/lean-impl.mjs
node --import ./scripts/engine-hook.mjs scripts/differential.mjs
node --import ./scripts/engine-hook.mjs scripts/primitives-differential.mjs
node --import ./scripts/engine-hook.mjs scripts/window-field-check.mjs   # the v0.3 receipts' proof_window_ms
```

The results above were produced that way, against the engine at the
commit that applies errata 5, 6 and 7 and v0.3 erratum 1.

`lake build` fails if any proof is wrong. Every other command exits
non-zero on any mismatch. `compare.mjs` also fails
if `vectors/lowered/` is not exactly what `node scripts/lower.mjs` produces.

To print the model's answer for each case, one JSON object per line:

```sh
.lake/build/bin/delegus-check-model vectors/cases vectors/lowered
```

---

## Technical detail

### Layout

| Path | Contents |
|---|---|
| `DelegusCheckSpec/Basic.lean` | `Check` (24), `order` (§5.4), the two layers, `Reason` (21 §5.2 codes, 5 §5.3 codes, reserved `ISSUER_NOT_TRUSTED`), `codes`, `Outcome`, `Checks`, `Decision` |
| `DelegusCheckSpec/Kernel.lean` | Phase 0: `firstFail`, `decisionOf`, `kernel`, `Prereq`, `enginePrereq`, `Backward`, `Respects`, `WellCoded` |
| `DelegusCheckSpec/Theorems.lean` | Phase 0 theorems |
| `DelegusCheckSpec/Inputs.lean` | Phase 1 inputs: `Request`, `Clock`, `IssuerLookup`, `StatusLookup`, `Snapshots`, `TrustConfig`, `ReplayAnswer`, and the primitives `Prims` |
| `DelegusCheckSpec/Syntax.lean` | `did:web`, DID URLs, ULID and Grant ids, `jti`, HTTP methods, currencies, `sha256:` references, resource globs (§3.3), all in Lean |
| `DelegusCheckSpec/Readings.lean` | Every reading where the specification is silent, in one place; the erratum 5 replay operation (`replayQuery`) and the erratum 6 P6 rule |
| `DelegusCheckSpec/Replay.lean` | Erratum 5: the replay store, verifications against it, and the at-most-one-ALLOW theorem |
| `scripts/engine-hook.mjs` | Runs the scripts against a source checkout of the engine |
| `scripts/window-field-check.mjs` | v0.3 erratum 1: the model's encoding of the Proof window against every v0.3 receipt |
| `DelegusCheckSpec/Grant.lean` | P1 (`parseGrant`, §3, field by field) and P8 (`parseProof`, §4) |
| `DelegusCheckSpec/Rules.lean` | P2 (`findKey`), P6 (`statusOk`), P7, P15 (`validateAction`), P16–P20 (`authorize`) |
| `DelegusCheckSpec/Evaluate.lean` | `base` (each check's rule), `table` (declarative), `staged` (engine-shaped), `evaluate`, attribution and `request_hash` |
| `DelegusCheckSpec/Staged.lean` | `staged_eq_table` |
| `DelegusCheckSpec/Facts.lean` | What a passing parser guarantees |
| `DelegusCheckSpec/Phase1.lean`, `Phase1Rows.lean` | Phase 1 theorems |
| `DelegusCheckSpec/Effects.lean` | Phase 4: `Op`, `Seams`, the effectful evaluator `evaluateM`, the recording run `traceOf`, and the operation-order theorems |
| `DelegusCheckSpec/Revocation.lean` | Phase 5: the revocation store (`status_ver`, revoked entries), node caches, the status read, histories, and the §7 theorems |
| `DelegusCheckSpec/Historical.lean` | Phase 3: `Receipt`, `receiptOf`, `Artifacts`, `reverify`, and the historical-clock theorems |
| `scripts/readme-axioms.py` | Refreshes the axiom audit below from `check-axioms.sh` |
| `DelegusCheckVectors/Case.lean` | Running the model on a case (not used by any proof) |
| `DelegusCheckModel.lean`, `ModelTest.lean` | `delegus-check-model`, and the `lake test` driver |
| `scripts/lowering.mjs`, `scripts/lower.mjs` | The lowering: the primitive facts for a case, and the command that writes `vectors/lowered/` |
| `bridge/lean-impl.mjs` | The model as an `Implementation` for the `@delegus/conformance` runner |
| `scripts/differential.mjs` | The mutation differential |
| `scripts/primitives-differential.mjs` | The model's `htu` and JCS against the engine's, on generated inputs |
| `DelegusCheckSpec/Htu.lean`, `DelegusCheckSpec/Jcs.lean` | Phase 6: the §4.3 `htu` canonical form and RFC 8785 JCS, in Lean |
| `vectors/sets/` | The `htu`, JCS and `jti` sets, byte for byte from `@delegus/conformance` 0.7.0 |
| `.github/workflows/ci.yml` | CI on push and nightly against the latest `@delegus/conformance`; off until the repository variable `CI_ENABLED` is `true` |
| `scripts/compare.mjs` | Model against the reference engine, live, on all 52 cases |
| `scripts/check-axioms.sh` | `#print axioms` for every theorem, failing on anything but the standard three |
| `vectors/cases/` | The 52 cases, byte for byte from `@delegus/conformance` 0.7.0 |
| `vectors/lowered/` | Their primitive facts, generated by `scripts/lower.mjs` |

No Mathlib, no other dependency: the model uses only Lean's core library,
including `Lean.Json` from Lean's own source tree. No `native_decide`.

### Toolchain

`lean-toolchain` pins `leanprover/lean4:v4.36.0`, the release marked Latest
on GitHub (published 16 November 2026). Upgrades are deliberate commits.

### The model

`evaluate π req s tc clk ρ` is pure and total. Its inputs are exactly the
ones §0 constraint 2 and §5.2 name:

- `req : Request`: the Grant and Proof as received, the Action as
  submitted, the RP DID, the Proof window;
- `clk : Clock`: `now`, read by every time-dependent check (P4, P5, P6, P13);
- `s : Snapshots`: the issuer registry's answer per Principal (with its DID
  document snapshot) and the status-list credential per URL;
- `tc : TrustConfig`: the Delegus DID and its status-list keys;
- `ρ`: the replay store's answer to the one operation T5 performs.

Cryptography and decoding are the parameter `π : Prims`: strict JWS
decoding, strict JSON parsing, `did:key` and multibase key decoding, key
safety (erratum 3), Ed25519 verification, SHA-256, RFC 3339 parsing, and
status-list decoding. Every theorem holds for every `π`. The `htu`
canonical form (`normalizeHtu`), RFC 8785 JCS (`jcs`) and the `jti` rule
(`isJti`) are computed by the model.

`jcs` works on exact integers: a JSON number's decimal value is rounded to
the nearest double (ties to even, with subnormals and overflow), and the
shortest decimal that rounds back is printed in ECMAScript's
`Number::toString` format, with no floating point anywhere.

Each check's own rule is `base e k`. `table` runs it only when every
prerequisite is `true` (`enginePrereq`); `staged` is written as the engine
runs. `staged_eq_table` proves them equal.

### Theorems

All in namespace `DelegusCheck`. Main Phase 1 statements (`r` is
`evaluate π req s tc clk ρ`):

| Theorem | Statement |
|---|---|
| `staged_eq_table` | `staged e = table (base e)` |
| `staged_get` | check `k` is `base e k` when all of `enginePrereq k` are `true`, `skipped` otherwise |
| `evaluate_respects`, `evaluate_wellCoded` | the evaluator's outcomes follow the table, and each `false` carries one of its check's codes; so every Phase 0 theorem applies |
| `evaluate_reason_none_iff_allow` | `r.result.reason = none ↔ r.result.decision = .allow` |
| `evaluate_skipped_has_earlier_fail` | a skipped check has a `false` check earlier in §5.4 order |
| `evaluate_reason_never_reserved` | `r.result.reason ≠ some .ISSUER_NOT_TRUSTED` |
| `issuer_unavailable_denies` | `(∀ d, s.issuer d = .unavailable) → deny` |
| `status_unavailable_denies` | `(∀ u, s.status u = .unavailable) → deny` |
| `replay_unavailable_denies` | `(∀ q, ρ q = .unavailable) → deny` |
| `no_status_entry_denies` | a Grant payload without `credentialStatus` → deny |
| `grant_non_eddsa_denies`, `proof_non_eddsa_denies` | header `alg` not `EdDSA` → deny |
| `grant_undecodable_denies`, `proof_undecodable_denies` | `π.decodeJws` gives `none` → deny |
| `parent_grant_denies_any` | `parentGrant` present → deny |
| `parent_grant_denies` | `parentGrant` present, header well formed, within 8 KB → `reason = UNSUPPORTED_FEATURE` |
| `unknown_constraint_denies` | a candidate Capability with a key outside `knownConstraintKeys` → deny |
| `unknown_action_field_denies` | Action members not exactly its type's fields → deny |
| `deterministic` | `rfl`; the content is the signature of `evaluate` |
| `protocol_local` | the 20 protocol checks depend on the service state only through the registration answer and DID document for the Grant's Principal and, once P3 passed, the status snapshot for its URL |
| `protocol_reproducible` | same request, clock, status snapshot, trust configuration and per-Principal registration and DID document → the same 20 protocol checks, for any T2, T3 and replay answers |
| `no_unauthenticated_attribution` | P3 not `true` → `r.attribution = none` (§6.4) |
| `request_hash_eq_action_hash` | P14 `true` → `r.requestHash = some p.actionHash` (§6.3) |
| `grant_window` | ALLOW → `validFrom ≤ now < validUntil` and `validUntil − validFrom ≤ 90 days` |
| `authorization_sound` | ALLOW → a Capability with the action's type, only known keys, every constraint satisfied, the resource matched, and it is the receipt `authority` |
| `integers_only` | ALLOW → every number in the Action is an integer |
| `key_rotation` | T3 fails exactly for a compromised `kid`; a retired key passes (§11) |
| `isJti_iff`, `p8_jti` | the `jti` format, and P8 `true` → the Proof's `jti` has it |
| `isCanonicalHtu_iff`, `p8_htu` | canonical means a fixed point of the model's `normalizeHtu`, and P8 `true` → the Proof's `htu` is one |
| `normalizeHtu_host_no_percent`, `p8_htu_host` | erratum 7: an `htu` with a canonical form has no `%` in its host, so P8 `true` → the Proof's `htu` host has none |
| `tm05_…` to `tm13_…` | the §13.1 rows TM-05, TM-07, TM-08, TM-09, TM-11, TM-12, TM-13 as DENY statements |
| `tm01_grant_signed`, `tm03_proof_signed_by_agent`, `tm06_action_bound` | TM-01/02, TM-03 and TM-06 under the explicit hypotheses that a verifying signature under a safe key means its holder signed, and that SHA-256 is injective and JCS canonical |

Phase 3 statements (offline re-verification, §6.4 and erratum 2):

| Theorem | Statement |
|---|---|
| `reverify_ignores_wall` | `reverify π rc art w₁ = reverify π rc art w₂`: the verifier's clock is not used |
| `reverify_clock` | re-verification evaluates at the receipt's `evaluated_at` |
| `reverify_reproduces` | v0.2: for the receipt of any evaluation, artifacts matching its pinned hashes, the same Action, the RP's Proof window (supplied by the caller, since a v0.2 receipt doesn't record it) and the status-list keys: the 20 protocol checks are reproduced exactly; hypothesis: SHA-256 injective |
| `windowOf_encode`, `encode_windowOf` | v0.3 erratum 1's `proof_window_ms`: every window from 1 to 300 s has a well-formed encoding (absent for 60 s) that decodes back to it, and each window has exactly one encoding |
| `reverify_reproduces_signed_window` | the v0.2 rules, with the window recorded in the receipt that way: re-verification reproduces the 20 protocol checks with no outside window, whatever window the verifier is handed |
| `wall_clock_breaks` | an ALLOW at time `t`, re-run at any `w ≥ validUntil`, gives `GRANT_EXPIRED` |
| `evaluated_at_bound` | under explicit signature, signing-policy and encoding hypotheses, a receipt that verifies is one Delegus issued, with its `evaluated_at` |

Phase 4 statements (the hot path's operations, §5.5, §7, erratum 1):

| Theorem | Statement |
|---|---|
| `run_eq`, `evaluateM_result`, `trace_eq` | the effectful evaluator, answered from the snapshots, gives exactly `evaluate`'s result, and its recorded trace is `opsOf` |
| `trace_shape` | the trace is `[]`, `[issuer]`, `[issuer, status]` or `[issuer, status, replay]`: only the three operations, each at most once, in that order |
| `issuer_read_iff_p1`, `status_read_iff_p3` | the registry is read exactly when P1 passed; the revocation state exactly when P3 passed |
| `replay_write_iff`, `setnx_only_after_p14` | the replay write happens exactly when P1–P14 all passed |
| `revoked_never_burns_jti` | P6 not `true` → no replay write |
| `status_read_before_replay_write` | the revocation read precedes the replay write |
| `revoked_beats_replayed` | everything before P6 passed and P6 is `AUTHORITY_REVOKED` → that is the reason, whatever the replay store says |
| `seams_congr` | two service states that answer the operations actually performed the same way give the same result and trace |

Phase 5 statements (`/revoke` and its guarantee, §7 with erratum 1):

| Theorem | Statement |
|---|---|
| `revoke_idempotent` | `revoke g (revoke g σ) = revoke g σ` |
| `revoke_revokes`, `revoke_permanent` | after `/revoke` the entry is revoked, and no later operation un-revokes it |
| `storeInv_revoke`, `cacheInv_revoke`, `cacheInv_read`, `worldInv_run` | the store and every node cache stay consistent through any history |
| `statusRead_fresh` | the status read returns a credential issued at a version at least the current `status_ver`, showing every revocation already made |
| `verify_denies_revoked` | a verification of a Grant whose entry is revoked in the store it reads is DENY |
| `verify_reason_revoked` | …and if every check before P6 passed, the reason is `AUTHORITY_REVOKED`, whatever the replay store says |
| `revoke_then_deny` | in any history from the empty store, once `/revoke` returned, every later verification of that Grant on any node is DENY |
| `revoke_then_reason` | the §15 step 5 test: revoke, then the same action with a fresh Proof whose other checks pass → `AUTHORITY_REVOKED` |

The hypotheses are explicit: the history is one sequence of atomic
operations (linearizability, by the model's shape), and `FaithfulSigner`:
the credential Delegus's signer issues for a list is usable at the
verification's clock and keys and shows its bits correctly.

Erratum 5 statements (one-time use, §5.3 T5):

| Theorem | Statement |
|---|---|
| `replay_denied` | the store holds the Proof's key up to `E = iat·1000 + w1 + 5000`; a later verification of a Proof with the same `(rp_did, jti)` and `iat` under a window `w2 ≤ w1` is DENY: if its write reaches the store at most 4 000 ms (store clock) after its `now`, the key is present (`PROOF_REPLAYED`), otherwise the store refuses (`SERVICE_UNAVAILABLE`) |
| `at_most_one_allow` | in any history through one replay store, an earlier and a later verification of Proofs with the same relying party, `jti` and `iat`, the later window no larger, are not both ALLOW |
| `allow_writes` | an ALLOW leaves its key in the store until `iat·1000 + w + 5000` |
| `t5_pass_write`, `writeOf_of_mem`, `present_storeAfter` | T5 passing means the write was made and answered OK; records persist through any later operations |

The hypotheses, in plain words: the history is one sequence of atomic
store operations, and a record is kept until its expiry (the model's
shape); the two Proofs have the same relying party, `jti` and `iat` (a
`jti` names one Proof); the later Proof's window is no larger than the
earlier's. The 1 000 ms write timeout and the store's 4 000 ms clock check
are part of the model, not hypotheses: the theorem holds for any delay and
any store clock.

Erratum 6 statements (P6):

| Theorem | Statement |
|---|---|
| `p6_revoked_iff` | P6's rule is `AUTHORITY_REVOKED` exactly when the status store returned a credential that verifies, is valid at `now` and has the Grant's bit set |
| `p6_codes` | P6 fails only with `AUTHORITY_REVOKED` or `SERVICE_UNAVAILABLE` |

Phase 0 statements (the kernel, for any outcomes):

| Theorem | Statement |
|---|---|
| `order_is_spec` | `order` is the §5.4 list |
| `p6_before_t5`, `p14_before_t5`, `p1_to_p14_before_t5` | the §7 ordering constraints |
| `allow_iff_all_pass`, `allow_iff_every_check`, `allow_iff_layers` | ALLOW iff all 24 checks are `true`, iff both layers PASS |
| `reason_first_fail`, `reason_first_fail_idx` | the reason is the first `false` in §5.4 order |
| `skipped_has_earlier_fail`, `reason_none_iff_allow` | for any backward prerequisite table the outcomes respect |
| `reason_never_reserved`, `enginePrereq_backward` | as named |

### Axiom audit

Output of `./scripts/check-axioms.sh` with Lean 4.36.0, every theorem in
`DelegusCheckSpec/`:

```
'DelegusCheck.pureEnv_grant' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.run_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.trace_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.evaluateM_result' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.trace_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.issuer_read_iff_p1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.status_read_iff_p3' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.actionStage_early' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.proofStage_early_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.replay_write_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.setnx_only_after_p14' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.revoked_never_burns_jti' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.status_read_before_replay_write' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.revoked_beats_replayed' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.seams_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.req_eq_some' depends on axioms: [propext]
'DelegusCheck.grantPayload_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.parseGrant_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.grantHeaderOk_alg' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.parseGrant_parent' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.parseGrant_undecodable' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.parseProof_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.statusBit_signed' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.reverify_ignores_wall' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.reverify_clock' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.t1_of_grant' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.reverify_reproduces' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.wall_clock_breaks' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.evaluated_at_bound' depends on axioms: [propext, Quot.sound]
'DelegusCheck.windowOf_encode' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.encode_windowOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.reverify_reproduces_signed_window' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.normalizeHtu_host_no_percent' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.staged_get' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.not_pass_of_base' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.base_of_pass' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.prereq_of_pass' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.evaluate_result' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.deny_of_base' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.base_of_allow' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.ok_pass' depends on axioms: [propext]
'DelegusCheck.ok_ne_skipped' depends on axioms: [propext]
'DelegusCheck.issuer_unavailable_denies' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.status_unavailable_denies' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.replay_unavailable_denies' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.exactKeys_has' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.no_status_entry_denies' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.grant_non_eddsa_denies' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.proof_non_eddsa_denies' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.grant_undecodable_denies' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.proof_undecodable_denies' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.reason_of_p1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.parent_grant_denies' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.authorize_p17_pass' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.parent_grant_denies_any' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.unknown_constraint_denies' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.validateAction_fields' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.unknown_action_field_denies' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.deterministic' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.t1Of_view' depends on axioms: [propext]
'DelegusCheck.p2Of_view' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.p3Of_view' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.gate_congr' depends on axioms: [propext, Quot.sound]
'DelegusCheck.protocol_local' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.protocol_reproducible' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.pass_prereq' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.grant_of_p3' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.proof_of_p8' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.action_of_p15' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.p3_of_p8' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.p8_of_p14' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.p14_of_p15' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.p15_of_p16' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.p16_of_p17' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.p17_of_p18' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.p18_of_p19' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.p19_of_p20' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.authorize_next' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.t1Of_ne_skipped' depends on axioms: [propext]
'DelegusCheck.replayOutcome_ne_skipped' depends on axioms: [propext]
'DelegusCheck.p6Of_ne_skipped' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.base_ne_skipped' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.evaluate_respects' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.ok_fail' depends on axioms: [propext]
'DelegusCheck.parseGrant_error' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.authorize_codes' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.base_codes' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.evaluate_wellCoded' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.evaluate_reason_none_iff_allow' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.evaluate_skipped_has_earlier_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.evaluate_reason_never_reserved' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.no_unauthenticated_attribution' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.request_hash_eq_action_hash' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.grant_window' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.exists_find' depends on axioms: [propext, Quot.sound]
'DelegusCheck.authorize_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.authorization_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.validateAction_values' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.integers_only' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.key_rotation' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.isJti_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.p8_jti' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.isCanonicalHtu_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.parseProof_htu' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.p8_htu' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.p8_htu_host' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.tm05_other_rp_denies' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.tm06_action_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.tm07_outside_window_denies' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.tm08_revoked_denies' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.p6_revoked_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.p6_codes' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.tm09_compromised_denies' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.tm11_unknown_issuer_denies' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.tm11_unverified_issuer_denies' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.tm12_unsigned_status_denies' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.tm13_excluded_rp_denies' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.findKey_safe' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.tm01_grant_signed' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.tm03_proof_signed_by_agent' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.opsOf_replay_query' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.writeOf_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.t5_pass_write' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.present_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.present_after' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.present_storeAfter' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.allow_writes' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.replay_denied' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.at_most_one_allow' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.storeInv_empty' depends on axioms: [propext, Quot.sound]
'DelegusCheck.matchesEntry_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.revoke_idempotent' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.revoke_revokes' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.revoke_permanent' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.revoke_ver_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.storeInv_revoke' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.bitsAt_revoke' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.cacheInv_revoke' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.cacheInv_refreshed' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.cacheInv_read' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.bitsAt_of_revoked' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.statusRead_fresh' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.grant_statusIndex_decimal' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.p3_status_indep' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.verify_denies_revoked' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.verify_reason_revoked' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.worldInv_init' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.cacheInv_verify' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.worldInv_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.worldInv_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.revoked_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.revoked_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.revoke_in_history' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.revoke_then_deny' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.revoke_then_reason' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.gate_nil' does not depend on any axioms
'DelegusCheck.gate_cons' depends on axioms: [propext, Quot.sound]
'DelegusCheck.gate_pass' depends on axioms: [propext, Quot.sound]
'DelegusCheck.gate_skipped' depends on axioms: [propext, Quot.sound]
'DelegusCheck.gate_fail' depends on axioms: [propext, Quot.sound]
'DelegusCheck.gate_of_skipped' does not depend on any axioms
'DelegusCheck.ite_chain' depends on axioms: [propext]
'DelegusCheck.authorize_chain' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.authorize_p16' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.stagedRow_eq_tableRow' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.staged_eq_table' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.evaluate_eq_evalTable' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.order_is_spec' does not depend on any axioms
'DelegusCheck.order_length' does not depend on any axioms
'DelegusCheck.order_nodup' does not depend on any axioms
'DelegusCheck.order_complete' depends on axioms: [propext]
'DelegusCheck.p6_before_t5' does not depend on any axioms
'DelegusCheck.p14_before_t5' does not depend on any axioms
'DelegusCheck.p1_to_p14_before_t5' does not depend on any axioms
'DelegusCheck.layers_partition' depends on axioms: [propext]
'DelegusCheck.Outcome.isPass_iff' depends on axioms: [propext]
'DelegusCheck.Outcome.failReason_eq_none_iff' depends on axioms: [propext]
'DelegusCheck.Outcome.failReason_eq_some_iff' depends on axioms: [propext]
'DelegusCheck.allPass_iff' depends on axioms: [propext, Quot.sound]
'DelegusCheck.allow_iff_all_pass' depends on axioms: [propext, Quot.sound]
'DelegusCheck.allow_iff_every_check' depends on axioms: [propext, Quot.sound]
'DelegusCheck.deny_of_not_pass' depends on axioms: [propext, Quot.sound]
'DelegusCheck.deny_of_fail' depends on axioms: [propext, Quot.sound]
'DelegusCheck.protocolPass_iff' depends on axioms: [propext, Quot.sound]
'DelegusCheck.trustPass_iff' depends on axioms: [propext, Quot.sound]
'DelegusCheck.allow_iff_layers' depends on axioms: [propext, Quot.sound]
'DelegusCheck.reason_first_fail' depends on axioms: [propext, Quot.sound]
'DelegusCheck.reason_first_fail_idx' depends on axioms: [propext, Quot.sound]
'DelegusCheck.reason_eq_firstFailCheck' depends on axioms: [propext]
'DelegusCheck.skipped_has_earlier_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.reason_none_iff_allow' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.reason_mem_codes' depends on axioms: [propext, Quot.sound]
'DelegusCheck.reason_never_reserved' depends on axioms: [propext, Quot.sound]
'DelegusCheck.backwardB_sound' depends on axioms: [propext, Quot.sound]
'DelegusCheck.enginePrereq_backward' depends on axioms: [propext, Quot.sound]
'DelegusCheck.exactB_sound' depends on axioms: [propext, Quot.sound]
'DelegusCheck.wellCodedB_sound' depends on axioms: [propext, Quot.sound]
OK: 197 theorems, standard axioms only
```

`propext`, `Quot.sound` and `Classical.choice` are Lean's three standard
axioms. `sorryAx` appears nowhere.

### How a case is run

`scripts/lower.mjs` computes only primitive facts, using only the primitive
functions of `@delegus/core` 0.3.2 (strict JWS and JSON decoding, base58 and
base64url, Ed25519 verification and key safety, SHA-256, RFC 3339 parsing,
GZIP). It also runs the engine's JCS on the Action, but only to know which
text to fingerprint: the model computes its own JCS, and the fingerprint is
found only if the two texts are identical. It never imports the engine's
evaluator, Grant or Proof parsers or capability rules. The facts are tables
over every value the model could ask about: every string inside the decoded
Grant, Proof, status credential and DID document, every candidate key, every
key and signed-artifact pair. Whatever is not in a table, the model's
primitives answer "no".

`DelegusCheckVectors/Case.lean` reads each case's inputs (Grant, Proof,
Action, RP DID, clock, window, Delegus DID and the service state) and its
lowered facts, and runs `evaluate`. Nothing is read from the case's
expected results except by the test driver, which compares against them.

`scripts/compare.mjs` runs the reference engine live through
`coreImplementation` from `@delegus/conformance` and compares the
decision, the reason, both layer results, all 24 outcomes, `request_hash`
and the attributed Principal. `--engine <module>` points it at another
module exporting `coreImplementation`.

`bridge/lean-impl.mjs` implements the runner's `Implementation`: it lowers
the input it is given, runs the Lean executable and returns the model's
answer, so `npx delegus-conformance --impl ./bridge/lean-impl.mjs` checks
the model with the runner's own comparison.

`scripts/differential.mjs` builds the mutants, runs the engine on each and
the model on all of them in one batch, and compares. It also runs each
mutant through `@delegus/core`'s `evaluate` with the conformance package's
in-memory service and compares that service's call log with the model's
operation trace. Cases with earlier uses run each earlier use through the
same replay store first, on both sides. A mutant the engine rejects as
invalid service input (it throws by design, for example a Proof window
outside 1–300 seconds) is counted and skipped: 45 in the current run.

### CI

`.github/workflows/ci.yml` runs on every push (build, `lake test`, the axiom
audit, `compare.mjs`, the conformance runner with the model, the
differential) and nightly against the latest published
`@delegus/conformance` and `@delegus/core`, so an engine release that
changes behaviour turns it red. It is off while the repository is private:
every job runs only when the repository variable `CI_ENABLED` is `true`.

### Source of the cases

`vectors/cases/` holds the 52 `delegus-base-v1` cases of
[`@delegus/conformance`](https://www.npmjs.com/package/@delegus/conformance)
version 0.7.0 (vector-set hash
`sha256:e4ed80177c231a7b36e37d0690879a11715c3f11ce647a35d0e9daf33e023ce7`),
byte for byte; `scripts/compare.mjs` fails if they differ from the
engine's own set. They use
test keys and non-production identifiers only (`did:web:acme.example`,
`did:web:test.delegus.example`).

### Readings

The only normative source is the Delegus Check v0.2 specification
(`delegus-spec-v0.2-final.md`), frozen, with errata 1 and 2. None of the
points below changes or extends the protocol.

**Decided by the owner.**

- **Erratum 3 is in scope for v0.2** (22 November 2026). An Ed25519 key that
  is non-canonical or of small order is rejected: P1 for the Agent key, P2
  for a DID-document key, P8 for the Proof key. It is part of the protocol
  (`Prims.keyOk`), not a reading.
- **One clock.** Every check in a decision reads the same `now`, P6
  included (the status credential's own validity window). This is the
  specification's reading (§5.4, erratum 2), confirmed by the owner on
  22 November 2026.

**Engine readings, owner-confirmed 22 November 2026** (each isolated in
`DelegusCheckSpec/Readings.lean`):

- **`merchantCategory`** (`knownConstraintKeys`). §3.3 defines it, but the
  Action carries no category (§4.3), so it cannot be evaluated; P17 fails
  with `UNKNOWN_CONSTRAINT`. Hence `authorization_sound` is stated in the
  safe direction only.
- **Which P1 code wins** (`p1Code`). For a Grant that both carries
  `parentGrant` and is malformed, the specification does not say. A
  malformed header is reported first, then `parentGrant`, then the payload
  rules.
- **`jti` format** (`isJti`). §4.2 says "MUST be 22–64 ASCII characters";
  the owner's clarification published with erratum 6 states the base64url
  alphabet with no padding, which is what the engine and the model accept.

**Applied errata found by this model.** Erratum 5 (the replay key could
expire at the last instant P13 accepts), erratum 6 (an unusable status
credential was reported as a revocation) and erratum 7 (an escaped `htu`
host had two canonical forms) all came out of this work. In the model,
erratum 5 is `replayQuery` and the store's clock check in `setNX`;
erratum 6 is `unusableStatusCode`; erratum 7 is the host check in
`normalizeHtu`, with `normalizeHtu_host_no_percent`.

**Found while proving the historical clock (Phase 3).** Offline
re-verification (§6.4) is described as needing the receipt, the Delegus
receipt key and the artifacts named by hash. P13 also needs the RP's Proof
window, which a v0.2 receipt does not record (§6.2) and which the RP can
configure (§4.2). For v0.2 this stands: `reverify_reproduces` takes the
window as an input, as the engine's `reverifyReceipt` does for a v0.2
receipt (`proofWindowSeconds`, default 60). v0.3 erratum 1 fixes it for
v0.3 by signing `proof_window_ms` in the receipt;
`reverify_reproduces_signed_window` shows the fix works for the v0.2
rules, and `scripts/window-field-check.mjs` checks the encoding against
every v0.3 receipt (`53 of 53 v0.3 receipts carry exactly the model's
proof_window_ms encoding (2 carry the field)`).

**Engine readings the specification leaves open**:

1. Which check depends on which (`enginePrereq`); the Phase 0 theorems hold
   for any table in which dependencies come earlier.
2. "Failed" includes skipped: a check is skipped when a prerequisite is not
   true.
3. ALLOW needs all 24 checks true; `evaluate_reason_none_iff_allow` shows
   this agrees with "DENY if any check is false" for the evaluator.
4. `SERVICE_UNAVAILABLE` sits at P6 when revocation state cannot be read
   (§7 names the code, not the check) and at T1 when the issuer registry
   cannot be read (the specification names no code).
5. The replay operation (T5) runs once P1–P14 pass, so a request denied at
   T2 or T3 still consumes its `jti` (plan §1.7 item 6).
6. Integers follow ECMAScript: a JSON number such as `1.0` counts as the
   integer 1. `did:web` syntax is the engine's: lowercase host, optional
   `%3A` port, optional path segments. The default Proof window is 60
   seconds.

### Licence

Apache-2.0 (`LICENSE`, `NOTICE`). The cases in `vectors/cases/` are
Apache-2.0 from Delegus. Doc comments that restate the specification's
check tables carry the attribution it asks for: "Delegus Specification
v0.2, © Delegus (delegus.ai)", CC BY 4.0.
