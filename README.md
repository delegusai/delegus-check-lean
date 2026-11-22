# Delegus Check decision rules in Lean 4

By Inam Haq

Delegus Check by Delegus answers one question for a business: is this AI
agent really allowed to do this, right now, for this company? The answer
comes from a fixed list of 24 checks, run in a fixed order, written down in
the Delegus Check v0.2 specification. This repository writes those rules as
a precise model in Lean 4, a tool that checks mathematical proofs by
machine, and proves properties of them that hold for every possible input,
not only the cases we happened to test.

Two stages are done. Phase 0 proved the order of the checks, the yes-or-no
answer and the reason given for a no. Phase 1 writes every one of the 24
checks as a real rule, field by field, and proves what the specification
promises about the whole decision.

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
   required format; and the receipt never names a Principal or Agent unless
   the Grant's signature checked out.
8. **The protections the specification lists (§13.1) hold in the model.**
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

- **Cryptography.** Signatures, fingerprints (hashes), canonical JSON and
  decoding are inputs to the model, not part of it. Where a theorem needs
  "signatures cannot be forged" or "hashes do not collide", it says so as an
  explicit assumption.
- **The live databases.** Revocation and one-time use depend on how the
  stores behave over many requests. Those proofs are later phases and will
  assume the stores behave like one ordered ledger.
- **One-time use (replay).** The replay check is modelled as the frozen
  specification states it, and an unavailable replay store is proven to give
  a no. The theorem that a Proof is accepted at most once waits for the
  replay erratum the owner has chosen (erratum 4), whose text is being
  drafted.
- **That the real engine equals the model.** The engine is TypeScript. The
  two are tied together by running the same 40 published test cases through
  both and failing if they differ in any way. That is strong testing, not a
  proof that the code equals the model.

## The 40 published test cases

The 40 conformance cases of `@delegus/conformance` 0.4.0 (3 ALLOW cases,
one DENY case for every reason code, and cases that pin particular
readings) run through both the model and the reference engine. The model
computes every check itself, from the case's inputs and a small set of
cryptographic and decoding facts. On every case the two agree:

```
40 of 40 cases match on decision, reason, both layer results, all 24 checks, request_hash and principal; 0 mismatch(es)
```

The same 40 cases run inside `lake test`, against each case's expected
result:

```
40 of 40 cases match on decision, reason, both layers and all 24 checks; 0 failure(s)
```

## How to re-run it

You need [elan](https://github.com/leanprover/elan) (the Lean version
manager) and, for the engine comparison, Node.js 22 or later.

```sh
git clone https://github.com/delegusai/delegus-check-lean.git
cd delegus-check-lean
lake build                      # the model, the proofs and the case runner
lake test                       # the 40 cases through the model, against each case's expected result
./scripts/check-axioms.sh       # what every theorem rests on
npm ci --ignore-scripts         # the reference engine, pinned: @delegus/conformance 0.4.0
node scripts/compare.mjs        # model and engine, case by case
```

`lake build` fails if any proof is wrong. `lake test`, `check-axioms.sh` and
`compare.mjs` each exit non-zero on any mismatch. `compare.mjs` also fails
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
| `DelegusCheckSpec/Readings.lean` | Every reading where the specification is silent, in one place; the replay operation (`replayQuery`), ready for erratum 4 |
| `DelegusCheckSpec/Grant.lean` | P1 (`parseGrant`, §3, field by field) and P8 (`parseProof`, §4) |
| `DelegusCheckSpec/Rules.lean` | P2 (`findKey`), P6 (`statusOk`), P7, P15 (`validateAction`), P16–P20 (`authorize`) |
| `DelegusCheckSpec/Evaluate.lean` | `base` (each check's rule), `table` (declarative), `staged` (engine-shaped), `evaluate`, attribution and `request_hash` |
| `DelegusCheckSpec/Staged.lean` | `staged_eq_table` |
| `DelegusCheckSpec/Facts.lean` | What a passing parser guarantees |
| `DelegusCheckSpec/Phase1.lean`, `Phase1Rows.lean` | Phase 1 theorems |
| `DelegusCheckVectors/Case.lean` | Running the model on a case (not used by any proof) |
| `DelegusCheckModel.lean`, `ModelTest.lean` | `delegus-check-model`, and the `lake test` driver |
| `scripts/lower.mjs` | The lowering: the primitive facts for each case |
| `scripts/compare.mjs` | Model against the reference engine, live, on all 40 cases |
| `scripts/check-axioms.sh` | `#print axioms` for every theorem, failing on anything but the standard three |
| `vectors/cases/` | The 40 cases, byte for byte from `@delegus/conformance` 0.4.0 |
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
safety (erratum 3), Ed25519 verification, SHA-256, RFC 8785 JCS, the `htu`
canonical form, RFC 3339 parsing, and status-list decoding. Every theorem
holds for every `π`.

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
| `protocol_reproducible` | same request, clock, status snapshot, trust configuration and per-Principal registration and DID document → the same 20 protocol checks, for any T2, T3 and replay answers |
| `no_unauthenticated_attribution` | P3 not `true` → `r.attribution = none` (§6.4) |
| `request_hash_eq_action_hash` | P14 `true` → `r.requestHash = some p.actionHash` (§6.3) |
| `grant_window` | ALLOW → `validFrom ≤ now < validUntil` and `validUntil − validFrom ≤ 90 days` |
| `authorization_sound` | ALLOW → a Capability with the action's type, only known keys, every constraint satisfied, the resource matched, and it is the receipt `authority` |
| `integers_only` | ALLOW → every number in the Action is an integer |
| `key_rotation` | T3 fails exactly for a compromised `kid`; a retired key passes (§11) |
| `isJti_iff`, `p8_jti` | the `jti` format, and P8 `true` → the Proof's `jti` has it |
| `tm05_…` to `tm13_…` | the §13.1 rows TM-05, TM-07, TM-08, TM-09, TM-11, TM-12, TM-13 as DENY statements |
| `tm01_grant_signed`, `tm03_proof_signed_by_agent`, `tm06_action_bound` | TM-01/02, TM-03 and TM-06 under the explicit hypotheses that a verifying signature under a safe key means its holder signed, and that SHA-256 is injective and JCS canonical |

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
'DelegusCheck.req_eq_some' depends on axioms: [propext]
'DelegusCheck.grantPayload_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.parseGrant_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.grantHeaderOk_alg' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.parseGrant_parent' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.parseGrant_undecodable' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.parseProof_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.statusOk_signed' depends on axioms: [propext, Classical.choice, Quot.sound]
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
'DelegusCheck.tm05_other_rp_denies' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.tm06_action_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.tm07_outside_window_denies' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.tm08_revoked_denies' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.tm09_compromised_denies' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.tm11_unknown_issuer_denies' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.tm11_unverified_issuer_denies' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.tm12_unsigned_status_denies' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.tm13_excluded_rp_denies' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.findKey_safe' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.tm01_grant_signed' depends on axioms: [propext, Classical.choice, Quot.sound]
'DelegusCheck.tm03_proof_signed_by_agent' depends on axioms: [propext, Classical.choice, Quot.sound]
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
OK: 129 theorems, standard axioms only
```

`propext`, `Quot.sound` and `Classical.choice` are Lean's three standard
axioms. `sorryAx` appears nowhere.

### How a case is run

`scripts/lower.mjs` computes only primitive facts, using only the primitive
functions of `@delegus/core` 0.3.2 (strict JWS and JSON decoding, base58 and
base64url, Ed25519 verification and key safety, SHA-256, JCS, the `htu`
canonical form, RFC 3339 parsing, GZIP). It never imports the engine's
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
`coreImplementation` from `@delegus/conformance` 0.4.0 and compares the
decision, the reason, both layer results, all 24 outcomes, `request_hash`
and the attributed Principal. `--engine <module>` points it at another
module exporting `coreImplementation`. The conformance runner's `--impl`
adapter and CI on push and nightly come with Phase 2; the lowering was
built now so that every Phase 1 step is checked against all 40 cases.

### Source of the cases

`vectors/cases/` holds the 40 `delegus-base-v1` cases of
[`@delegus/conformance`](https://www.npmjs.com/package/@delegus/conformance)
version 0.4.0 (npm integrity
`sha512-jZQUL1oRaD4WQXWpNCTFYVQgcsPHT9SYMyImiUyliUN8J41XgrsEemIGzMbuz7GLiXSRjtdG7R3+BFl8gKkH9A==`),
byte for byte; `scripts/compare.mjs` fails if they ever differ. They use
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

**Engine readings, pending the owner** (each isolated in
`DelegusCheckSpec/Readings.lean`):

- **`merchantCategory`** (`knownConstraintKeys`). §3.3 defines it, but the
  Action carries no category (§4.3), so it cannot be evaluated; P17 fails
  with `UNKNOWN_CONSTRAINT`. Hence `authorization_sound` is stated in the
  safe direction only.
- **Which P1 code wins** (`p1Code`). For a Grant that both carries
  `parentGrant` and is malformed, the specification does not say. The
  engine reports a malformed header first, then `parentGrant`, then the
  payload rules.

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
5. A status credential that is present but unusable (bad signature, wrong
   URL, not yet valid or expired, index outside the list) gives
   `AUTHORITY_REVOKED` at P6, not `SERVICE_UNAVAILABLE`. §5.2 gives P6 only
   `AUTHORITY_REVOKED`; §7 gives `SERVICE_UNAVAILABLE` when current
   revocation state "cannot be established". Which of the two an unusable
   credential is, the specification does not say.
6. `jti` (§4.2) "MUST be 22–64 ASCII characters"; the engine, and so the
   model, accepts only the base64url alphabet, the SHOULD encoding. This is
   narrower than the text.
7. The replay operation (T5) runs once P1–P14 pass, so a request denied at
   T2 or T3 still consumes its `jti` (plan §1.7 item 6). Its key expiry is
   the frozen `PX 2 × window_ms`, isolated in `replayQuery` for erratum 4.
8. Integers follow ECMAScript: a JSON number such as `1.0` counts as the
   integer 1. `did:web` syntax is the engine's: lowercase host, optional
   `%3A` port, optional path segments. The default Proof window is 60
   seconds.

### Licence

Apache-2.0 (`LICENSE`, `NOTICE`). The cases in `vectors/cases/` are
Apache-2.0 from Delegus. Doc comments that restate the specification's
check tables carry the attribution it asks for: "Delegus Specification
v0.2, © Delegus (delegus.ai)", CC BY 4.0.
