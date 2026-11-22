# Delegus decision rules in Lean 4

By Inam Haq

Delegus answers one question for a business: is this AI agent really allowed
to do this, right now, for this company? The answer comes from a fixed list
of 24 checks, run in a fixed order, written down in the Delegus v0.2
specification. This repository writes those rules as a precise model in
Lean 4, a tool that checks mathematical proofs by machine, and proves
properties of them that hold for every possible input, not only the cases
we happened to test.

This is the first stage (Phase 0): the order of the checks, the yes-or-no
answer, and the reason given for a no.

## What is proven

Lean has checked each of these for every possible combination of check
results:

1. **The order is the specification's order.** The model's list of 24 checks
   is, symbol for symbol, the order in §5.4. Each check appears once. The
   revocation check (P6) comes before the replay check (T5), and every check
   from P1 to P14 comes before T5, as §7 requires.
2. **There is no path to yes except every check passing.** The answer is
   ALLOW if and only if all 24 checks are true. A false check, or a check
   that was skipped, always gives DENY.
3. **The reason given is the first check that failed.** The reason is
   exactly the reason carried by the first false check in §5.4 order, and no
   earlier check is false.
4. **A skipped check always has an earlier failure behind it.** If a check
   was skipped because something it depends on did not pass, there is a false
   check earlier in the order. This holds for any table of dependencies in
   which every dependency comes earlier, so it does not rest on one reading
   of which check depends on which.
5. **Every no comes with a reason, and only a yes has none.** Given point 4,
   the reason is empty exactly when the answer is ALLOW.
6. **The two layer results mean what §5.4 says.** The protocol layer passes
   if and only if P1 to P20 are all true, the trust layer passes if and only
   if T1, T2, T3 and T5 are all true, and ALLOW holds if and only if both
   layers pass.
7. **The reserved reason is never given.** `ISSUER_NOT_TRUSTED` is reserved
   in §5.3; as long as each false check carries one of its own codes, it can
   never be the reason.

The proofs use no unproven steps (no `sorry`) and add no assumptions of
their own (no `axiom`). Each theorem rests only on Lean's standard
foundations; the full audit is under [Axiom audit](#axiom-audit).

## What is not proven

- **The 24 checks themselves.** At this stage the model takes each check's
  result (true, false or skipped) as given. It proves what follows from
  those results. Whether a signature verifies, a grant has expired or an
  amount is too high is computed by the model only from Phase 1 on.
- **Cryptography.** Nothing here proves that signatures cannot be forged or
  that fingerprints (hashes) do not collide. Later phases state these as
  explicit assumptions on the theorems that need them.
- **The live databases.** Revocation and one-time use depend on how the
  stores behave. Those proofs come in later phases and will assume the
  stores behave like one ordered ledger.
- **That the real engine equals the model.** The engine is TypeScript. The
  two are tied together by running the same 40 published test cases through
  both and failing if they differ in any way. That is strong testing, not a
  proof that the code equals the model.

## The 40 published test cases

The 40 conformance cases of `@delegus/conformance` 0.4.0 (3 ALLOW cases,
one DENY case for every reason code, and cases that pin particular
readings) run through both the model and the reference engine. On every
case the two agree on the decision, the reason, both layer results and all
24 check outcomes:

```
40 of 40 cases match on decision, reason, both layer results and all 24 checks; 0 mismatch(es)
```

At this stage the 24 check outcomes are an input to the model, read from
each case, so their agreement shows that the model read them correctly. The
decision, the reason and the layer results are computed by the model on its
own; the reason in particular is never copied from the case (see
[How a case is read](#how-a-case-is-read)).

## How to re-run it

You need [elan](https://github.com/leanprover/elan) (the Lean version
manager) and, for the engine comparison, Node.js 22 or later.

```sh
lake build                      # the model, the proofs and the case runner
lake test                       # the 40 cases through the model, against each case's expected result
./scripts/check-axioms.sh       # what every theorem rests on
npm ci --ignore-scripts         # the reference engine, pinned: @delegus/conformance 0.4.0
node scripts/compare.mjs        # model and engine, case by case
```

`lake build` fails if any proof is wrong. `lake test`, `check-axioms.sh` and
`compare.mjs` each exit non-zero on any mismatch. The same steps run in CI
on every push (`.github/workflows/ci.yml`).

To print the model's answer for each case, one JSON object per line:

```sh
.lake/build/bin/delegus-model vectors/cases
```

---

## Technical detail

### Layout

| Path | Contents |
|---|---|
| `DelegusSpec/Basic.lean` | `Check` (24 constructors), `order` (§5.4), `protocolChecks`, `trustChecks`, `Reason` (21 §5.2 codes, 5 §5.3 codes, reserved `ISSUER_NOT_TRUSTED`), `codes` (which codes each check may carry), `Outcome` (`pass`, `fail r`, `skipped`), `Checks`, `Decision` |
| `DelegusSpec/Kernel.lean` | `firstFail`, `firstFailCheck`, `allPass`, `decisionOf`, `Result`, `kernel` (the pure Phase 0 evaluator), `Prereq`, `enginePrereq`, `Backward`, `Respects`, `WellCoded`, and executable versions `backwardB`, `exactB`, `wellCodedB` |
| `DelegusSpec/Theorems.lean` | The theorems below |
| `DelegusVectors/Lower.lean` | Reading a conformance case into the kernel's input (not used by any proof) |
| `DelegusModel.lean` | `delegus-model`: prints the kernel's result per case |
| `KernelTest.lean` | `lake test` driver: the 40 cases against their expected decision, reason and layer results |
| `scripts/check-axioms.sh` | `#print axioms` for every theorem, failing on anything but the standard three |
| `scripts/compare.mjs` | Model against the reference engine, live, on all 40 cases |
| `vectors/cases/` | The 40 cases, byte for byte from `@delegus/conformance` 0.4.0 |

No Mathlib, no other dependency: the model uses only Lean's core library.
No `native_decide`, so the compiler is not part of what is trusted for the
proofs.

### Toolchain

`lean-toolchain` pins `leanprover/lean4:v4.36.0`, the release marked Latest
on GitHub (published 16 November 2026). Upgrades are deliberate commits.

### The kernel

```lean
def firstFail (c : Checks) : Option Reason :=
  order.findSome? fun k => (c.get k).failReason

def decisionOf (c : Checks) : Decision :=
  if allPass c order then .allow else .deny

def kernel (c : Checks) : Result where
  decision := decisionOf c
  reason := firstFail c
  protocolPass := allPass c protocolChecks
  trustPass := allPass c trustChecks
  checks := c
```

`kernel` is pure and total. In Phase 0, store answers (issuer registry,
status list, replay store) and cryptographic results reach it only through
the 24 check outcomes. The staged evaluator that takes them as explicit
inputs and parameters is Phase 1.

### Theorems

All in namespace `Delegus`. `c : Checks` is arbitrary; `pr : Prereq` is any
prerequisite table.

| Theorem | Statement |
|---|---|
| `order_is_spec` | `order = [P1, T1, T2, T3, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, T5, P15, P16, P17, P18, P19, P20]` |
| `order_length`, `order_nodup`, `order_complete` | 24 entries, no repeats, every `Check` is in `order` |
| `p6_before_t5` | `order.idxOf .P6 < order.idxOf .T5` |
| `p14_before_t5` | `order.idxOf .P14 < order.idxOf .T5` |
| `p1_to_p14_before_t5` | every check P1 to P14 precedes T5 |
| `layers_partition` | every check is in exactly one of `protocolChecks`, `trustChecks` |
| `allow_iff_all_pass` | `(kernel c).decision = .allow ↔ ∀ k ∈ order, c.get k = .pass` |
| `allow_iff_every_check` | the same, `∀ k : Check` |
| `deny_of_not_pass`, `deny_of_fail` | any check not `.pass` (or `.fail r`) gives `.deny` |
| `protocolPass_iff`, `trustPass_iff` | each layer passes iff all its checks pass |
| `allow_iff_layers` | `.allow ↔ protocolPass ∧ trustPass` |
| `reason_first_fail` | `(kernel c).reason = some x ↔ ∃ before k after, order = before ++ k :: after ∧ c.get k = .fail x ∧ ∀ k' ∈ before, (c.get k').isFail = false` |
| `reason_first_fail_idx` | the same with indices: position `i` fails with `x` and no position `j < i` fails |
| `reason_eq_firstFailCheck` | the reason is the failure reason of `firstFailCheck c` |
| `skipped_has_earlier_fail` | `Backward pr → Respects pr c → c.get k = .skipped → ∃ k', order.idxOf k' < order.idxOf k ∧ (c.get k').isFail` |
| `reason_none_iff_allow` | `Backward pr → Respects pr c → ((kernel c).reason = none ↔ (kernel c).decision = .allow)` |
| `reason_mem_codes` | `WellCoded c → (kernel c).reason = some r → ∃ k, c.get k = .fail r ∧ r ∈ codes k` |
| `reason_never_reserved` | `WellCoded c → (kernel c).reason ≠ some .ISSUER_NOT_TRUSTED` |
| `enginePrereq_backward` | `Backward enginePrereq` |
| `backwardB_sound`, `exactB_sound`, `wellCodedB_sound` | the executable checks used on the cases imply `Backward`, `Respects` and `WellCoded` |
| `Outcome.isPass_iff`, `Outcome.failReason_eq_none_iff`, `Outcome.failReason_eq_some_iff`, `allPass_iff` | helper facts |

Every one of the 40 cases passes `exactB enginePrereq` and `wellCodedB`, so
by `exactB_sound` and `wellCodedB_sound` the hypotheses of
`skipped_has_earlier_fail`, `reason_none_iff_allow` and
`reason_never_reserved` hold for each of them.

### Axiom audit

Output of `./scripts/check-axioms.sh` with Lean 4.36.0:

```
'Delegus.order_is_spec' does not depend on any axioms
'Delegus.order_length' does not depend on any axioms
'Delegus.order_nodup' does not depend on any axioms
'Delegus.order_complete' depends on axioms: [propext]
'Delegus.p6_before_t5' does not depend on any axioms
'Delegus.p14_before_t5' does not depend on any axioms
'Delegus.p1_to_p14_before_t5' does not depend on any axioms
'Delegus.layers_partition' depends on axioms: [propext]
'Delegus.Outcome.isPass_iff' depends on axioms: [propext]
'Delegus.Outcome.failReason_eq_none_iff' depends on axioms: [propext]
'Delegus.Outcome.failReason_eq_some_iff' depends on axioms: [propext]
'Delegus.allPass_iff' depends on axioms: [propext, Quot.sound]
'Delegus.allow_iff_all_pass' depends on axioms: [propext, Quot.sound]
'Delegus.allow_iff_every_check' depends on axioms: [propext, Quot.sound]
'Delegus.deny_of_not_pass' depends on axioms: [propext, Quot.sound]
'Delegus.deny_of_fail' depends on axioms: [propext, Quot.sound]
'Delegus.protocolPass_iff' depends on axioms: [propext, Quot.sound]
'Delegus.trustPass_iff' depends on axioms: [propext, Quot.sound]
'Delegus.allow_iff_layers' depends on axioms: [propext, Quot.sound]
'Delegus.reason_first_fail' depends on axioms: [propext, Quot.sound]
'Delegus.reason_first_fail_idx' depends on axioms: [propext, Quot.sound]
'Delegus.reason_eq_firstFailCheck' depends on axioms: [propext]
'Delegus.skipped_has_earlier_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
'Delegus.reason_none_iff_allow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Delegus.reason_mem_codes' depends on axioms: [propext, Quot.sound]
'Delegus.reason_never_reserved' depends on axioms: [propext, Quot.sound]
'Delegus.backwardB_sound' depends on axioms: [propext, Quot.sound]
'Delegus.enginePrereq_backward' depends on axioms: [propext, Quot.sound]
'Delegus.exactB_sound' depends on axioms: [propext, Quot.sound]
'Delegus.wellCodedB_sound' depends on axioms: [propext, Quot.sound]
OK: 30 theorems, standard axioms only
```

`propext`, `Quot.sound` and `Classical.choice` are Lean's three standard
axioms. `sorryAx` appears nowhere.

### How a case is read

`DelegusVectors/Lower.lean` turns one case file into the kernel's input.

- The 24 outcomes come from the case's `expected.protocol_checks` and
  `expected.trust_checks` (`true` → `pass`, `false` → `fail`, `"skipped"`
  → `skipped`). All 24 must be present.
- The reason a `false` check carries is not read from `expected.reason`. For
  20 checks it is the single code in the §5.2 or §5.3 table. For the four
  checks with two codes it is derived from the case's inputs:
  - P1: `UNSUPPORTED_FEATURE` if the Grant payload has a `parentGrant`
    member (§3.2 row 15), otherwise `GRANT_MALFORMED`;
  - T1: `SERVICE_UNAVAILABLE` if `input.state.issuer` is `"unavailable"`,
    otherwise `ISSUER_UNKNOWN`;
  - P6: `SERVICE_UNAVAILABLE` if `input.state.status_list` is
    `"unavailable"`, otherwise `AUTHORITY_REVOKED`;
  - T5: `SERVICE_UNAVAILABLE` if `input.state.replay.unavailable` is true,
    otherwise `PROOF_REPLAYED`.

`scripts/compare.mjs` then runs the reference engine live on each case's
`input` through `coreImplementation` from `@delegus/conformance` (which
wraps `@delegus/core` 0.3.2) and compares the decision, the reason, both
layer results and all 24 outcomes with the model's. It also checks that
`vectors/cases/` is byte-identical to the package's cases. `--engine
<module>` points it at another module exporting `coreImplementation`.

The conformance runner's `--impl` plug-in is not used yet: it hands an
implementation only the case's `input`, and the Phase 0 model needs the
check outcomes. It becomes the bridge in Phase 2, once the model computes
the checks itself.

### Source of the cases

`vectors/cases/` holds the 40 `delegus-base-v1` cases of
[`@delegus/conformance`](https://www.npmjs.com/package/@delegus/conformance)
version 0.4.0 (npm integrity
`sha512-jZQUL1oRaD4WQXWpNCTFYVQgcsPHT9SYMyImiUyliUN8J41XgrsEemIGzMbuz7GLiXSRjtdG7R3+BFl8gKkH9A==`),
byte for byte; `scripts/compare.mjs` fails if they ever differ. They are the
same bytes as `packages/core/test/vectors/cases/` in the Delegus reference
engine. They use test keys and non-production identifiers only
(`did:web:acme.example`, `did:web:test.delegus.example`).

### Readings

The specification is the only normative source: Delegus Specification v0.2,
frozen, with errata 1 and 2. Where it is silent, the model takes the
readings below. None changes or extends the protocol.

1. **Which check depends on which.** §5.4 says checks "whose prerequisites
   failed are skipped" but does not list the prerequisites. `enginePrereq`
   is the reference engine's table: T1 needs P1; T2, T3 and P2 need T1; P3
   needs P2; P4 to P8 need P3; P9 to P14 need P8; T5 needs all of P1 to
   P14; P15 needs P14; P16 to P20 each need the one before. The theorems
   that mention prerequisites hold for every table in which each
   prerequisite comes earlier, so they do not depend on this choice.
2. **"Failed" includes skipped.** §5.4 says a check is skipped when its
   prerequisites "failed". The model reads that as "is not true": a
   prerequisite that was false, or was itself skipped, both cause a skip.
   The engine does the same, and all 40 cases follow it.
3. **ALLOW needs all 24 checks true.** §5.4 says DENY if any check is false.
   The model allows only when every check is true, so a skipped check can
   never lead to ALLOW. `reason_none_iff_allow` shows the two agree whenever
   skips follow a backward table.
4. **`SERVICE_UNAVAILABLE` at P6.** §7 requires `SERVICE_UNAVAILABLE` when
   current revocation state cannot be established, without naming a check.
   The model places it at P6, the check that uses revocation state, as the
   engine does.
5. **`SERVICE_UNAVAILABLE` at T1.** The specification names no code for an
   unreadable issuer registry; §0 constraint 3 requires DENY. The model
   places `SERVICE_UNAVAILABLE` at T1, as the engine does.
6. **Which P1 code wins.** When a Grant both carries `parentGrant` and is
   malformed in another way, the specification does not say whether the
   reason is `UNSUPPORTED_FEATURE` or `GRANT_MALFORMED`. The engine checks
   the JOSE header first and `parentGrant` before the payload fields. The
   Phase 0 reader looks only at `parentGrant`. No published case has both
   conditions, so this does not affect the 40 results; Phase 1, which
   models P1 field by field, has to pin it.

The plan's other open points (the `merchantCategory` reading, erratum 3,
the status credential's own validity window at P6, the replay window edge,
T5 after a trust failure) concern checks and stores that Phase 0 does not
model. They are not touched here.

### Licence

Apache-2.0 (`LICENSE`, `NOTICE`). The cases in `vectors/cases/` are
Apache-2.0 from Delegus. Doc comments that restate the specification's
check tables carry its attribution: "Delegus Specification v0.2, © Delegus
(delegus.ai)", CC BY 4.0.
