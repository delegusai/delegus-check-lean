# Research Companion Proofs

This directory holds standalone Lean 4.36 protocol-comparison models that sit alongside (and do not alter) the frozen 197-theorem `DelegusCheckSpec` model of Delegus Check v0.2.

## `ProtocolSecurityComparison.lean`

Twelve machine-checked theorems comparing public wire contracts for identity/transport protocols (`RFC 8693` / `ID-JAG` OAuth token exchange, `RFC 9421` HTTP Message Signatures) and self-attesting agent verifiers against Delegus Check `v0.2`, `v0.3` (`P21/T7`), and `v0.4-draft` (`X/T8` principal exposure pools, `S1–S8` monotonic sub-delegation chains, and self-learning enterprise hardening `H1–H4`).

### Verify locally

```bash
lean research/ProtocolSecurityComparison.lean
```

Expected result: exit code `0`, zero warnings, zero `sorryAx`, and `#print axioms` listing only Lean's standard kernel axioms (`propext`, `Classical.choice`, `Quot.sound`).

### Scope

These proofs model the public wire contracts and decision rules under explicit assumptions (unforgeable signatures, collision-resistant hashes, linearizable atomic stores, honest relying-party action construction, and isolated enclave/interpreter attestation for `policyDigest` and external taint). They do not model proprietary closed-source server code.
