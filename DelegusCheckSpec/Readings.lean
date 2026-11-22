/-
Copyright 2026 Inam Haq. Licensed under the Apache License, Version 2.0.

Every point where the Delegus Check v0.2 specification is silent and the
model has to choose, in one place, so each can be swapped without touching
the rest of the model. Each definition says whose reading it is and its
status.

Decided by the owner, and therefore not readings:
* Erratum 3 (unusable Ed25519 keys) is in scope for v0.2 (owner, 22 Nov
  2026). It is part of the protocol: `Prims.keyOk` is applied at P1 (the
  Agent `did:key`), P2 (the DID-document key) and P8 (the Proof `iss`).
* One clock: every check in a decision, P6 included, reads the same `now`
  (`Clock.nowMs`). This is the specification's reading (§5.4, erratum 2),
  owner-confirmed 22 Nov 2026.
-/
import DelegusCheckSpec.Syntax

namespace DelegusCheck

open Lean (Json)

/-- **Engine reading, owner-confirmed 22 Nov 2026: `merchantCategory`.** §3.3 defines it for
    `commerce:purchase`, but the Action wire fields (§4.3) carry no
    category, so it cannot be evaluated. The engine treats it as a key this
    version does not evaluate, so P17 fails with `UNKNOWN_CONSTRAINT`
    (vector `deny-unknown-constraint-merchant-category`). To change the
    reading, change this list (and give P18–P20 a rule for it). -/
def knownConstraintKeys : String → List String
  | "commerce:purchase" => ["maxAmount", "currency"]
  | "api:call" => ["methods"]
  | _ => []

/-- **Engine reading, owner-confirmed 22 Nov 2026: which P1 code wins.** When a Grant both
    carries `parentGrant` and is malformed in another way, §3.2 and §5.2 do
    not say which code is reported. The engine decides in this order: a
    malformed JOSE header is `GRANT_MALFORMED`; then `parentGrant` present is
    `UNSUPPORTED_FEATURE`; then any payload rule failing is
    `GRANT_MALFORMED`. (Size and JWS decoding failures come first in every
    reading, since no payload has been read.) -/
def p1Code {α : Type} (headerOk hasParentGrant : Bool) (payload : Option α) : Except Reason α :=
  if !headerOk then .error .GRANT_MALFORMED
  else if hasParentGrant then .error .UNSUPPORTED_FEATURE
  else match payload with
    | some a => .ok a
    | none => .error .GRANT_MALFORMED

/-- **Reading, owner-ruled 22 Nov 2026, switch pending erratum 5: an
    unusable status credential.** When a status credential is present but
    unusable (bad signature, wrong URL, outside its own validity, index out
    of range), the frozen text and the published engine give
    `AUTHORITY_REVOKED` (§5.2 lists only that code for P6). The owner ruled
    that this means current revocation state "cannot be established" (§7),
    so P6 gives `SERVICE_UNAVAILABLE`; that changes engine behaviour and
    lands as erratum 5 with new vectors. Until then this stays at the
    frozen behaviour so the model matches the published conformance cases;
    flip it to `SERVICE_UNAVAILABLE` when erratum 5's vectors land. -/
def unusableStatusCode : Reason := .AUTHORITY_REVOKED

/-! `jti` format (§4.2) — **engine reading, owner-confirmed 22 Nov 2026.**
The text says "22–64 ASCII characters"; the engine, and so the model
(`isJti` in `Syntax.lean`), accepts only the base64url alphabet, the SHOULD
encoding and the only checkable proxy for ≥ 128 random bits. This is
narrower than the text. -/

/-! ## Replay key and expiry (T5)

The frozen specification (§5.3): `SET replay:{rp_did}:{jti} 1 NX PX
{2 × window_ms}`. The owner has chosen erratum 4, an absolute expiry
`PXAT(iat·1000 + window_ms + margin_ms)`; its text is being drafted. Only
`replayQuery` changes when it lands. -/

/-- When a replay key expires. -/
inductive Expiry
  /-- Relative: `PX ms` (frozen §5.3). -/
  | px (ms : Nat)
  /-- Absolute: `PXAT ms` (erratum 4, pending text). -/
  | pxat (ms : Int)
  deriving DecidableEq, Repr

/-- The replay store operation T5 performs. -/
structure ReplayQuery where
  rp : Did
  jti : String
  expiry : Expiry
  deriving DecidableEq, Repr

/-- The frozen §5.3 operation for an RP, a `jti` and a Proof window. The
    Proof's `iat` is passed so the erratum 4 form can be dropped in. -/
def replayQuery (rp : Did) (jti : String) (_iat : Int) (windowS : Nat) : ReplayQuery :=
  { rp, jti, expiry := .px (2 * windowS * 1000) }

end DelegusCheck
