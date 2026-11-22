/-
Copyright 2026 Inam Haq. Licensed under the Apache License, Version 2.0.

Phase 0 lowering: read one conformance case and build the kernel's input.

What this reads, and from where:
* The 24 check outcomes (`true`, `false`, `"skipped"`) come from the case's
  `expected.protocol_checks` and `expected.trust_checks`. In Phase 0 the
  model does not compute checks; Phase 1 does.
* The reason code a `false` check carries is NOT read from the case's
  `expected.reason`. For checks with one code it is the §5.2 / §5.3 table
  (`Delegus.codes`). For the four checks with two codes it is derived from
  the case's inputs:
    P1: `UNSUPPORTED_FEATURE` when the Grant payload has a `parentGrant`
        member (§3.2 row 15), otherwise `GRANT_MALFORMED`;
    T1: `SERVICE_UNAVAILABLE` when `input.state.issuer` is "unavailable",
        otherwise `ISSUER_UNKNOWN`;
    P6: `SERVICE_UNAVAILABLE` when `input.state.status_list` is
        "unavailable", otherwise `AUTHORITY_REVOKED`;
    T5: `SERVICE_UNAVAILABLE` when `input.state.replay.unavailable` is true,
        otherwise `PROOF_REPLAYED`.
So the decision, the reason and both layer results are computed by the
kernel, independently of the engine's reported decision and reason.
-/
import Lean.Data.Json
import DelegusCheckSpec

namespace DelegusCheck.Vectors

open Lean (Json)

/-! ## base64url (RFC 4648 §5, no padding), only to look inside the Grant payload -/

private def b64val (c : Char) : Option Nat :=
  if 'A' ≤ c ∧ c ≤ 'Z' then some (c.toNat - 'A'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'z' then some (c.toNat - 'a'.toNat + 26)
  else if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat + 52)
  else if c = '-' then some 62
  else if c = '_' then some 63
  else none

def base64urlDecode (s : String) : Option ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut acc : Nat := 0
  let mut bits : Nat := 0
  for c in s.toList do
    match b64val c with
    | none => return none
    | some v =>
      acc := (acc <<< 6) ||| v
      bits := bits + 6
      if bits ≥ 8 then
        bits := bits - 8
        out := out.push (UInt8.ofNat ((acc >>> bits) &&& 0xff))
        acc := acc &&& ((1 <<< bits) - 1)
  return some out

/-- The Grant's JWS payload as JSON, if it decodes. -/
def grantPayload (grant : String) : Option Json := do
  match grant.splitOn "." with
  | [_, p, _] =>
    let bytes ← base64urlDecode p
    let text ← String.fromUTF8? bytes
    (Json.parse text).toOption
  | _ => none

/-! ## Reading a case -/

def checkOfName (s : String) : Option Check :=
  order.find? fun k => k.name == s

def reasonOfName (s : String) : Option Reason :=
  [Reason.GRANT_MALFORMED, .UNSUPPORTED_FEATURE, .ISSUER_KEY_NOT_FOUND,
   .GRANT_SIGNATURE_INVALID, .GRANT_NOT_YET_VALID, .GRANT_EXPIRED,
   .AUTHORITY_REVOKED, .AUDIENCE_MISMATCH, .PROOF_MALFORMED,
   .PROOF_SIGNATURE_INVALID, .PROOF_AGENT_MISMATCH, .PROOF_GRANT_MISMATCH,
   .PROOF_AUDIENCE_MISMATCH, .PROOF_EXPIRED, .PROOF_ACTION_MISMATCH,
   .ACTION_MALFORMED, .ACTION_NOT_AUTHORIZED, .UNKNOWN_CONSTRAINT,
   .CURRENCY_NOT_AUTHORIZED, .AMOUNT_EXCEEDS_AUTHORITY, .RESOURCE_NOT_AUTHORIZED,
   .ISSUER_UNKNOWN, .ISSUER_UNVERIFIED, .ISSUER_KEY_COMPROMISED,
   .PROOF_REPLAYED, .SERVICE_UNAVAILABLE, .ISSUER_NOT_TRUSTED].find? fun r => r.name == s

/-- A raw check value from a case: `true`, `false` or `"skipped"`. -/
inductive Raw | t | f | skipped
  deriving DecidableEq, Repr

def rawOf (j : Json) : Except String Raw :=
  match j with
  | .bool true => .ok .t
  | .bool false => .ok .f
  | .str "skipped" => .ok .skipped
  | other => .error s!"bad check value {other.compress}"

/-- The facts from the case input that pick between two codes. -/
structure Details where
  grantHasParent : Bool
  issuerUnavailable : Bool
  statusUnavailable : Bool
  replayUnavailable : Bool

def failCode (d : Details) : Check → Reason
  | .P1 => if d.grantHasParent then .UNSUPPORTED_FEATURE else .GRANT_MALFORMED
  | .T1 => if d.issuerUnavailable then .SERVICE_UNAVAILABLE else .ISSUER_UNKNOWN
  | .P6 => if d.statusUnavailable then .SERVICE_UNAVAILABLE else .AUTHORITY_REVOKED
  | .T5 => if d.replayUnavailable then .SERVICE_UNAVAILABLE else .PROOF_REPLAYED
  | k => (codes k).headD .SERVICE_UNAVAILABLE   -- every other row has exactly one code

/-- Everything the runner needs from one case. -/
structure Case where
  id : String
  raw : Check → Raw
  details : Details
  /-- The case's expected values, used only by the test driver for comparison. -/
  expDecision : String
  expReason : Option String
  expProtocol : String
  expTrust : String

def Case.checks (c : Case) : Checks where
  get k := match c.raw k with
    | .t => .pass
    | .skipped => .skipped
    | .f => .fail (failCode c.details k)

private def isStr (j : Json) (s : String) : Bool :=
  match j with
  | .str t => t == s
  | _ => false

def parseCase (text : String) : Except String Case := do
  let j ← Json.parse text
  let id ← j.getObjValAs? String "vector"
  let input ← j.getObjVal? "input"
  let expected ← j.getObjVal? "expected"
  let pc ← expected.getObjVal? "protocol_checks"
  let tc ← expected.getObjVal? "trust_checks"
  -- every one of the 24 checks must be present, in the right layer
  let mut table : List (Check × Raw) := []
  for k in protocolChecks do
    table := (k, ← rawOf (← pc.getObjVal? k.name)) :: table
  for k in trustChecks do
    table := (k, ← rawOf (← tc.getObjVal? k.name)) :: table
  let (pcFields, tcFields) ← match pc, tc with
    | .obj a, .obj b => pure (a.toArray.size, b.toArray.size)
    | _, _ => throw "checks are not objects"
  if pcFields != 20 || tcFields != 4 then
    throw s!"{id}: expected 20 protocol and 4 trust checks, got {pcFields} and {tcFields}"
  let table' := table
  let raw : Check → Raw := fun k => ((table'.find? fun e => e.1 == k).map (·.2)).getD .skipped
  let grant ← input.getObjValAs? String "grant"
  let state ← input.getObjVal? "state"
  let issuer ← state.getObjVal? "issuer"
  let status ← state.getObjVal? "status_list"
  let replay ← state.getObjVal? "replay"
  let replayUnavailable ← replay.getObjValAs? Bool "unavailable"
  let grantHasParent := match grantPayload grant with
    | some p => (p.getObjVal? "parentGrant").toOption.isSome
    | none => false
  let details : Details :=
    { grantHasParent, issuerUnavailable := isStr issuer "unavailable",
      statusUnavailable := isStr status "unavailable", replayUnavailable }
  let expDecision ← expected.getObjValAs? String "decision"
  let expReason ← match expected.getObjValD "reason" with
    | .null => pure none
    | .str s => pure (some s)
    | other => throw s!"bad reason {other.compress}"
  let expProtocol ← expected.getObjValAs? String "protocol_result"
  let expTrust ← expected.getObjValAs? String "trust_result"
  return { id, raw, details, expDecision, expReason, expProtocol, expTrust }

/-! ## Rendering the kernel's result -/

def _root_.DelegusCheck.Decision.name : Decision → String
  | .allow => "ALLOW"
  | .deny => "DENY"

def layerName (b : Bool) : String := if b then "PASS" else "FAIL"

def outcomeJson : Outcome → Json
  | .pass => .bool true
  | .fail _ => .bool false
  | .skipped => .str "skipped"

def resultJson (id : String) (c : Checks) : Json :=
  let r := kernel c
  Json.mkObj [
    ("vector", .str id),
    ("decision", .str r.decision.name),
    ("reason", match r.reason with | some x => .str x.name | none => .null),
    ("protocol_result", .str (layerName r.protocolPass)),
    ("trust_result", .str (layerName r.trustPass)),
    ("protocol_checks", Json.mkObj (protocolChecks.map fun k => (k.name, outcomeJson (c.get k)))),
    ("trust_checks", Json.mkObj (trustChecks.map fun k => (k.name, outcomeJson (c.get k)))),
    ("first_failed_check", match firstFailCheck c with | some k => .str k.name | none => .null),
    ("prerequisite_table_followed", .bool (exactB enginePrereq c)),
    ("reason_codes_well_formed", .bool (wellCodedB c))
  ]

/-- The `.json` files of a directory, sorted by name. -/
def caseFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let entries ← dir.readDir
  let files := entries.filter (·.fileName.endsWith ".json") |>.map (·.path)
  return files.qsort (fun a b => a.toString < b.toString)

end DelegusCheck.Vectors
