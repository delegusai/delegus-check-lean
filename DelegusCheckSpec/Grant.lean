/-
Copyright 2026 Inam Haq. Licensed under the Apache License, Version 2.0.

P1: the Grant parses and conforms to §3 (incl. `parentGrant` absent), field
by field, and P8: the Proof parses and conforms to §4 (incl. `jti` format).
Attribution for restated spec text: "Delegus Specification v0.2, © Delegus
(delegus.ai)", CC BY 4.0.
-/
import DelegusCheckSpec.Readings
import DelegusCheckSpec.Htu

namespace DelegusCheck

open Lean (Json)

/-- A rule: continue when it holds. -/
def req (b : Bool) : Option Unit := if b then some () else none

/-! ## Capabilities (§3.3) -/

structure Capability where
  action : String
  /-- The constraint members, as given. -/
  constraints : List (String × Json)
  /-- P20 patterns; `["*"]` when absent (§3.3). -/
  resources : List String
  /-- The Capability exactly as it appeared (receipt `authority`, §6.2). -/
  wire : Json

def constraintVal? (c : Capability) (k : String) : Option Json :=
  (c.constraints.find? (·.1 == k)).map (·.2)

/-- `resources`: absent is `["*"]`; otherwise an array of non-empty strings. -/
def parseResources : Option Json → Option (List String)
  | none => some ["*"]
  | some r => do
    let xs ← arr? r
    let ss := xs.filterMap str?
    req (ss.length == xs.length && ss.all (!·.isEmpty))
    some ss

/-- One §3.3 Capability. Well-typed values for the keys this version
    evaluates are required here (P1); unknown keys are left for P17. -/
def parseCapability (e : Json) : Option Capability := do
  req (onlyKeys e ["action", "constraints", "resources"])
  let action ← fieldStr? e "action"
  req (action == "commerce:purchase" || action == "api:call")
  let cj ← field? e "constraints"
  req (isObj cj)
  let constraints := members cj
  let resources ← parseResources (field? e "resources")
  let cap : Capability := { action, constraints, resources, wire := e }
  if action == "commerce:purchase" then
    let m ← (constraintVal? cap "maxAmount").bind safeInt?
    req (0 ≤ m)
    let cur ← (constraintVal? cap "currency").bind str?
    req (isCurrency cur)
  else
    let ms ← (constraintVal? cap "methods").bind arr?
    let ss := ms.filterMap str?
    req (!ms.isEmpty && ss.length == ms.length && ss.all isHttpMethod)
  some cap

/-! ## The Grant (§3) -/

/-- The Grant fields the later checks read. -/
structure GrantF where
  kid : String
  id : String
  issuer : Did
  validFrom : String
  validUntil : String
  validFromMs : Int
  validUntilMs : Int
  /-- `credentialSubject.id`, the Agent `did:key`. -/
  agent : Did
  agentKey : PubKey
  authority : List Capability
  audience : Option (List Did)
  statusIndex : String
  statusUrl : String
  signingInput : String
  signature : String

def grantContext : List String := ["https://www.w3.org/ns/credentials/v2", "https://delegus.ai/ns/grant/v1"]
def grantType : List String := ["VerifiableCredential", "DelegusGrant"]
def grantTop : List String :=
  ["@context", "type", "id", "issuer", "validFrom", "validUntil", "credentialSubject",
   "credentialStatus", "iss", "sub", "jti", "nbf", "exp"]
def grantMaxBytes : Nat := 8 * 1024
/-- 90 days (§3.2 row 9). -/
def grantMaxLifetimeMs : Int := 90 * 24 * 60 * 60 * 1000

/-- §3.1: exactly `alg`, `typ`, `kid`; EdDSA only; `vc+jwt`; a `did:web` DID URL. -/
def grantHeaderOk (h : Json) : Bool :=
  exactKeys h ["alg", "typ", "kid"] && fieldIs h "alg" "EdDSA" && fieldIs h "typ" "vc+jwt" &&
  ((fieldStr? h "kid").bind didWebUrlDid).isSome

/-- `credentialSubject.audience` (§3.2 row 13): optional array of `did:web` DIDs. -/
def parseAudience : Option Json → Option (Option (List Did))
  | none => some none
  | some a => do
    let xs ← arr? a
    let ss := xs.filterMap str?
    req (ss.length == xs.length && ss.all isDidWeb)
    some (some ss)

/-- The §3.2 payload rules (fields 4–14, 16–20), in the engine's order. -/
def grantPayload (π : Prims) (j : Jws) : Option GrantF := do
  let h := j.header
  let p := j.payload
  let kid ← fieldStr? h "kid"
  let kidDid ← didWebUrlDid kid
  req (exactKeys p grantTop)
  req (((field? p "@context").map (isStrArray · grantContext)).getD false)
  req (((field? p "type").map (isStrArray · grantType)).getD false)
  let id ← fieldStr? p "id"
  req (isGrantId id)
  let issuer ← fieldStr? p "issuer"
  req (isDidWeb issuer)
  req (issuer == kidDid)
  let validFrom ← fieldStr? p "validFrom"
  let validUntil ← fieldStr? p "validUntil"
  let vf ← π.rfc3339 validFrom
  let vu ← π.rfc3339 validUntil
  req (decide (vu - vf ≤ grantMaxLifetimeMs))
  -- credentialSubject (rows 10–13)
  let cs ← field? p "credentialSubject"
  req (onlyKeys cs ["id", "principal", "authority", "audience"])
  let agent ← fieldStr? cs "id"
  let agentKey ← π.didKeyPub agent
  req (π.keyOk agentKey)                                   -- erratum 3
  req (fieldIs cs "principal" issuer)
  let auth ← (field? cs "authority").bind arr?
  req (1 ≤ auth.length && auth.length ≤ 16)
  let authority ← auth.mapM parseCapability
  let audience ← parseAudience (field? cs "audience")
  -- credentialStatus (row 14)
  let st ← field? p "credentialStatus"
  req (onlyKeys st ["id", "type", "statusPurpose", "statusListIndex", "statusListCredential"])
  req (fieldIs st "type" "BitstringStatusListEntry")
  req (fieldIs st "statusPurpose" "revocation")
  let idx ← fieldStr? st "statusListIndex"
  req (isDecimal idx && decide ((decimalValue idx : Int) ≤ maxSafe))
  let url ← fieldStr? st "statusListCredential"
  req (isCanonicalHtu url && url.startsWith "https://")
  req (match field? st "id" with | none => true | some v => (str? v).isSome)
  -- registered claims (rows 16–20)
  req (fieldIs p "iss" issuer)
  req (fieldIs p "sub" agent)
  req (fieldIs p "jti" id)
  let nbf ← (field? p "nbf").bind safeInt?
  let exp ← (field? p "exp").bind safeInt?
  req (vf % 1000 == 0 && nbf * 1000 == vf)
  req (vu % 1000 == 0 && exp * 1000 == vu)
  some { kid, id, issuer, validFrom, validUntil, validFromMs := vf, validUntilMs := vu,
         agent, agentKey, authority, audience, statusIndex := idx, statusUrl := url,
         signingInput := j.signingInput, signature := j.signature }

/-- P1. Size and JWS decoding first; then the header, `parentGrant` and the
    payload rules, combined by the pending reading `p1Code`. -/
def parseGrant (π : Prims) (grant : String) : Except Reason GrantF :=
  if grant.length > grantMaxBytes then .error .GRANT_MALFORMED else
  match π.decodeJws grant with
  | none => .error .GRANT_MALFORMED
  | some j => p1Code (grantHeaderOk j.header) (has j.payload "parentGrant") (grantPayload π j)

/-! ## The Proof (§4) -/

structure ProofF where
  iss : Did
  agentKey : PubKey
  aud : Did
  grant : String
  jti : String
  iat : Int
  htm : String
  htu : String
  actionHash : String
  signingInput : String
  signature : String

def proofClaims : List String := ["iss", "aud", "grant", "jti", "iat", "htm", "htu", "action_hash"]

/-- P8, in the engine's order. -/
def parseProof (π : Prims) (proof : String) : Option ProofF := do
  let j ← π.decodeJws proof
  let h := j.header
  let p := j.payload
  -- §4.1
  req (exactKeys h ["alg", "typ", "kid"])
  req (fieldIs h "alg" "EdDSA")
  req (fieldIs h "typ" "delegus-proof+jwt")
  let kid ← fieldStr? h "kid"
  -- §4.2
  req (exactKeys p proofClaims)
  let iss ← fieldStr? p "iss"
  let agentKey ← π.didKeyPub iss
  req (π.keyOk agentKey)                                   -- erratum 3
  req (kid == agentKidFor iss)
  let aud ← fieldStr? p "aud"
  req (isDidWeb aud)
  let grant ← fieldStr? p "grant"
  req (isGrantId grant)
  let jti ← fieldStr? p "jti"
  req (isJti jti)
  let iat ← (field? p "iat").bind safeInt?
  req (0 ≤ iat)
  let htm ← fieldStr? p "htm"
  req (isHttpMethod htm)
  let htu ← fieldStr? p "htu"
  req (isCanonicalHtu htu)
  let actionHash ← fieldStr? p "action_hash"
  req (isSha256Ref actionHash)
  some { iss, agentKey, aud, grant, jti, iat, htm, htu, actionHash,
         signingInput := j.signingInput, signature := j.signature }

end DelegusCheck
