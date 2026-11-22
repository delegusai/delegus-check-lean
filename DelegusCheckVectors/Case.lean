/-
Copyright 2026 Inam Haq. Licensed under the Apache License, Version 2.0.

Running the model on a conformance case.

The case file (`vectors/cases/<id>.json`) supplies the inputs: the Grant,
Proof and Action as received, the RP DID, the clock, the Proof window, the
service DID and the service state the three hot-path operations observe.
The lowered file (`vectors/lowered/<id>.json`, written by
`scripts/lower.mjs`) supplies only primitive facts: decoded JWS, parsed JSON,
decoded keys, key safety, which key × JWS pairs verify, SHA-256, JCS, the
htu canonical form, RFC 3339 times and decoded status bitstrings.

Nothing here reads the case's expected results except `expected`, which only
the test driver compares against. The model computes all 24 checks, the
decision and the reason.
-/
import Lean.Data.Json
import DelegusCheckSpec

namespace DelegusCheck.Vectors

open Lean (Json)
open DelegusCheck

def getStr (j : Json) (k : String) : Except String String := j.getObjValAs? String k
def getArr (j : Json) (k : String) : Except String (Array Json) := do (← j.getObjVal? k).getArr?

/-! ## Primitive facts as tables -/

structure Facts where
  jws : List (String × Jws)
  json : List (String × Json)
  didKey : List (String × PubKey)
  multibase : List (String × PubKey)
  keyOk : List (PubKey × Bool)
  /-- Key × (signing input, signature) pairs that verify. -/
  sig : List (PubKey × String × String)
  /-- (compressed action, JCS text). -/
  jcs : Option (String × String)
  sha256 : List (String × String)
  htu : List String
  time : List (String × Int)
  list : List (String × ByteArray)
  statusKeys : List (String × PubKey)

def lookup {α} (l : List (String × α)) (k : String) : Option α :=
  (l.find? (fun (e : String × α) => e.1 == k)).map (fun (e : String × α) => e.2)

/-- Every primitive answers from the tables; anything absent is "no". -/
def Facts.prims (f : Facts) : Prims where
  decodeJws s := lookup f.jws s
  parseJson s := lookup f.json s
  didKeyPub s := lookup f.didKey s
  multibasePub s := lookup f.multibase s
  keyOk k := (lookup f.keyOk k).getD false
  sigOk k m σ := f.sig.any fun (e : PubKey × String × String) => e.1 == k && e.2.1 == m && e.2.2 == σ
  sha256 t := (lookup f.sha256 t).getD "sha256:unknown"
  jcs j := match f.jcs with
    | some (c, t) => if j.compress == c then some t else none
    | none => none
  htuCanon s := f.htu.contains s
  rfc3339 s := lookup f.time s
  decodeList s := lookup f.list s

def bitstring (bytes : Nat) (set : List Nat) : ByteArray := Id.run do
  let mut b := ByteArray.mk (Array.replicate bytes 0)
  for i in set do
    let idx := i / 8
    let v := b.get! idx
    b := b.set! idx (v ||| (UInt8.ofNat (1 <<< (7 - i % 8))))
  return b

def pair (k v : String) (e : Json) : Except String (String × String) := do
  return (← getStr e k, ← getStr e v)

def parseFacts (j : Json) (action : Json) : Except String Facts := do
  let p ← j.getObjVal? "prims"
  let jws ← (← getArr p "jws").toList.mapM fun e => do
    let w : Jws := { header := ← e.getObjVal? "header", payload := ← e.getObjVal? "payload",
                     signingInput := ← getStr e "signingInput", signature := ← getStr e "signature" }
    return (← getStr e "text", w)
  let json ← (← getArr p "json").toList.mapM fun e => do return (← getStr e "text", ← e.getObjVal? "value")
  let didKey ← (← getArr p "didKey").toList.mapM (pair "s" "pub")
  let multibase ← (← getArr p "multibase").toList.mapM (pair "s" "pub")
  let keyOk ← (← getArr p "keyOk").toList.mapM fun e => do return (← getStr e "pub", ← e.getObjValAs? Bool "ok")
  let sig ← (← getArr p "sig").toList.mapM fun e => do
    let i ← e.getObjValAs? Nat "jws"
    match jws[i]? with
    | some (_, w) => return (← getStr e "pub", w.signingInput, w.signature)
    | none => throw "sig: bad jws index"
  let jcs := match p.getObjValD "jcs" with
    | .str t => some (action.compress, t)
    | _ => none
  let sha256 ← (← getArr p "sha256").toList.mapM (pair "text" "hash")
  let htu ← (← getArr p "htu").toList.mapM fun e => e.getStr?
  let time ← (← getArr p "time").toList.mapM fun e => do return (← getStr e "s", ← e.getObjValAs? Int "ms")
  let list ← (← getArr p "list").toList.mapM fun e => do
    let set ← (← getArr e "set").toList.mapM fun x => x.getNat?
    return (← getStr e "s", bitstring (← e.getObjValAs? Nat "bytes") set)
  let statusKeys ← (← getArr j "statusKeys").toList.mapM fun e => do
    match e with
    | .arr #[.str k, .str v] => pure (k, v)
    | _ => throw "statusKeys entry"
  return { jws, json, didKey, multibase, keyOk, sig, jcs, sha256, htu, time, list, statusKeys }

/-! ## The case inputs -/

structure Loaded where
  id : String
  env : Env
  /-- The case's expected values, read only by the test driver. -/
  expected : Json

def isStrJ (j : Json) (s : String) : Bool :=
  match j with
  | .str t => t == s
  | _ => false

def loadCase (caseText loweredText : String) : Except String Loaded := do
  let c ← Json.parse caseText
  let l ← Json.parse loweredText
  let id ← getStr c "vector"
  if (← getStr l "vector") != id then throw s!"{id}: lowered file is for another case"
  let input ← c.getObjVal? "input"
  let action ← input.getObjVal? "action"
  let facts ← parseFacts l action
  let π := facts.prims
  let req : Request := {
    grant := ← getStr input "grant", proof := ← getStr input "proof", action,
    rp := ← getStr input "relying_party",
    windowS := (input.getObjValAs? Nat "proof_window_seconds").toOption.getD 60 }
  let evaluatedAt ← getStr input "evaluated_at"
  let nowMs ← match π.rfc3339 evaluatedAt with
    | some ms => pure ms
    | none => throw s!"{id}: evaluated_at has no time fact"
  let service ← input.getObjVal? "service"
  let tc : TrustConfig := { serviceDid := ← getStr service "did", statusKeys := facts.statusKeys }
  let st ← input.getObjVal? "state"
  -- The registry, the status-list cache and the replay store as the case describes them.
  let iss ← st.getObjVal? "issuer"
  let issuer : Did → IssuerLookup ←
    if isStrJ iss "unavailable" then pure fun _ => .unavailable
    else if (iss.getObjValAs? Bool "registered").toOption == some true then do
      let did ← getStr iss "did"
      let dv := (iss.getObjValAs? Bool "domain_verified").toOption.getD false
      let comp := ((iss.getObjValAs? (Array String) "compromised_kids").toOption.getD #[]).toList
      let doc := (getStr iss "did_document").toOption.getD ""
      pure fun d => if d == did then .registered dv comp doc else .unknown
    else pure fun _ => .unknown
  let sl ← st.getObjVal? "status_list"
  let status : String → StatusLookup ←
    if isStrJ sl "unavailable" then pure fun _ => .unavailable
    else do
      let url ← getStr sl "url"
      let cred ← getStr sl "credential"
      pure fun u => if u == url then .snapshot cred else .unavailable
  let rs ← st.getObjVal? "replay"
  let replayDown ← rs.getObjValAs? Bool "unavailable"
  let consumed ← rs.getObjValAs? (Array String) "consumed"
  let rp := req.rp
  let ρ : ReplayQuery → ReplayAnswer := fun q =>
    if replayDown then .unavailable
    else if q.rp == rp && consumed.contains q.jti then .replayed
    else .ok
  return { id, env := ⟨π, req, ⟨issuer, status⟩, tc, ⟨nowMs⟩, ρ⟩, expected := ← c.getObjVal? "expected" }

/-! ## Output -/

def _root_.DelegusCheck.Decision.name : Decision → String
  | .allow => "ALLOW"
  | .deny => "DENY"

def layerName (b : Bool) : String := if b then "PASS" else "FAIL"

def outcomeJson : Outcome → Json
  | .pass => .bool true
  | .fail _ => .bool false
  | .skipped => .str "skipped"

def resultJson (id : String) (ev : Evaluation) : Json :=
  let r := ev.result
  let c := r.checks
  Json.mkObj [
    ("vector", .str id),
    ("decision", .str r.decision.name),
    ("reason", match r.reason with | some x => .str x.name | none => .null),
    ("protocol_result", .str (layerName r.protocolPass)),
    ("trust_result", .str (layerName r.trustPass)),
    ("protocol_checks", Json.mkObj (protocolChecks.map fun k => (k.name, outcomeJson (c.get k)))),
    ("trust_checks", Json.mkObj (trustChecks.map fun k => (k.name, outcomeJson (c.get k)))),
    ("first_failed_check", match firstFailCheck c with | some k => .str k.name | none => .null),
    ("principal", match ev.attribution with | some a => .str a.principal | none => .null),
    ("request_hash", match ev.requestHash with | some h => .str h | none => .null),
    ("prerequisite_table_followed", .bool (exactB enginePrereq c)),
    ("reason_codes_well_formed", .bool (wellCodedB c))
  ]

def runLoaded (l : Loaded) : Evaluation :=
  let e := l.env
  evaluate e.π e.req e.s e.tc e.clk e.ρ

/-- The `.json` files of a directory, sorted by name. -/
def caseFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let entries ← dir.readDir
  let files := entries.filter (·.fileName.endsWith ".json") |>.map (·.path)
  return files.qsort (fun a b => a.toString < b.toString)

/-- Load a case and its lowered facts (same file name under `loweredDir`). -/
def loadFile (casePath loweredDir : System.FilePath) : IO (Except String Loaded) := do
  let name := casePath.fileName.getD ""
  let lp := loweredDir / name
  if !(← lp.pathExists) then return .error s!"{name}: no lowered file at {lp}"
  return loadCase (← IO.FS.readFile casePath) (← IO.FS.readFile lp)

end DelegusCheck.Vectors
