/-
Copyright 2026 Inam Haq. Licensed under the Apache License, Version 2.0.

Phase 1: the evaluator of `/verify` (§5), in two forms.

* `table`: declarative. Each check is `skipped` unless every prerequisite
  (`enginePrereq`) is `true`, and otherwise is its own rule, `base`.
* `staged`: written the way the engine runs, stage by stage (P1, one issuer
  answer for T1–T3 and P2, P3, then P4–P8, then P9–P14, the replay
  operation and T5, then P15–P20).

`staged_eq_table` (in `Phase1.lean`) proves they are equal.
-/
import DelegusCheckSpec.Rules
import DelegusCheckSpec.Kernel

namespace DelegusCheck

open Lean (Json)

/-- Everything one evaluation reads. `ρ` is the replay store's answer to the
    operation T5 performs. -/
structure Env where
  π : Prims
  req : Request
  s : Snapshots
  tc : TrustConfig
  clk : Clock
  ρ : ReplayQuery → ReplayAnswer

/-- P1's result. -/
def Env.grant (e : Env) : Except Reason GrantF := parseGrant e.π e.req.grant
/-- P8's result. -/
def Env.proof (e : Env) : Option ProofF := parseProof e.π e.req.proof
/-- P15's result. -/
def Env.action (e : Env) : Option Action := validateAction e.req.action
/-- §6.3 `request_hash`: SHA-256 of the UTF-8 of `JCS(action)`. -/
def Env.requestHash (e : Env) : Option String := (e.π.jcs e.req.action).map e.π.sha256
/-- The replay operation for a Proof. -/
def Env.query (e : Env) (p : ProofF) : ReplayQuery := replayQuery e.req.rp p.jti p.iat e.req.windowS

/-- A check with one reason code. -/
def ok (b : Bool) (r : Reason) : Outcome := if b then .pass else .fail r

/-! ## Each check's own rule -/

def t1Of : IssuerLookup → Outcome
  | .unavailable => .fail .SERVICE_UNAVAILABLE
  | .unknown => .fail .ISSUER_UNKNOWN
  | .registered .. => .pass

def t2Of : IssuerLookup → Outcome
  | .registered dv _ _ => ok dv .ISSUER_UNVERIFIED
  | _ => .skipped

def t3Of (kid : String) : IssuerLookup → Outcome
  | .registered _ comp _ => ok (!comp.contains kid) .ISSUER_KEY_COMPROMISED
  | _ => .skipped

def p2Of (π : Prims) (g : GrantF) : IssuerLookup → Outcome
  | .registered _ _ doc => ok (findKey π doc g.issuer g.kid).isSome .ISSUER_KEY_NOT_FOUND
  | _ => .skipped

def p3Of (π : Prims) (g : GrantF) : IssuerLookup → Outcome
  | .registered _ _ doc =>
    match findKey π doc g.issuer g.kid with
    | some k => ok (π.sigOk k g.signingInput g.signature) .GRANT_SIGNATURE_INVALID
    | none => .skipped
  | _ => .skipped

def p4Of (e : Env) (g : GrantF) : Outcome := ok (decide (g.validFromMs ≤ e.clk.nowMs)) .GRANT_NOT_YET_VALID
def p5Of (e : Env) (g : GrantF) : Outcome := ok (decide (e.clk.nowMs < g.validUntilMs)) .GRANT_EXPIRED

/-- P6: unavailable revocation state is `SERVICE_UNAVAILABLE` (§7); an
    unusable or revoking credential is `AUTHORITY_REVOKED`. -/
def p6Of (e : Env) (g : GrantF) : Outcome :=
  match e.s.status g.statusUrl with
  | .unavailable => .fail .SERVICE_UNAVAILABLE
  | .snapshot cred => ok (statusOk e.π e.tc e.clk.nowMs cred g.statusUrl g.statusIndex) .AUTHORITY_REVOKED

def p7Of (e : Env) (g : GrantF) : Outcome := ok (audienceOk g e.req.rp) .AUDIENCE_MISMATCH
def p9Of (e : Env) (p : ProofF) : Outcome := ok (e.π.sigOk p.agentKey p.signingInput p.signature) .PROOF_SIGNATURE_INVALID
def p10Of (g : GrantF) (p : ProofF) : Outcome := ok (p.iss == g.agent) .PROOF_AGENT_MISMATCH
def p11Of (g : GrantF) (p : ProofF) : Outcome := ok (p.grant == g.id) .PROOF_GRANT_MISMATCH
def p12Of (e : Env) (p : ProofF) : Outcome := ok (p.aud == e.req.rp) .PROOF_AUDIENCE_MISMATCH
/-- P13: `|now − iat| ≤ window` (§4.2), in milliseconds. -/
def p13Of (e : Env) (p : ProofF) : Outcome :=
  ok (decide ((e.clk.nowMs - p.iat * 1000).natAbs ≤ e.req.windowS * 1000)) .PROOF_EXPIRED
def p14Of (e : Env) (p : ProofF) : Outcome := ok (e.requestHash == some p.actionHash) .PROOF_ACTION_MISMATCH

def replayOutcome : ReplayAnswer → Outcome
  | .ok => .pass
  | .replayed => .fail .PROOF_REPLAYED
  | .unavailable => .fail .SERVICE_UNAVAILABLE

/-- Each check's own rule, read as if its prerequisites passed. Where the
    data a rule needs does not exist (a prerequisite failed) it is
    `skipped`; the table never uses that value. -/
def base (e : Env) : Check → Outcome
  | .P1 => match e.grant with | .ok _ => .pass | .error r => .fail r
  | .T1 => match e.grant with | .ok g => t1Of (e.s.issuer g.issuer) | .error _ => .skipped
  | .T2 => match e.grant with | .ok g => t2Of (e.s.issuer g.issuer) | .error _ => .skipped
  | .T3 => match e.grant with | .ok g => t3Of g.kid (e.s.issuer g.issuer) | .error _ => .skipped
  | .P2 => match e.grant with | .ok g => p2Of e.π g (e.s.issuer g.issuer) | .error _ => .skipped
  | .P3 => match e.grant with | .ok g => p3Of e.π g (e.s.issuer g.issuer) | .error _ => .skipped
  | .P4 => match e.grant with | .ok g => p4Of e g | .error _ => .skipped
  | .P5 => match e.grant with | .ok g => p5Of e g | .error _ => .skipped
  | .P6 => match e.grant with | .ok g => p6Of e g | .error _ => .skipped
  | .P7 => match e.grant with | .ok g => p7Of e g | .error _ => .skipped
  | .P8 => ok e.proof.isSome .PROOF_MALFORMED
  | .P9 => match e.proof with | some p => p9Of e p | none => .skipped
  | .P10 => match e.grant, e.proof with | .ok g, some p => p10Of g p | _, _ => .skipped
  | .P11 => match e.grant, e.proof with | .ok g, some p => p11Of g p | _, _ => .skipped
  | .P12 => match e.proof with | some p => p12Of e p | none => .skipped
  | .P13 => match e.proof with | some p => p13Of e p | none => .skipped
  | .P14 => match e.proof with | some p => p14Of e p | none => .skipped
  | .T5 => match e.proof with | some p => replayOutcome (e.ρ (e.query p)) | none => .skipped
  | .P15 => ok e.action.isSome .ACTION_MALFORMED
  | .P16 => match e.grant, e.action with | .ok g, some a => (authorize g.authority a).p16 | _, _ => .skipped
  | .P17 => match e.grant, e.action with | .ok g, some a => (authorize g.authority a).p17 | _, _ => .skipped
  | .P18 => match e.grant, e.action with | .ok g, some a => (authorize g.authority a).p18 | _, _ => .skipped
  | .P19 => match e.grant, e.action with | .ok g, some a => (authorize g.authority a).p19 | _, _ => .skipped
  | .P20 => match e.grant, e.action with | .ok g, some a => (authorize g.authority a).p20 | _, _ => .skipped

/-! ## Rows of outcomes -/

structure Row where
  p1 : Outcome := .skipped
  t1 : Outcome := .skipped
  t2 : Outcome := .skipped
  t3 : Outcome := .skipped
  p2 : Outcome := .skipped
  p3 : Outcome := .skipped
  p4 : Outcome := .skipped
  p5 : Outcome := .skipped
  p6 : Outcome := .skipped
  p7 : Outcome := .skipped
  p8 : Outcome := .skipped
  p9 : Outcome := .skipped
  p10 : Outcome := .skipped
  p11 : Outcome := .skipped
  p12 : Outcome := .skipped
  p13 : Outcome := .skipped
  p14 : Outcome := .skipped
  t5 : Outcome := .skipped
  p15 : Outcome := .skipped
  p16 : Outcome := .skipped
  p17 : Outcome := .skipped
  p18 : Outcome := .skipped
  p19 : Outcome := .skipped
  p20 : Outcome := .skipped

def Row.get (r : Row) : Check → Outcome
  | .P1 => r.p1 | .T1 => r.t1 | .T2 => r.t2 | .T3 => r.t3 | .P2 => r.p2 | .P3 => r.p3
  | .P4 => r.p4 | .P5 => r.p5 | .P6 => r.p6 | .P7 => r.p7 | .P8 => r.p8 | .P9 => r.p9
  | .P10 => r.p10 | .P11 => r.p11 | .P12 => r.p12 | .P13 => r.p13 | .P14 => r.p14
  | .T5 => r.t5 | .P15 => r.p15 | .P16 => r.p16 | .P17 => r.p17 | .P18 => r.p18
  | .P19 => r.p19 | .P20 => r.p20

def Row.toChecks (r : Row) : Checks := ⟨r.get⟩

/-! ## The declarative table -/

/-- A check runs only when all its prerequisites are `true`. -/
def gate (ps : List Outcome) (o : Outcome) : Outcome :=
  if ps.all (· == .pass) then o else .skipped

/-- The §5.4 table with the engine's prerequisites (`enginePrereq`), one
    line per check, in evaluation order. -/
def tableRow (b : Check → Outcome) : Row :=
  let p1 := gate [] (b .P1)
  let t1 := gate [p1] (b .T1)
  let t2 := gate [t1] (b .T2)
  let t3 := gate [t1] (b .T3)
  let p2 := gate [t1] (b .P2)
  let p3 := gate [p2] (b .P3)
  let p4 := gate [p3] (b .P4)
  let p5 := gate [p3] (b .P5)
  let p6 := gate [p3] (b .P6)
  let p7 := gate [p3] (b .P7)
  let p8 := gate [p3] (b .P8)
  let p9 := gate [p8] (b .P9)
  let p10 := gate [p8] (b .P10)
  let p11 := gate [p8] (b .P11)
  let p12 := gate [p8] (b .P12)
  let p13 := gate [p8] (b .P13)
  let p14 := gate [p8] (b .P14)
  let t5 := gate [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14] (b .T5)
  let p15 := gate [p14] (b .P15)
  let p16 := gate [p15] (b .P16)
  let p17 := gate [p16] (b .P17)
  let p18 := gate [p17] (b .P18)
  let p19 := gate [p18] (b .P19)
  let p20 := gate [p19] (b .P20)
  { p1, t1, t2, t3, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, t5,
    p15, p16, p17, p18, p19, p20 }

def table (b : Check → Outcome) : Checks := (tableRow b).toChecks

/-! ## The staged evaluator -/

/-- P15–P20 after P14 passed. -/
def actionStage (e : Env) (g : GrantF) (r : Row) : Row :=
  match e.action with
  | none => { r with p15 := .fail .ACTION_MALFORMED }
  | some a =>
    let au := authorize g.authority a
    { r with p15 := .pass, p16 := au.p16, p17 := au.p17, p18 := au.p18, p19 := au.p19, p20 := au.p20 }

/-- P9–P14, the replay operation and T5, then P15–P20. Reached once P1–P8
    and T1 passed. -/
def proofStage (e : Env) (g : GrantF) (t2 t3 p4 p5 p6 p7 : Outcome) (p : ProofF) : Row :=
  let p9 := p9Of e p
  let p10 := p10Of g p
  let p11 := p11Of g p
  let p12 := p12Of e p
  let p13 := p13Of e p
  let p14 := p14Of e p
  -- [atomic replay SET NX], only after P1–P14 pass (§5.3, §7)
  let t5 := if [p4, p5, p6, p7, p9, p10, p11, p12, p13, p14].all (· == .pass)
    then replayOutcome (e.ρ (e.query p)) else .skipped
  let r : Row := { p1 := .pass, t1 := .pass, t2, t3, p2 := .pass, p3 := .pass, p4, p5, p6, p7,
                   p8 := .pass, p9, p10, p11, p12, p13, p14, t5 }
  if p14 == .pass then actionStage e g r else r

/-- The engine-shaped evaluator. -/
def stagedRow (e : Env) : Row :=
  match e.grant with
  | .error r => { p1 := .fail r }
  | .ok g =>
    -- one issuer lookup answers T1–T3 and hands over the DID document for P2
    match e.s.issuer g.issuer with
    | .unavailable => { p1 := .pass, t1 := .fail .SERVICE_UNAVAILABLE }
    | .unknown => { p1 := .pass, t1 := .fail .ISSUER_UNKNOWN }
    | .registered dv comp doc =>
      let t2 := ok dv .ISSUER_UNVERIFIED
      let t3 := ok (!comp.contains g.kid) .ISSUER_KEY_COMPROMISED
      match findKey e.π doc g.issuer g.kid with
      | none => { p1 := .pass, t1 := .pass, t2, t3, p2 := .fail .ISSUER_KEY_NOT_FOUND }
      | some key =>
        if e.π.sigOk key g.signingInput g.signature then
          let p4 := p4Of e g
          let p5 := p5Of e g
          -- [read status_ver; refresh cached status credential] → P6
          let p6 := p6Of e g
          let p7 := p7Of e g
          match e.proof with
          | none => { p1 := .pass, t1 := .pass, t2, t3, p2 := .pass, p3 := .pass, p4, p5, p6, p7,
                      p8 := .fail .PROOF_MALFORMED }
          | some p => proofStage e g t2 t3 p4 p5 p6 p7 p
        else
          { p1 := .pass, t1 := .pass, t2, t3, p2 := .pass, p3 := .fail .GRANT_SIGNATURE_INVALID }

def staged (e : Env) : Checks := (stagedRow e).toChecks

/-! ## The result -/

/-- §6.4 attribution: present only once the Grant signature verified (P3). -/
structure Attribution where
  principal : Did
  /-- `"domain"` or `"unverified"`. -/
  verification : String
  agent : Did
  grantId : String
  /-- The authorizing Capability (first survivor of P20), if any. -/
  authority : Option Json
  expiresAt : String

structure Evaluation where
  result : Result
  attribution : Option Attribution
  /-- §6.3; equals the Proof's `action_hash` when P14 passes. -/
  requestHash : Option String
  evaluatedAt : Clock

def attributionOf (e : Env) (c : Checks) : Option Attribution :=
  match c.get .P3, e.grant with
  | .pass, .ok g =>
    let dv := match e.s.issuer g.issuer with
      | .registered dv _ _ => dv
      | _ => false
    let authority := match c.get .P20, e.action with
      | .pass, some a => (authorize g.authority a).matched.map (·.wire)
      | _, _ => none
    some { principal := g.issuer, verification := if dv then "domain" else "unverified",
           agent := g.agent, grantId := g.id, authority, expiresAt := g.validUntil }
  | _, _ => none

def evaluateWith (checks : Env → Checks) (e : Env) : Evaluation :=
  let c := checks e
  { result := kernel c, attribution := attributionOf e c, requestHash := e.requestHash,
    evaluatedAt := e.clk }

/-- `/verify` (§5): pure; every store answer is an input. -/
def evaluate (π : Prims) (req : Request) (s : Snapshots) (tc : TrustConfig) (clk : Clock)
    (ρ : ReplayQuery → ReplayAnswer) : Evaluation :=
  evaluateWith staged ⟨π, req, s, tc, clk, ρ⟩

/-- The same, through the declarative table. -/
def evalTable (π : Prims) (req : Request) (s : Snapshots) (tc : TrustConfig) (clk : Clock)
    (ρ : ReplayQuery → ReplayAnswer) : Evaluation :=
  evaluateWith (fun e => table (base e)) ⟨π, req, s, tc, clk, ρ⟩

end DelegusCheck
