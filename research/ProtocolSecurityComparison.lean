/-
  Companion Protocol-Comparison Model:
  Identity & Transport Wire Contracts (Okta XAA / ID-JAG / RFC 8693,
  Cloudflare Web Bot Auth RFC 9421 / AI Gateway) vs. Delegus Check
  (v0.2 frozen, v0.3 live RC1 P21/T7, v0.4-draft X/T8 pooled exposure &
  S1–S8 sub-delegation + self-learning enterprise hardening H1–H4).

  Standalone Lean 4.36.0 — zero external dependencies, zero custom axioms,
  zero `sorry`. Run directly with:

      lean research/ProtocolSecurityComparison.lean

  Note: This file models the *public wire contracts* (what inputs exist on the
  wire and what invariants follow from them). It does not model Okta's or
  Cloudflare's proprietary server code. For the full 197-theorem model of
  Delegus Check v0.2's 24 checks, see `DelegusCheckSpec/`.
-/

namespace DelegusSecurityReview

/-! ## 1. Core Domain Types -/

abbrev PrincipalId := Nat
abbrev AgentId := Nat
abbrev GrantId := Nat
abbrev RpId := Nat
abbrev ActionHash := Nat
abbrev PolicyDigest := Nat
abbrev Nonce := Nat
abbrev Timestamp := Nat

inductive Decision where
  | allow
  | deny
  deriving DecidableEq, Repr

/-- Coarse OAuth / XAA scope class (identity-layer verb permission). -/
inductive OAuthScope where
  | paymentsWrite
  | erpRead
  deriving DecidableEq, Repr

/-- Provenance taint stamped by an isolated ingress / CaMeL-style interpreter boundary
    (never self-reported by the untrusted LLM loop). -/
inductive Provenance where
  | trustedPrincipal
  | untrustedExternal   -- e.g., indirect prompt injection from external vendor PDF / email
  deriving DecidableEq, Repr

/-- Physical-world precondition status (e.g., receiving bin NFC / 3-way match). -/
structure PhysicalAttestation where
  required : Bool
  nfcVerified : Bool
  deriving DecidableEq, Repr

/-- Hardware Pocket Signet step-up seal bound cryptographically to an exact ActionHash. -/
structure SignetSeal where
  present : Bool
  sealedActionHash : ActionHash
  deriving DecidableEq, Repr

/-- An enterprise action submitted by the Relying Party (bank, vendor, ERP). -/
structure Action where
  rp           : RpId
  scope        : OAuthScope
  amount       : Nat
  actionHash   : ActionHash
  provenance   : Provenance
  phys         : PhysicalAttestation
  highImpact   : Bool
  deriving DecidableEq, Repr

/-- An autonomous agent's runtime identity + enclave/supervisor-attested policy digest. -/
structure AgentState where
  agentId      : AgentId
  keyValid     : Bool          -- holds valid Ed25519 / XAA workload credential
  policyDigest : PolicyDigest  -- attested hash of weights/prompt/tool-policy at current epoch
  deriving DecidableEq, Repr

/-- Request presented at execution time. -/
structure ExecRequest where
  principal       : PrincipalId
  agent           : AgentState
  grantId         : GrantId
  nonce           : Nonce
  now             : Timestamp
  action          : Action
  proofActionHash : ActionHash
  gatewayClean    : Bool       -- edge heuristic prompt/PII filter passed
  signet          : SignetSeal
  deriving DecidableEq, Repr

/-! ## 2. Wire-Contract Models: Identity (ID-JAG / RFC 8693) & Edge Signatures (RFC 9421) -/

structure OktaToken where
  agentId   : AgentId
  scope     : OAuthScope
  expiresAt : Timestamp
  active    : Bool
  deriving DecidableEq, Repr

/-- Wire-contract model of OAuth 2.1 / XAA / ID-JAG token verification:
    validates active status, workload identity, coarse scope, and expiry. -/
def oktaVerify (tok : OktaToken) (req : ExecRequest) : Decision :=
  if tok.active && tok.agentId == req.agent.agentId &&
     tok.scope == req.action.scope && req.now < tok.expiresAt
  then .allow else .deny

/-- Wire-contract model of Cloudflare Web Bot Auth (RFC 9421) + AI Gateway:
    validates Ed25519 HTTP signature authenticity and edge heuristic scan. -/
def cloudflareVerify (req : ExecRequest) : Decision :=
  if req.agent.keyValid && req.gatewayClean
  then .allow else .deny

/-! ## 3. Models of Delegus Check v0.2, v0.3 (P21/T7), and v0.4-draft (X/T8 + H1–H4) -/

structure DelegusGrant where
  grantId          : GrantId
  principal        : PrincipalId
  agentId          : AgentId
  allowedRp        : RpId
  maxPerTx         : Nat           -- v0.2 P19: per-purchase cap
  grantTotalCap    : Nat           -- v0.3 P21: cumulative cap on THIS grant
  validFrom        : Timestamp
  validUntil       : Timestamp
  revoked          : Bool          -- v0.2 P6
  pinnedPolicy     : PolicyDigest  -- v0.4 H2: approved learning-epoch policy hash
  deriving DecidableEq, Repr

/-- Delegus Check v0.2 (24 checks core): cross-org RP verification, exact actionHash (P14),
    revocation (P6), per-tx cap (P19), replay (T5). No cumulative budget. -/
def delegusV02Verify (g : DelegusGrant) (usedNonces : List Nonce) (req : ExecRequest) : Decision :=
  if !g.revoked &&
     g.principal == req.principal &&
     g.agentId == req.agent.agentId &&
     g.grantId == req.grantId &&
     g.allowedRp == req.action.rp &&
     req.agent.keyValid &&
     g.validFrom <= req.now && req.now < g.validUntil &&
     req.proofActionHash == req.action.actionHash &&     -- P14
     !(req.nonce ∈ usedNonces) &&                        -- T5
     req.action.amount <= g.maxPerTx                     -- P19
  then .allow else .deny

/-- Delegus Check v0.3 (+P21 / T7): adds atomic per-grant cumulative spend budget. -/
def delegusV03Verify
    (g : DelegusGrant) (usedNonces : List Nonce) (grantSpent : Nat) (req : ExecRequest) : Decision :=
  if delegusV02Verify g usedNonces req == .allow &&
     grantSpent + req.action.amount <= g.grantTotalCap   -- P21 / T7
  then .allow else .deny

/-- Enterprise-wide state tracked by Delegus Check v0.4-draft across ALL agents & grants
    belonging to a Principal (X/T8 principal exposure pool + H1–H4 self-learning hardening). -/
structure V04State where
  orgPoolCap   : Nat
  orgSpent     : Nat
  grantSpent   : GrantId → Nat
  usedNonces   : List Nonce

/-- Delegus Check v0.4-draft + Self-Learning Hardening:
    - X / T8: Principal-wide pooled exposure cap across all sibling grants
    - H2: Enclave/supervisor-attested policy-digest pinning
    - H3: CaMeL-style taint gate requiring hardware Pocket Signet bound to exact actionHash
    - H4: Physical-world precondition attestation (e.g., NFC receiving proof) -/
def delegusV04Verify (g : DelegusGrant) (st : V04State) (req : ExecRequest) : Decision :=
  let v03Ok := delegusV03Verify g st.usedNonces (st.grantSpent g.grantId) req == .allow
  let exposurePoolOk := st.orgSpent + req.action.amount <= st.orgPoolCap
  let taintOk :=
    match req.action.provenance with
    | .trustedPrincipal => true
    | .untrustedExternal =>
        !req.action.highImpact ||
        (req.signet.present && req.signet.sealedActionHash == req.action.actionHash)
  let policyOk := req.agent.policyDigest == g.pinnedPolicy
  let physOk := !req.action.phys.required || req.action.phys.nfcVerified
  if v03Ok && exposurePoolOk && taintOk && policyOk && physOk
  then .allow else .deny

def stepV04 (g : DelegusGrant) (st : V04State) (req : ExecRequest) : V04State :=
  if delegusV04Verify g st req == .allow then
    { orgPoolCap := st.orgPoolCap
      orgSpent   := st.orgSpent + req.action.amount
      grantSpent := fun gid =>
        if gid == g.grantId then st.grantSpent gid + req.action.amount else st.grantSpent gid
      usedNonces := req.nonce :: st.usedNonces }
  else st

/-! ## 4. Theorem 1: Identity + Edge Signatures Pass Valid-Scope Over-Limit Execution;
        Delegus Check v0.2 Rejects It -/

theorem okta_and_cloudflare_fail_semantic_fraud :
    ∃ (tok : OktaToken) (g : DelegusGrant) (req : ExecRequest),
      oktaVerify tok req = .allow ∧
      cloudflareVerify req = .allow ∧
      req.action.amount > g.maxPerTx ∧
      delegusV02Verify g [] req = .deny := by
  let tok : OktaToken := { agentId := 1, scope := .paymentsWrite, expiresAt := 1000, active := true }
  let g : DelegusGrant :=
    { grantId := 10, principal := 100, agentId := 1, allowedRp := 7,
      maxPerTx := 25000, grantTotalCap := 50000,
      validFrom := 0, validUntil := 1000, revoked := false, pinnedPolicy := 42 }
  let act : Action :=
    { rp := 7, scope := .paymentsWrite, amount := 142000, actionHash := 999,
      provenance := .untrustedExternal, phys := { required := true, nfcVerified := false },
      highImpact := true }
  let req : ExecRequest :=
    { principal := 100,
      agent := { agentId := 1, keyValid := true, policyDigest := 42 },
      grantId := 10, nonce := 1, now := 500,
      action := act, proofActionHash := 999,
      gatewayClean := true,
      signet := { present := false, sealedActionHash := 0 } }
  exact ⟨tok, g, req, by decide, by decide, by decide, by decide⟩

/-! ## 5. Theorem 2: Budget Smurfing Breaks Identity, Edge Signatures, and v0.2;
        v0.3 (P21/T7) Preserves Single-Grant Cumulative Caps Universally -/

def runV02Outflow (g : DelegusGrant) : List ExecRequest → List Nonce → Nat
  | [], _ => 0
  | r :: rs, nonces =>
      if delegusV02Verify g nonces r == .allow
      then r.action.amount + runV02Outflow g rs (r.nonce :: nonces)
      else runV02Outflow g rs nonces

theorem smurfing_breaks_okta_cloudflare_and_v02 :
    ∃ (tok : OktaToken) (g : DelegusGrant) (trace : List ExecRequest),
      (∀ r ∈ trace, oktaVerify tok r = .allow ∧ cloudflareVerify r = .allow) ∧
      runV02Outflow g trace [] > g.grantTotalCap := by
  let tok : OktaToken := { agentId := 1, scope := .paymentsWrite, expiresAt := 1000, active := true }
  let g : DelegusGrant :=
    { grantId := 10, principal := 100, agentId := 1, allowedRp := 7,
      maxPerTx := 25000, grantTotalCap := 50000,
      validFrom := 0, validUntil := 1000, revoked := false, pinnedPolicy := 42 }
  let mkReq (n : Nonce) : ExecRequest :=
    { principal := 100,
      agent := { agentId := 1, keyValid := true, policyDigest := 42 },
      grantId := 10, nonce := n, now := 500,
      action := { rp := 7, scope := .paymentsWrite, amount := 15000, actionHash := 100 + n,
                  provenance := .trustedPrincipal, phys := { required := false, nfcVerified := false },
                  highImpact := false },
      proofActionHash := 100 + n, gatewayClean := true,
      signet := { present := false, sealedActionHash := 0 } }
  let trace := [mkReq 1, mkReq 2, mkReq 3, mkReq 4]
  refine ⟨tok, g, trace, ?_, ?_⟩
  · intro r hr
    simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide
  · decide

def runV03Spent (g : DelegusGrant) : List ExecRequest → List Nonce → Nat → Nat
  | [], _, spent => spent
  | r :: rs, nonces, spent =>
      if delegusV03Verify g nonces spent r == .allow
      then runV03Spent g rs (r.nonce :: nonces) (spent + r.action.amount)
      else runV03Spent g rs nonces spent

theorem v03_preserves_single_grant_budget
    (g : DelegusGrant) (trace : List ExecRequest) (nonces : List Nonce) (spent : Nat)
    (h0 : spent <= g.grantTotalCap) :
    runV03Spent g trace nonces spent <= g.grantTotalCap := by
  induction trace generalizing nonces spent with
  | nil => exact h0
  | cons r rs ih =>
      unfold runV03Spent
      by_cases h : delegusV03Verify g nonces spent r == .allow
      · simp only [h, ↓reduceIte]
        apply ih
        unfold delegusV03Verify at h
        simp only [beq_iff_eq] at h
        split at h
        · rename_i hcond
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
          exact hcond.2
        · cases h
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
        exact ih nonces spent h0

/-! ## 6. Theorem 3: Multi-Agent Sibling Collusion Breaks Per-Grant v0.3 Budgets;
        v0.4-draft Principal Exposure Pool (X/T8) Closes It Universally -/

theorem multi_agent_collusion_breaks_v03 :
    ∃ (orgCap : Nat) (g1 g2 g3 : DelegusGrant) (r1 r2 r3 : ExecRequest),
      g1.principal = g2.principal ∧ g2.principal = g3.principal ∧
      delegusV03Verify g1 [] 0 r1 = .allow ∧
      delegusV03Verify g2 [] 0 r2 = .allow ∧
      delegusV03Verify g3 [] 0 r3 = .allow ∧
      r1.action.amount + r2.action.amount + r3.action.amount > orgCap := by
  let mkGrant (gid aid : Nat) : DelegusGrant :=
    { grantId := gid, principal := 100, agentId := aid, allowedRp := 7,
      maxPerTx := 20000, grantTotalCap := 20000,
      validFrom := 0, validUntil := 1000, revoked := false, pinnedPolicy := 42 }
  let mkReq (gid aid n : Nat) : ExecRequest :=
    { principal := 100,
      agent := { agentId := aid, keyValid := true, policyDigest := 42 },
      grantId := gid, nonce := n, now := 500,
      action := { rp := 7, scope := .paymentsWrite, amount := 20000, actionHash := 200 + n,
                  provenance := .trustedPrincipal, phys := { required := false, nfcVerified := false },
                  highImpact := false },
      proofActionHash := 200 + n, gatewayClean := true,
      signet := { present := false, sealedActionHash := 0 } }
  exact ⟨40000, mkGrant 1 1, mkGrant 2 2, mkGrant 3 3,
         mkReq 1 1 1, mkReq 2 2 2, mkReq 3 3 3,
         rfl, rfl, by decide, by decide, by decide, by decide⟩

/-! ## 7. Theorem 4: Identity-Keyed Wire Contracts Are Blind to Self-Learning Policy Drift;
        Policy-Digest Pinning (H2) Blocks Unapproved Drift -/

theorem identity_protocols_blind_to_self_learning_drift
    (tok : OktaToken) (req : ExecRequest) (driftedDigest : PolicyDigest) :
    let reqDrifted : ExecRequest :=
      { req with agent := { req.agent with policyDigest := driftedDigest } }
    oktaVerify tok reqDrifted = oktaVerify tok req ∧
    cloudflareVerify reqDrifted = cloudflareVerify req := by
  constructor <;> rfl

theorem v04_blocks_self_learning_policy_drift
    (g : DelegusGrant) (st : V04State) (req : ExecRequest)
    (hdrift : req.agent.policyDigest ≠ g.pinnedPolicy) :
    delegusV04Verify g st req = .deny := by
  unfold delegusV04Verify
  have hbeq : (req.agent.policyDigest == g.pinnedPolicy) = false := beq_false_of_ne hdrift
  simp [hbeq]

/-! ## 8. Theorem 5: Tainted External Data Cannot Drive High-Impact Actions Without Hardware Signet (H3) -/

theorem v04_blocks_tainted_high_impact_without_signet
    (g : DelegusGrant) (st : V04State) (req : ExecRequest)
    (htaint : req.action.provenance = .untrustedExternal)
    (hhigh  : req.action.highImpact = true)
    (hallow : delegusV04Verify g st req = .allow) :
    req.signet.present = true ∧ req.signet.sealedActionHash = req.action.actionHash := by
  unfold delegusV04Verify at hallow
  simp only [htaint, hhigh, Bool.not_true, Bool.false_or] at hallow
  split at hallow
  · rename_i hcond
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    exact ⟨hcond.1.1.2.1, hcond.1.1.2.2⟩
  · cases hallow

/-! ## 9. Theorem 6: Monotonic Recursive Sub-Delegation Soundness (S1–S8) -/

structure DelegatedCap where
  maxAmount  : Nat
  validUntil : Timestamp
  revoked    : Bool
  deriving DecidableEq, Repr

def validHop (parent child : DelegatedCap) : Prop :=
  child.maxAmount <= parent.maxAmount ∧
  child.validUntil <= parent.validUntil ∧
  parent.revoked = false ∧
  child.revoked = false

def validChain : List DelegatedCap → Prop
  | [] => False
  | [root] => root.revoked = false
  | p :: c :: rest => validHop p c ∧ validChain (c :: rest)

theorem monotonic_delegation_no_amplification :
    ∀ (chain : List DelegatedCap) (root leaf : DelegatedCap),
      chain.head? = some root →
      chain.getLast? = some leaf →
      validChain chain →
      leaf.maxAmount <= root.maxAmount ∧
      leaf.validUntil <= root.validUntil ∧
      root.revoked = false ∧
      leaf.revoked = false := by
  intro chain
  induction chain with
  | nil =>
      intro _ _ hhead
      cases hhead
  | cons p tail ih =>
      intro root leaf hhead hlast hvalid
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      cases tail with
      | nil =>
          simp only [List.getLast?_singleton, Option.some.injEq] at hlast
          subst hlast
          exact ⟨Nat.le_refl _, Nat.le_refl _, hvalid, hvalid⟩
      | cons c rest =>
          rcases hvalid with ⟨⟨hamt, htime, hpr, _⟩, hrest⟩
          have hlast' : (c :: rest).getLast? = some leaf := by
            simpa [List.getLast?_cons_cons] using hlast
          have hsub := ih c leaf rfl hlast' hrest
          exact ⟨Nat.le_trans hsub.1 hamt, Nat.le_trans hsub.2.1 htime, hpr, hsub.2.2.2⟩

/-! ## 10. Theorem 7: Principal-Wide Exposure Pool Invariant (X/T8) & Physical Precondition (H4) -/

def runV04Trace : List (DelegusGrant × ExecRequest) → V04State → V04State
  | [], st => st
  | (g, r) :: rest, st => runV04Trace rest (stepV04 g st r)

theorem delegusV04Verify_allow_parts
    (g : DelegusGrant) (st : V04State) (req : ExecRequest)
    (h : delegusV04Verify g st req = .allow) :
    st.orgSpent + req.action.amount <= st.orgPoolCap ∧
    req.agent.policyDigest = g.pinnedPolicy ∧
    (!req.action.phys.required || req.action.phys.nfcVerified) = true := by
  unfold delegusV04Verify at h
  dsimp only at h
  by_cases hc :
      (delegusV03Verify g st.usedNonces (st.grantSpent g.grantId) req == .allow &&
       decide (st.orgSpent + req.action.amount ≤ st.orgPoolCap) &&
       (match req.action.provenance with
        | .trustedPrincipal => true
        | .untrustedExternal =>
            !req.action.highImpact ||
            (req.signet.present && req.signet.sealedActionHash == req.action.actionHash)) &&
       (req.agent.policyDigest == g.pinnedPolicy) &&
       (!req.action.phys.required || req.action.phys.nfcVerified)) = true
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    exact ⟨hc.1.1.1.2, hc.1.2, hc.2⟩
  · simp [hc] at h

theorem delegus_v04_master_pool_invariant
    (trace : List (DelegusGrant × ExecRequest)) (st0 : V04State)
    (h0 : st0.orgSpent <= st0.orgPoolCap) :
    (runV04Trace trace st0).orgSpent <= (runV04Trace trace st0).orgPoolCap := by
  induction trace generalizing st0 with
  | nil => exact h0
  | cons pair rest ih =>
      rcases pair with ⟨g, r⟩
      unfold runV04Trace
      apply ih
      unfold stepV04
      by_cases h : delegusV04Verify g st0 r == .allow
      · simp only [h, ↓reduceIte]
        exact (delegusV04Verify_allow_parts g st0 r (beq_iff_eq.mp h)).1
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
        exact h0

theorem v04_blocks_unverified_physical_reality
    (g : DelegusGrant) (st : V04State) (req : ExecRequest)
    (hreq : req.action.phys.required = true)
    (hallow : delegusV04Verify g st req = .allow) :
    req.action.phys.nfcVerified = true := by
  have hphys := (delegusV04Verify_allow_parts g st req hallow).2.2
  simpa [hreq] using hphys

/-! ## 11. Theorem 8 (Omission in Self-Attesting Receipts) & Theorem 9 (SoD Non-Collusion, H1) -/

structure SelfAuditState where
  chainIntact   : Bool
  recordedActs  : List ActionHash
  executedActs  : List ActionHash
  deriving DecidableEq, Repr

def compromisedAgentSkipCheck (s : SelfAuditState) (unauthorizedHash : ActionHash) : SelfAuditState :=
  { chainIntact  := s.chainIntact
    recordedActs := s.recordedActs
    executedActs := unauthorizedHash :: s.executedActs }

theorem self_verifier_omission_vulnerability :
    ∃ (s0 : SelfAuditState) (badAct : ActionHash),
      s0.chainIntact = true ∧
      let s1 := compromisedAgentSkipCheck s0 badAct
      s1.chainIntact = true ∧
      badAct ∈ s1.executedActs ∧
      badAct ∉ s1.recordedActs := by
  exact ⟨{ chainIntact := true, recordedActs := [], executedActs := [] }, 999,
         rfl, rfl, by decide, by decide⟩

def sodCheck (creatorAgent approverAgent creatorKey approverKey : Nat) : Decision :=
  if creatorAgent != approverAgent && creatorKey != approverKey then .allow else .deny

theorem v04_sod_blocks_self_approval
    (cA aA cK aK : Nat)
    (hallow : sodCheck cA aA cK aK = .allow) :
    cA ≠ aA ∧ cK ≠ aK := by
  unfold sodCheck at hallow
  by_cases hc : (cA != aA && cK != aK) = true
  · simp only [Bool.and_eq_true, bne_iff_ne] at hc
    exact hc
  · simp [hc] at hallow

end DelegusSecurityReview

/-! ## 12. Axiom Audit (Verify ZERO `sorryAx` and ZERO Custom Axioms) -/
#print axioms DelegusSecurityReview.okta_and_cloudflare_fail_semantic_fraud
#print axioms DelegusSecurityReview.smurfing_breaks_okta_cloudflare_and_v02
#print axioms DelegusSecurityReview.v03_preserves_single_grant_budget
#print axioms DelegusSecurityReview.multi_agent_collusion_breaks_v03
#print axioms DelegusSecurityReview.identity_protocols_blind_to_self_learning_drift
#print axioms DelegusSecurityReview.v04_blocks_self_learning_policy_drift
#print axioms DelegusSecurityReview.v04_blocks_tainted_high_impact_without_signet
#print axioms DelegusSecurityReview.monotonic_delegation_no_amplification
#print axioms DelegusSecurityReview.delegus_v04_master_pool_invariant
#print axioms DelegusSecurityReview.v04_blocks_unverified_physical_reality
#print axioms DelegusSecurityReview.self_verifier_omission_vulnerability
#print axioms DelegusSecurityReview.v04_sod_blocks_self_approval
