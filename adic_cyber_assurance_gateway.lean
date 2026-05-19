/-
ADIC Cyber Assurance Gateway - Lean 4 proof-oriented core.

This artifact models the authorization/evidence/replay core of the Python
reference implementation `adic_cyber_assurance_gateway.py`.

It intentionally does not prove real SHA-256 security, signature security,
wall-clock correctness, OS permissions, cloud IAM, or hardware isolation.
Those assumptions are isolated in `namespace TCB`.

The main point of this version is non-circularity:
`CommittedByLedger` is defined from ledger facts, entry validity, pre/post
links, state digests, and commit result.  It is not defined as witness
existence.  The main theorem constructs an `ADICWitness` from those facts.
-/

namespace ADIC

open Classical

abbrev Principal := String
abbrev Resource := String
abbrev Operation := String
abbrev Value := Nat
abbrev Time := Nat
abbrev Digest := String
abbrev Nonce := String
abbrev Role := String

inductive Risk where
  | low
  | medium
  | high
  | critical
  | blocked
  deriving Repr, DecidableEq

inductive Requirement where
  | none
  | operatorSignature
  | managerSignature
  | dualAndSecuritySignature
  | notApprovable
  deriving Repr, DecidableEq

inductive PermissionDelta where
  | noChange
  | readGrant
  | writeGrant
  | adminGrant
  deriving Repr, DecidableEq

inductive DeploymentDelta where
  | none
  | staging
  | production
  deriving Repr, DecidableEq

inductive PolicyDelta where
  | noChange
  | restrictsControl
  | neutral
  | weakensControl
  | disablesGateway
  deriving Repr, DecidableEq

inductive ModelDelta where
  | noChange
  | parameterChange
  | behaviorChange
  | highResponsibilityBehaviorChange
  deriving Repr, DecidableEq

inductive EvidenceDelta where
  | appendOnly
  | metadataAppend
  | rewrite
  | delete
  deriving Repr, DecidableEq

inductive EntryKind where
  | precommit
  | postcommit
  | rejected
  deriving Repr, DecidableEq

inductive CommitResult where
  | precommitted
  | committed
  | rejected
  | rejectedAfterPrecommit
  | incidentPostcheckFailed
  deriving Repr, DecidableEq

inductive Check where
  | identityCheck
  | authorityCheck
  | phiOverapproxCheck
  | protectedImpactCheck
  | riskClassCheck
  | approvalPolicyCheck
  | approvalValidityCheck
  | preStateDigestCheck
  | executionPathBoundCheck
  | ledgerPrecommitCheck
  deriving Repr, DecidableEq

namespace PermissionDelta
def rank : PermissionDelta -> Nat
  | noChange => 0
  | readGrant => 1
  | writeGrant => 2
  | adminGrant => 3
end PermissionDelta

namespace DeploymentDelta
def rank : DeploymentDelta -> Nat
  | none => 0
  | staging => 1
  | production => 2
end DeploymentDelta

namespace PolicyDelta
def rank : PolicyDelta -> Nat
  | noChange => 0
  | restrictsControl => 1
  | neutral => 2
  | weakensControl => 3
  | disablesGateway => 4
end PolicyDelta

namespace ModelDelta
def rank : ModelDelta -> Nat
  | noChange => 0
  | parameterChange => 1
  | behaviorChange => 2
  | highResponsibilityBehaviorChange => 3
end ModelDelta

namespace EvidenceDelta
def rank : EvidenceDelta -> Nat
  | appendOnly => 0
  | metadataAppend => 1
  | rewrite => 2
  | delete => 3
end EvidenceDelta

structure Flow where
  source : Resource
  destination : Resource
  dataClass : String
  deriving Repr

structure OperationRequest where
  cid : String
  actor : Principal
  operation : Operation
  target : Resource
  payloadDigest : Digest
  payloadValue : Value
  payloadPrincipal : Principal
  payloadDestination : Resource
  payloadDataClass : String
  payloadArtifact : Digest
  requestedBy : String
  aiGenerated : Bool
  deriving Repr

structure State where
  resourcePresent : Resource -> Bool
  resourceValue : Resource -> Value
  canWrite : Principal -> Resource -> Bool
  actorAuthority : Principal -> Operation -> Bool
  policyVersion : String
  gatewayEnabled : Bool
  usedNonce : Nonce -> Bool
  revokedApprovalId : String -> Bool

structure EffectBound where
  readSet : Resource -> Prop
  writeSet : Resource -> Prop
  deleteSet : Resource -> Prop
  permissionDelta : PermissionDelta
  secretFlow : Resource -> Prop
  externalFlow : Flow -> Prop
  deploymentDelta : DeploymentDelta
  policyDelta : PolicyDelta
  modelDelta : ModelDelta
  evidenceDelta : EvidenceDelta

structure Approval where
  approvalId : String
  subjectDigest : Digest
  approvedOperation : Operation
  approvedTarget : Resource
  approvedRiskClass : Risk
  approvedPreStateDigest : Digest
  approvedPolicyVersion : String
  approverRole : Role
  issuedAt : Time
  expiresAt : Time
  nonce : Nonce
  deriving Repr

structure ApprovalSubject where
  subjectDigest : Digest
  operation : Operation
  target : Resource
  operationDigest : Digest
  preStateDigest : Digest
  policyVersion : String
  phiDigest : Digest
  riskClass : Risk
  approvalRequirement : Requirement
  obligationDigest : Digest
  deriving Repr

structure DecisionPackage where
  jid : Digest
  subjectDigest : Digest
  actor : Principal
  operation : Operation
  target : Resource
  payloadDigest : Digest
  preStateDigest : Digest
  policyVersion : String
  phiDigest : Digest
  riskClass : Risk
  approvalRequirement : Requirement
  approvalDigest : Digest
  obligationDigest : Digest
  timestamp : Time
  deriving Repr

structure VerificationObligations where
  requires : Check -> Prop

def defaultObligations : VerificationObligations :=
  { requires := fun _ => True }

structure LedgerEntry where
  index : Nat
  kind : EntryKind
  previousHash : Digest
  precommitHash : Option Digest
  operationDigest : Digest
  decisionDigest : Digest
  phiDigest : Digest
  obligationsDigest : Digest
  approvalDigest : Digest
  preStateDigest : Digest
  postStateDigest : Digest
  diffDigest : Digest
  result : CommitResult
  timestamp : Time
  entryHash : Digest
  deriving Repr

structure LedgerEntryBody where
  index : Nat
  kind : EntryKind
  previousHash : Digest
  precommitHash : Option Digest
  operationDigest : Digest
  decisionDigest : Digest
  phiDigest : Digest
  obligationsDigest : Digest
  approvalDigest : Digest
  preStateDigest : Digest
  postStateDigest : Digest
  diffDigest : Digest
  result : CommitResult
  timestamp : Time
  deriving Repr

def LedgerEntry.body (entry : LedgerEntry) : LedgerEntryBody :=
  { index := entry.index,
    kind := entry.kind,
    previousHash := entry.previousHash,
    precommitHash := entry.precommitHash,
    operationDigest := entry.operationDigest,
    decisionDigest := entry.decisionDigest,
    phiDigest := entry.phiDigest,
    obligationsDigest := entry.obligationsDigest,
    approvalDigest := entry.approvalDigest,
    preStateDigest := entry.preStateDigest,
    postStateDigest := entry.postStateDigest,
    diffDigest := entry.diffDigest,
    result := entry.result,
    timestamp := entry.timestamp }

structure EvidenceRecord where
  operation : OperationRequest
  subject : ApprovalSubject
  decision : DecisionPackage
  phi : EffectBound
  obligations : VerificationObligations
  approval : Option Approval
  preStateDigest : Digest
  postStateDigest : Digest
  result : CommitResult

structure Ledger where
  contains : LedgerEntry -> Prop
  evidenceOf : LedgerEntry -> EvidenceRecord -> Prop
  before : LedgerEntry -> LedgerEntry -> Prop
  genesisHash : Digest

namespace TCB

axiom digest_state : State -> Digest
axiom digest_operation : OperationRequest -> Digest
axiom digest_phi : EffectBound -> Digest
axiom digest_decision : DecisionPackage -> Digest
axiom digest_approval : Option Approval -> Digest
axiom digest_obligations : VerificationObligations -> Digest
axiom digest_entry_body : LedgerEntryBody -> Digest
axiom signature_valid : Approval -> Prop
axiom time_valid : Approval -> Time -> Prop

noncomputable def digest_entry (entry : LedgerEntry) : Digest :=
  digest_entry_body entry.body

end TCB

structure TCBAssumptionProfile : Prop where
  stateDigestCollisionFreeOnCommitted :
    forall {s t : State}, TCB.digest_state s = TCB.digest_state t -> s = t
  operationDigestCollisionFreeOnCommitted :
    forall {a b : OperationRequest}, TCB.digest_operation a = TCB.digest_operation b -> a = b
  entryDigestCollisionFreeOnCommitted :
    forall {a b : LedgerEntry}, TCB.digest_entry a = TCB.digest_entry b -> a = b

def IsProtected (r : Resource) : Prop :=
  r.startsWith "secret:" = true \/
  r.startsWith "prod_data:" = true \/
  r.startsWith "access:" = true \/
  r.startsWith "admin:" = true \/
  r.startsWith "deploy:" = true \/
  r.startsWith "model_policy:" = true \/
  r.startsWith "audit:" = true \/
  r.startsWith "ledger:" = true \/
  r.startsWith "external_route:" = true \/
  r.startsWith "high_responsibility:" = true

def EmptyEffectBound : EffectBound :=
  { readSet := fun _ => False,
    writeSet := fun _ => False,
    deleteSet := fun _ => False,
    permissionDelta := PermissionDelta.noChange,
    secretFlow := fun _ => False,
    externalFlow := fun _ => False,
    deploymentDelta := DeploymentDelta.none,
    policyDelta := PolicyDelta.noChange,
    modelDelta := ModelDelta.noChange,
    evidenceDelta := EvidenceDelta.appendOnly }

def WriteResource (s : State) (target : Resource) (value : Value) : State :=
  { s with
    resourcePresent := fun r => if r = target then true else s.resourcePresent r,
    resourceValue := fun r => if r = target then value else s.resourceValue r }

def DeleteResource (s : State) (target : Resource) : State :=
  { s with
    resourcePresent := fun r => if r = target then false else s.resourcePresent r }

def GrantWrite (s : State) (principal : Principal) (target : Resource) : State :=
  { s with
    canWrite := fun p r =>
      if p = principal then
        if r = target then true else s.canWrite p r
      else s.canWrite p r }

def DisableGateway (s : State) : State :=
  { s with gatewayEnabled := false }

def DeployArtifact (s : State) (target : Resource) (_artifact : Digest) : State :=
  WriteResource s target 1

def ExternalRouteKey (destination : Resource) : Resource :=
  "external_route:" ++ destination

def ExportExternal (s : State) (c : OperationRequest) : State :=
  WriteResource s (ExternalRouteKey c.payloadDestination) 1

def Diff (before after : State) : EffectBound :=
  { EmptyEffectBound with
    writeSet := fun r =>
      after.resourcePresent r = true /\
      (before.resourcePresent r = false \/
       Not (before.resourceValue r = after.resourceValue r)),
    deleteSet := fun r =>
      before.resourcePresent r = true /\ after.resourcePresent r = false }

def Sem (c : OperationRequest) (before after : State) : Prop :=
  (c.operation = "write_resource" /\
    after = WriteResource before c.target c.payloadValue) \/
  (c.operation = "read_resource" /\ after = before) \/
  (c.operation = "export_external" /\
    after = ExportExternal before c) \/
  (c.operation = "delete_resource" /\
    after = DeleteResource before c.target) \/
  (c.operation = "grant_write" /\
    after = GrantWrite before c.payloadPrincipal c.target) \/
  (c.operation = "deploy" /\
    after = DeployArtifact before c.target c.payloadArtifact) \/
  (c.operation = "disable_gateway" /\
    after = DisableGateway before)

theorem sem_unknown_operation_is_false
    (c : OperationRequest) (before after : State)
    (h : Sem c before after)
    (hunknown :
      c.operation ≠ "write_resource" /\
      c.operation ≠ "read_resource" /\
      c.operation ≠ "export_external" /\
      c.operation ≠ "delete_resource" /\
      c.operation ≠ "grant_write" /\
      c.operation ≠ "deploy" /\
      c.operation ≠ "disable_gateway") : False := by
  unfold Sem at h
  rcases hunknown with ⟨hw, hr, he, hd, hg, hp, hdis⟩
  rcases h with h | h | h | h | h | h | h
  · exact hw h.left
  · exact hr h.left
  · exact he h.left
  · exact hd h.left
  · exact hg h.left
  · exact hp h.left
  · exact hdis h.left

def PermissionEffect (c : OperationRequest) : PermissionDelta :=
  if c.operation = "grant_write" then
    if c.target.startsWith "admin:" then PermissionDelta.adminGrant
    else PermissionDelta.writeGrant
  else PermissionDelta.noChange

def DeploymentEffect (c : OperationRequest) : DeploymentDelta :=
  if c.operation = "deploy" then
    if c.target.startsWith "deploy:prod" then DeploymentDelta.production
    else DeploymentDelta.staging
  else DeploymentDelta.none

def PolicyEffect (c : OperationRequest) : PolicyDelta :=
  if c.operation = "disable_gateway" then PolicyDelta.disablesGateway
  else if
      (c.operation == "write_resource" || c.operation == "grant_write") &&
        (c.target.startsWith "model_policy:" || c.target.startsWith "access:") then
    PolicyDelta.weakensControl
  else PolicyDelta.noChange

def ModelEffect (c : OperationRequest) : ModelDelta :=
  if
      (c.operation == "write_resource" || c.operation == "deploy") &&
        c.target.startsWith "high_responsibility:" then
    ModelDelta.highResponsibilityBehaviorChange
  else if
      (c.operation == "write_resource" || c.operation == "deploy") &&
        c.target.startsWith "model_policy:" then
    ModelDelta.behaviorChange
  else ModelDelta.noChange

def IsEvidenceResource (r : Resource) : Bool :=
  r.startsWith "ledger:" || r.startsWith "audit:"

def EvidenceEffect (c : OperationRequest) : EvidenceDelta :=
  if (c.operation == "delete_resource") && IsEvidenceResource c.target then
    EvidenceDelta.delete
  else if (c.operation == "write_resource") && IsEvidenceResource c.target then
    EvidenceDelta.rewrite
  else EvidenceDelta.appendOnly

def Eff (c : OperationRequest) (before after : State) : EffectBound :=
  let base := Diff before after
  { base with
    readSet := fun r =>
      base.readSet r \/
      ((c.operation = "read_resource" \/ c.operation = "export_external") /\
        before.resourcePresent c.target = true /\
        r = c.target),
    permissionDelta := PermissionEffect c,
    secretFlow := fun r =>
      base.secretFlow r \/
      (c.operation = "export_external" /\
        c.target.startsWith "secret:" = true /\ r = c.target),
    externalFlow := fun f =>
      base.externalFlow f \/
      (c.operation = "export_external" /\
        f.source = c.target /\
        f.destination = c.payloadDestination /\
        f.dataClass = c.payloadDataClass),
    deploymentDelta := DeploymentEffect c,
    policyDelta := PolicyEffect c,
    modelDelta := ModelEffect c,
    evidenceDelta := EvidenceEffect c }

def SetLe (a b : Resource -> Prop) : Prop :=
  forall r, a r -> b r

def FlowSetLe (a b : Flow -> Prop) : Prop :=
  forall f, a f -> b f

def EffectLe (actual phi : EffectBound) : Prop :=
  SetLe actual.readSet phi.readSet /\
  SetLe actual.writeSet phi.writeSet /\
  SetLe actual.deleteSet phi.deleteSet /\
  actual.permissionDelta.rank <= phi.permissionDelta.rank /\
  SetLe actual.secretFlow phi.secretFlow /\
  FlowSetLe actual.externalFlow phi.externalFlow /\
  actual.deploymentDelta.rank <= phi.deploymentDelta.rank /\
  actual.policyDelta.rank <= phi.policyDelta.rank /\
  actual.modelDelta.rank <= phi.modelDelta.rank /\
  actual.evidenceDelta.rank <= phi.evidenceDelta.rank

infix:50 " <=e " => EffectLe

def PhiOverApprox (c : OperationRequest) (s : State) (phi : EffectBound) : Prop :=
  forall s', Sem c s s' -> Eff c s s' <=e phi

def ProtectedChanged (before after : State) : Prop :=
  exists r : Resource,
    IsProtected r /\
    (Not (before.resourcePresent r = after.resourcePresent r) \/
     Not (before.resourceValue r = after.resourceValue r))

def IdentityValid (actor : Principal) : Prop :=
  Not (actor = "")

def AuthorityAllows (c : OperationRequest) (s : State) : Prop :=
  s.actorAuthority c.actor c.operation = true

def ExecutionPathBound (s : State) : Prop :=
  s.gatewayEnabled = true /\
  forall principal resource,
    s.canWrite principal resource = true ->
    IsProtected resource ->
    principal = "ADIC_Gateway_Principal"

def HasResource (set : Resource -> Prop) (p : Resource -> Prop) : Prop :=
  exists r, set r /\ p r

def HasAnyResource (set : Resource -> Prop) : Prop :=
  exists r, set r

def HasAnyFlow (set : Flow -> Prop) : Prop :=
  exists f, set f

def ProtectedImpact (phi : EffectBound) : Prop :=
  HasResource phi.readSet IsProtected \/
  HasResource phi.writeSet IsProtected \/
  HasResource phi.deleteSet IsProtected \/
  PermissionDelta.writeGrant.rank <= phi.permissionDelta.rank \/
  HasAnyResource phi.secretFlow \/
  HasAnyFlow phi.externalFlow \/
  DeploymentDelta.production.rank <= phi.deploymentDelta.rank \/
  PolicyDelta.weakensControl.rank <= phi.policyDelta.rank \/
  ModelDelta.behaviorChange.rank <= phi.modelDelta.rank \/
  EvidenceDelta.rewrite.rank <= phi.evidenceDelta.rank

def BlockedImpact (phi : EffectBound) : Prop :=
  PolicyDelta.disablesGateway.rank <= phi.policyDelta.rank \/
  EvidenceDelta.delete.rank <= phi.evidenceDelta.rank

def CriticalImpact (phi : EffectBound) : Prop :=
  PermissionDelta.adminGrant.rank <= phi.permissionDelta.rank \/
  HasResource phi.readSet (fun r =>
    r.startsWith "secret:" = true \/ r.startsWith "prod_data:" = true) \/
  HasResource phi.deleteSet (fun r => r.startsWith "prod_data:" = true) \/
  HasAnyResource phi.secretFlow \/
  DeploymentDelta.production.rank <= phi.deploymentDelta.rank \/
  ModelDelta.highResponsibilityBehaviorChange.rank <= phi.modelDelta.rank \/
  HasAnyFlow phi.externalFlow

def HighImpact (phi : EffectBound) : Prop :=
  HasResource phi.writeSet (fun r =>
    r.startsWith "access:" = true \/ r.startsWith "model_policy:" = true) \/
  HasResource phi.readSet IsProtected \/
  PermissionDelta.writeGrant.rank <= phi.permissionDelta.rank

noncomputable def RiskClass (c : OperationRequest) (s : State) (phi : EffectBound) : Risk :=
  if _hphi : Not (PhiOverApprox c s phi) then Risk.blocked
  else if _hauth : s.actorAuthority c.actor c.operation = false then Risk.blocked
  else if _blockedImpact : BlockedImpact phi then Risk.blocked
  else if _hcritical : CriticalImpact phi then Risk.critical
  else if _hhigh : HighImpact phi then Risk.high
  else if _hmedium : ProtectedImpact phi then Risk.medium
  else Risk.low

def ApprovalPolicy : Risk -> Requirement
  | Risk.low => Requirement.none
  | Risk.medium => Requirement.operatorSignature
  | Risk.high => Requirement.managerSignature
  | Risk.critical => Requirement.dualAndSecuritySignature
  | Risk.blocked => Requirement.notApprovable

def RoleSatisfies (role : Role) (req : Requirement) : Prop :=
  match req with
  | Requirement.none => True
  | Requirement.operatorSignature =>
      role = "operator" \/ role = "manager" \/ role = "security" \/ role = "dual_security"
  | Requirement.managerSignature =>
      role = "manager" \/ role = "security" \/ role = "dual_security"
  | Requirement.dualAndSecuritySignature =>
      role = "dual_security"
  | Requirement.notApprovable => False

def ApprovalValid
    (approval : Option Approval)
    (subject : ApprovalSubject)
    (s : State)
    (atTime : Time) : Prop :=
  match subject.approvalRequirement with
  | Requirement.none => True
  | Requirement.notApprovable => False
  | req =>
      match approval with
      | none => False
      | some u =>
          s.revokedApprovalId u.approvalId = false /\
          s.usedNonce u.nonce = false /\
          u.subjectDigest = subject.subjectDigest /\
          u.approvedOperation = subject.operation /\
          u.approvedTarget = subject.target /\
          u.approvedRiskClass = subject.riskClass /\
          u.approvedPreStateDigest = TCB.digest_state s /\
          u.approvedPolicyVersion = s.policyVersion /\
          TCB.signature_valid u /\
          RoleSatisfies u.approverRole req /\
          TCB.time_valid u atTime

def ApprovalValidForRecord (record : EvidenceRecord) (s : State) (atTime : Time) : Prop :=
  ApprovalValid record.approval record.subject s atTime

noncomputable def SubjectFor
    (c : OperationRequest)
    (s : State)
    (phi : EffectBound)
    (obligations : VerificationObligations)
    (subjectDigest : Digest) : ApprovalSubject :=
  { subjectDigest := subjectDigest,
    operation := c.operation,
    target := c.target,
    operationDigest := TCB.digest_operation c,
    preStateDigest := TCB.digest_state s,
    policyVersion := s.policyVersion,
    phiDigest := TCB.digest_phi phi,
    riskClass := RiskClass c s phi,
    approvalRequirement := ApprovalPolicy (RiskClass c s phi),
    obligationDigest := TCB.digest_obligations obligations }

def ApprovalPolicyValidAt
    (c : OperationRequest)
    (s : State)
    (phi : EffectBound)
    (approval : Option Approval)
    (obligations : VerificationObligations)
    (subjectDigest : Digest)
    (atTime : Time) : Prop :=
  let subject := SubjectFor c s phi obligations subjectDigest
  ApprovalValid approval subject s atTime

def AllowCore
    (c : OperationRequest)
    (s : State)
    (phi : EffectBound)
    (approval : Option Approval)
    (obligations : VerificationObligations)
    (subjectDigest : Digest)
    (atTime : Time) : Prop :=
  IdentityValid c.actor /\
  AuthorityAllows c s /\
  PhiOverApprox c s phi /\
  Not (RiskClass c s phi = Risk.blocked) /\
  ApprovalPolicyValidAt c s phi approval obligations subjectDigest atTime /\
  ExecutionPathBound s

def IsPreCommit (entry : LedgerEntry) : Prop :=
  entry.kind = EntryKind.precommit

def IsPostCommit (entry : LedgerEntry) : Prop :=
  entry.kind = EntryKind.postcommit

def PreCommitMatches
    (pre : LedgerEntry)
    (c : OperationRequest)
    (s : State)
    (phi : EffectBound)
    (approval : Option Approval) : Prop :=
  pre.operationDigest = TCB.digest_operation c /\
  pre.phiDigest = TCB.digest_phi phi /\
  pre.approvalDigest = TCB.digest_approval approval /\
  pre.preStateDigest = TCB.digest_state s /\
  pre.result = CommitResult.precommitted

def PrePostSameDecision
    (pre post : LedgerEntry) : Prop :=
  pre.operationDigest = post.operationDigest /\
  pre.phiDigest = post.phiDigest /\
  pre.obligationsDigest = post.obligationsDigest /\
  pre.approvalDigest = post.approvalDigest /\
  pre.preStateDigest = post.preStateDigest

def Allow
    (c : OperationRequest)
    (s : State)
    (phi : EffectBound)
    (approval : Option Approval)
    (obligations : VerificationObligations)
    (subjectDigest : Digest)
    (atTime : Time)
    (pre : LedgerEntry) : Prop :=
  AllowCore c s phi approval obligations subjectDigest atTime /\
  IsPreCommit pre /\
  PreCommitMatches pre c s phi approval

def ObligationCover (v : VerificationObligations) : Prop :=
  v.requires Check.identityCheck /\
  v.requires Check.authorityCheck /\
  v.requires Check.phiOverapproxCheck /\
  v.requires Check.protectedImpactCheck /\
  v.requires Check.riskClassCheck /\
  v.requires Check.approvalPolicyCheck /\
  v.requires Check.approvalValidityCheck /\
  v.requires Check.preStateDigestCheck /\
  v.requires Check.executionPathBoundCheck /\
  v.requires Check.ledgerPrecommitCheck

def SubjectValidForRecord (record : EvidenceRecord) (before : State) : Prop :=
  record.subject.operation = record.operation.operation /\
  record.subject.target = record.operation.target /\
  record.subject.operationDigest = TCB.digest_operation record.operation /\
  record.subject.preStateDigest = TCB.digest_state before /\
  record.subject.policyVersion = before.policyVersion /\
  record.subject.phiDigest = TCB.digest_phi record.phi /\
  record.subject.riskClass = RiskClass record.operation before record.phi /\
  record.subject.approvalRequirement =
    ApprovalPolicy (RiskClass record.operation before record.phi) /\
  record.subject.obligationDigest = TCB.digest_obligations record.obligations

def DecisionPackageValidForRecord (record : EvidenceRecord) (before : State) : Prop :=
  record.decision.subjectDigest = record.subject.subjectDigest /\
  record.decision.actor = record.operation.actor /\
  record.decision.operation = record.operation.operation /\
  record.decision.target = record.operation.target /\
  record.decision.payloadDigest = record.operation.payloadDigest /\
  record.decision.preStateDigest = TCB.digest_state before /\
  record.decision.policyVersion = before.policyVersion /\
  record.decision.phiDigest = TCB.digest_phi record.phi /\
  record.decision.riskClass = RiskClass record.operation before record.phi /\
  record.decision.approvalRequirement = ApprovalPolicy record.decision.riskClass /\
  record.decision.approvalDigest = TCB.digest_approval record.approval /\
  record.decision.obligationDigest = TCB.digest_obligations record.obligations

def VerificationValidForRecord (record : EvidenceRecord) (before : State) (_atTime : Time) : Prop :=
  ObligationCover record.obligations /\
  SubjectValidForRecord record before /\
  DecisionPackageValidForRecord record before

def EntryValid (entry : LedgerEntry) (record : EvidenceRecord) : Prop :=
  entry.operationDigest = TCB.digest_operation record.operation /\
  entry.decisionDigest = TCB.digest_decision record.decision /\
  entry.phiDigest = TCB.digest_phi record.phi /\
  entry.obligationsDigest = TCB.digest_obligations record.obligations /\
  entry.approvalDigest = TCB.digest_approval record.approval /\
  entry.preStateDigest = record.preStateDigest /\
  entry.postStateDigest = record.postStateDigest /\
  entry.result = record.result

def EntryHashValid (entry : LedgerEntry) : Prop :=
  entry.entryHash = TCB.digest_entry entry

def LedgerValid (ledger : Ledger) : Prop :=
  (forall entry,
    ledger.contains entry ->
    EntryHashValid entry /\
    (exists record, ledger.evidenceOf entry record /\ EntryValid entry record) /\
    (entry.index = 0 \/
      exists previous,
        ledger.contains previous /\
        ledger.before previous entry /\
        entry.previousHash = previous.entryHash /\
        previous.index < entry.index)) /\
  (forall previous entry,
    ledger.before previous entry ->
    ledger.contains previous /\
    ledger.contains entry /\
    previous.index < entry.index /\
    entry.previousHash = previous.entryHash)

def CommittedByLedger
    (before after : State)
    (ledger : Ledger)
    (pre post : LedgerEntry)
    (preRecord record : EvidenceRecord) : Prop :=
  LedgerValid ledger /\
  ledger.contains pre /\
  ledger.contains post /\
  ledger.evidenceOf pre preRecord /\
  ledger.evidenceOf post record /\
  IsPreCommit pre /\
  IsPostCommit post /\
  post.result = CommitResult.committed /\
  pre.index < post.index /\
  post.precommitHash = some pre.entryHash /\
  PrePostSameDecision pre post /\
  EntryValid pre preRecord /\
  EntryValid post record /\
  post.preStateDigest = TCB.digest_state before /\
  post.postStateDigest = TCB.digest_state after /\
  record.preStateDigest = TCB.digest_state before /\
  record.postStateDigest = TCB.digest_state after /\
  record.result = CommitResult.committed /\
  post.phiDigest = TCB.digest_phi record.phi /\
  post.decisionDigest = TCB.digest_decision record.decision /\
  post.operationDigest = TCB.digest_operation record.operation /\
  SubjectValidForRecord record before /\
  DecisionPackageValidForRecord record before /\
  VerificationValidForRecord record before post.timestamp /\
  Sem record.operation before after /\
  PhiOverApprox record.operation before record.phi /\
  Eff record.operation before after <=e record.phi /\
  ApprovalValidForRecord record before post.timestamp /\
  ExecutionPathBound before

namespace NonVacuity

def concreteBefore : State :=
  { resourcePresent := fun _ => false,
    resourceValue := fun _ => 0,
    canWrite := fun _ _ => false,
    actorAuthority := fun actor op =>
      (actor == "alice") && (op == "read_resource"),
    policyVersion := "v1",
    gatewayEnabled := true,
    usedNonce := fun _ => false,
    revokedApprovalId := fun _ => false }

def concreteOperation : OperationRequest :=
  { cid := "cid:demo",
    actor := "alice",
    operation := "read_resource",
    target := "public:demo",
    payloadDigest := "payload:demo",
    payloadValue := 0,
    payloadPrincipal := "",
    payloadDestination := "",
    payloadDataClass := "",
    payloadArtifact := "",
    requestedBy := "alice",
    aiGenerated := false }

def concreteAfter : State :=
  concreteBefore

def concretePhi : EffectBound :=
  EmptyEffectBound

def concreteObligations : VerificationObligations :=
  defaultObligations

noncomputable def concreteSubject : ApprovalSubject :=
  SubjectFor concreteOperation concreteBefore concretePhi concreteObligations
    "subject:demo"

noncomputable def concreteDecision : DecisionPackage :=
  { jid := "decision:demo",
    subjectDigest := concreteSubject.subjectDigest,
    actor := concreteOperation.actor,
    operation := concreteOperation.operation,
    target := concreteOperation.target,
    payloadDigest := concreteOperation.payloadDigest,
    preStateDigest := TCB.digest_state concreteBefore,
    policyVersion := concreteBefore.policyVersion,
    phiDigest := TCB.digest_phi concretePhi,
    riskClass := RiskClass concreteOperation concreteBefore concretePhi,
    approvalRequirement :=
      ApprovalPolicy (RiskClass concreteOperation concreteBefore concretePhi),
    approvalDigest := TCB.digest_approval none,
    obligationDigest := TCB.digest_obligations concreteObligations,
    timestamp := 1 }

noncomputable def concreteRecord : EvidenceRecord :=
  { operation := concreteOperation,
    subject := concreteSubject,
    decision := concreteDecision,
    phi := concretePhi,
    obligations := concreteObligations,
    approval := none,
    preStateDigest := TCB.digest_state concreteBefore,
    postStateDigest := TCB.digest_state concreteAfter,
    result := CommitResult.committed }

noncomputable def concretePreRecord : EvidenceRecord :=
  { concreteRecord with result := CommitResult.precommitted }

noncomputable def mkLedgerEntry (body : LedgerEntryBody) : LedgerEntry :=
  { index := body.index,
    kind := body.kind,
    previousHash := body.previousHash,
    precommitHash := body.precommitHash,
    operationDigest := body.operationDigest,
    decisionDigest := body.decisionDigest,
    phiDigest := body.phiDigest,
    obligationsDigest := body.obligationsDigest,
    approvalDigest := body.approvalDigest,
    preStateDigest := body.preStateDigest,
    postStateDigest := body.postStateDigest,
    diffDigest := body.diffDigest,
    result := body.result,
    timestamp := body.timestamp,
    entryHash := TCB.digest_entry_body body }

theorem mkLedgerEntry_hash_valid (body : LedgerEntryBody) :
    EntryHashValid (mkLedgerEntry body) := by
  rfl

noncomputable def concretePreEntryBody : LedgerEntryBody :=
  { index := 0,
    kind := EntryKind.precommit,
    previousHash := "genesis",
    precommitHash := none,
    operationDigest := TCB.digest_operation concreteOperation,
    decisionDigest := TCB.digest_decision concretePreRecord.decision,
    phiDigest := TCB.digest_phi concretePreRecord.phi,
    obligationsDigest := TCB.digest_obligations concretePreRecord.obligations,
    approvalDigest := TCB.digest_approval concretePreRecord.approval,
    preStateDigest := concretePreRecord.preStateDigest,
    postStateDigest := concretePreRecord.postStateDigest,
    diffDigest := "",
    result := CommitResult.precommitted,
    timestamp := 0 }

noncomputable def concretePreEntry : LedgerEntry :=
  mkLedgerEntry concretePreEntryBody

noncomputable def concretePostEntryBody : LedgerEntryBody :=
  { index := 1,
    kind := EntryKind.postcommit,
    previousHash := concretePreEntry.entryHash,
    precommitHash := some concretePreEntry.entryHash,
    operationDigest := TCB.digest_operation concreteOperation,
    decisionDigest := TCB.digest_decision concreteRecord.decision,
    phiDigest := TCB.digest_phi concreteRecord.phi,
    obligationsDigest := TCB.digest_obligations concreteRecord.obligations,
    approvalDigest := TCB.digest_approval concreteRecord.approval,
    preStateDigest := concreteRecord.preStateDigest,
    postStateDigest := concreteRecord.postStateDigest,
    diffDigest := "",
    result := CommitResult.committed,
    timestamp := 1 }

noncomputable def concretePostEntry : LedgerEntry :=
  mkLedgerEntry concretePostEntryBody

noncomputable def concreteLedger : Ledger :=
  { contains := fun entry =>
      entry = concretePreEntry \/ entry = concretePostEntry,
    evidenceOf := fun entry record =>
      (entry = concretePreEntry /\ record = concretePreRecord) \/
      (entry = concretePostEntry /\ record = concreteRecord),
    before := fun previous entry =>
      previous = concretePreEntry /\ entry = concretePostEntry,
    genesisHash := "genesis" }

theorem concrete_sem :
    Sem concreteOperation concreteBefore concreteAfter := by
  unfold concreteAfter Sem
  simp [concreteOperation]

theorem effect_le_refl (phi : EffectBound) :
    phi <=e phi := by
  exact
    ⟨ (fun _ h => h),
      (fun _ h => h),
      (fun _ h => h),
      Nat.le_refl _,
      (fun _ h => h),
      (fun _ h => h),
      Nat.le_refl _,
      Nat.le_refl _,
      Nat.le_refl _,
      Nat.le_refl _ ⟩

theorem concrete_phi_overapprox :
    PhiOverApprox concreteOperation concreteBefore concretePhi := by
  intro s' hsem
  unfold Sem at hsem
  simp [concreteOperation] at hsem
  subst s'
  unfold EffectLe SetLe FlowSetLe Eff Diff concretePhi concreteBefore
    EmptyEffectBound
  exact
    ⟨ (by
        intro r h
        simp [concreteOperation] at h),
      (by
        intro r h
        simp at h),
      (by
        intro r h
        simp at h),
      (by decide),
      (by
        intro r h
        simp [concreteOperation] at h),
      (by
        intro f h
        simp [concreteOperation] at h),
      (by decide),
      (by decide),
      (by decide),
      (by decide) ⟩

theorem concrete_not_blocked_impact :
    Not (BlockedImpact concretePhi) := by
  unfold BlockedImpact concretePhi EmptyEffectBound
  decide

theorem concrete_not_critical_impact :
    Not (CriticalImpact concretePhi) := by
  unfold CriticalImpact HasResource HasAnyResource HasAnyFlow concretePhi
    EmptyEffectBound
  intro h
  rcases h with h | h | h | h | h | h | h
  · have hnot : Not (PermissionDelta.adminGrant.rank <=
        PermissionDelta.noChange.rank) := by decide
    exact hnot h
  · rcases h with ⟨r, hr, hsecret⟩
    cases hr
  · rcases h with ⟨r, hr, _hdelete⟩
    simp at hr
  · simp at h
  · have hnot : Not (DeploymentDelta.production.rank <=
        DeploymentDelta.none.rank) := by decide
    exact hnot h
  · have hnot : Not (ModelDelta.highResponsibilityBehaviorChange.rank <=
        ModelDelta.noChange.rank) := by decide
    exact hnot h
  · simp at h

theorem concrete_not_high_impact :
    Not (HighImpact concretePhi) := by
  unfold HighImpact HasResource concretePhi EmptyEffectBound
  intro h
  rcases h with h | h | h
  · rcases h with ⟨r, hr, _hwrite⟩
    simp at hr
  · rcases h with ⟨r, hr, hprotected⟩
    cases hr
  · have hnot : Not (PermissionDelta.writeGrant.rank <=
        PermissionDelta.noChange.rank) := by decide
    exact hnot h

theorem concrete_not_protected_impact :
    Not (ProtectedImpact concretePhi) := by
  unfold ProtectedImpact HasResource HasAnyResource HasAnyFlow concretePhi
    EmptyEffectBound
  intro h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · rcases h with ⟨r, hr, hprotected⟩
    cases hr
  · rcases h with ⟨r, hr, _hwrite⟩
    simp at hr
  · rcases h with ⟨r, hr, _hdelete⟩
    simp at hr
  · have hnot : Not (PermissionDelta.writeGrant.rank <=
        PermissionDelta.noChange.rank) := by decide
    exact hnot h
  · rcases h with ⟨r, hr⟩
    simp at hr
  · rcases h with ⟨f, hf⟩
    simp at hf
  · have hnot : Not (DeploymentDelta.production.rank <=
        DeploymentDelta.none.rank) := by decide
    exact hnot h
  · have hnot : Not (PolicyDelta.weakensControl.rank <=
        PolicyDelta.noChange.rank) := by decide
    exact hnot h
  · have hnot : Not (ModelDelta.behaviorChange.rank <=
        ModelDelta.noChange.rank) := by decide
    exact hnot h
  · have hnot : Not (EvidenceDelta.rewrite.rank <=
        EvidenceDelta.appendOnly.rank) := by decide
    exact hnot h

theorem concrete_risk_low :
    RiskClass concreteOperation concreteBefore concretePhi = Risk.low := by
  unfold RiskClass
  rw [dif_neg (by
    intro h
    exact h concrete_phi_overapprox)]
  rw [dif_neg (by decide)]
  rw [dif_neg concrete_not_blocked_impact]
  rw [dif_neg concrete_not_critical_impact]
  rw [dif_neg concrete_not_high_impact]
  rw [dif_neg concrete_not_protected_impact]

theorem concrete_approval_valid :
    ApprovalValidForRecord concreteRecord concreteBefore concretePostEntry.timestamp := by
  unfold ApprovalValidForRecord ApprovalValid concreteRecord concreteSubject SubjectFor
  simp [concrete_risk_low, ApprovalPolicy]

theorem concrete_subject_valid :
    SubjectValidForRecord concreteRecord concreteBefore := by
  unfold SubjectValidForRecord concreteRecord concreteSubject SubjectFor
  simp [concrete_risk_low]

theorem concrete_decision_valid :
    DecisionPackageValidForRecord concreteRecord concreteBefore := by
  unfold DecisionPackageValidForRecord concreteRecord concreteDecision
  simp [concrete_risk_low]

theorem concrete_verification_valid :
    VerificationValidForRecord concreteRecord concreteBefore concretePostEntry.timestamp := by
  unfold VerificationValidForRecord ObligationCover
  exact
    ⟨ by simp [concreteRecord, concreteObligations, defaultObligations],
      concrete_subject_valid,
      concrete_decision_valid ⟩

theorem concrete_execution_path_bound :
    ExecutionPathBound concreteBefore := by
  unfold ExecutionPathBound concreteBefore
  simp

theorem concrete_entry_valid_pre :
    EntryValid concretePreEntry concretePreRecord := by
  unfold EntryValid concretePreEntry concretePreEntryBody mkLedgerEntry
    concretePreRecord concreteRecord
  simp

theorem concrete_entry_valid_post :
    EntryValid concretePostEntry concreteRecord := by
  unfold EntryValid concretePostEntry concretePostEntryBody mkLedgerEntry concreteRecord
  simp

theorem concrete_pre_post_same_decision :
    PrePostSameDecision concretePreEntry concretePostEntry := by
  unfold PrePostSameDecision concretePreEntry concretePostEntry concretePreEntryBody
    concretePostEntryBody mkLedgerEntry concretePreRecord concreteRecord
  simp

theorem concrete_ledger_valid :
    LedgerValid concreteLedger := by
  unfold LedgerValid concreteLedger
  constructor
  · intro entry hcontains
    rcases hcontains with hpre | hpost
    · subst entry
      exact
        ⟨ mkLedgerEntry_hash_valid concretePreEntryBody,
          ⟨concretePreRecord, Or.inl ⟨rfl, rfl⟩, concrete_entry_valid_pre⟩,
          Or.inl rfl ⟩
    · subst entry
      exact
        ⟨ mkLedgerEntry_hash_valid concretePostEntryBody,
          ⟨concreteRecord, Or.inr ⟨rfl, rfl⟩, concrete_entry_valid_post⟩,
          Or.inr
            ⟨concretePreEntry,
              Or.inl rfl,
              ⟨rfl, rfl⟩,
              rfl,
              by decide⟩ ⟩
  · intro previous entry hbefore
    rcases hbefore with ⟨hprevious, hentry⟩
    subst previous
    subst entry
    exact
      ⟨Or.inl rfl,
        Or.inr rfl,
        by decide,
        rfl⟩

theorem committed_by_ledger_nonempty :
    exists before after ledger pre post preRecord record,
      CommittedByLedger before after ledger pre post preRecord record := by
  refine
    ⟨concreteBefore, concreteAfter, concreteLedger, concretePreEntry,
      concretePostEntry, concretePreRecord, concreteRecord, ?_⟩
  unfold CommittedByLedger
  exact
    ⟨ concrete_ledger_valid,
      Or.inl rfl,
      Or.inr rfl,
      Or.inl ⟨rfl, rfl⟩,
      Or.inr ⟨rfl, rfl⟩,
      rfl,
      rfl,
      rfl,
      by decide,
      rfl,
      concrete_pre_post_same_decision,
      concrete_entry_valid_pre,
      concrete_entry_valid_post,
      rfl,
      rfl,
      rfl,
      rfl,
      rfl,
      rfl,
      rfl,
      rfl,
      concrete_subject_valid,
      concrete_decision_valid,
      concrete_verification_valid,
      concrete_sem,
      concrete_phi_overapprox,
      concrete_phi_overapprox concreteAfter concrete_sem,
      concrete_approval_valid,
      concrete_execution_path_bound ⟩

end NonVacuity

structure ADICWitness where
  before : State
  after : State
  ledger : Ledger
  precommit : LedgerEntry
  postcommit : LedgerEntry
  preRecord : EvidenceRecord
  record : EvidenceRecord
  phi : EffectBound
  approval : Option Approval

def ValidLedgerLink (w : ADICWitness) : Prop :=
  LedgerValid w.ledger /\
  w.ledger.contains w.precommit /\
  w.ledger.contains w.postcommit /\
  w.ledger.evidenceOf w.precommit w.preRecord /\
  w.ledger.evidenceOf w.postcommit w.record

def ValidPrePostLink (w : ADICWitness) : Prop :=
  IsPreCommit w.precommit /\
  IsPostCommit w.postcommit /\
  w.postcommit.result = CommitResult.committed /\
  w.precommit.index < w.postcommit.index /\
  w.postcommit.precommitHash = some w.precommit.entryHash /\
  PrePostSameDecision w.precommit w.postcommit

def ValidStateLink (w : ADICWitness) : Prop :=
  w.postcommit.preStateDigest = TCB.digest_state w.before /\
  w.postcommit.postStateDigest = TCB.digest_state w.after /\
  w.record.preStateDigest = TCB.digest_state w.before /\
  w.record.postStateDigest = TCB.digest_state w.after /\
  w.record.result = CommitResult.committed

def ValidEntryLink (w : ADICWitness) : Prop :=
  EntryValid w.precommit w.preRecord /\
  EntryValid w.postcommit w.record /\
  w.postcommit.phiDigest = TCB.digest_phi w.record.phi /\
  w.postcommit.decisionDigest = TCB.digest_decision w.record.decision /\
  w.postcommit.operationDigest = TCB.digest_operation w.record.operation /\
  w.phi = w.record.phi /\
  w.approval = w.record.approval

def ValidEffectLink (w : ADICWitness) : Prop :=
  PhiOverApprox w.record.operation w.before w.record.phi /\
  Eff w.record.operation w.before w.after <=e w.record.phi

def ValidApprovalLink (w : ADICWitness) : Prop :=
  ApprovalValidForRecord w.record w.before w.postcommit.timestamp /\
  SubjectValidForRecord w.record w.before /\
  DecisionPackageValidForRecord w.record w.before /\
  VerificationValidForRecord w.record w.before w.postcommit.timestamp

def ValidExecutionLink (w : ADICWitness) : Prop :=
  Sem w.record.operation w.before w.after /\
  ExecutionPathBound w.before

def ValidADICWitness (w : ADICWitness) : Prop :=
  ValidLedgerLink w /\
  ValidPrePostLink w /\
  ValidStateLink w /\
  ValidEntryLink w /\
  ValidEffectLink w /\
  ValidApprovalLink w /\
  ValidExecutionLink w

def RejectedStep (c : OperationRequest) (before after : State) : Prop :=
  RiskClass c before (Eff c before after) = Risk.blocked /\
  forall r,
    before.resourcePresent r = after.resourcePresent r /\
    before.resourceValue r = after.resourceValue r

def Generated (c : OperationRequest) : Prop :=
  c.aiGenerated = true

def AuthorizedByAllowCore (c : OperationRequest) (s : State) : Prop :=
  exists phi approval obligations subjectDigest atTime,
    AllowCore c s phi approval obligations subjectDigest atTime

def GeneratedOnly (c : OperationRequest) (s : State) : Prop :=
  Generated c /\
  Not (AuthorizedByAllowCore c s)

theorem committed_transition_yields_witness
    (before after : State)
    (ledger : Ledger)
    (pre post : LedgerEntry)
    (preRecord record : EvidenceRecord)
    (hcommit : CommittedByLedger before after ledger pre post preRecord record) :
    exists w : ADICWitness,
      ValidADICWitness w /\
      w.before = before /\
      w.after = after /\
      w.ledger = ledger /\
      w.precommit = pre /\
      w.postcommit = post /\
      w.preRecord = preRecord /\
      w.record = record := by
  rcases hcommit with
    ⟨hLedger, hContainsPre, hContainsPost, hEvidencePre, hEvidencePost,
     hIsPre, hIsPost, hCommitted, hIndex, hHash, hSameDecision,
     hEntryPre, hEntryPost,
     hPostPreState, hPostPostState, hRecordPreState, hRecordPostState,
     hRecordResult, hPhiDigest, hDecisionDigest, hOperationDigest,
     hSubject, hDecision, hVerification,
     hsem, hphi, heff, happroval, hpath⟩
  let w : ADICWitness :=
    { before := before,
      after := after,
      ledger := ledger,
      precommit := pre,
      postcommit := post,
      preRecord := preRecord,
      record := record,
      phi := record.phi,
      approval := record.approval }
  refine ⟨w, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  unfold ValidADICWitness
    ValidLedgerLink
    ValidPrePostLink
    ValidStateLink
    ValidEntryLink
    ValidEffectLink
    ValidApprovalLink
    ValidExecutionLink
  dsimp [w]
  -- ValidADICWitness component order:
  -- ValidLedgerLink, ValidPrePostLink, ValidStateLink, ValidEntryLink,
  -- ValidEffectLink, ValidApprovalLink, ValidExecutionLink.
  exact
    ⟨ ⟨hLedger, hContainsPre, hContainsPost, hEvidencePre, hEvidencePost⟩,
      ⟨hIsPre, hIsPost, hCommitted, hIndex, hHash, hSameDecision⟩,
      ⟨hPostPreState, hPostPostState, hRecordPreState, hRecordPostState,
        hRecordResult⟩,
      ⟨hEntryPre, hEntryPost, hPhiDigest, hDecisionDigest, hOperationDigest,
        rfl, rfl⟩,
      ⟨hphi, heff⟩,
      ⟨happroval, hSubject, hDecision, hVerification⟩,
      ⟨hsem, hpath⟩ ⟩

theorem valid_witness_has_semantic_execution
    (w : ADICWitness)
    (h : ValidADICWitness w) :
    Sem w.record.operation w.before w.after := by
  rcases h with
    ⟨_hLedger, _hPrePost, _hState, _hEntry, _hEffect, _hApproval, hExec⟩
  exact hExec.left

theorem valid_witness_effect_is_within_phi
    (w : ADICWitness)
    (h : ValidADICWitness w) :
    Eff w.record.operation w.before w.after <=e w.record.phi := by
  rcases h with
    ⟨_hLedger, _hPrePost, _hState, _hEntry, hEffect, _hApproval, _hExec⟩
  exact hEffect.right

theorem protected_change_requires_valid_adic_witness
    (before after : State)
    (ledger : Ledger)
    (pre post : LedgerEntry)
    (preRecord record : EvidenceRecord)
    (_hchg : ProtectedChanged before after)
    (hcommit : CommittedByLedger before after ledger pre post preRecord record) :
    exists w : ADICWitness,
      ValidADICWitness w /\
      w.before = before /\
      w.after = after /\
      w.ledger = ledger /\
      w.precommit = pre /\
      w.postcommit = post /\
      w.preRecord = preRecord /\
      w.record = record := by
  exact committed_transition_yields_witness
    before after ledger pre post preRecord record
    hcommit

theorem blocked_operation_has_no_protected_effect
    (before after : State)
    (c : OperationRequest)
    (hreject : RejectedStep c before after) :
    Not (ProtectedChanged before after) := by
  intro hchanged
  rcases hchanged with ⟨r, _hProtected, hChanged⟩
  cases hChanged with
  | inl hPresentChanged =>
      exact hPresentChanged (hreject.right r).left
  | inr hValueChanged =>
      exact hValueChanged (hreject.right r).right

theorem generated_only_does_not_authorize
    (c : OperationRequest)
    (s : State)
    (h : GeneratedOnly c s) :
    Not (AuthorizedByAllowCore c s) := by
  exact h.right

theorem committed_effect_within_phi
    (before after : State)
    (c : OperationRequest)
    (phi : EffectBound)
    (hsem : Sem c before after)
    (hphi : PhiOverApprox c before phi) :
    Eff c before after <=e phi := by
  exact hphi after hsem

-- === Axiom Audit ===
-- Expected: TCB.* plus Lean's ordinary classical/propositional axioms only.
-- Unexpected axioms here indicate a trust-boundary leak or an unfinished proof.
#print axioms ADIC.sem_unknown_operation_is_false
#print axioms ADIC.NonVacuity.committed_by_ledger_nonempty
#print axioms ADIC.committed_transition_yields_witness
#print axioms ADIC.valid_witness_has_semantic_execution
#print axioms ADIC.valid_witness_effect_is_within_phi
#print axioms ADIC.protected_change_requires_valid_adic_witness
#print axioms ADIC.blocked_operation_has_no_protected_effect
#print axioms ADIC.generated_only_does_not_authorize
#print axioms ADIC.committed_effect_within_phi

end ADIC
