import Ref.Connection

/-!
# The reference implementation of the transaction layer (Part 4)

Written from Part 4's sections and independently of `Spec.Transactions`: the two share no
definition, so their agreement over the exchange corpus is evidence rather than a
tautology. This is the same independence the two connection and session layers have, and
it reads the declared surface through `Ref.Connection`'s own helpers rather than through
the specification's.

The transaction performatives are message bodies rather than frames — the section's
worked exchanges send `TRANSFER(delivery-id=0)` carrying an `amqp-value` section whose
value is a `declare`, and the coordinator answers with a `disposition` whose state is a
`declared` — so this module is a machine over those values and the session's dispatch is
what hands it one. The clauses it implements are the declare/discharge lifecycle:
allocation at the coordinator, the `declared` outcome that teaches the id to the
controller, the `unknown-id` error for a commit against a transaction that is not live,
the unconditional completion of a rollback, the pre-settled error the section names, and
the `global-id` field rule against the coordinator's announced capabilities.

The `txn-work` obligations — transactional delivery states, the provisional outcome, the
partial-delivery rider — are the delivery-state layer's, and are carried rather than
judged here, with one exception that is written over the register: the `txn-id` a
`transactional-state` carries "identifies the transaction with which the state is
associated", so an outcome naming an id this endpoint does not hold is refused with the
transaction-error family's `unknown-id`. That is the half of the section this machine can
decide; what the state does to the delivery it names is not.
-/

namespace SpecAMQP.Ref.Transactions

open SpecAMQP.Generated.Oasis (TypeDecl)
open SpecAMQP.Ref
open SpecAMQP.Ref.Connection (bodyType declaredChoice invalidFieldCondition
  missingMandatory numberOf symbolList valueOfField)

/-! ## The family -/

/-- The transaction performatives, by the declared type a value's descriptor names. -/
inductive Act where
  | declare
  | discharge
  | declared
  | transactionalState
  | other
deriving Repr, BEq, DecidableEq

/-- The act's name, which is the declared type's. -/
def Act.label : Act → String
  | .declare => "declare"
  | .discharge => "discharge"
  | .declared => "declared"
  | .transactionalState => "transactional-state"
  | .other => "another performative"

def Act.ofDeclared (declaration : TypeDecl) : Act :=
  if declaration.name == "declare" then .declare
  else if declaration.name == "discharge" then .discharge
  else if declaration.name == "declared" then .declared
  else if declaration.name == "transactional-state" then .transactionalState
  else .other

/-- The act a value is. -/
def actOf (value : Value) : Act :=
  match bodyType value with
  | none => .other
  | some declaration => Act.ofDeclared declaration

/-! ## Conditions -/

/-- The `amqp-error` family's `illegal-state`: the section's own condition for a
transaction message sent at a moment its clauses forbid. -/
def preSettledCondition : String :=
  (declaredChoice "amqp-error" "illegal-state").getD "no illegal-state in the choice table"

/-- The `transaction-error` family's `unknown-id`, read from the generated table. -/
def unknownIdCondition : String :=
  (declaredChoice "transaction-error" "unknown-id").getD "no unknown-id in the choice table"

/-- The capability a coordinator must announce before a declare may carry a global id. The
section states the rule as a reference to this choice of the `txn-capability` type, so it
is read from the table rather than typed. -/
def distributedCapability : String :=
  (declaredChoice "txn-capability" "distributed-transactions").getD "no distributed-transactions"

/-! ## Refusals -/

/-- A refusal: the condition the mandated detach would carry, the reason class the corpus
reads, and the prose. The layer writes no frame; where the refusal is placed is the
session's business. -/
structure Refusal where
  condition : String
  reasonClass : String
  text : String
deriving Repr

def Refusal.detail (refusal : Refusal) : String := s!"{refusal.reasonClass}: {refusal.text}"

def refuse (condition reasonClass text : String) : Refusal := ⟨condition, reasonClass, text⟩

/-! ## The state a control link carries -/

/-- A transaction this endpoint knows: the txn-id and whether it is still in use. -/
structure Txn where
  id : Nat
  live : Bool
deriving Repr, BEq

/-- The transaction layer: the transactions this endpoint knows, the id a coordinator
would allocate next, and the capabilities each end announced for the control link's
coordinator target. -/
structure Layer where
  known : List Txn
  next : Nat
  own : List String
  other : List String
deriving Repr

/-- A control link with nothing allocated: the coordinator's first txn-id is zero, which
is the id the section's own worked exchange allocates first. -/
def Layer.fresh : Layer := ⟨[], 0, [], []⟩

/-- The txn-id's transaction, where this endpoint holds it. -/
def Layer.find? (layer : Layer) (id : Nat) : Option Txn :=
  layer.known.find? (fun txn => txn.id == id)

/-- Whether the txn-id names a transaction still in use. -/
def Layer.isLive (layer : Layer) (id : Nat) : Bool :=
  match layer.find? id with
  | some txn => txn.live
  | none => false

/-- Whether this endpoint's register holds the txn-id at all, retired or not. This is the
question an outcome's `transactional-state` asks, and it is not `isLive`'s: a state naming
a transaction a discharge has already retired still names the transaction its delivery
belonged to, which is what an outcome settling that delivery has to say. -/
def Layer.holds (layer : Layer) (id : Nat) : Bool :=
  (layer.find? id).isSome

/-- The txn-id stops being in use: what a discharge says, and what the control link's
close does to every transaction it created. -/
def Layer.retired (layer : Layer) (id : Nat) : Layer :=
  { layer with
      known := layer.known.map (fun txn => if txn.id == id then { txn with live := false } else txn) }

/-- Every transaction retired: the control link's close rolls back the transactions it
created, so further transactional work on them fails, which for this machine is a commit
with no live transaction to name. -/
def Layer.retiredAll (layer : Layer) : Layer :=
  { layer with known := layer.known.map (fun txn => { txn with live := false }) }

/-- The txn-id this endpoint knows, added where it is new. -/
def Layer.learned (layer : Layer) (id : Nat) : Layer :=
  if layer.holds id then layer else { layer with known := ⟨id, true⟩ :: layer.known }

/-- The coordinator's capabilities, as the `global-id` rule reads them: the end that
receives a declare is the coordinator, so an outbound declare is judged against what the
partner announced and an inbound one against what this endpoint announced. -/
def Layer.coordinatorCapabilities (layer : Layer) (outbound : Bool) : List String :=
  if outbound then layer.other else layer.own

/-- The capabilities a link target announces where it is a `coordinator`, and `none` for
any other target: the control link is the link whose target is the coordinator. -/
def coordinatorCapabilities (target : Value) : Option (List String) :=
  match bodyType target with
  | none => none
  | some declaration =>
    if declaration.name == "coordinator" then
      some (symbolList ((valueOfField "coordinator" "capabilities" target).getD .null))
    else none

/-! ## The rules -/

/-- The pre-settled error: "This message MUST NOT be sent settled as the sender is
REQUIRED to receive and interpret the outcome of the declare from the receiver", and the
coordinator that receives one detaches with `illegal-state`. -/
def settledRefusal (act : String) : Refusal :=
  refuse preSettledCondition "illegalState"
    s!"a {act} MUST NOT be sent settled: the sender is required to receive and interpret \
      the outcome"

/-- The coordinator's verdict on a `global-id`. -/
def globalIdRefusal (capabilities : List String) : Refusal :=
  refuse invalidFieldCondition "malformed"
    s!"the declare carries a global-id and the coordinator's capabilities \
      {capabilities} do not include {distributedCapability}"

/-- The commit's error: the txn-id is not one this endpoint holds live, which the
`transaction-error` family names `unknown-id` — "The specified txn-id does not exist." -/
def unknownIdRefusal (id : Nat) : Refusal :=
  refuse unknownIdCondition "illegalState"
    s!"the discharge names txn-id {id}, and this endpoint holds no live transaction with \
      that id"

/-- A declare: the id is the coordinator's to allocate, so the end that receives the
declare allocates one and the end that sent it learns the id from the outcome. -/
def onDeclare (layer : Layer) (outbound : Bool) (globalId : Bool) (settled : Bool) :
    Except Refusal Layer := do
  if settled then .error (settledRefusal "declare")
  let capabilities := layer.coordinatorCapabilities outbound
  if globalId && !capabilities.contains distributedCapability then
    .error (globalIdRefusal capabilities)
  if outbound then return layer
  else
    let allocated : Layer := { layer with next := layer.next + 1 }
    return { allocated with known := ⟨layer.next, true⟩ :: layer.known }

/-- A discharge: a rollback completes whatever the register says, a commit does not. -/
def onDischarge (layer : Layer) (id : Nat) (fail : Bool) (settled : Bool) :
    Except Refusal Layer := do
  if settled then .error (settledRefusal "discharge")
  if fail then return layer.retired id
  if !layer.isLive id then .error (unknownIdRefusal id)
  return layer.retired id

/-- The `declared` outcome teaches the controller the id it may discharge; the end that
allocated it learns nothing new. -/
def onDeclared (layer : Layer) (outbound : Bool) (id : Nat) : Layer :=
  if outbound then layer else layer.learned id

/-- The error for an outcome whose state names a txn-id this endpoint does not hold. The
condition is the `transaction-error` family's `unknown-id`, which is the same condition a
commit against an absent id is refused with, because the defect is the same one: an id
nothing here holds. -/
def absentTransactionRefusal (id : Nat) : Refusal :=
  refuse unknownIdCondition "illegalState"
    s!"the outcome carries a transactional-state naming txn-id {id}, which is not one this \
      endpoint holds"

/-- The same error for a state whose `txn-id` is a value of another kind: this coordinator
allocates integer identifiers, so a value that is not an integer names no transaction. -/
def nonIntegerIdRefusal (typeName : String) : Refusal :=
  refuse unknownIdCondition "illegalState"
    s!"the {typeName}'s txn-id is not an integer identifier, and this coordinator allocates \
      integer identifiers"

/-- The `transactional-state` outcome: the transaction an outcome's state names, read
against the register.

`transactional-state`'s `txn-id` "identifies the transaction with which the state is
associated", so a state naming an id this endpoint has never held names no transaction
here, and it is refused with `unknown-id`. A state naming a transaction a discharge has
retired is admitted: the state is then what settles a delivery that transaction's work
created. What the state does to the *delivery* — the terminal state it carries in that
composite and the outcome beside it — is not this machine's, and is carried. -/
def onTransactionalState (layer : Layer) (value : Value) : Except Refusal Layer :=
  match (valueOfField "transactional-state" "txn-id" value).bind numberOf with
  | some id =>
    if layer.holds id then .ok layer else .error (absentTransactionRefusal id)
  | none => .error (nonIntegerIdRefusal "transactional-state")

/-- Where a transaction value arrived, which decides what it may be. The control link
carries the declare and discharge dialogue — "they do not represent the demarcation of
transactional work" — and "No transactional work is allowed on the control link", so a
transfer's payload and a disposition's `state` are judged differently even where they carry
the same composite. -/
inductive Carrier where
  | payload
  | state
deriving Repr, BEq, DecidableEq

/-- The refusal for a transaction composite arriving as a message on the control link. The
sentence names no condition, so the amqp-error family's `illegal-state` is used: "The peer
sent a frame that is not permitted in the current state". -/
def notTheControlDialogue (typeName : String) : Refusal :=
  refuse preSettledCondition "illegalState"
    s!"the control link carries the declare and discharge messages and no transactional \
      work, and this message carries a {typeName}"

/-- One transaction value, dispatched by its declared type. `settled` is the transfer's
settlement where the value arrived in one; the outcomes do not arrive in a transfer and
ignore it. `carrier` says which frame carried the value, which is what makes the
no-work-on-the-control-link sentence checkable. -/
def step (layer : Layer) (carrier : Carrier) (outbound : Bool) (value : Value)
    (settled : Bool) : Except Refusal Layer := do
  let act := actOf value
  if act == .other then return layer
  let missing := missingMandatory act.label value
  if !missing.isEmpty then
    .error (refuse invalidFieldCondition "malformed"
      s!"the {act.label} composite does not carry {missing}, which the declared surface \
        marks mandatory")
  match act with
  | .declare =>
    let globalId :=
      match valueOfField "declare" "global-id" value with
      | some .null | none => false
      | some _ => true
    onDeclare layer outbound globalId settled
  | .discharge =>
    match (valueOfField "discharge" "txn-id" value).bind numberOf with
    | none => .error (nonIntegerIdRefusal "discharge")
    | some id =>
      let fail :=
        match valueOfField "discharge" "fail" value with
        | some (.boolean true) => true
        | _ => false
      onDischarge layer id fail settled
  | .declared =>
    match carrier with
    | .payload => .error (notTheControlDialogue act.label)
    | .state =>
      match (valueOfField "declared" "txn-id" value).bind numberOf with
      | some id => return onDeclared layer outbound id
      | none => return layer
  | .transactionalState =>
    match carrier with
    | .payload => .error (notTheControlDialogue act.label)
    | .state => onTransactionalState layer value
  | .other => return layer

end SpecAMQP.Ref.Transactions
