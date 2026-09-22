import Spec.Connection

/-!
# The transaction layer (Part 4: `amqp:transactions`)

Part 4 is not a frame layer. A `declare` and a `discharge` are *message bodies*: the
artifact's own worked exchanges write `TRANSFER(delivery-id=0){ AmqpValue( Declare() ) }`
and answer it with `DISPOSITION(first=0, last=0, state=Declared(txn-id=0))`, so the
transaction performatives travel where `Spec.Session`'s transfer carries its payload and
their outcomes travel in a `disposition`'s `state`. This module is the family and the
state machine; the arm that hands it a message lives in the session's dispatch, which is
what keeps the two layers' rules separable.

The readings this module rests on, each from the section rather than from memory:

* **A transaction is a txn-id the coordinator allocated, and it stops being in use when
  it is discharged.** "To begin transactional work, the transaction controller needs to
  obtain a transaction identifier from the resource. It does this by sending a message to
  the «coordinator» whose body consists of the «declare» type in a single «amqp-value»
  section", and "If the declaration is successful, the coordinator responds with a
  disposition outcome of «declared» which carries the assigned identifier for the
  transaction." The `discharge` type "defines the message body sent to the coordinator to
  indicate that the txn-id is no longer in use." So a declare *allocates* at the end that
  receives it, a `declared` outcome *teaches* the id to the end that sent it, and a
  discharge *retires* it. The ids start at zero, which is the id the artifact's worked
  example allocates first.
* **The settle rule is the sender's, and the condition is `amqp:illegal-state`.** "This
  message MUST NOT be sent settled as the sender is REQUIRED to receive and interpret the
  outcome of the declare from the receiver", and the coordinator that receives one "SHOULD
  «detach» with an «amqp:illegal-state» error" — the artifact's own symbol for a frame that
  is perfectly well formed at a moment its rules do not allow. The discharge's section says
  the same ("As with the «declare» message, it is an error if the sender sends the
  «discharge» pre-settled").
* **A rollback is always completable, a commit is not.** "Note that the coordinator MUST
  always be able to complete a «discharge» where the fail flag is set to true (since
  coordinator failure leads to rollback, which is what the controller is asking for)", so a
  discharge whose `fail` flag is set consults nothing. A discharge whose `fail` flag is not
  set needs a transaction that is still live, and one that is not is the artifact's own
  `amqp:transaction:unknown-id` ("The specified txn-id does not exist").
* **`global-id` needs the coordinator's `distributed-transactions` capability.** "This
  field MUST NOT be set if the coordinator does not have the «txn-capability»
  [distributed-transactions] capability", which the artifact states as a reference to that
  choice rather than as prose. The capabilities the field is judged against are the
  coordinator's *actual* ones: "When sent by the transaction controller (the sending
  endpoint), [the coordinator's capabilities field] indicates the desired capabilities of
  the coordinator. When sent by the resource (the receiving endpoint), [it defines] the
  actual capabilities of the coordinator."

**What is not here, and where it is instead.** Part 4's `txn-work` section states the
obligations that attach to transactional *delivery states*: posting, acquiring and
retiring a message, the `transactional-state` a transfer or a disposition carries, the
provisional outcome a resource owes before a discharge can succeed, and the rule that a
partial delivery makes a discharge an error. Those are the delivery-state layer's — the
message and link layers carry the states they are about, and this machine would have to
model a transfer's delivery state to see them. The `transactional-state` composite is
recognised as part of the family here and *carried* rather than judged, and its clauses
are dispositioned to that layer in the ledger rather than absorbed here. One sentence of
that family is where the difference is sharpest: `txn-work.3`'s rider, "It is an error for
the controller to attempt to discharge a transaction against which a partial delivery has
been posted", needs fragmentation state this layer does not have.

**Two cells the artifact leaves open, which this machine therefore decides without
enforcing either reading in the corpus.** A discharge whose `fail` flag is set is
*admitted without consulting the register*, because the MUST above is unconditional; the
alternative reading — that an unknown id is `unknown-id` whatever `fail` says — is not
refuted by the text, and no vector in the corpus pins either. And a `rejected` outcome
carrying a `transaction-error` is carried rather than read: "In the event of ... a
resource-initiated rollback (the «discharge» message being rejected, or the link to the
«coordinator» being detached with an error), the outcome will not be applied, and the
deliveries will still be 'live'" says what happens to the *deliveries* while this machine
tracks the txn-id, and whether a rejected discharge leaves the txn-id dischargeable again
is not stated.
-/

namespace SpecAMQP.Spec.Transactions

open SpecAMQP.Generated.Oasis (TypeDecl)
open SpecAMQP.Spec.Codec (Value)
open SpecAMQP.Spec.Connection
  (choiceValue? fieldValue fieldSet missingMandatory symbolsOf valueNat)

/-! ## The family (Part 4's `coordination` section) -/

/-- The transaction performatives: the two message bodies the control link carries, the
two outcomes they produce, and `other` for every value that is not one of them. The four
are named by the declared types the generated table holds, not by their descriptors. -/
inductive Performative where
  | declare
  | discharge
  /-- The outcome a successful declare is answered with, which "carries the assigned
  identifier for the transaction". -/
  | declared
  /-- The delivery state that "combines a txn-id together with one of the terminal
  delivery states": part of this family, and the delivery-state layer's to judge. -/
  | transactionalState
  | other
deriving Repr, BEq, DecidableEq

/-- The performative's name, which is the declared type's. -/
def Performative.name : Performative → String
  | .declare => "declare"
  | .discharge => "discharge"
  | .declared => "declared"
  | .transactionalState => "transactional-state"
  | .other => "another performative"

/-- The performative a declared type names. -/
def performativeOfDeclared (declaration : TypeDecl) : Performative :=
  if declaration.name == "declare" then .declare
  else if declaration.name == "discharge" then .discharge
  else if declaration.name == "declared" then .declared
  else if declaration.name == "transactional-state" then .transactionalState
  else .other

/-- The performative a value is, from the declared type its descriptor names. -/
def Performative.ofValue (value : Value) : Performative :=
  match value with
  | .described descriptor _ =>
    match SpecAMQP.Spec.Frame.typeOfDescriptor descriptor with
    | some declaration => performativeOfDeclared declaration
    | none => .other
  | _ => .other

/-! ## Conditions, read from the generated choice tables -/

/-- The condition for a transaction message sent at a moment its clauses forbid: the
`amqp-error` family's `illegal-state`, which is the artifact's own name for a frame that is
well formed and early. -/
def illegalStateCondition : String :=
  (choiceValue? "amqp-error" "illegal-state").getD "the amqp-error choice declares no illegal-state"

/-- The condition for a field that breaks the rule its own declaration states. -/
def invalidFieldCondition : String :=
  (choiceValue? "amqp-error" "invalid-field").getD "the amqp-error choice declares no invalid-field"

/-- The condition for a discharge that names a transaction this coordinator does not have
live, read from the `transaction-error` family. -/
def transactionErrorCondition (choice : String) : String :=
  match choiceValue? "transaction-error" choice with
  | some value => value
  | none => s!"the transaction-error choice declares no {choice}"

/-- "The specified txn-id does not exist." -/
def unknownId : String := transactionErrorCondition "unknown-id"

/-- The capability a coordinator needs before a declare may carry a global id — the
choice the artifact's `global-id` clause references. -/
def distributedTransactions : String :=
  match choiceValue? "txn-capability" "distributed-transactions" with
  | some value => value
  | none => "the txn-capability choice declares no distributed-transactions"

/-! ## Refusals -/

/-- A refusal the transaction layer raises: the condition the detach the artifact mandates
would carry, the class-led detail the corpus vocabulary reads, and the prose. The layer
owns no frame, so where the refusal is *placed* — the session's discarding phase, or the
connection's close — is the session's decision and not this module's. -/
structure Refusal where
  condition : String
  reasonClass : String
  text : String
deriving Repr

/-- The rendered detail: the class first, which is what the corpus and the differential
comparison read. -/
def Refusal.detail (refusal : Refusal) : String :=
  s!"{refusal.reasonClass}: {refusal.text}"

/-- A refusal of one class. -/
def refusal (condition reasonClass text : String) : Refusal :=
  ⟨condition, reasonClass, text⟩

/-- Refuse unless a condition holds. -/
def refuseUnless (condition : Bool) (reason : Refusal) : Except Refusal Unit :=
  if condition then .ok () else .error reason

/-! ## The state a control link carries -/

/-- One transaction, as the endpoint that holds it knows it: the txn-id the coordinator
allocated, and whether it is still in use. "The «discharge» type defines the message body
sent to the coordinator to indicate that the txn-id is no longer in use", so a discharge
is what retires one, and a transaction the control link's close rolled back is retired
with it. -/
structure Transaction where
  id : Nat
  discharged : Bool
deriving Repr, BEq, DecidableEq

/-- The transaction layer's state: the transactions this endpoint knows, the txn-id the
coordinator would allocate next, and both ends' announced coordinator capabilities.

The capabilities are the one quantity here that no rule of the declare/discharge
lifecycle reads *except* `global-id`'s, which asks the coordinator's set; they are
recorded because the attach that establishes the control link carries them and the field
rule is stated against them. -/
structure Layer where
  /-- The transactions this endpoint knows, newest first. -/
  transactions : List Transaction
  /-- The txn-id the coordinator allocates next: "the coordinator responds with a
  disposition outcome of «declared» which carries the assigned identifier", and the
  artifact's worked example allocates zero first. -/
  nextId : Nat
  /-- The coordinator capabilities this endpoint announced in its own attach: the
  resource's attach carries "the actual capabilities of the coordinator". -/
  capabilities : List String
  /-- The coordinator capabilities the partner announced. -/
  peerCapabilities : List String
deriving Repr

/-- The layer a control link starts at: nothing allocated, the first id zero, and no
capability announced yet. -/
def Layer.fresh : Layer := ⟨[], 0, [], []⟩

/-- The txn-ids this endpoint knows are still in use. -/
def Layer.live (layer : Layer) (id : Nat) : Bool :=
  layer.transactions.any (fun transaction => transaction.id == id && !transaction.discharged)

/-- One transaction, retired when it is the one an id names. -/
def Transaction.retireIf (transaction : Transaction) (id : Nat) : Transaction :=
  if transaction.id == id then { transaction with discharged := true } else transaction

/-- One transaction, retired whatever its id: what the control link's close does to every
transaction it created. -/
def Transaction.retired (transaction : Transaction) : Transaction :=
  { transaction with discharged := true }

/-- Retire a txn-id: the discharge "indicate[s] that the txn-id is no longer in use", and
"all such transactions are immediately rolled back" when the control link closes. -/
def Layer.retire (layer : Layer) (id : Nat) : Layer :=
  { layer with transactions := layer.transactions.map (fun entry => entry.retireIf id) }

/-- Every transaction this endpoint holds, retired: the control link's close "roll[s] back"
the transactions it created, so "attempts to perform further transactional work on them
will lead to failure" — which for this machine is a commit that no longer has a live
transaction to name, and therefore the `unknown-id` refusal. -/
def Layer.retireAll (layer : Layer) : Layer :=
  { layer with transactions := layer.transactions.map Transaction.retired }

/-- The refusal for a transaction composite arriving as a message on the control link.

"No transactional work is allowed on the control link": the declare and discharge messages
"do not represent the demarcation of transactional work", so what the link carries is that
dialogue and nothing else. The condition is the artifact's own for input its rules do not
admit at the moment it arrives — `illegal-state`, "The peer sent a frame that is not
permitted in the current state" — and no clause names a condition for this sentence, so the
failure-mode taxonomy's existing value is the one used rather than a new one. -/
def notTheControlDialogue (typeName : String) : Refusal :=
  refusal illegalStateCondition "illegalState"
    s!"the control link carries the declare and discharge messages and no transactional \
      work, and this message carries a {typeName}"

/-- The coordinator's capabilities, as `global-id`'s rule needs them.

A declare travels from the controller to the resource, so the end that receives an
outbound declare is the coordinator and its capabilities are the ones the partner
announced; the end that receives an inbound declare *is* the coordinator, and they are
the ones this endpoint announced. -/
def Layer.coordinatorCapabilities (layer : Layer) (outbound : Bool) : List String :=
  if outbound then layer.peerCapabilities else layer.capabilities

/-- The capabilities a link's `target` announces, where that target is a coordinator.

`none` for any other target, which is how a link that is not a control link is recognised:
"The container acting as the transactional resource defines a special target that functions
as a transaction coordinator. The transaction controller establishes a control link to this
target." -/
def coordinatorCapabilities (target : Value) : Option (List String) :=
  match target with
  | .described descriptor _ =>
    match SpecAMQP.Spec.Frame.typeOfDescriptor descriptor with
    | some declaration =>
      if declaration.name == "coordinator" then
        some (symbolsOf ((fieldValue "coordinator" "capabilities" target).getD .null))
      else none
    | none => none
  | _ => none

/-! ## The declare/discharge lifecycle -/

/-- A declare: admitted unsettled, and allocating a txn-id at the end that receives it.

"To begin transactional work, the transaction controller needs to obtain a transaction
identifier from the resource", so the id is the coordinator's to assign and a controller
learns it from the `declared` outcome rather than from this step. -/
def declare (layer : Layer) (outbound : Bool) (globalId : Bool) (settled : Bool) :
    Except Refusal Layer := do
  refuseUnless (!settled)
    (refusal illegalStateCondition "illegalState"
      "a declare MUST NOT be sent settled, since the sender is required to receive and \
        interpret the outcome of the declare from the receiver")
  refuseUnless (!globalId ||
      (layer.coordinatorCapabilities outbound).contains distributedTransactions)
    (refusal invalidFieldCondition "malformed"
      s!"the declare carries a global-id, and the coordinator's announced capabilities for \
        this control link do not include {distributedTransactions}")
  if outbound then return layer
  else
    let transaction : Transaction := ⟨layer.nextId, false⟩
    let next : Layer := { layer with nextId := layer.nextId + 1 }
    return { next with transactions := List.cons transaction next.transactions }

/-- A discharge: admitted unsettled, retiring the txn-id it names.

A discharge whose `fail` flag is set is a rollback, and the artifact says the coordinator
"can always ... complete" one, so nothing is consulted and an id this endpoint never
allocated is still completed. A discharge without it is a commit, and it needs a
transaction that is still in use: anything else is `unknown-id`.

The rule is the same in both directions — the section states it once and it is a rule
about the txn-id rather than about who is holding it: the end that sent the declare stops
using the id, and the end that allocated it stops holding it. -/
def discharge (layer : Layer) (txnId : Nat) (fail : Bool) (settled : Bool) :
    Except Refusal Layer := do
  refuseUnless (!settled)
    (refusal illegalStateCondition "illegalState"
      "a discharge MUST NOT be sent settled, as with the declare: the sender is required \
        to receive and interpret the outcome")
  if fail then return layer.retire txnId
  refuseUnless (layer.live txnId)
    (refusal unknownId "illegalState"
      s!"the discharge names txn-id {txnId}, and this endpoint holds no transaction with \
        that id that is still in use")
  return layer.retire txnId

/-- The `declared` outcome: the id a successful declare allocated, arriving at the end
that asked for it. It is what makes the id dischargeable — the controller "obtains a
transaction identifier from the resource" by being told it — so a controller that was
never told, and a coordinator answering its own declare, both leave the register alone. -/
def declared (layer : Layer) (outbound : Bool) (txnId : Nat) : Layer :=
  if outbound || layer.transactions.any (fun transaction => transaction.id == txnId) then layer
  else { layer with transactions := ⟨txnId, false⟩ :: layer.transactions }

/-! ## The dispatch -/

/-- Where a transaction value arrived, which decides what it may be.

The control link carries one dialogue: "The «declare» and «discharge» messages are sent by
the transactional controller over the control link to allocate and complete transactions
respectively (they do not represent the demarcation of transactional work)", and "No
transactional work is allowed on the control link." A transfer's payload is a message, and
a disposition's `state` is the outcome a coordinator answers a declare with — the same
composite means different things in the two, so the carrier is an input to the dispatch
rather than something the dispatch guesses. -/
inductive Carrier where
  /-- A transfer's payload: the declare and discharge messages' carrier. -/
  | payload
  /-- A disposition's `state`: the `declared` outcome's carrier. -/
  | state
deriving Repr, BEq, DecidableEq

/-- One transaction value, dispatched by the declared type its descriptor names.

`settled` is the settlement of the transfer the value arrived in, as
`transfer/field:settled.4` interprets it, and only the two message bodies travel in a
transfer, so the outcomes ignore it. `carrier` says which frame carried the value, which is
what makes "No transactional work is allowed on the control link" checkable: the two control
messages are what the link is for, and any other transaction composite arriving as a
*message* is work being carried where the section says none is.

The declared surface's mandatory rule comes first because it is the same rule at both
sites: a composite that does not carry a field the artifact marks mandatory is not the
composite its descriptor names, which is what `discharge`'s, `declared`'s and
`transactional-state`'s `txn-id` are. -/
def step (layer : Layer) (carrier : Carrier) (outbound : Bool) (value : Value)
    (settled : Bool) : Except Refusal Layer := do
  let performative := Performative.ofValue value
  let typeName :=
    match performative with
    | .declare => "declare" | .discharge => "discharge"
    | .declared => "declared" | .transactionalState => "transactional-state"
    | .other => ""
  if performative == .other then return layer
  refuseUnless ((missingMandatory typeName value).isEmpty)
    (refusal invalidFieldCondition "malformed"
      s!"the {typeName} composite does not carry {missingMandatory typeName value}, and the \
        declared surface marks it mandatory")
  match performative with
  | .declare => declare layer outbound (fieldSet "declare" "global-id" value) settled
  | .discharge =>
    -- "If set, this flag indicates that the work associated with this transaction has
    -- failed, and the controller wishes the transaction to be rolled back": what the flag
    -- *says* is the boolean it carries, not that the field is present — a discharge that
    -- sets `fail` to false is a commit. As elsewhere in this layer, a field that carries
    -- something other than the boolean the declared surface declares is read as the false
    -- the flag's absence means rather than refused, which is the convention the session
    -- layer already follows for `snd-settle-mode`.
    let fail :=
      match fieldValue "discharge" "fail" value with
      | some (.boolean flag) => flag
      | _ => false
    match (fieldValue "discharge" "txn-id" value).bind valueNat with
    | some txnId => discharge layer txnId fail settled
    | none =>
      -- `txn-id` is declared `*` and its capability is the restricted `transaction-id` a
      -- coordinator may allocate as binary, so a value that is not an integer is a
      -- txn-id this coordinator did not allocate rather than a value to coerce
      .error (refusal unknownId "illegalState"
        "the discharge's txn-id is not an integer identifier, and this coordinator \
          allocates integer identifiers")
  | .declared =>
    match carrier with
    | .payload =>
      -- a transaction composite arriving as a message on the control link, which carries
      -- the declare and discharge messages and no transactional work
      .error (notTheControlDialogue typeName)
    | .state =>
      match (fieldValue "declared" "txn-id" value).bind valueNat with
      | some txnId => return declared layer outbound txnId
      | none => return layer
  | .transactionalState =>
    match carrier with
    | .payload => .error (notTheControlDialogue typeName)
    | .state =>
      -- the delivery-state layer's: `transactional-state` "combines a txn-id together with
      -- one of the terminal delivery states" and its obligations are the txn-work clauses',
      -- which are about posting, acquiring and retiring rather than about this machine's
      -- declare/discharge lifecycle. Carried here, and dispositioned to that layer.
      return layer
  | .other => return layer

end SpecAMQP.Spec.Transactions
