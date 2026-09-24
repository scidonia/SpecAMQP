import Spec.Connection
import Spec.Message
import Spec.Transactions

/-!
# The session layer (Part 2: `amqp:transport/section:sessions`)

The session layer differs from the connection layer in the shape of its evidence: the
connection's state table is a picture with three columns, while the session's rules are
a *diagram* (picture 30, "State Transitions") plus seven state descriptions in prose
that say what each state may send and receive, and a set of clauses about the begin, the
end, the flows and the errors. The artifact carries no table for the session, so each
declaration here cites what it transcribed.

The declared surface — which fields a performative has, which are mandatory, what their
defaults are, and what condition an error names — is *not* duplicated here:
`Spec.Connection`'s declared-surface section reads the generated tables once, and both
layers use it, so a performative missing a mandatory field does not refuse differently
depending on which layer read it.

Scope, as the milestone fixes it: `begin`/`end`, `attach`/`detach`, `flow` and `transfer`
carrying one unfragmented `data` section. The *link* state machine is not here: `attach`'s
fields are read and their mandatory rules enforced, but nothing tracks a link's lifecycle,
its credit, its delivery numbers or its unsettled map. A `transfer`'s payload is opaque to
this layer, which is what the frame layer already says it is — "the remaining bytes in the
frame body form the payload for that frame", whose meaning "is defined by the semantics of
the given performative".

Two readings are worth stating before the code:

* **The state descriptions are the permission columns.** There is no table for the
  session, so `UNMAPPED` "cannot send or receive frames", `BEGIN_SENT` "MAY send frames
  but cannot receive them", `BEGIN_RCVD` "MAY receive frames, but cannot send them",
  `MAPPED` "MAY both send and receive", `END_SENT` "MAY receive frames, but cannot send
  them", `END_RCVD` "MAY send frames, but cannot receive them", and `DISCARDING` — "a
  variant of the END_SENT state" — receives what it then discards. Those sentences are
  `State.maySend` and `State.mayReceive`.
* **A session that cannot process input ends itself.** The section says it "MUST indicate
  this by issuing an END with an appropriate «error» indicating the cause of the problem",
  and "MUST then proceed to discard all incoming frames from the remote endpoint until
  receiving the remote endpoint's corresponding «end» frame" — which is the diagram's
  `MAPPED --S:END(error)--> DISCARDING` arrow. So a frame received in a session that
  cannot take it leaves the session in DISCARDING and the refusal carries the condition
  that END would name; where the state's own description says the endpoint cannot send at
  all, no END can be issued, so the state stands and the refusal says so.

A third reading is the interface's rather than this module's, recorded in
`ledger/ambiguities/channel-zero-layering.json`: dispatch is by channel, so a session
performative arriving on channel zero is answered by the *connection*'s rules and not by
this machine, and no vector exercises it.
-/

namespace SpecAMQP.Spec.Session

open SpecAMQP.Generated.Oasis (TypeDecl)
open SpecAMQP.Harness (Octets)
open SpecAMQP.Spec.Codec (Value)
open SpecAMQP.Spec.Connection
  (choiceValue? fieldBool fieldDefault fieldValue fieldSet framingError invalidField
   missingMandatory valueBool valueNat valueOctets)

/-! ## The session state machine (picture 30, "State Transitions") -/

/-- The seven session states, in the artifact's own names. -/
inductive State where
  | unmapped
  | beginSent
  | beginRcvd
  | mapped
  | endSent
  | endRcvd
  | discarding
deriving Repr, BEq, DecidableEq

/-- Every state, in the order the artifact lists them. -/
def State.all : List State :=
  [.unmapped, .beginSent, .beginRcvd, .mapped, .endSent, .endRcvd, .discarding]

/-- The state's name, exactly as the artifact writes it. -/
def State.name : State → String
  | .unmapped => "UNMAPPED"
  | .beginSent => "BEGIN_SENT"
  | .beginRcvd => "BEGIN_RCVD"
  | .mapped => "MAPPED"
  | .endSent => "END_SENT"
  | .endRcvd => "END_RCVD"
  | .discarding => "DISCARDING"

/-- The state a name denotes, or `none` for a name the artifact does not have. -/
def State.ofName (name : String) : Option State :=
  State.all.find? (fun state => state.name == name)

/-- Whether the state's description lets the endpoint send frames: UNMAPPED cannot,
BEGIN_SENT may, BEGIN_RCVD cannot, MAPPED may, END_SENT cannot, END_RCVD may, and
DISCARDING — "a variant of the END_SENT state" — cannot. -/
def State.maySend : State → Bool
  | .unmapped => false
  | .beginSent => true
  | .beginRcvd => false
  | .mapped => true
  | .endSent => false
  | .endRcvd => true
  | .discarding => false

/-- Whether the state's description lets the endpoint receive frames. -/
def State.mayReceive : State → Bool
  | .unmapped => false
  | .beginSent => false
  | .beginRcvd => true
  | .mapped => true
  | .endSent => true
  | .endRcvd => false
  | .discarding => true

/-! ## The performatives this layer answers for -/

/-- The session performatives, by the declared type their descriptor names. `other` is
every performative a frame can carry that this layer does not answer for: the dispatch
table hands `open` and `close` to the connection endpoint, so a body this layer does not
know is a frame the session cannot process. -/
inductive Performative where
  | begin
  | end
  | attach
  | detach
  | flow
  | transfer
  | other
deriving Repr, BEq, DecidableEq

/-- The performative's name, for diagnostics. -/
def Performative.name : Performative → String
  | .begin => "begin"
  | .end => "end"
  | .attach => "attach"
  | .detach => "detach"
  | .flow => "flow"
  | .transfer => "transfer"
  | .other => "another performative"

/-- The performative a declared type names. -/
def performativeOfDeclared (declaration : TypeDecl) : Performative :=
  if declaration.name == "begin" then .begin
  else if declaration.name == "end" then .end
  else if declaration.name == "attach" then .attach
  else if declaration.name == "detach" then .detach
  else if declaration.name == "flow" then .flow
  else if declaration.name == "transfer" then .transfer
  else .other

/-- The performative a frame body is, from the declared type its descriptor names. -/
def Performative.ofBody (body : Value) : Performative :=
  match body with
  | .described descriptor _ =>
    match SpecAMQP.Spec.Frame.typeOfDescriptor descriptor with
    | some declaration => performativeOfDeclared declaration
    | none => .other
  | _ => .other

/-! ## Refusals -/

/-- A refusal the session layer raises: the condition the END it issues would name, the
class-led detail the corpus vocabulary reads, and the state the refusal leaves. -/
structure Refusal where
  condition : String
  detail : String
  /-- The state the refusal leaves the session in, or `none` where it leaves it alone. -/
  state : Option State
  /-- Whether the peer's response is to close the *connection* rather than end the
  session: `attach/field:handle.2` and `begin/field:handle-max.2` both mandate an
  immediate connection close, which is the connection layer's move to make. -/
  closesConnection : Bool := false
deriving Repr

/-- The condition an END carries when the session cannot process what it received: the
`amqp-error` family's `illegal-state`, the artifact's own symbol for a perfectly well
formed frame arriving at the wrong moment. A table that stopped declaring it yields a
condition that is not a protocol condition at all, which the corpus reports as a mismatch
rather than accepting. -/
def illegalStateCondition : String :=
  (choiceValue? "amqp-error" "illegal-state").getD "the amqp-error choice declares no illegal-state"

/-- The condition an END carries when it ends a session that cannot be reached at the
channel the frame arrived on. No session-error value means "no session is mapped here",
so this is the condition the register adopts for every wire-level failure. -/
def wireCondition : String := framingError

/-- The condition for a transfer that exceeds a window: the `session-error` family's
`window-violation`, which is the artifact's own symbol for exactly this, read from the
generated choice table. No clause raises it — the windows' definitions and the doc's
update paragraphs imply it — so the rule it names is a reading of those, and it is
reported as one. -/
def windowViolation : String :=
  (choiceValue? "session-error" "window-violation").getD "the session-error choice declares no window-violation"


/-- A refusal of a given class, which leaves the state alone. -/
def refusal (condition reasonClass prose : String) : Refusal :=
  ⟨condition, s!"{reasonClass}: {prose}", none, false⟩

/-- A refusal whose consequence is the connection's close, per `attach/field:handle.2`
("MUST be responded to with an immediate «close» carrying a handle-in-use session-error")
and `begin/field:handle-max.2` ("MUST close the connection with the framing-error
error-code"). The session layer cannot write the close — the connection layer owns that
frame — so the refusal says what must follow and the codec performs it. -/
def closingRefusal (condition reasonClass prose : String) : Refusal :=
  ⟨condition, s!"{reasonClass}: {prose}", none, true⟩

/-- The condition for a link error, read from the generated `session-error` choice table:
the family is where the artifact keeps the session's own errors; a link-level *session*
error — `unattached-handle` — is one of them, while the link-error family carries the
errors a detach names. -/
def sessionErrorCondition (choice : String) : String :=
  match choiceValue? "session-error" choice with
  | some value => value
  | none => s!"the session-error choice declares no {choice}"

/-- The condition for an attach or flow naming a link this endpoint does not have. -/
def unattachedHandle : String := sessionErrorCondition "unattached-handle"

/-- The condition for an attach whose handle is already in use, per
`attach/field:handle.2`. -/
def handleInUse : String := sessionErrorCondition "handle-in-use"

/-- Refuse unless a condition holds. -/
def refuseUnless (condition : Bool) (reason : Refusal) : Except Refusal Unit :=
  if condition then .ok () else .error reason

/-! ## The session's flow-control state (doc `session-flow-control`) -/

/-- The id space the transfer numbers run in: a `transfer-number` is a `uint`, and
`next-outgoing-id` is "incremented after each successive «transfer» according to
RFC-1982 serial number arithmetic". -/
def serialModulus : Nat := 2 ^ 32

/-- The six variables the session's flow-control doc names, plus the value
`next-outgoing-id` had when this endpoint began: the `initial-outgoing-id` of the
artifact's second formula for `remote-incoming-window`.

`next-incoming-id` "identifies the expected transfer-id of the next incoming «transfer»
frame"; `incoming-window` "defines the maximum number of incoming «transfer» frames that
the endpoint can currently receive"; `next-outgoing-id` "is the transfer-id to assign to
the next transfer frame"; `outgoing-window` "defines the maximum number of outgoing
«transfer» frames that the endpoint can currently send"; `remote-incoming-window`
"reflects the maximum number of outgoing transfers that can be sent without exceeding the
remote endpoint's incoming-window"; `remote-outgoing-window` "reflects the maximum number
of incoming transfers that MAY arrive without exceeding the remote endpoint's
outgoing-window". -/
structure Windows where
  nextIncomingId : Nat
  incomingWindow : Nat
  nextOutgoingId : Nat
  outgoingWindow : Nat
  remoteIncomingWindow : Nat
  remoteOutgoingWindow : Nat
  initialOutgoingId : Nat
deriving Repr, BEq, DecidableEq

/-- The windows a session starts at when a corpus names a state without the begins that
would have set them: both peers' windows 1000 and both next ids 0, which is the arithmetic
baseline a `session:` start assumes and which every vector that cares about the numbers
sets for itself by running the begins. -/
def Windows.start : Windows :=
  ⟨0, 1000, 0, 1000, 1000, 1000, 0⟩

/-- The windows this endpoint's own begin sets: the field labels call them "the initial
incoming-window of the sender" and "the initial outgoing-window of the sender", and
`next-outgoing-id` is "the transfer-id of the first transfer id the sender will send". -/
def Windows.afterSendingBegin (windows : Windows) (nextOutgoing incoming outgoing : Nat) :
    Windows :=
  { windows with nextOutgoingId := nextOutgoing % serialModulus,
                 initialOutgoingId := nextOutgoing % serialModulus,
                 incomingWindow := incoming, outgoingWindow := outgoing }

/-- The windows the peer's begin sets. `next-incoming-id` becomes "the expected
transfer-id of the next incoming «transfer» frame", which is the id the partner will put
on its first transfer — the `next-outgoing-id` it announced — and the two remote windows
come from the same formula the doc gives for a received flow, with the unset branch taken:
`initial-outgoing-id + incoming-window - next-outgoing-id` for the peer's incoming window,
and its announced `outgoing-window` for its outgoing one. -/
def Windows.afterReceivingBegin (windows : Windows) (theirNextOutgoing theirIncoming
    theirOutgoing : Nat) : Windows :=
  { windows with nextIncomingId := theirNextOutgoing % serialModulus,
                 remoteIncomingWindow :=
                   (windows.initialOutgoingId + theirIncoming) % serialModulus -
                     windows.nextOutgoingId,
                 remoteOutgoingWindow := theirOutgoing }

/-- The windows a sent transfer leaves, per the doc's "sending a transfer": the endpoint
"will increment its next-outgoing-id, decrement its remote-incoming-window, and MAY
(depending on policy) decrement its outgoing-window". The policy is a parameter rather
than a silent choice, because the artifact leaves it open and a MAY that is compiled into
one branch is a decision nobody can see. -/
def Windows.afterSendingTransfer (windows : Windows) (policy : Bool) : Windows :=
  { windows with
      nextOutgoingId := (windows.nextOutgoingId + 1) % serialModulus,
      remoteIncomingWindow := windows.remoteIncomingWindow - 1,
      outgoingWindow := if policy then windows.outgoingWindow - 1 else windows.outgoingWindow }

/-- The windows a received transfer leaves, per the doc's "receiving a transfer": the
endpoint "will increment the next-incoming-id to match the implicit transfer-id of the
incoming transfer plus one, as well as decrementing the remote-outgoing-window, and MAY
(depending on policy) decrement its incoming-window". -/
def Windows.afterReceivingTransfer (windows : Windows) (transferId : Nat)
    (policy : Bool) : Windows :=
  { windows with
      nextIncomingId := (transferId + 1) % serialModulus,
      remoteOutgoingWindow := windows.remoteOutgoingWindow - 1,
      incomingWindow := if policy then windows.incomingWindow - 1 else windows.incomingWindow }

/-- The windows a received flow leaves: the doc says the endpoint "MUST update the
next-incoming-id directly from the next-outgoing-id of the frame, and ... the
remote-outgoing-window directly from the outgoing-window of the frame", and gives
`remote-incoming-window` as `next-incoming-id_flow + incoming-window_flow -
next-outgoing-id_endpoint`, or, "if the next-incoming-id field of the flow frame is not
set", as `initial-outgoing-id_endpoint + incoming-window_flow - next-outgoing-id_endpoint`.

The subtraction is over the id space the transfer numbers live in, so it wraps there
rather than going negative: a window is a count of transfers that may arrive, and an id
arithmetic that would make it negative is one the doc's RFC-1982 sentence already places
in that space. -/
def Windows.afterReceivingFlow (windows : Windows) (frameNextOutgoing frameIncoming
    frameOutgoing : Nat) (frameNextIncoming : Option Nat) : Windows :=
  let incomingId := frameNextIncoming.getD windows.initialOutgoingId
  { windows with
      nextIncomingId := frameNextOutgoing % serialModulus,
      remoteOutgoingWindow := frameOutgoing,
      -- a Nat subtraction here truncates at zero, which is the exhausted window rather
      -- than a wrapped one: the doc gives the formula and not what happens when the
      -- numbers leave no room, and an exhausted window fails the next send loudly rather
      -- than permitting it quietly
      remoteIncomingWindow :=
        (incomingId + frameIncoming) % serialModulus - windows.nextOutgoingId }

/-! ## The link machine (`link-handles`, the performatives, doc `flow-control`) -/

/-- The role a link endpoint attached as: "the role of the link endpoint", which decides
which end sends transfers and which receives them. -/
inductive LinkRole where
  | sender
  | receiver
deriving Repr, BEq, DecidableEq

def LinkRole.name : LinkRole → String
  | .sender => "sender"
  | .receiver => "receiver"

/-- The role an `attach`'s or `disposition`'s `role` field names. The field is declared
`role`, a restricted `boolean`, and its two values are `sender` and `receiver`; which
boolean means which is read from the generated choice table rather than typed, so a table
that changes the mapping takes this with it. A table that mapped both names to one value
determines no role at all, and that is `none` rather than a guess. -/
def LinkRole.ofValue (value : Value) : Option LinkRole :=
  match value with
  | .boolean bit =>
    let sender := (choiceValue? "role" "sender").getD "false" == "true"
    let receiver := (choiceValue? "role" "receiver").getD "true" == "true"
    if bit == sender && bit != receiver then some .sender
    else if bit == receiver && bit != sender then some .receiver
    else none
  | _ => none

/-- The doc's two per-link flow variables: `delivery-count`, which "despite its name ...
is not a count but a sequence number initialized at an arbitrary point by the sender", and
`link-credit`, "the current maximum legal amount that the delivery-count can be increased
by". A link that has not been attached carries neither. -/
structure Position where
  deliveryCount : Nat
  credit : Nat
deriving Repr, BEq, DecidableEq

/-- A link that has not been attached, and the credit a sender has before the receiver's
first flow: "Only the receiver can independently choose a value for this field", so a
sender begins with nothing to spend. -/
def Position.unattached : Position := ⟨0, 0⟩

/-- The doc's formula for a sender's `link-credit`: `link-credit_snd :=
delivery-count_rcv + link-credit_rcv - delivery-count_snd`. It is a conservation law
rather than an update rule — the sender's credit is whatever the receiver's pair leaves
room for — and `Proofs/` states it as one.

The subtraction is over the naturals and truncates: a receiver whose numbers leave the
sender no room grants credit zero, which fails the next send loudly, rather than a
negative credit the doc does not describe. -/
def Position.creditFor (receivedCount receivedCredit sentCount : Nat) : Nat :=
  receivedCount + receivedCredit - sentCount

/-- The arithmetic a transfer that begins a delivery needs: incrementing the delivery-count
lowers what the receiver's pair leaves room for by exactly one, because the subtraction
truncates at zero rather than wrapping. This is the fact the credit invariant's transfer
case rests on, and it lives beside the constructor it is about so the two cannot drift. -/
theorem Position.creditFor_succ (count credit sent : Nat) :
    Position.creditFor count credit (sent + 1) = Position.creditFor count credit sent - 1 := by
  unfold Position.creditFor
  omega

/-- The delivery a transfer carries. `delivery-id` names it in a disposition, and
`settled` is the transfer clauses' *interpretation* rather than the field of the last
frame that carried it: "If not set on the first (or only) transfer for a (multi-transfer)
delivery, then the settled flag MUST be interpreted as being false", and for a subsequent
transfer "true if and only if the value of the settled flag on any of the preceding
transfers was true". -/
structure Delivery where
  id : Nat
  settled : Bool
deriving Repr, BEq, DecidableEq

/-- The interpretation the two `settled` clauses give: `or` accumulates the flag across a
delivery's transfers, and false is the first transfer's value when the field is unset. -/
def Delivery.step (current : Option Delivery) (deliveryId : Nat) (settled : Bool) :
    Delivery :=
  match current with
  | some delivery => { delivery with settled := delivery.settled || settled }
  | none => ⟨deliveryId, settled⟩

/-! ## The session endpoint -/

/-- One session endpoint: the state, the outgoing channel it is assigned to, the
incoming channel the partner's begin arrived on, whether the partner's begin has arrived
at all — which `flow`'s `next-incoming-id` rule turns on, and which the state alone
cannot say, since `END_RCVD` is reached from a session whose begin had arrived and which
no longer has an incoming channel — and the flow-control state the doc calls for. -/
structure Session where
  state : State
  /-- The channel this endpoint sends on, assigned by its own begin. -/
  outgoing : Option Nat
  /-- The channel the partner sends on, learned from the partner's begin. -/
  incoming : Option Nat
  /-- Whether the partner's begin has arrived. -/
  peerBegun : Bool
  /-- The session's flow-control state. -/
  windows : Windows
  /-- The role this endpoint's attach declared. -/
  role : Option LinkRole
  /-- The role the partner's attach declared. -/
  peerRole : Option LinkRole
  /-- The handle this endpoint assigned: the doc's "output handle". -/
  handle : Option Nat
  /-- The handle the partner assigned: the "input handle" a received frame names. -/
  peerHandle : Option Nat
  /-- Every handle this endpoint has claimed, newest first. `attach/field:handle.1` —
  "The handle MUST NOT be used for other open links" — is checked against this list, and
  the uniqueness invariant this field owes is one of the four the slice's acceptance list
  names: no module in `Proofs/` states it yet, so the docstring says what is owed rather
  than what exists. -/
  handles : List Nat
  /-- Every handle the partner has claimed, on the same terms. -/
  peerHandles : List Nat
  /-- The highest handle this endpoint's own begin announced it would accept, defaulting
  to the value the generated field table declares for `handle-max`. -/
  handleMax : Nat
  /-- The highest handle the partner's begin announced. -/
  peerHandleMax : Nat
  /-- The link's flow state, once attached. -/
  position : Option Position
  /-- The partner's delivery-count and link-credit, as the last flow from it reported
  them. -/
  peerCount : Nat
  peerCredit : Nat
  /-- Whether the settlement mode negotiated for this link's sender side is the `settled`
  **choice** of the `sender-settle-mode` element, which is what `transfer/field:settled.4`
  turns on — "If the negotiated value for snd-settle-mode at attachment is
  <xref name="sender-settle-mode" choice="settled"/>, then this field MUST be true on at least
  one transfer frame for a delivery".

  The distinction is the whole of a defect: `sender-settle-mode` is the declared *type* of
  `attach`'s `snd-settle-mode` field, whose choices are `unsettled`, `settled` and `mixed`,
  and each of `.4` and `.6` additionally selects one choice within it. Reading the element's
  *name* as though it named one value of its own type makes `.4`'s obligation — settle at
  least once — govern the `unsettled` negotiation and `.6`'s — never settle — govern the
  `settled` one, which is neither sentence. -/
  senderSettleMode : Bool
  /-- Whether the settlement mode negotiated for this link's sender side is the `unsettled`
  **choice** of the same element `senderSettleMode` reads the `settled` choice of, which is what
  `transfer/field:settled.6` turns on — "If the negotiated value for snd-settle-mode at
  attachment is <xref name="sender-settle-mode" choice="unsettled"/>, then this field MUST be
  false (or unset) on every transfer frame for a delivery (unless the delivery is aborted)".

  `.4` selects the `settled` choice and `.6` selects the `unsettled` one, so the two recorded
  outcomes are opposite obligations on the same field and a single boolean cannot carry both: the
  negotiation is three-valued (`unsettled`, `settled`, `mixed`), and the one-property-per-field
  shape would make `.6`'s obligation fire under `settled`, which is the inversion `senderSettleMode`'s
  own docstring records. A link whose attach has not been seen records neither, and the obligations
  are then vacuous, which is what "before the negotiation" means. -/
  senderSettleUnsettled : Bool := false
  /-- Whether the settlement mode negotiated for this link's **receiver** side is the `second`
  **choice** of the `receiver-settle-mode` element, which is what
  `transfer/field:rcv-settle-mode.u1` turns on — "If the negotiated link value is «first», then it
  is illegal to set this field to «second»".

  The distinction is the same one `.4` and `.6` carry: `receiver-settle-mode` is the declared
  *type* of `attach`'s `rcv-settle-mode` field, whose choices are `first` and `second`, and the
  transfer's own `rcv-settle-mode` field names one of those choices. The attach field's declared
  default is `first`, so a link whose attach leaves it unset is one this flag is `false` at —
  absence is the `first` negotiation, and a transfer naming `second` against it is exactly the
  refusal the clause states. -/
  receiverSettleSecond : Bool := false
  /-- The delivery a transfer is carrying, while one is in progress. -/
  delivery : Option Delivery
  /-- The `delivery-tag` the transfer that *began* the delivery in progress carried, and the
  `message-format` it carried with it. `delivery-tag.u1` and `message-format.u1` compare those
  fields on a continuation transfer against the first transfer's — "It is an error if the
  delivery-tag on a continuation transfer differs from the delivery-tag on the first transfer of
  a delivery" — and `delivery-id.u1` does the same for a field the delivery already holds.

  Both live exactly as long as the delivery they are about: the transfer that begins one records
  what it carried, a continuation leaves the recording alone, and a delivery that completes,
  aborts or is released takes it with it. A recorded value that outlived its delivery would be
  compared against the wrong one, which is worse than not comparing at all.

  A value this endpoint has no reading of — a first transfer whose `delivery-tag` was not a
  `binary` field — records `none`, and a continuation is then unconstrained rather than refused:
  the rule is about a *differing* value, and absence is not a difference. -/
  deliveryTag : Option Octets
  /-- The `message-format` the transfer that began the delivery in progress carried. Cleared
  with `deliveryTag`, for the same reason. -/
  deliveryFormat : Option Nat
  /-- The transaction layer, where this session's link is a **control link**: `some` once
  either end's `attach` names a `coordinator` target, and `none` — which is the behaviour
  every session has always had — where it does not.

  Part 4 is explicit that the control link is what the transaction performatives travel
  on: "The container acting as the transactional resource defines a special target that
  functions as a transaction coordinator. The transaction controller establishes a control
  link to this target", and "The «declare» and «discharge» messages are sent by the
  transactional controller over the control link". So the layer's presence is a fact about
  the link rather than a switch, and a session that never attaches to a coordinator never
  reaches Part 4's rules — which is the regression this field exists to make impossible. -/
  transactions : Option Transactions.Layer := none
deriving Repr

/-- The policy the two MAY-decrements of the doc's update paragraphs are subject to.
Held as a value rather than compiled in, so the choice is visible: this is the reading the
corpus runs with, and the other branch is conforming too. -/
def startPolicy : Bool := true

/-- The lowest channel number a session can be assigned: "it is RECOMMENDED that
implementations always assign the lowest available unused channel number", and channel
zero is the connection's under the register's reading, so this is one. -/
def startChannel : Nat := 1

/-- The handle maximum this endpoint announces in its begin: the value the generated field
table declares as `handle-max`'s default, read rather than typed so that a table change
moves it. -/
def startHandleMax : Nat := (fieldDefault "begin" "handle-max").getD 0

/-- A session endpoint that has been created and has not begun, with no link attached and
the handle maximum its begin will announce. -/
def Session.initial : Session where
  state := .unmapped
  outgoing := none
  incoming := none
  peerBegun := false
  windows := Windows.start
  role := none
  peerRole := none
  handle := none
  peerHandle := none
  handles := []
  peerHandles := []
  handleMax := startHandleMax
  peerHandleMax := startHandleMax
  position := none
  peerCount := 0
  peerCredit := 0
  senderSettleMode := false
  senderSettleUnsettled := false
  receiverSettleSecond := false
  delivery := none
  deliveryTag := none
  deliveryFormat := none

/-- The session a state name starts at, with the channels its own description says it
has: "UNMAPPED ... is not mapped to any incoming or outgoing channels", `BEGIN_SENT` "is
assigned an outgoing channel number, but there is no entry in the incoming channel map",
`BEGIN_RCVD` "has an entry in the incoming channel map, but has not yet been assigned an
outgoing channel number", `MAPPED` "has both", `END_SENT` "has an entry in the incoming
channel map, but is no longer assigned an outgoing channel number", `END_RCVD` "is
assigned an outgoing channel number, but there is no entry in the incoming channel map",
and `DISCARDING` is "a variant of the END_SENT state". Whether the partner's begin has
arrived follows the same sentences: every state a begin had reached has one, and the two
that a begin has not — `UNMAPPED` and `BEGIN_SENT` — do not. -/
def Session.atState (state : State) : Session :=
  let base : Session := Session.initial
  match state with
  | .unmapped => { base with state := .unmapped }
  | .beginSent => { base with state := .beginSent, outgoing := some startChannel }
  | .beginRcvd => { base with state := .beginRcvd, incoming := some startChannel,
                              peerBegun := true }
  | .mapped => { base with state := .mapped, outgoing := some startChannel,
                           incoming := some startChannel, peerBegun := true }
  | .endSent => { base with state := .endSent, incoming := some startChannel,
                            peerBegun := true }
  | .endRcvd => { base with state := .endRcvd, outgoing := some startChannel,
                            peerBegun := true }
  | .discarding => { base with state := .discarding, incoming := some startChannel,
                               peerBegun := true }

/-- The session an `attach` leaves, where that attach names a coordinator target: the
control link exists, and with it the transaction layer.

Part 4's two directions announce different things — "When sent by the transaction
controller (the sending endpoint), [the capabilities field] indicates the desired
capabilities of the coordinator. When sent by the resource (the receiving endpoint), [it
defines] the actual capabilities of the coordinator" — so an attach this endpoint sends
records its own announcement and an attach it receives records the partner's. A later
attach that names no coordinator leaves the layer where it is: a session has one link, and
Transaction-layer presence is a fact about the link rather than a switch a frame may flip
off. -/
def Session.withControlLink (session : Session) (outbound : Bool) (body : Value) : Session :=
  match (fieldValue "attach" "target" body).bind Transactions.coordinatorCapabilities with
  | none => session
  | some capabilities =>
    let layer := session.transactions.getD Transactions.Layer.fresh
    { session with
        transactions := some (if outbound then { layer with capabilities }
                              else { layer with peerCapabilities := capabilities }) }

/-- The session a released link leaves: the control link's transactions are rolled back.

"Note that links to the «coordinator» cannot be resumed", and "If the control link is
closed while there exist non-discharged transactions it created, then all such
transactions are immediately rolled back, and attempts to perform further transactional
work on them will lead to failure." The link's close is the detach that releases it, which
is the release `detachLink` performs rather than every detach a peer may send. -/
def Session.afterLinkRelease (session : Session) : Session :=
  { session with transactions := session.transactions.map Transactions.Layer.retireAll }

/-- The handle a frame names, in the direction it travels: a received frame names the
handle the *peer* assigned, and a sent frame names ours, which is the meaning `link-handles`
gives the two — "the locally chosen handle is referred to as the output handle", "the
remotely chosen handle is referred to as the input handle", and the handle "is used by the
peer as a shorthand to refer to the link in all frames that reference the link".

A frame that names a handle other than the attached one is refused with the
`unattached-handle` session error, which is `flow/field:handle.1`'s rule: "If set to a
handle that is not currently associated with an attached link, the recipient MUST respond
by ending the session with a «session-error» session error."

A frame that names *no* handle is left to the declared surface: `flow/field:handle` is not
mandatory (a flow carrying only the session's windows is legal), while `attach`, `detach`
and `transfer` are, and `missingMandatory` is what refuses those. What a handle-less flow
must not do is carry the link's fields, and `flowLink` enforces the four clauses that say
so. -/
def linkHandleOf (session : Session) (outbound : Bool) (typeName : String) (body : Value) :
    Except Refusal Unit := do
  match fieldValue typeName "handle" body with
  | none | some .null => return ()
  | some value =>
    let handle ←
      match valueNat value with
      | some handle => pure handle
      | none => .error (refusal invalidField "malformed"
          s!"the {typeName}'s handle field is not an integer")
    let mine ←
      match (if outbound then session.handle else session.peerHandle) with
      | some mine => pure mine
      | none => .error (refusal unattachedHandle "illegalState"
          s!"a {typeName} names handle {handle}, and this endpoint has no attached link")
    refuseUnless (handle == mine)
      (refusal unattachedHandle "illegalState"
        s!"the {typeName} names handle {handle}, and this endpoint's link is handle {mine}")

/-- The delivery-count a `flow` must carry, in every direction and in both its halves:
`flow/field:delivery-count.2` — "When the handle identifies that the flow state is being sent
from the sender link endpoint to receiver link endpoint this field MUST be set to the current
delivery-count of the link endpoint" — `.3`, the same field sent the other way, which "MUST be
set to the last known value of the corresponding sending endpoint", and `.4`, its exception —
"In the event that the receiving link endpoint has not yet seen the initial «attach» frame from
the sender this field MUST NOT be set".

One quantity answers all four directions, and that is why the rule is one function rather than
one per direction: this endpoint's `position.deliveryCount` *is* "the current delivery-count of
the link endpoint" when the issuing link endpoint is the sender, and *is* "the last known value
of the corresponding sending endpoint" when it is the receiver — a receiver's count is its
record of the sender's, advanced by the messages it receives. So a flow that names the link must
carry the field, and what it carries must be that one value, whichever end issued the frame.

`.4` is the one case where the field must be *absent*, and its subject is the receiving link
endpoint that has not yet seen the sender's attach: the issuing end is the receiver and the
link's sender has not attached yet, which is `session.role`/`session.peerRole` asked of the
direction the frame travels. `none` is the field the body's list stops short of; a null the list
*reaches* is a value the frame carries, which `valueNat` reports as not an integer, the reading
`flow/field:delivery-count.2`'s null vector is refused by. -/
def flowCountRefusal? (session : Session) (outbound : Bool) (body : Value) :
    Option Refusal :=
  if !fieldSet "flow" "handle" body then none
  else
    let issuing := if outbound then session.role else session.peerRole
    let senderSeen := if outbound then session.peerRole.isSome else session.role.isSome
    let receiverBeforeSender := issuing == some LinkRole.receiver && !senderSeen
    match fieldValue "flow" "delivery-count" body with
    | none =>
      if receiverBeforeSender then none
      else some (refusal invalidField "malformed"
        "a flow that names the link MUST set its delivery-count, and this one omits it")
    | some value =>
      if receiverBeforeSender then
        some (refusal invalidField "malformed"
          "the receiving link endpoint has not yet seen the initial attach frame from the \
            sender, so its flow MUST NOT set the delivery-count")
      else
        match session.position, valueNat value with
        | none, _ => none
        | some _, none => some (refusal invalidField "malformed"
            "the flow's delivery-count is not an integer")
        | some current, some carried =>
          if carried == current.deliveryCount then none
          else some (refusal invalidField "malformed"
            s!"the flow carries delivery-count {carried}, and this endpoint's \
              {if outbound then "current" else "last known"} count is \
              {current.deliveryCount}")

/-- The `link-credit` echo, in the direction the issuing end writes: `links/doc:flow-control.u1`
— "Only the receiver can independently choose a value for this field" — `.u3` — "Only the receiver
can independently modify this field" — and the flow field's own `link-credit.u1` — "Only the
receiver endpoint can independently set this value" — which the doc's following sentence states the
other half of: "The sender's value is always the last known value indicated by the receiver."

The subject is the issuing link endpoint, so the rule is one function: a flow from the sender
echoes the receiver's last known value — which is this endpoint's `position.credit`, whether the
frame arrives from the peer's sender or is one this endpoint writes as its own sender — while a
flow from the receiver sets it, which is why the rule is silent there. -/
def flowCreditEchoRefusal? (session : Session) (outbound : Bool) (body : Value) :
    Option Refusal :=
  if !fieldSet "flow" "handle" body then none
  else
    let issuing := if outbound then session.role else session.peerRole
    if issuing != some LinkRole.sender then none
    else
      match session.position, (fieldValue "flow" "link-credit" body).bind valueNat with
      | some current, some credit =>
        if credit == current.credit then none
        else some (refusal invalidField "malformed"
          s!"a flow from the link's sender carries link-credit {credit}, and this endpoint's last \
            known value for it is {current.credit}")
      | _, _ => none

/-- The attach exchange: the handle rules (`attach/field:handle.1` — "The handle MUST NOT
be used for other open links" — with `.2`'s mandated close, and `begin/field:handle-max`
in both directions), the delivery-count the sender's attach must carry
(`attach/field:initial-delivery-count.1` — "This MUST NOT be null if role is sender"),
and the flow state the doc's `flow-control` defines for a fresh link. -/
def attachLink (session : Session) (outbound : Bool) (body : Value) :
    Except Refusal Session := do
  let role ←
    match (fieldValue "attach" "role" body).bind LinkRole.ofValue with
    | some role => pure role
    | none => .error (refusal invalidField "malformed"
        "the attach must carry a role, and it must be one of the values the declared \
          role type names")
  let handle ←
    match (fieldValue "attach" "handle" body).bind valueNat with
    | some handle => pure handle
    | none => .error (refusal invalidField "malformed"
        "the attach must carry an integer handle")
  let claimed := if outbound then session.handles else session.peerHandles
  let bound := if outbound then session.peerHandleMax else session.handleMax
  -- `begin/field:handle-max.1/.2`: a peer MUST NOT attach outside its partner's range,
  -- and a peer that receives one MUST close the connection with the framing-error. The
  -- condition is the artifact's own for an out-of-range value in the `open`'s doc; the
  -- class names the bound.
  refuseUnless (handle ≤ bound)
    (if outbound then
      closingRefusal framingError "limit"
        s!"the handle {handle} is outside the range {session.peerHandleMax} the partner's \
          begin declared it would accept"
     else
      closingRefusal framingError "limit"
        s!"handle {handle} is outside the range {session.handleMax} this endpoint's begin \
          declared")
  -- `attach/field:handle.2`: an attach using a handle already associated with a link is
  -- answered with an immediate close carrying a handle-in-use session error
  refuseUnless (!claimed.contains handle)
    (closingRefusal handleInUse "illegalState"
      s!"handle {handle} is already associated with a link, and a handle MUST NOT be used \
        for other open links")
  let initialCount ←
    match (fieldValue "attach" "initial-delivery-count" body).bind valueNat with
    | some count => pure count
    | none =>
      if role == LinkRole.sender then
        .error (refusal invalidField "malformed"
          "a sender's attach MUST carry its initial delivery-count")
      else pure 0
  let senderSettle :=
    -- `transfer/field:settled.4`'s antecedent is the *choice* `<xref name="sender-settle-mode"
    -- choice="settled"/>` of `attach`'s `snd-settle-mode` field, not the field's declared
    -- *type*. `sender-settle-mode` names the type, whose choices are `unsettled`, `settled`
    -- and `mixed`; `.4` and `.6` each select one choice within it, and reading the name where
    -- the sentence selects a choice inverts which obligation governs which negotiated value —
    -- settling on at least one transfer would be required of the sender that negotiated
    -- `unsettled` and forbidden to the one that negotiated `settled`. The number is the
    -- table's, read through the choice table rather than typed, and the selection is written
    -- as the comparison the clause states so that what the session records is definitionally
    -- the choice the artifact names.
    (fieldValue "attach" "snd-settle-mode" body).bind valueNat ==
      ((choiceValue? "sender-settle-mode" "settled").bind String.toNat?)
  let senderUnsettled :=
    -- `.6`'s antecedent is the *other* choice of the same element, `.4`'s is the `settled` one:
    -- the negotiation is three-valued, so the two obligations are recorded separately rather
    -- than collapsed into one flag. See `Session.senderSettleUnsettled`.
    (fieldValue "attach" "snd-settle-mode" body).bind valueNat ==
      ((choiceValue? "sender-settle-mode" "unsettled").bind String.toNat?)
  let receiverSecond :=
    -- `transfer/field:rcv-settle-mode.u1`'s antecedent, from the same element's receiver half:
    -- "If the negotiated link value is «first», then it is illegal to set this field to
    -- «second»". The attach field's declared default is `first`, so an attach that leaves the
    -- field unset is `first`, which is what `none == some second` already answers.
    (fieldValue "attach" "rcv-settle-mode" body).bind valueNat ==
      ((choiceValue? "receiver-settle-mode" "second").bind String.toNat?)
  let position : Option Position :=
    match role with
    | LinkRole.sender => some ⟨initialCount, 0⟩
    | LinkRole.receiver => some ⟨0, 0⟩
  if outbound then
    -- a link that is being established starts with nothing agreed: the credit is the
    -- partner's to grant and the partner's count is its own announcement, so until this
    -- link's first flow arrives this endpoint's view of both is empty
    return { session with
               handle := some handle, handles := handle :: session.handles,
               role := some role, position, peerCount := 0, peerCredit := 0, delivery := none,
               deliveryTag := none, deliveryFormat := none,
               senderSettleMode := if role == LinkRole.sender then senderSettle else session.senderSettleMode,
               senderSettleUnsettled := if role == LinkRole.sender then senderUnsettled else session.senderSettleUnsettled,
               receiverSettleSecond := if role == LinkRole.receiver then receiverSecond else session.receiverSettleSecond }
  else
    return { session with
               peerHandle := some handle, peerHandles := handle :: session.peerHandles,
               -- the partner's delivery-count is a quantity its owner announces: it is
               -- the sender's ("Only the sender MAY independently modify this field", and
               -- its `initial-delivery-count` "MUST NOT be null if role is sender"), so a
               -- received attach sets this endpoint's view of it only when the partner is
               -- the link's sender and this endpoint is its receiver
               peerRole := some role,
               peerCount := (if role == LinkRole.sender && session.role == some LinkRole.receiver
                             then initialCount else session.peerCount),
               position := (if role == LinkRole.sender || session.position.isSome then
                              session.position
                            else position),
               delivery := none,
               deliveryTag := none, deliveryFormat := none,
               senderSettleMode := if role == LinkRole.sender then senderSettle else session.senderSettleMode,
               senderSettleUnsettled := if role == LinkRole.sender then senderUnsettled else session.senderSettleUnsettled,
               receiverSettleSecond := if role == LinkRole.receiver then receiverSecond else session.receiverSettleSecond }

/-- The flow exchange: the flow's own fields against the link's state. The windows'
arithmetic lives at the session, above; what is here is the link's half of the doc's
`flow-control` — the credit formula in the sender's direction, the delivery-count a flow
carries in each direction, and the handle it must name. -/
def flowLink (session : Session) (outbound : Bool) (body : Value) :
    Except Refusal Session := do
  -- the five clauses that couple the link's fields to the handle: `available`, `drain`,
  -- `delivery-count`, `link-credit` and `properties` each say "When the handle field is
  -- not set, this field MUST NOT be set", so a flow carrying only the session's state
  -- carries none of them. `echo` is not among them: its own clause says that set with no
  -- handle it asks for the *session's* state, which is the case it exists for.
  if !fieldSet "flow" "handle" body then
    let linkFields :=
      [("delivery-count", fieldSet "flow" "delivery-count" body),
       ("link-credit", fieldSet "flow" "link-credit" body),
       ("available", fieldSet "flow" "available" body),
       ("drain", fieldSet "flow" "drain" body),
       ("properties", fieldSet "flow" "properties" body)]
    let carried := (linkFields.filter (fun entry => entry.2)).map (fun entry => entry.1)
    refuseUnless carried.isEmpty
      (refusal invalidField "malformed"
        s!"a flow that does not set the handle MUST NOT set {carried}, and this one carries \
          the link's fields without naming the link")
  let _ ← linkHandleOf session outbound "flow" body
  refuseUnless ((flowCountRefusal? session outbound body).isNone)
    ((flowCountRefusal? session outbound body).getD
      (refusal invalidField "malformed" "the flow's delivery-count is wrong"))
  refuseUnless ((flowCreditEchoRefusal? session outbound body).isNone)
    ((flowCreditEchoRefusal? session outbound body).getD
      (refusal invalidField "malformed" "the flow's link-credit is wrong"))
  if !fieldSet "flow" "handle" body then
    -- a flow that names no link carries the session's windows and nothing of the link's:
    -- the four field clauses forbid it carrying the link's fields, so nothing here reads
    -- them and the link's own accounting is left where it was
    return session
  if outbound then
    -- nothing here recomputes our own grant: a flow this endpoint writes as the receiver *sets*
    -- the credit, and the echo rule above has already answered for the sender's direction
    return session
  else
    let receivedCredit ←
      match (fieldValue "flow" "link-credit" body).bind valueNat with
      | some credit => pure credit
      | none => pure 0
    let receivedCount ←
      match (fieldValue "flow" "delivery-count" body).bind valueNat with
      | some count => pure count
      | none => pure 0
    if session.role == some LinkRole.sender then
      -- the doc's formula, applied where a sender's credit is set
      let position : Option Position :=
        match session.position with
        | some current => some { current with
            credit := Position.creditFor receivedCount receivedCredit current.deliveryCount }
        | none => session.position
      return { session with position, peerCount := receivedCount, peerCredit := receivedCredit }
    else
      match session.position with
      | some current =>
        -- "The receiver's value is calculated based on the last known value from the
        -- sender and any subsequent messages received on the link"
        return { session with
                   position := some { current with deliveryCount := receivedCount },
                   peerCredit := receivedCredit }
      | none => return session

/-- `transfer/field:rcv-settle-mode.u1` and `.u2`. `.u1` states the rule — "If the negotiated
link value is «first», then it is illegal to set this field to «second»" — against a *choice* the
attach fixed the link at, and `.u2` gives the exemption the field's own doc states: "If the
message is being sent settled by the sender, the value of this field is ignored".

So a transfer setting the field to the `second` choice is refused exactly when the link's
receiver settled on the `first` choice — which is what an attach that leaves the field unset
declares, the field's declared default being `first` — and the transfer does not carry `settled`
true. The choice's number is read from the generated table, so neither the number nor the
element's name is typed here. -/
def rcvSettleRefusal? (session : Session) (body : Value) (settled : Bool) : Option Refusal :=
  match (fieldValue "transfer" "rcv-settle-mode" body).bind valueNat with
  | none => none
  | some mode =>
    if settled || session.receiverSettleSecond then none
    else if some mode == ((choiceValue? "receiver-settle-mode" "second").bind String.toNat?) then
      some (refusal invalidField "malformed"
        "the transfer sets rcv-settle-mode to the second choice, and the link negotiated the \
          first choice")
    else none

/-- `transfer/field:settled.6`: "If the negotiated value for snd-settle-mode at attachment is
<xref name="sender-settle-mode" choice="unsettled"/>, then this field MUST be false (or unset) on
every transfer frame for a delivery (unless the delivery is aborted)".

The negotiation is the `unsettled` *choice* of the element `.4` selects the `settled` choice of —
the two are opposite obligations on the one field, which is why the session records both — and the
exemption is the transfer's own `aborted` flag, which voids the delivery the sentence is about. The
flag is read by its *value*, so an explicit `false` is the conforming encoding as much as an absent
field. -/
def unsettledSettleRefusal? (session : Session) (settled aborted : Bool) : Option Refusal :=
  if session.senderSettleUnsettled && settled && !aborted then
    some (refusal invalidField "malformed"
      "the link negotiated the unsettled choice of sender-settle-mode, so the settled flag MUST \
        be false (or unset) on a transfer for a delivery unless the delivery is aborted")
  else none

/-- The two negotiated-settlement rules on a transfer's own fields, as the one guard `transferLink`
runs: `rcv-settle-mode.u1`'s refusal — with `.u2`'s exemption — or, where that is silent,
`settled.6`'s. Each sentence keeps its own predicate above, so a disposition names the declaration
the clause it carries turns on; this is only the composition, and it is one guard rather than two
because the two are the two halves of one negotiation: a link is `unsettled` on its sender's side
or `second` on its receiver's, and a transfer can break at most one of the two sentences at once. -/
def negotiatedSettleRefusal? (session : Session) (body : Value) (settled aborted : Bool) :
    Option Refusal :=
  match rcvSettleRefusal? session body settled with
  | some reason => some reason
  | none => unsettledSettleRefusal? session settled aborted

/-- The transfer exchange. What is here is what the transfer clauses and the doc's
`flow-control` make checkable per frame: the role the direction requires, the credit a
sender spends, the first-transfer fields `delivery-id`, `delivery-tag` and
`message-format` require ("MUST be supplied on the first transfer of a multi-transfer
delivery", "MUST be specified for the first transfer of a multi-transfer message and can
only be omitted for continuation transfers"), the `settled` interpretation, `settled.4`'s
obligation at the end of a delivery, and `aborted`'s discard. -/
def transferLink (session : Session) (outbound : Bool) (body : Value) :
    Except Refusal Session := do
  let _ ← linkHandleOf session outbound "transfer" body
  -- the direction the role fixes: a transfer is the sender's frame
  let sender := session.role == some LinkRole.sender
  refuseUnless (outbound == sender)
    (refusal illegalStateCondition "illegalState"
      s!"a transfer is the sender's frame, and this endpoint attached as \
        {(session.role.getD LinkRole.receiver).name}")
  let continued := session.delivery.isSome
  -- the three fields a continuation may repeat, omit or *contradict*, read once here: the two
  -- the held delivery does not carry are recorded by the transfer that begins a delivery, and
  -- `delivery-id` is compared against the id the delivery already holds
  let carriedId := (fieldValue "transfer" "delivery-id" body).bind valueNat
  let carriedTag := (fieldValue "transfer" "delivery-tag" body).bind valueOctets
  let carriedFormat := (fieldValue "transfer" "message-format" body).bind valueNat
  let id ←
    match carriedId with
    | some id => pure id
    | none =>
      match session.delivery with
      | some delivery => pure delivery.id
      | none => .error (refusal invalidField "malformed"
          "the first transfer of a delivery MUST carry its delivery-id")
  -- `delivery-tag.1` and `message-format.1`: both "MUST be specified for the first
  -- transfer of a multi-transfer message and can only be omitted for continuation
  -- transfers"
  refuseUnless (continued || (fieldSet "transfer" "delivery-tag" body &&
                              fieldSet "transfer" "message-format" body))
    (refusal invalidField "malformed"
      "a first transfer MUST carry its delivery-tag and message-format, which only a \
        continuation transfer may omit")
  -- `delivery-id.u1`, `delivery-tag.u1` and `message-format.u1`: each says "It is an error if
  -- [the field] on a continuation transfer differs from [the field] on the first transfer of a
  -- delivery". Only a continuation can contradict anything — a first transfer's values are what
  -- a later transfer is compared against, so they cannot differ from themselves — and omission is
  -- not a difference: `delivery-id.2` makes it a MAY and the other two's first sentence lets a
  -- continuation omit them. So each rule is checked against a value the frame *carries*, and one
  -- this endpoint has no reading of leaves the continuation unconstrained rather than refused.
  if continued then do
    refuseUnless (carriedId.isNone || session.delivery.map (fun held => held.id) == carriedId)
      (refusal invalidField "malformed"
        "the delivery-id of a continuation transfer differs from the delivery-id of the \
          delivery it continues, which `transfer/field:delivery-id.u1` makes an error")
    refuseUnless (carriedTag.isNone || carriedTag == session.deliveryTag)
      (refusal invalidField "malformed"
        "the delivery-tag of a continuation transfer differs from the delivery-tag of the \
          delivery it continues, which `transfer/field:delivery-tag.u1` makes an error")
    refuseUnless (carriedFormat.isNone || carriedFormat == session.deliveryFormat)
      (refusal invalidField "malformed"
        "the message-format of a continuation transfer differs from the message-format of \
          the delivery it continues, which `transfer/field:message-format.u1` makes an error")
  -- a boolean means its value: `settled`, `aborted` and `more` set to false are not the
  -- same as unset, which `settled.6`'s "false (or unset)" and the artifact's `settled=False`
  -- diagrams both turn on
  let settled := fieldBool "transfer" "settled" body
  let aborted := fieldBool "transfer" "aborted" body
  -- `more` decides whether this transfer completes the delivery; `aborted` discards it
  -- ("Aborted messages SHOULD be discarded by the recipient"), and `more.u1` gives
  -- `aborted` precedence when both are set to true
  let more := !aborted && fieldBool "transfer" "more" body
  let delivery : Except Refusal (Option Delivery) :=
    if aborted then pure none
    else if more then pure (some (Delivery.step session.delivery id settled))
    else
      -- the delivery completes here: `settled.4` obliges a sender whose negotiated mode is
      -- the `settled` *choice* of `sender-settle-mode` to settle it in at least one of its
      -- transfers. The element names the field's declared type; the sentence selects a
      -- choice within it, and reading the name where the sentence selects a choice is what
      -- put this guard under the wrong negotiation.
      let completed := Delivery.step session.delivery id settled
      if session.senderSettleMode && !completed.settled then
        .error (refusal invalidField "malformed"
          s!"the negotiated settlement mode is the settled choice of sender-settle-mode, so \
            a delivery MUST be \
            settled in at least one of its transfers, and delivery {id} is not")
      else pure none
  let delivery ← delivery
  -- The recorded identity lives exactly as long as the delivery it is about: the transfer that
  -- *begins* a delivery records what it carried, a continuation leaves the recording alone, and a
  -- delivery that completes or is discarded takes the recording with it — `delivery-id.u1` says
  -- "differs from the delivery-id on the first transfer of *a* delivery", so a value that outlived
  -- its delivery could be compared against the wrong one.
  let deliveryTag := if delivery.isSome then (if continued then session.deliveryTag else carriedTag)
                     else none
  let deliveryFormat :=
    if delivery.isSome then (if continued then session.deliveryFormat else carriedFormat) else none
  match session.position with
  | none => return { session with delivery, deliveryTag, deliveryFormat }
  | some current =>
      -- what the credit bounds is *messages*, not frames: `link-credit` is "the current
      -- maximum number of messages that can be handled at the receiver endpoint" and "the
      -- maximum legal amount that the delivery-count can be increased by", and the
      -- delivery-count "is incremented whenever a message is sent". So both move on the
      -- transfer that *begins* a delivery, and a continuation transfer of a delivery
      -- already counted moves neither and needs no credit to proceed.
      let starting := !continued
      if sender then
        refuseUnless (!starting || current.credit > 0)
          (refusal framingError "limit"
            "the link has no credit left: the sender's delivery-count has reached the \
              delivery-limit the receiver granted, and this transfer begins a delivery")
        let position : Position :=
          { current with
              credit := if starting then current.credit - 1 else current.credit,
              deliveryCount :=
                if starting then current.deliveryCount + 1 else current.deliveryCount }
        return { session with position := some position, delivery, deliveryTag, deliveryFormat }
      else
        -- the receiver's count follows the sender's: "any subsequent messages received"
        let position : Position :=
          { current with
              deliveryCount :=
                if starting then current.deliveryCount + 1 else current.deliveryCount }
        return { session with position := some position, delivery, deliveryTag, deliveryFormat }

/-- Whether a body is a disposition performative. The dispatch table gives it to the
session endpoint; this module's `Performative` names only the frames the session state
machine itself turns on, so the disposition is recognised by its declared type here. -/
def isDisposition (body : Value) : Bool :=
  match body with
  | .described descriptor _ =>
    match SpecAMQP.Spec.Frame.typeOfDescriptor descriptor with
    | some declaration => declaration.name == "disposition"
    | none => false
  | _ => false

/-- The detach exchange: the handle rules, and the effect `link-handles` gives a detach —
"this handle ... remains in use until the link is detached", so a detach releases it, and
a later frame that names it is refused with `unattached-handle`. A detach carrying an
`error` ends the link with that error, whose details this layer carries rather than
judges.

A detach is the one frame the links section excepts from its rule about input for a
detached link endpoint, which reads "other than a detach": a detach naming a handle this
endpoint does not have is therefore admitted, and it releases the link only when the
handle is the attached one. -/
def detachLink (session : Session) (outbound : Bool) (body : Value) :
    Except Refusal Session := do
  let named := ((fieldValue "detach" "handle" body).bind valueNat)
  let releasable := named == (if outbound then session.handle else session.peerHandle)
  if !releasable then return session
  if outbound then
    -- a released link takes its flow state with it: the credit is a quantity the partner
    -- granted for this link, and the partner's own count is its announcement about it, so
    -- neither outlives the link they are about. A control link's release also rolls back
    -- the transactions it created, "all such transactions are immediately rolled back"
    return Session.afterLinkRelease
      { session with handle := none, role := none, position := none,
                     peerCount := 0, peerCredit := 0, delivery := none,
                     deliveryTag := none, deliveryFormat := none }
  else
    return Session.afterLinkRelease
      { session with peerHandle := none, peerRole := none,
                     peerCount := 0, peerCredit := 0, delivery := none,
                     deliveryTag := none, deliveryFormat := none }

/-- The disposition exchange: `disposition.1/.2`'s directionality ("all links MUST have
the directionality indicated by the specified role"), the range `first`/`last` name, and
the settlement a disposition carries — which, when it settles the delivery this endpoint
is holding, releases it. -/
def dispositionLink (session : Session) (outbound : Bool) (body : Value) :
    Except Refusal Session := do
  let _ ← linkHandleOf session outbound "disposition" body
  let role ←
    match (fieldValue "disposition" "role" body).bind LinkRole.ofValue with
    | some role => pure role
    | none => .error (refusal invalidField "malformed"
        "the disposition must carry a role, and it must be one of the values the \
          declared role type names")
  -- the disposition is sent by the end the role names, so a disposition whose role is not
  -- the sender's is one this endpoint may not be holding at all
  refuseUnless (role == session.role.getD LinkRole.sender)
    (refusal invalidField "malformed"
      s!"the disposition names the {role.name}'s deliveries, and this endpoint is the \
        {(session.role.getD LinkRole.sender).name}")
  let first ←
    match (fieldValue "disposition" "first" body).bind valueNat with
    | some first => pure first
    | none => pure 0
  let last ←
    match (fieldValue "disposition" "last" body).bind valueNat with
    | some last => pure last
    | none => pure first
  refuseUnless (first ≤ last)
    (refusal invalidField "malformed"
      s!"the disposition's range runs from delivery {first} to {last}, which is not a \
        range")
  match session.delivery with
  | some delivery =>
    if fieldBool "disposition" "settled" body && first ≤ delivery.id && delivery.id ≤ last then
      return { session with delivery := none, deliveryTag := none, deliveryFormat := none }
    else return session
  | none => return session

/-! ## The transaction layer's carriers

Part 4's transaction performatives travel in two frames and nowhere else: the two message
bodies as a transfer's payload, and the outcome a coordinator answers with as a
disposition's `state`. Both reach the layer here, and only where the session has one — a
session whose link is not a control link dispatches exactly as it did before the layer
existed, which is what keeps the added arms unreachable for every exchange that does not
ask for them. -/

/-- One transaction value, from the frame that carried it.

Nothing is decided here: whether the value is a transaction performative at all is the
layer's question, and a value that is not one is carried. A refusal is placed the way the
link's other refusals are, by the caller. -/
def stepTransaction (session : Session) (carrier : Transactions.Carrier) (outbound : Bool)
    (value : Value) (settled : Bool) : Except Refusal Session := do
  match session.transactions with
  | none => return session
  | some layer =>
    match Transactions.step layer carrier outbound value settled with
    | .ok layer => return { session with transactions := some layer }
    | .error reason =>
      .error { condition := reason.condition, detail := reason.detail, state := none,
               closesConnection := false }

/-- The transaction layer's step for a transfer's payload.

Part 4's declare and discharge are message bodies, so the payload is read as a message
whose body is exactly one `amqp-value` section — the shape the section's own worked
exchange draws, `TRANSFER(delivery-id=0){ AmqpValue( Declare() ) }` — and the value it
carries is handed to the transaction layer.

Two shapes are deliberately *not* refusals here. A session whose link is not a control link
has no transaction layer, so its payload is what the transfer layer has always said it was,
opaque. And a payload that is not one amqp-value section is not a transaction message at
all — a `data` message is a perfectly ordinary body — which is the message layer's business
and not a rule this layer may invent; the clause that *is* about messages on a control link
states what they are for rather than refusing what they are not, and it is recorded as an
unpinned cell rather than enforced here. -/
def stepTransactionPayload (session : Session) (outbound : Bool) (payload : Octets)
    (settled : Bool) : Except Refusal Session := do
  match session.transactions with
  | none => return session
  | some _ =>
    match Message.bodyValue Message.Policy.empty payload with
    | .error _ => return session
    | .ok value => stepTransaction session .payload outbound value settled

/-- The transaction layer's step for a disposition's `state`, which is where a coordinator's
answer arrives: "If the declaration is successful, the coordinator responds with a
disposition outcome of «declared» which carries the assigned identifier for the
transaction." The settlement a disposition may carry is the disposition's own and not the
transfer's, so the value is handed over unsettled. -/
def stepTransactionState (session : Session) (outbound : Bool) (body : Value) :
    Except Refusal Session :=
  match fieldValue "disposition" "state" body with
  | some state => stepTransaction session .state outbound state false
  | none => .ok session

/-! ## Applying a step -/

/-- A window field as a number: the fields the arithmetic reads are mandatory, so a
performative that reaches the arithmetic carries them, and a field that is not a number
reads as zero rather than aborting the step — the mandatory rule has already refused the
performatives that omit them. -/
def fieldNumber (typeName : String) (body : Value) (fieldName : String) : Nat :=
  ((fieldValue typeName fieldName body).bind valueNat).getD 0

/-- The session a begin frame leaves, with the channel rules the artifact states for the
frame that announces a session endpoint: the `remote-channel` field "MUST be empty for a
locally initiated session, and MUST be set when announcing the endpoint created as a
result of a remotely initiated session" — where it is "the channel on which the remote
session sent the begin". -/
def stepBegin (session : Session) (outbound : Bool) (channel : Nat) (body : Value) :
    Except Refusal Session := do
  if outbound then
    match session.state with
    | .unmapped =>
      refuseUnless (!fieldSet "begin" "remote-channel" body)
        (refusal invalidField "malformed"
          "a locally initiated begin MUST NOT set a remote-channel, and this one does")
      let windows :=
        session.windows.afterSendingBegin (fieldNumber "begin" body "next-outgoing-id")
          (fieldNumber "begin" body "incoming-window") (fieldNumber "begin" body "outgoing-window")
      -- the handle maximum this endpoint announces, which `begin/field:handle-max.1`
      -- makes the bound its partner may not attach outside; a begin that leaves it unset
      -- announces the declared default
      let handleMax :=
        ((fieldValue "begin" "handle-max" body).bind valueNat).getD startHandleMax
      return { session with state := .beginSent, outgoing := some channel, windows, handleMax }
    | .beginRcvd =>
      match session.incoming, fieldValue "begin" "remote-channel" body with
      | some theirChannel, some value =>
        refuseUnless (valueNat value == some theirChannel)
          (refusal invalidField "malformed"
            s!"a begin answering a remotely initiated session MUST set the remote-channel \
              to the channel its begin arrived on, {theirChannel}")
        let windows :=
          session.windows.afterSendingBegin (fieldNumber "begin" body "next-outgoing-id")
            (fieldNumber "begin" body "incoming-window") (fieldNumber "begin" body "outgoing-window")
        let handleMax :=
          ((fieldValue "begin" "handle-max" body).bind valueNat).getD startHandleMax
        return { session with state := .mapped, outgoing := some channel, windows, handleMax }
      | _, _ =>
        .error (refusal invalidField "malformed"
          "a begin answering a remotely initiated session MUST set the remote-channel, \
            and this one leaves it empty")
    | other =>
      .error (refusal illegalStateCondition "illegalState"
        s!"a session sends one begin, and this one is already {other.name}")
  else
    match session.state with
    | .unmapped =>
      let windows := session.windows.afterReceivingBegin (fieldNumber "begin" body "next-outgoing-id")
        (fieldNumber "begin" body "incoming-window") (fieldNumber "begin" body "outgoing-window")
      let peerHandleMax :=
        ((fieldValue "begin" "handle-max" body).bind valueNat).getD startHandleMax
      return { session with state := .beginRcvd, incoming := some channel, peerBegun := true,
                            windows, peerHandleMax }
    | .beginSent =>
      let windows := session.windows.afterReceivingBegin (fieldNumber "begin" body "next-outgoing-id")
        (fieldNumber "begin" body "incoming-window") (fieldNumber "begin" body "outgoing-window")
      let peerHandleMax :=
        ((fieldValue "begin" "handle-max" body).bind valueNat).getD startHandleMax
      return { session with state := .mapped, incoming := some channel, peerBegun := true,
                            windows, peerHandleMax }
    | other =>
      .error (refusal illegalStateCondition "illegalState"
        s!"a session receives one begin, and this one is already {other.name}")

/-- The session an end frame leaves, following the diagram's arrows: a sent end goes to
END_SENT, or to DISCARDING when it carries an error; a received end goes to END_RCVD, and
to UNMAPPED where this endpoint had already sent its own. -/
def Session.afterEnd (session : Session) (outbound : Bool) (withError : Bool) : Session :=
  if outbound then
    match session.state with
    | .mapped =>
      { session with state := (if withError then .discarding else .endSent),
                     outgoing := none }
    | .endRcvd =>
      { session with state := .unmapped, outgoing := none, incoming := none,
                     peerBegun := false }
    | .beginSent =>
      -- the diagram's BEGIN_SENT --S:END--> END_SENT arrow: the label moves with the
      -- channel the end releases, because BEGIN_SENT's description claims that outgoing
      -- channel while END_SENT's claims no outgoing number and an incoming entry — the
      -- maps this record has
      { session with state := .endSent, outgoing := none }
    | other => { session with state := other, outgoing := none }
  else
    match session.state with
    | .endSent | .discarding =>
      { session with state := .unmapped, outgoing := none, incoming := none,
                     peerBegun := false }
    | _ => { session with state := .endRcvd, incoming := none, peerBegun := true }

/-- One frame the session layer answers for.

The checks are the artifact's: the frame must be one this session's channel carries (the
connection maps incoming frames to sessions by channel, so a frame on another channel is
not this session's to process), its mandatory fields must be set, and the state's own
description must permit the direction. A receive the session cannot process is answered by
the END the section mandates where the state can send at all — which is DISCARDING — and a
send it cannot take is simply not taken, leaving the state where it was.

`payload` is the octets after the performative, which the frame layer calls "the remaining
bytes in the frame body" whose meaning "is defined by the semantics of the given
performative": opaque for every performative but the transfer, whose payload a session
with a transaction layer reads as the transaction message it may carry. -/
def step (session : Session) (outbound : Bool) (channel : Nat) (body : Value)
    (payload : Octets) : Except Refusal Session := do
  let performative := Performative.ofBody body
  let typeName :=
    match performative with
    | .begin => "begin" | .end => "end" | .attach => "attach" | .detach => "detach"
    | .flow => "flow" | .transfer => "transfer"
    | .other => if isDisposition body then "disposition" else ""
  -- "any incoming frames on the session MUST be silently discarded until the peer's end
  -- frame is received": in the error-triggered close of DISCARDING what arrives is
  -- discarded without being looked at, and only the peer's end is answered
  if !outbound && session.state == .discarding && performative != .end then
    return session
  -- the channel this session answers on: the two begins are what establish the mapping,
  -- so they are the frames that arrive and leave before it exists
  let mapped := if outbound then session.outgoing else session.incoming
  refuseUnless (performative == .begin || mapped == some channel)
    (refusal wireCondition "illegalState"
      s!"channel {channel} is not mapped to this session, whose \
        {if outbound then "outgoing" else "incoming"} channel is {mapped}")
  -- what the state's own description permits: every frame but the begin, whose rule is
  -- the diagram's arrows rather than the permission column, since a session that is
  -- UNMAPPED "cannot send or receive frames" and the begin is the frame that maps it
  let permitted :=
    performative == .begin ||
      (if outbound then session.state.maySend else session.state.mayReceive)
  let placed (condition reasonClass prose : String) : Refusal :=
    if outbound then refusal condition reasonClass prose
    else
      -- the section's answer to input it cannot process: an END with an error, which the
      -- diagram draws from MAPPED to DISCARDING, and which a state that cannot send at
      -- all cannot issue
      -- `sessions.5` obliges an END with an error and `sessions.6` then obliges the
      -- session to discard incoming frames until the peer's end, so the phase is reached
      -- from every state that can still *receive*, not only from MAPPED: `END_SENT` may
      -- receive and so must reach it, while the states that cannot receive cannot issue
      -- the END at all and so stand where they are
      { refusal condition reasonClass prose with
          state := if session.state.mayReceive then some State.discarding else none }
  -- a refusal the link raises is placed the way every session refusal is: the section
  -- answers input it cannot process with the END an error, which is the diagram's
  -- MAPPED --S:END(error)--> DISCARDING arrow
  -- Three sites place a refusal, and each behaves differently, which is worth knowing
  -- before adding a rule: a *wire-level* refusal (the channel map, and the frames the
  -- decoder cannot read at all) is raised outside this path and leaves the state where it
  -- is; a *session-level* one goes through `placed` below; and a *link-level* one — the
  -- rules `flowLink`, `transferLink` and `detachLink` raise — goes through `place` here.
  -- The corpus reached this third site only once it had a vector whose refusal a channel
  -- map could not answer, so a rule added at the link level wants a vector keyed on that
  -- rule rather than on the channel it arrives by.
  let place (reason : Refusal) : Refusal :=
    if reason.closesConnection || outbound then reason
    else
      -- the same phase rule as `placed` below, for the refusals the link raises: a link
      -- refusal is input this session cannot process, so `sessions.6`'s discard reaches it
      -- from every state that can receive, not only from MAPPED
      { reason with
          state := if session.state.mayReceive then some State.discarding else reason.state }
  refuseUnless permitted
    (placed illegalStateCondition "illegalState"
      s!"{session.state.name} does not permit this session to \
        {if outbound then "send" else "receive"} a {performative.name} frame")
  -- the mandatory fields the generated field table states
  refuseUnless ((missingMandatory typeName body).isEmpty)
    (placed invalidField "malformed"
      s!"the {typeName} performative does not carry {missingMandatory typeName body}, \
        and the declared surface marks it mandatory")
  match performative with
  | .begin => stepBegin session outbound channel body
  | .attach =>
    match attachLink session outbound body with
    | .ok session => pure (session.withControlLink outbound body)
    | .error reason => .error (place reason)
  | .detach =>
    match detachLink session outbound body with
    | .ok session => pure session
    | .error reason => .error (place reason)
  | .end => return session.afterEnd outbound (fieldSet "end" "error" body)
  | .flow =>
    -- "This value MUST be set if the peer has received the begin frame for the session,
    -- and MUST NOT be set if it has not."
    let set := fieldSet "flow" "next-incoming-id" body
    refuseUnless (set == session.peerBegun)
      (placed invalidField "malformed"
        s!"a flow's next-incoming-id must be set exactly when the partner's begin has \
          arrived, and it is {if set then "set" else "unset"} while the begin has \
          {if session.peerBegun then "" else "not "}arrived")
    -- the link's half of the flow: the handle it names and the delivery-count it carries
    let session ←
      match flowLink session outbound body with
      | .ok session => pure session
      | .error reason => .error (place reason)
    if outbound then return session
    else
      -- "When the endpoint receives a «flow» frame from its peer, it MUST update the
      -- next-incoming-id directly from the next-outgoing-id of the frame, and it MUST
      -- update the remote-outgoing-window directly from the outgoing-window of the frame"
      let windows :=
        session.windows.afterReceivingFlow (fieldNumber "flow" body "next-outgoing-id")
          (fieldNumber "flow" body "incoming-window")
          (fieldNumber "flow" body "outgoing-window")
          ((fieldValue "flow" "next-incoming-id" body).bind valueNat)
      return { session with windows }
  | .transfer =>
    -- the settlement of the deliverable this transfer belongs to, as
    -- `transfer/field:settled.4` interprets it: a first transfer that leaves the flag
    -- unset means false, and a continuation carries what the delivery's earlier transfers
    -- set. Read here rather than after `transferLink`, which releases the delivery when
    -- the transfer completes it and would take the flag with it.
    let settled :=
      ((fieldValue "transfer" "settled" body).bind valueBool).getD
        ((session.delivery.map (fun delivery => delivery.settled)).getD false)
    -- The negotiated-settlement rules the transfer's own fields carry — `rcv-settle-mode.u1` with
    -- `.u2`'s exemption, and `settled.6` with `aborted`'s — answered here rather than inside
    -- `transferLink`, because the fields they read are the *link's* negotiation and the frame's
    -- own flags: this is the same gate that answers the flow's `next-incoming-id`, and it is where
    -- a frame the session cannot accept is refused whatever the link's other rules would say.
    let aborted := fieldBool "transfer" "aborted" body
    match negotiatedSettleRefusal? session body settled aborted with
    | some reason => .error (place reason)
    | none => pure ()
    if outbound then do
      -- the two windows a sent transfer is charged against: ours, which "defines the
      -- maximum number of outgoing «transfer» frames that the endpoint can currently
      -- send", and the partner's, which our remote-incoming-window mirrors
      refuseUnless (session.windows.outgoingWindow > 0)
        (placed windowViolation "limit" "this session's outgoing window is exhausted, so           it may not send another transfer")
      refuseUnless (session.windows.remoteIncomingWindow > 0)
        (placed windowViolation "limit" "the partner's incoming window is exhausted, so           it can accept no further transfers")
      -- the link's half: the role the direction requires, the credit the delivery spends,
      -- and the delivery the transfer carries
      let session ←
        match transferLink session outbound body with
        | .ok session => pure session
        | .error reason => .error (place reason)
      -- and the transaction layer's half, where the payload is a transaction message
      let session ←
        match stepTransactionPayload session outbound payload settled with
        | .ok session => pure session
        | .error reason => .error (place reason)
      return { session with
                 windows := session.windows.afterSendingTransfer startPolicy }
    else do
      refuseUnless (session.windows.incomingWindow > 0)
        (placed windowViolation "limit" "this session's incoming window is exhausted, so           it cannot receive another transfer")
      -- "the implicit transfer-id of the incoming transfer": the id the partner assigned
      -- it, which is the one this session expected
      let session ←
        match transferLink session outbound body with
        | .ok session => pure session
        | .error reason => .error (place reason)
      let session ←
        match stepTransactionPayload session outbound payload settled with
        | .ok session => pure session
        | .error reason => .error (place reason)
      return { session with
                 windows := session.windows.afterReceivingTransfer
                   session.windows.nextIncomingId startPolicy }
  | .other =>
    if isDisposition body then
      match dispositionLink session outbound body with
      | .ok session =>
        -- the outcome a coordinator answers a declare with arrives in the disposition's
        -- `state`, which is the second of the transaction layer's two carriers
        match stepTransactionState session outbound body with
        | .ok session => pure session
        | .error reason => .error (place reason)
      | .error reason => .error (place reason)
    -- a performative this slice does not model is carried rather than judged: the
    -- session's own state and channel rules still apply, and nothing here decides a
    -- moment the artifact leaves to a layer that is not here
    else return session

end SpecAMQP.Spec.Session
