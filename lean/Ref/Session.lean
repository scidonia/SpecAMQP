import Generated.Oasis.Fields
import Generated.Oasis.Types
import Ref.Connection
import Ref.Transactions

/-!
# The reference implementation of the session layer

Written from Part 2's session section — the seven state descriptions, the "State
Transitions" diagram, the clauses about the begin's `remote-channel`, the end, the
session error handling and the flow's `next-incoming-id` — and independently of
`Spec.Session`: the two share no definition, so their agreement over the exchange corpus
is evidence rather than a tautology. Where the specification reads the declared surface
from `Spec.Connection`'s readers, this reads the generated tables through its own
`Ref.Connection` helpers, which is the same independence the two connection layers have.

The scope is the milestone's: `begin`/`end`, `attach`/`detach`, `flow` and `transfer`
carrying one unfragmented `data` section. The link state machine is not here — `attach`'s
fields are read and its mandatory rule enforced from the declared surface, and nothing
tracks credit, delivery numbers or settlement — and a transfer's payload is opaque.
-/

namespace SpecAMQP.Ref.Session

open SpecAMQP.Generated.Oasis
  (ChoiceDecl TypeDecl choices errorConditionsOf types)
open SpecAMQP.Ref.Connection (missingMandatory numberOf valueOfField)
-- The transaction layer's state and the two names this module reads from it. Opened
-- selectively: `Ref.Transactions` also defines a `Refusal`, and this module has its own.
open SpecAMQP.Ref.Transactions (Layer coordinatorCapabilities)

/-! ## The state machine -/

/-- The seven session states, in the artifact's names. -/
inductive State where
  | unmapped
  | beginSent
  | beginRcvd
  | mapped
  | endSent
  | endRcvd
  | discarding
deriving Repr, BEq, DecidableEq

/-- The artifact's names, which are the vocabulary the corpus uses. -/
def State.label : State → String
  | .unmapped => "UNMAPPED"
  | .beginSent => "BEGIN_SENT"
  | .beginRcvd => "BEGIN_RCVD"
  | .mapped => "MAPPED"
  | .endSent => "END_SENT"
  | .endRcvd => "END_RCVD"
  | .discarding => "DISCARDING"

/-- Every state, in the artifact's order. -/
def State.labels : List State :=
  [.unmapped, .beginSent, .beginRcvd, .mapped, .endSent, .endRcvd, .discarding]

/-- The state a name denotes. -/
def State.lookup (name : String) : Option State :=
  State.labels.find? (fun state => state.label == name)

/-- The states whose descriptions say the endpoint MAY send: `BEGIN_SENT`, `MAPPED` and
`END_RCVD`; `UNMAPPED` "cannot send or receive frames", `BEGIN_RCVD` and `END_SENT`
"cannot send them", and `DISCARDING` is "a variant of the END_SENT state". -/
def sendAllowed : State → Bool
  | .beginSent => true
  | .mapped => true
  | .endRcvd => true
  | _ => false

/-- The states whose descriptions say the endpoint MAY receive: `BEGIN_RCVD`, `MAPPED`,
`END_SENT` and `DISCARDING`. -/
def receiveAllowed : State → Bool
  | .beginRcvd => true
  | .mapped => true
  | .endSent => true
  | .discarding => true
  | _ => false

/-- The performatives this layer answers for. -/
inductive Frame where
  | begin
  | end
  | attach
  | detach
  | flow
  | transfer
  | other
deriving Repr, BEq, DecidableEq

/-- The performative's name. -/
def Frame.label : Frame → String
  | .begin => "begin" | .end => "end" | .attach => "attach" | .detach => "detach"
  | .flow => "flow" | .transfer => "transfer" | .other => "another performative"

/-- The declared type a described value carries. -/
def declaredType (body : Value) : Option TypeDecl :=
  match body with
  | .described descriptor _ =>
    match descriptor with
    | .ulong code =>
      types.find? (fun t => match t.descriptor with
        | some d => d.domain * 2 ^ 32 + d.code == code.toNat
        | none => false)
    | .symbol name => types.find? (fun t => t.name == name)
    | _ => none
  | _ => none

/-- The performative a body is. -/
def frameOf (body : Value) : Frame :=
  match declaredType body with
  | none => .other
  | some t =>
    if t.name == "begin" then .begin
    else if t.name == "end" then .end
    else if t.name == "attach" then .attach
    else if t.name == "detach" then .detach
    else if t.name == "flow" then .flow
    else if t.name == "transfer" then .transfer
    else .other

/-! ## Refusals -/

/-- A refusal: the condition the END it raises would name, the reason class, the prose,
and the state it leaves. -/
structure Refusal where
  condition : String
  reasonClass : String
  text : String
  place : Option State
  /-- Whether the session's rule obliges an immediate *connection* close — `handle.2` and
  `handle-max.2` do — which the connection layer owns and the codec performs. -/
  closes : Bool := false

/-- A choice's declared value, looked up through the type that declares it, so a
condition is read from the generated table rather than typed. -/
def declaredChoice (typeName choiceName : String) : Option String :=
  match (types.find? (fun t => t.name == typeName)).map (fun t => t.path) with
  | none => none
  | some path =>
    (choices.find? (fun c => c.ownerPath == path && c.name == choiceName)).map
      (fun c => c.value)

/-- The condition for input a session cannot process: the `amqp-error` family's
`illegal-state`. -/
def illegalStateCondition : String :=
  (declaredChoice "amqp-error" "illegal-state").getD "no illegal-state in the choice table"

/-- The condition for a performative whose field breaks a rule the declared surface
states: the `amqp-error` family's `invalid-field`. -/
def invalidFieldCondition : String :=
  (declaredChoice "amqp-error" "invalid-field").getD "no invalid-field in the choice table"

/-- The condition for a transfer that exceeds a window: the `session-error` family's
`window-violation`, read from the generated choice table. -/
def windowViolationCondition : String :=
  (declaredChoice "session-error" "window-violation").getD "no window-violation in the choice table"

/-- The condition for a frame that is not this session's to answer: the one
connection-error the artifact raises for wire-level failures. -/
def wireCondition : String :=
  match (errorConditionsOf "connection-error").find?
      (fun c => c.name == "framing-error") with
  | some c => c.value
  | none => "no framing-error in the connection-error choice"

/-- A refusal of one class. -/
def refuse (condition reasonClass text : String) : Refusal :=
  ⟨condition, reasonClass, text, none, false⟩

/-- The rendered detail: the class first, which is what the corpus and the differential
comparison read. -/
def Refusal.detail (refusal : Refusal) : String :=
  s!"{refusal.reasonClass}: {refusal.text}"

/-! ## The declared surface, as this layer reads it -/

/-! ## The flow-control state (doc `session-flow-control`) -/

/-- The id space the transfer numbers run in: a `transfer-number` is a `uint`, and the
doc increments next-outgoing-id "according to RFC-1982 serial number arithmetic". -/
def idSpace : Nat := 2 ^ 32

/-- The six variables the doc names, plus the `initial-outgoing-id` its second formula for
`remote-incoming-window` refers to. -/
structure Windows where
  nextIncoming : Nat
  incoming : Nat
  nextOutgoing : Nat
  outgoing : Nat
  remoteIncoming : Nat
  remoteOutgoing : Nat
  initialOutgoing : Nat
deriving Repr, BEq

/-- The arithmetic baseline a corpus start assumes when the begins that would have set the
windows are not in the vector: both peers' windows 1000 and both ids 0. -/
def Windows.start : Windows := ⟨0, 1000, 0, 1000, 1000, 1000, 0⟩

/-- The windows this endpoint's own begin announces. -/
def Windows.afterSendingBegin (w : Windows) (nextOutgoing incoming outgoing : Nat) : Windows :=
  { w with nextOutgoing := nextOutgoing % idSpace, initialOutgoing := nextOutgoing % idSpace,
           incoming := incoming, outgoing := outgoing }

/-- The windows the partner's begin sets: the id it will put on its first transfer, and
the two remote windows the doc's formula gives with the unset branch taken. -/
def Windows.afterReceivingBegin (w : Windows) (theirNextOutgoing theirIncoming
    theirOutgoing : Nat) : Windows :=
  { w with nextIncoming := theirNextOutgoing % idSpace,
           remoteIncoming := (w.initialOutgoing + theirIncoming) % idSpace - w.nextOutgoing,
           remoteOutgoing := theirOutgoing }

/-- The doc's "sending a transfer": next-outgoing-id increments, remote-incoming-window
decrements, and outgoing-window decrements under the policy the artifact leaves open. -/
def Windows.afterSendingTransfer (w : Windows) (policy : Bool) : Windows :=
  { w with nextOutgoing := (w.nextOutgoing + 1) % idSpace,
           remoteIncoming := w.remoteIncoming - 1,
           outgoing := if policy then w.outgoing - 1 else w.outgoing }

/-- The doc's "receiving a transfer". -/
def Windows.afterReceivingTransfer (w : Windows) (transferId : Nat) (policy : Bool) : Windows :=
  { w with nextIncoming := (transferId + 1) % idSpace,
           remoteOutgoing := w.remoteOutgoing - 1,
           incoming := if policy then w.incoming - 1 else w.incoming }

/-- The doc's "receiving a flow": next-incoming-id comes "directly from the
next-outgoing-id of the frame", remote-outgoing-window "directly from the outgoing-window
of the frame", and remote-incoming-window from the formula, whose first branch needs the
frame's next-incoming-id and whose second uses this endpoint's initial-outgoing-id. -/
def Windows.afterReceivingFlow (w : Windows) (frameNextOutgoing frameIncoming frameOutgoing : Nat)
    (frameNextIncoming : Option Nat) : Windows :=
  { w with nextIncoming := frameNextOutgoing % idSpace,
           remoteOutgoing := frameOutgoing,
           remoteIncoming :=
             ((frameNextIncoming.getD w.initialOutgoing) + frameIncoming) % idSpace -
               w.nextOutgoing }

/-- The policy the doc's two MAY-decrements are subject to, held as a value so the choice
is visible rather than compiled in. -/
def windowPolicy : Bool := true

/-! ## The link machine -/

/-- The role an `attach`'s or `disposition`'s `role` field names. The field's declared type
is a restricted boolean and the choice table spells which boolean is which, so the mapping
is read rather than assumed. -/
inductive Role where
  | sender
  | receiver
deriving Repr, BEq

def Role.label : Role → String
  | .sender => "sender"
  | .receiver => "receiver"

def Role.ofValue (value : Value) : Option Role :=
  match value with
  | .boolean bit =>
    let sender := (declaredChoice "role" "sender").getD "false" == "true"
    let receiver := (declaredChoice "role" "receiver").getD "true" == "true"
    if bit == sender && bit != receiver then some .sender
    else if bit == receiver && bit != sender then some .receiver
    else none
  | _ => none

/-- The doc `flow-control` gives a link two variables: `delivery-count`, "not a count but a
sequence number initialized at an arbitrary point by the sender", and `link-credit`, "the
current maximum legal amount that the delivery-count can be increased by". -/
structure Position where
  count : Nat
  credit : Nat
deriving Repr, BEq

/-- The doc's formula for a sender: `link-credit_snd := delivery-count_rcv +
link-credit_rcv - delivery-count_snd`. -/
def Position.creditFor (receivedCount receivedCredit sentCount : Nat) : Nat :=
  receivedCount + receivedCredit - sentCount

/-- The delivery a transfer carries, with the `settled` flag the transfer clauses define as
an interpretation rather than a field: false on a first transfer that leaves it unset, and
on a continuation true if and only if a preceding transfer of the delivery set it. -/
structure Delivery where
  id : Nat
  settled : Bool
deriving Repr, BEq

def Delivery.advance (current : Option Delivery) (id : Nat) (settled : Bool) : Delivery :=
  match current with
  | some delivery => { delivery with settled := delivery.settled || settled }
  | none => ⟨id, settled⟩

/-- The handle maximum an endpoint announces when its begin leaves the field unset: the
default the generated field table declares, rather than a number typed here. -/
def declaredHandleMax : Nat :=
  match (SpecAMQP.Generated.Oasis.fieldsOf
      "amqp:transport/section:performatives/type:begin").find?
      (fun field => field.name == "handle-max") with
  | some field => (field.defaultValue.bind String.toNat?).getD 0
  | none => 0

/-- A window field read through the connection layer's reader, whose refusal is the same
rule and is re-stated in this layer's refusal: the field rules do not change with the
layer that reads them, and the condition it names is the one the session's refusal
carries. -/
def windowField (typeName fieldName : String) (body : Value) : Except Refusal Nat :=
  match SpecAMQP.Ref.Connection.integerField typeName fieldName body with
  | .ok number => .ok number
  | .error refusal =>
    .error ⟨refusal.condition, refusal.reasonClass, refusal.text, none, false⟩

/-! ## The endpoint -/

/-- One session endpoint: its state, the outgoing channel its begin assigned, the
incoming channel the partner's begin arrived on, and whether that begin has arrived. -/
structure Endpoint where
  state : State
  outgoing : Option Nat
  incoming : Option Nat
  peerBegun : Bool
  windows : Windows
  /-- The role this endpoint attached with, and the role its partner attached with. -/
  role : Option Role
  peerRole : Option Role
  /-- The output handle (this endpoint's) and the input handle (the partner's). -/
  handle : Option Nat
  peerHandle : Option Nat
  /-- The handles each side has claimed: `attach/field:handle.1` forbids reusing one, and
  the uniqueness invariant in `Proofs/` is about the first of these lists. -/
  handles : List Nat
  peerHandles : List Nat
  /-- The handle maximum this endpoint announced and the one the partner announced. -/
  handleMax : Nat
  peerHandleMax : Nat
  /-- The link's flow state, once attached. -/
  position : Option Position
  /-- The partner's delivery-count and link-credit as its last flow reported them. -/
  peerCount : Nat
  peerCredit : Nat
  /-- Whether the sender side's settlement mode is sender-settle-mode. -/
  senderSettleMode : Bool
  /-- The delivery in progress, while one is. -/
  delivery : Option Delivery
  /-- The transaction layer, where this session's link is a control link: `some` once
  either end's attach names a coordinator target, and `none` where it does not, which is
  every session that is not doing transactional work. Part 4 sends the declare and
  discharge messages "over the control link", so the layer's presence is a fact about the
  link. -/
  transactions : Option Transactions.Layer := none
deriving Repr

/-- The channel a session start assumes, on both sides: sessions are assigned "an unused
channel number" and the lowest is recommended, so channel one, zero being the
connection's. -/
def startChannel : Nat := 1

/-- A session endpoint with no link attached. -/
def Endpoint.fresh (state : State) : Endpoint where
  state := state
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
  handleMax := declaredHandleMax
  peerHandleMax := declaredHandleMax
  position := none
  peerCount := 0
  peerCredit := 0
  senderSettleMode := false
  delivery := none

/-- The endpoint a state name starts at, with the channels and the begin's arrival taken
from the state's own description. -/
def Endpoint.atState (state : State) : Endpoint :=
  let fresh := Endpoint.fresh state
  match state with
  | .unmapped => fresh
  | .beginSent => { fresh with outgoing := some startChannel }
  | .beginRcvd => { fresh with incoming := some startChannel, peerBegun := true }
  | .mapped =>
    let withOut := { fresh with outgoing := some startChannel }
    let withBoth := { withOut with incoming := some startChannel }
    { withBoth with peerBegun := true }
  | .endSent => { fresh with incoming := some startChannel, peerBegun := true }
  | .endRcvd => { fresh with outgoing := some startChannel, peerBegun := true }
  | .discarding => { fresh with incoming := some startChannel, peerBegun := true }

/-- The endpoint an attach leaves, where that attach's target is a coordinator: the
control link exists and the transaction layer is present. Each direction records what its
own attach announced — the controller's is the desired capability set and the resource's
the actual one — so the `global-id` field rule has the coordinator's set to read. -/
def Endpoint.withControlLink (endpoint : Endpoint) (outbound : Bool) (body : Value) : Endpoint :=
  match (valueOfField "attach" "target" body).bind coordinatorCapabilities with
  | none => endpoint
  | some capabilities =>
    let layer := endpoint.transactions.getD Layer.fresh
    { endpoint with
        transactions := some (if outbound then { layer with own := capabilities }
                              else { layer with other := capabilities }) }

/-- The endpoint a released link leaves: the control link's transactions are rolled back,
since closing it "roll[s] back" the transactions it created and further work on them fails.
Only the detach that releases the link counts, which is the release `detachLink` performs. -/
def Endpoint.afterLinkRelease (endpoint : Endpoint) : Endpoint :=
  { endpoint with transactions := endpoint.transactions.map Layer.retiredAll }

/-- The handle maximum a begin announces, or the declared default where it leaves the field
unset: `begin/field:handle-max.1` makes it the bound its partner may not attach outside. -/
def beginHandleMax (body : Value) : Nat :=
  match valueOfField "begin" "handle-max" body with
  | some value => (numberOf value).getD declaredHandleMax
  | none => declaredHandleMax

/-! ## The link's handlers -/

/-- The `unattached-handle` session error, read from the generated choice table: the value
the artifact declares for a frame sent on a handle that is not attached. -/
def unattachedHandleCondition : String :=
  (declaredChoice "session-error" "unattached-handle").getD "no unattached-handle choice"

/-- The `handle-in-use` session error, which `attach/field:handle.2` mandates an immediate
close for. -/
def handleInUseCondition : String :=
  (declaredChoice "session-error" "handle-in-use").getD "no handle-in-use choice"

/-- A refusal whose consequence is the connection's close. -/
def closingRefuse (condition reasonClass text : String) : Refusal :=
  { refuse condition reasonClass text with closes := true }

/-- The handle a frame names, checked against the attached link. A received frame names the
peer's handle and a sent one names ours, which is what `link-handles` means by input and
output handles; a frame that names no handle is left to the declared surface, which is what
refuses a frame whose handle is mandatory and missing. -/
def readHandle (endpoint : Endpoint) (outbound : Bool) (typeName : String) (body : Value) :
    Except Refusal Unit := do
  match valueOfField typeName "handle" body with
  | none | some .null => return ()
  | some value =>
    let handle ←
      match numberOf value with
      | some handle => pure handle
      | none => .error (refuse invalidFieldCondition "malformed"
          s!"the {typeName}'s handle field is not an integer")
    let mine ←
      match (if outbound then endpoint.handle else endpoint.peerHandle) with
      | some mine => pure mine
      | none => .error (refuse unattachedHandleCondition "illegalState"
          s!"a {typeName} names handle {handle}, and this endpoint has no attached link")
    if handle == mine then return ()
    else
      .error (refuse unattachedHandleCondition "illegalState"
        s!"the {typeName} names handle {handle}, and this endpoint's link is {mine}")

/-- One side of the attach exchange: the handle rules of `attach/field:handle` and
`begin/field:handle-max`, the delivery-count a sender's attach must carry, and the flow
state the doc's `flow-control` gives a fresh link. -/
def attachLink (endpoint : Endpoint) (outbound : Bool) (body : Value) :
    Except Refusal Endpoint := do
  let role ←
    match (valueOfField "attach" "role" body).bind Role.ofValue with
    | some role => pure role
    | none => .error (refuse invalidFieldCondition "malformed"
        "an attach must carry a role the declared type names")
  let handle ←
    match (valueOfField "attach" "handle" body).bind numberOf with
    | some handle => pure handle
    | none => .error (refuse invalidFieldCondition "malformed"
        "an attach must carry an integer handle")
  let claimed := if outbound then endpoint.handles else endpoint.peerHandles
  let bound := if outbound then endpoint.peerHandleMax else endpoint.handleMax
  if handle > bound then
    .error (closingRefuse wireCondition "limit"
      s!"handle {handle} is outside the range {bound} that begin announced")
  if claimed.contains handle then
    .error (closingRefuse handleInUseCondition "illegalState"
      s!"handle {handle} is already associated with a link, and a handle MUST NOT be used \
        for other open links")
  let initialCount ←
    match (valueOfField "attach" "initial-delivery-count" body).bind numberOf with
    | some count => pure count
    | none =>
      if role == Role.sender then
        .error (refuse invalidFieldCondition "malformed"
          "a sender's attach MUST carry its initial delivery-count")
      else pure 0
  let settle :=
    match valueOfField "attach" "snd-settle-mode" body with
    | some value =>
      numberOf value == (((declaredChoice "sender-settle-mode" "unsettled").bind String.toNat?).getD 0)
    | none => false
  if outbound then
    -- a fresh link starts with nothing agreed: see `Spec/Session`'s attach for the same
    -- reading, taken from the credit's ownership sentence
    return { endpoint with handle := some handle, handles := handle :: endpoint.handles,
                            role := some role, peerCount := 0, peerCredit := 0,
                            delivery := none,
                            position := some ⟨(if role == Role.sender then initialCount else 0), 0⟩,
                            senderSettleMode :=
                              if role == Role.sender then settle else endpoint.senderSettleMode }
  else
    return { endpoint with peerHandle := some handle,
                            peerHandles := handle :: endpoint.peerHandles,
                            peerRole := some role, delivery := none,
                            position := if role == Role.sender || endpoint.position.isSome
                                        then endpoint.position else some ⟨0, 0⟩,
                            peerCount := (if role == Role.sender
                                             && endpoint.role == some Role.receiver
                                          then initialCount else endpoint.peerCount),
                            senderSettleMode :=
                              if role == Role.sender then settle else endpoint.senderSettleMode }

/-- The link's half of a flow: the clauses that forbid the link's fields on a flow that
names no link, the delivery-count the doc's `flow-control` fixes per direction, and the
credit formula a sender applies to what the receiver announced. -/
def flowLink (endpoint : Endpoint) (outbound : Bool) (body : Value) :
    Except Refusal Endpoint := do
  let handleValue := valueOfField "flow" "handle" body
  let namesLink :=
    match handleValue with
    | some .null | none => false
    | some _ => true
  if !namesLink then
    let carried := ["delivery-count", "link-credit", "available", "drain"].filter
      (fun field =>
        match valueOfField "flow" field body with
        | some .null | none => false
        | some _ => true)
    if !carried.isEmpty then
      .error (refuse invalidFieldCondition "malformed"
        s!"a flow that sets no handle MUST NOT set {carried}")
  let _ ← readHandle endpoint outbound "flow" body
  match endpoint.position with
  | none => return endpoint
  | some position =>
    if !namesLink then return endpoint
    let count :=
      match valueOfField "flow" "delivery-count" body with
      | some value => numberOf value
      | none => none
    match count with
    | none => return endpoint
    | some count =>
      let ours := if outbound then endpoint.role == some Role.sender
                  else endpoint.role == some Role.receiver
      if ours && count != position.count then
        .error (refuse invalidFieldCondition "malformed"
          s!"the flow carries delivery-count {count}, and this endpoint's count is \
            {position.count}")
      if outbound then return endpoint
      else if endpoint.role == some Role.sender then
        let receivedCredit :=
          match valueOfField "flow" "link-credit" body with
          | some value => (numberOf value).getD 0
          | none => 0
        let credited :=
          { position with credit := Position.creditFor count receivedCredit position.count }
        return { endpoint with position := some credited, peerCount := count, peerCredit := receivedCredit }
      else
        -- the ownership sentence `link-credit` carries: only the receiver sets it, and the
        -- sender echoes the last value it was sent
        let echoed :=
          match valueOfField "flow" "link-credit" body with
          | some value => (numberOf value).getD 0
          | none => 0
        if echoed != position.credit then
          .error (refuse invalidFieldCondition "malformed"
            s!"a flow from the link's sender carries link-credit {echoed}, and this \
              receiver's last known value is {position.credit}")
        let counted := { position with count }
        return { endpoint with position := some counted, peerCredit := echoed }

/-- The link's half of a transfer: the role its direction requires, the credit a sender
spends, the fields a first transfer must carry, the `settled` interpretation with
`settled.4`'s obligation at the end of a delivery, and `aborted`'s discard. -/
def transferLink (endpoint : Endpoint) (outbound : Bool) (body : Value) :
    Except Refusal Endpoint := do
  let _ ← readHandle endpoint outbound "transfer" body
  if outbound != (endpoint.role == some Role.sender) then
    .error (refuse illegalStateCondition "illegalState"
      s!"a transfer is the sender's frame, and this endpoint attached as \
        {(endpoint.role.getD Role.receiver).label}")
  let present (field : String) : Bool :=
    match valueOfField "transfer" field body with
    | some .null | none => false
    | some _ => true
  let continued := endpoint.delivery.isSome
  let id ←
    match (valueOfField "transfer" "delivery-id" body).bind numberOf with
    | some id => pure id
    | none =>
      match endpoint.delivery with
      | some delivery => pure delivery.id
      | none => .error (refuse invalidFieldCondition "malformed"
          "the first transfer of a delivery MUST carry its delivery-id")
  if !continued && !(present "delivery-tag" && present "message-format") then
    .error (refuse invalidFieldCondition "malformed"
      "a first transfer MUST carry its delivery-tag and message-format")
  let settled := present "settled"
  let aborted := present "aborted"
  let more := !aborted && present "more"
  let completed := Delivery.advance endpoint.delivery id settled
  if aborted then return { endpoint with delivery := none }
  if !more && endpoint.senderSettleMode && !completed.settled then
    .error (refuse invalidFieldCondition "malformed"
      s!"with sender-settle-mode negotiated, a delivery MUST be settled in at least one of \
        its transfers, and delivery {id} is not")
  let progress := if more then some completed else none
  match endpoint.position with
  | none => return { endpoint with delivery := progress }
  | some position =>
    -- the credit bounds messages rather than frames, and the delivery-count "is
    -- incremented whenever a message is sent": both move on the transfer that begins a
    -- delivery, so a continuation of an already-counted delivery moves neither
    let starting := !continued
    let counted :=
      { position with count := if starting then position.count + 1 else position.count }
    if outbound then
      if starting && position.credit == 0 then
        .error (refuse wireCondition "limit"
          "the link has no credit left: the sender has reached the receiver's delivery-limit")
      if !starting then return { endpoint with position := some counted, delivery := progress }
      let spent := { counted with credit := position.credit - 1 }
      return { endpoint with position := some spent, delivery := progress }
    else
      return { endpoint with position := some counted, delivery := progress }

/-- The detach exchange: the handle rules, the release `link-handles` gives a detach — "this
handle ... remains in use until the link is detached" — and `links.15`'s exception, since
its rule for input related to a detached link endpoint reads "other than a detach". A
detach naming a handle this endpoint does not have is therefore admitted, and it releases
the link only when the handle is the attached one. -/
def detachLink (endpoint : Endpoint) (outbound : Bool) (body : Value) :
    Except Refusal Endpoint := do
  let named := (valueOfField "detach" "handle" body).bind numberOf
  let releasable := named == (if outbound then endpoint.handle else endpoint.peerHandle)
  if !releasable then return endpoint
  if outbound then
    -- the flow state belongs to the link the detach releases, so it goes with it; and a
    -- control link's release rolls back the transactions it created
    return Endpoint.afterLinkRelease
      { endpoint with handle := none, role := none, position := none,
                      peerCount := 0, peerCredit := 0, delivery := none }
  else
    return Endpoint.afterLinkRelease
      { endpoint with peerHandle := none, peerRole := none,
                      peerCount := 0, peerCredit := 0, delivery := none }

/-- Whether a body is a disposition: the dispatch table gives it to the session, and this
module's `Frame` names only the frames the state machine itself turns on. -/
def isDisposition (body : Value) : Bool :=
  match declaredType body with
  | some t => t.name == "disposition"
  | none => false

/-- The disposition exchange: `disposition.1`'s directionality and the range it names. -/
def dispositionLink (endpoint : Endpoint) (outbound : Bool) (body : Value) :
    Except Refusal Endpoint := do
  let _ ← readHandle endpoint outbound "disposition" body
  let role ←
    match (valueOfField "disposition" "role" body).bind Role.ofValue with
    | some role => pure role
    | none => .error (refuse invalidFieldCondition "malformed"
        "a disposition must carry a role the declared type names")
  if role != endpoint.role.getD Role.sender then
    .error (refuse invalidFieldCondition "malformed"
      s!"the disposition names the {role.label}'s deliveries, and this endpoint is the \
        {(endpoint.role.getD Role.sender).label}")
  let first :=
    match valueOfField "disposition" "first" body with
    | some value => (numberOf value).getD 0
    | none => 0
  let last :=
    match valueOfField "disposition" "last" body with
    | some value => (numberOf value).getD 0
    | none => first
  if first > last then
    .error (refuse invalidFieldCondition "malformed"
      s!"the disposition's range runs from {first} to {last}, which is not a range")
  match endpoint.delivery with
  | none => return endpoint
  | some delivery =>
    let settled :=
      match valueOfField "disposition" "settled" body with
      | some .null | none => false
      | some _ => true
    if settled && first ≤ delivery.id && delivery.id ≤ last then
      return { endpoint with delivery := none }
    else return endpoint


/-- The endpoint a begin leaves, with its `remote-channel` rule: the field "MUST be empty
for a locally initiated session, and MUST be set when announcing the endpoint created as
a result of a remotely initiated session", where it is the channel the partner's begin
arrived on. -/
def takeBegin (endpoint : Endpoint) (outbound : Bool) (channel : Nat) (body : Value) :
    Except Refusal Endpoint := do
  if outbound then
    match endpoint.state with
    | .unmapped =>
      if (valueOfField "begin" "remote-channel" body).isSome &&
          (valueOfField "begin" "remote-channel" body) != some .null then
        .error (refuse invalidFieldCondition "malformed"
          "a locally initiated begin must not name a remote-channel")
      else
        let windows :=
          endpoint.windows.afterSendingBegin (← windowField "begin" "next-outgoing-id" body)
            (← windowField "begin" "incoming-window" body)
            (← windowField "begin" "outgoing-window" body)
        return { endpoint with state := .beginSent, outgoing := some channel, windows, handleMax := beginHandleMax body }
    | .beginRcvd =>
      match endpoint.incoming, valueOfField "begin" "remote-channel" body with
      | some theirChannel, some value =>
        if numberOf value == some theirChannel then
          let windows :=
            endpoint.windows.afterSendingBegin (← windowField "begin" "next-outgoing-id" body)
              (← windowField "begin" "incoming-window" body)
              (← windowField "begin" "outgoing-window" body)
          return { endpoint with state := .mapped, outgoing := some channel, windows, handleMax := beginHandleMax body }
        else
          .error (refuse invalidFieldCondition "malformed"
            s!"a begin answering a remotely initiated session must set remote-channel to \
              {theirChannel}, the channel its begin arrived on")
      | _, _ =>
        .error (refuse invalidFieldCondition "malformed"
          "a begin answering a remotely initiated session must set remote-channel")
    | other =>
      .error (refuse illegalStateCondition "illegalState"
        s!"this session has already sent its begin, and is {other.label}")
  else
    match endpoint.state with
    | .unmapped =>
      let windows :=
        endpoint.windows.afterReceivingBegin (← windowField "begin" "next-outgoing-id" body)
          (← windowField "begin" "incoming-window" body)
          (← windowField "begin" "outgoing-window" body)
      let withMax := { endpoint with peerHandleMax := beginHandleMax body }
      return { withMax with state := .beginRcvd, incoming := some channel, peerBegun := true, windows := windows }
    | .beginSent =>
      let windows :=
        endpoint.windows.afterReceivingBegin (← windowField "begin" "next-outgoing-id" body)
          (← windowField "begin" "incoming-window" body)
          (← windowField "begin" "outgoing-window" body)
      let withMax := { endpoint with peerHandleMax := beginHandleMax body }
      return { withMax with state := .mapped, incoming := some channel, peerBegun := true, windows := windows }
    | other =>
      .error (refuse illegalStateCondition "illegalState"
        s!"this session has already received a begin, and is {other.label}")

/-- The endpoint an end leaves, following the diagram: `MAPPED --S:END--> END_SENT`,
`MAPPED --S:END(error)--> DISCARDING`, `MAPPED --R:END--> END_RCVD`, and either end after
the other's puts it back in `UNMAPPED`. -/
def afterEnd (endpoint : Endpoint) (outbound : Bool) (withError : Bool) : Endpoint :=
  if outbound then
    match endpoint.state with
    | .mapped =>
      { endpoint with state := (if withError then .discarding else .endSent), outgoing := none }

    | .endRcvd => Endpoint.fresh .unmapped
    | .beginSent =>
      -- the diagram's BEGIN_SENT --S:END--> END_SENT arrow: the label moves with the
      -- channel the end releases, because BEGIN_SENT's description claims that outgoing
      -- channel while END_SENT's claims no outgoing number and an incoming entry — the
      -- maps this record has
      { endpoint with state := .endSent, outgoing := none }
    | other => { endpoint with state := other, outgoing := none }
  else
    match endpoint.state with
    | .endSent | .discarding => Endpoint.fresh .unmapped
    | _ => { endpoint with state := .endRcvd, incoming := none, peerBegun := true }

/-- One frame the session layer answers for. -/
def step (endpoint : Endpoint) (outbound : Bool) (channel : Nat) (body : Value) :
    Except Refusal Endpoint := do
  let frame := frameOf body
  let typeName :=
    match frame with
    | .begin => "begin" | .end => "end" | .attach => "attach" | .detach => "detach"
    | .flow => "flow" | .transfer => "transfer" | .other => ""
  -- DISCARDING discards what arrives until the peer's end, without looking at it
  if !outbound && endpoint.state == .discarding && frame != .end then
    return endpoint
  -- the begins are what map the channels, so they are the frames that arrive on a
  -- channel that is not mapped yet
  let mapped := if outbound then endpoint.outgoing else endpoint.incoming
  if frame != .begin && mapped != some channel then
    .error (refuse wireCondition "illegalState"
      s!"channel {channel} is not this session's \
        {if outbound then "outgoing" else "incoming"} channel, {mapped}")
  let allowed := frame == .begin ||
    (if outbound then sendAllowed endpoint.state else receiveAllowed endpoint.state)
  -- the third of the three placement sites: wire-level refusals take no placement,
  -- session-level ones go through `placed`, and these — the link's rules — go through here
  let placeLink (reason : Refusal) : Refusal :=
    if reason.closes || outbound then reason
    else
      -- `sessions.5` and `sessions.6`: the discarding phase is reached from every state
      -- that can still receive, which is what this layer's own permission column says
      { reason with
          place := if receiveAllowed endpoint.state then some State.discarding
                   else reason.place }
  let placed (condition reasonClass text : String) : Refusal :=
    if outbound then refuse condition reasonClass text
    else { refuse condition reasonClass text with
             place := if endpoint.state == .mapped then some State.discarding else none }
  if !allowed then
    .error (placed illegalStateCondition "illegalState"
      s!"{endpoint.state.label} does not let this session {if outbound then "send" else "receive"} \
        a {frame.label} frame")
  let missing := missingMandatory typeName body
  if !missing.isEmpty then
    .error (placed invalidFieldCondition "malformed"
      s!"the {typeName} performative does not carry {missing}, which the declared surface \
        marks mandatory")
  match frame with
  | .begin => takeBegin endpoint outbound channel body
  | .end =>
    let withError :=
      match valueOfField "end" "error" body with
      | some .null | none => false
      | some _ => true
    return afterEnd endpoint outbound withError
  | .flow =>
    let set :=
      match valueOfField "flow" "next-incoming-id" body with
      | some .null | none => false
      | some _ => true
    if set != endpoint.peerBegun then
      .error (placed invalidFieldCondition "malformed"
        "a flow's next-incoming-id is set exactly when the partner's begin has arrived")
    let endpoint ←
      match flowLink endpoint outbound body with
      | .ok next => pure next
      | .error reason => .error (placeLink reason)
    if outbound then return endpoint
    else
      let windows :=
        endpoint.windows.afterReceivingFlow (← windowField "flow" "next-outgoing-id" body)
          (← windowField "flow" "incoming-window" body)
          (← windowField "flow" "outgoing-window" body)
          (match valueOfField "flow" "next-incoming-id" body with
           | some .null | none => none
           | some value => numberOf value)
      return { endpoint with windows := windows }
  | .transfer =>
    if outbound then
      if endpoint.windows.outgoing == 0 then
        .error (placed windowViolationCondition "limit"
          "this session's outgoing window is exhausted, so it may not send another transfer")
      else if endpoint.windows.remoteIncoming == 0 then
        .error (placed windowViolationCondition "limit"
          "the partner's incoming window is exhausted, so it can accept no further transfers")
      else
        let endpoint ←
          match transferLink endpoint outbound body with
          | .ok next => pure next
          | .error reason => .error (placeLink reason)
        return { endpoint with
                   windows := endpoint.windows.afterSendingTransfer windowPolicy }
    else
      if endpoint.windows.incoming == 0 then
        .error (placed windowViolationCondition "limit"
          "this session's incoming window is exhausted, so it cannot receive another transfer")
      else
        let endpoint ←
          match transferLink endpoint outbound body with
          | .ok next => pure next
          | .error reason => .error (placeLink reason)
        return { endpoint with
                   windows := endpoint.windows.afterReceivingTransfer
                     endpoint.windows.nextIncoming windowPolicy }
  | .attach =>
    match attachLink endpoint outbound body with
    | .ok next => pure (next.withControlLink outbound body)
    | .error reason => .error (placeLink reason)
  | .detach =>
    match detachLink endpoint outbound body with
    | .ok next => pure next
    | .error reason => .error (placeLink reason)
  | .other =>
    if isDisposition body then
      match dispositionLink endpoint outbound body with
      | .ok next => pure next
      | .error reason => .error (placeLink reason)
    else return endpoint

end SpecAMQP.Ref.Session
