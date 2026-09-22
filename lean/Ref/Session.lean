import Generated.Oasis.Fields
import Generated.Oasis.Types
import Ref.Connection

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
  ⟨condition, reasonClass, text, none⟩

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

/-- A window field read through the connection layer's reader, whose refusal is the same
rule and is re-stated in this layer's refusal: the field rules do not change with the
layer that reads them, and the condition it names is the one the session's refusal
carries. -/
def windowField (typeName fieldName : String) (body : Value) : Except Refusal Nat :=
  match SpecAMQP.Ref.Connection.integerField typeName fieldName body with
  | .ok number => .ok number
  | .error refusal =>
    .error ⟨refusal.condition, refusal.reasonClass, refusal.text, none⟩

/-! ## The endpoint -/

/-- One session endpoint: its state, the outgoing channel its begin assigned, the
incoming channel the partner's begin arrived on, and whether that begin has arrived. -/
structure Endpoint where
  state : State
  outgoing : Option Nat
  incoming : Option Nat
  peerBegun : Bool
  windows : Windows
deriving Repr

/-- The channel a session start assumes, on both sides: sessions are assigned "an unused
channel number" and the lowest is recommended, so channel one, zero being the
connection's. -/
def startChannel : Nat := 1

/-- The endpoint a state name starts at, with the channels and the begin's arrival taken
from the state's own description. -/
def Endpoint.atState (state : State) : Endpoint :=
  match state with
  | .unmapped => ⟨.unmapped, none, none, false, Windows.start⟩
  | .beginSent => ⟨.beginSent, some startChannel, none, false, Windows.start⟩
  | .beginRcvd => ⟨.beginRcvd, none, some startChannel, true, Windows.start⟩
  | .mapped => ⟨.mapped, some startChannel, some startChannel, true, Windows.start⟩
  | .endSent => ⟨.endSent, none, some startChannel, true, Windows.start⟩
  | .endRcvd => ⟨.endRcvd, some startChannel, none, true, Windows.start⟩
  | .discarding => ⟨.discarding, none, some startChannel, true, Windows.start⟩

/-! ## Applying a step -/

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
        return { endpoint with state := .beginSent, outgoing := some channel, windows }
    | .beginRcvd =>
      match endpoint.incoming, valueOfField "begin" "remote-channel" body with
      | some theirChannel, some value =>
        if numberOf value == some theirChannel then
          let windows :=
            endpoint.windows.afterSendingBegin (← windowField "begin" "next-outgoing-id" body)
              (← windowField "begin" "incoming-window" body)
              (← windowField "begin" "outgoing-window" body)
          return { endpoint with state := .mapped, outgoing := some channel, windows }
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
      return { endpoint with state := .beginRcvd, incoming := some channel, peerBegun := true,
                              windows }
    | .beginSent =>
      let windows :=
        endpoint.windows.afterReceivingBegin (← windowField "begin" "next-outgoing-id" body)
          (← windowField "begin" "incoming-window" body)
          (← windowField "begin" "outgoing-window" body)
      return { endpoint with state := .mapped, incoming := some channel, peerBegun := true,
                              windows }
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

    | .endRcvd => ⟨.unmapped, none, none, false, Windows.start⟩
    | other => { endpoint with state := other, outgoing := none }
  else
    match endpoint.state with
    | .endSent | .discarding => ⟨.unmapped, none, none, false, Windows.start⟩
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
        return { endpoint with
                   windows := endpoint.windows.afterSendingTransfer windowPolicy }
    else
      if endpoint.windows.incoming == 0 then
        .error (placed windowViolationCondition "limit"
          "this session's incoming window is exhausted, so it cannot receive another transfer")
      else
        return { endpoint with
                   windows := endpoint.windows.afterReceivingTransfer
                     endpoint.windows.nextIncoming windowPolicy }
  | .attach | .detach => return endpoint
  | .other => return endpoint

end SpecAMQP.Ref.Session
