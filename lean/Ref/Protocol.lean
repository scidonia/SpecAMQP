import Generated.Oasis.Choices
import Generated.Oasis.Fields
import Generated.Oasis.Types
import Ref.Session
import Ref.Transactions

/-!
# The reference's widened session layer

The second reading of the widening `Spec.Protocol` holds the specification's side of. It is written
independently of that module and shares no definition with it: the state below is the reference's
own, and the rules are this layer's reading of the same clauses. The restricted single-link reading
stays where it was, in `Ref.Session`; the two coexist, and `Ref.SessionCodec` dispatches to this one.

## What the widening adds

A session may hold several links. A link is identified by its *name* and *this endpoint's* role —
`attach`'s `role` field names the endpoint that sent the frame, so a frame this endpoint sends names
our role and one it receives names the peer's, and the name plus our role is the identity in both
cases. Each endpoint has its own handle space (`localHandles` maps the handles *we* use, and
`remoteHandles` the ones the peer uses), so both ends may use handle zero; a detach or a resume
moves one endpoint's handle without touching the other's. One logical-link record owns one unsettled
table keyed by delivery tag, so the two handle spaces cannot drift into two accounts of the same
deliveries.

`legacy` keeps the session-scope state the restricted reading already has — the state, the channel
map, the windows and the two handle maxima — and this module reads and writes those fields and no
others: the registry is the only live representation of link state, and the restricted reading's
single link slots are neither dispatched through nor synchronized.

## The rules, and where each is read

* **Identity and lifetime.** A sent attach looks up `(name, our role)`; a received one looks up
  `(name, the peer's role as its local role)`. An attach for a link whose own endpoint is already
  *associated* must carry its unsettled state (`links.5`); one whose endpoint is *detached* still
  names a live endpoint, so its map must be null (`unsettled.6`); one whose endpoint is *destroyed*
  can only be restored by a resume, which the unsettled map is the mark of (`links.16`–`.18`).
* **The map's structure.** A null key anywhere in the map is `attach/field:unsettled.5`'s
  prohibition. The map's *values* are recorded in the table only by the transfers that leave a
  delivery unsettled; `unsettled.1`'s comparison of the local and remote states is a held
  comparison, not a decision a step takes.
* **The latch.** `incomplete-unsettled` is assigned from each attach, and each endpoint holds its
  own: a *received* attach with the flag set stops this endpoint offering a new delivery
  (`incomplete-unsettled.1`/`.2`), and this endpoint's own flagged attach makes an incoming transfer
  that does not resume an error.
* **Resume.** A received resumed transfer whose tag the table does not hold is ignored, and records
  nothing (`resume.1`); a sent one is refused (`resume.2`); and a continuation that first claims
  resumption is refused because the flag belongs on the delivery's first transfer (`resume.3`).
* **Tag uniqueness.** A tag is unique among the deliveries either end could still consider
  unsettled, so a first transfer whose tag already holds a *different* delivery is refused
  (`links.23`) — read after the link's credit gate, because a link with no credit left cannot send
  the delivery at all.
* **Settlement outliving the detach.** `disposition.4`: a detach releases an endpoint's handle and
  its flow state but keeps the link's unsettled history, and a disposition declares no handle, so it
  applies to every registered link whose local role its `role` field names.
-/

namespace SpecAMQP.Ref.Protocol

open SpecAMQP.Harness (Octets)
open SpecAMQP.Ref.Connection
  (declaredChoice missingMandatory numberOf octetsOf valueOfField)
open SpecAMQP.Ref.Session
  (Endpoint Frame Position Refusal Role State Windows frameOf windowPolicy
   afterEnd booleanAtField closingRefuse deliveryTagInBounds handleInUseCondition
   illegalStateCondition invalidFieldCondition isDisposition receiveAllowed refuse sendAllowed
   takeBegin terminusRefusalOf unattachedHandleCondition windowField windowViolationCondition
   wireCondition)
open SpecAMQP.Ref.Transactions (Carrier Layer)

/-- The session error `links.18` names for a pipelined re-attach on a destroyed endpoint, read from
the generated choice table rather than typed. -/
def errantLinkCondition : String :=
  (declaredChoice "session-error" "errant-link").getD "no errant-link choice"

/-! ## The widened state -/

/-- A delivery tag: the binary key the link uses for unsettled delivery state. -/
abbrev DeliveryTag := List UInt8

/-- One unsettled delivery: the sender's id for it and the two observations an in-doubt delivery is
resolved from. The states travel with the entry but are not interpreted by any step —
`attach/field:unsettled.1`'s comparison is a held comparison, carried elsewhere — so an entry the
step writes carries whatever the entry at that tag already held. -/
structure UnsettledDelivery where
  deliveryId : Nat
  localState : Option Value
  remoteState : Option Value

/-- A delivery crossing the link. `resumed` records whether the transfer that *began* it carried
the resume flag, which is `transfer/field:resume.3`'s antecedent. -/
structure WidenedDelivery where
  id : Nat
  settled : Bool
  resumed : Bool
deriving Repr, BEq, DecidableEq

/-- A stable link identity: the uninterpreted name plus this endpoint's role. A name is unique only
among links of the same local direction, which is exactly what this key expresses. -/
structure LinkId where
  name : String
  localRole : Role
deriving Repr, BEq

/-- The four lives the attach rules distinguish. `suspended` is the artifact's own word for a link
whose termini exist without an associated endpoint, and is the life a peer's attach leaves on an
endpoint this end has never attached. -/
inductive LinkLife where
  | attached
  | detached
  | suspended
  | destroyed
deriving Repr, BEq, DecidableEq

/-- One end of a logical link: whether its terminus is associated, its life, and the incomplete-map
latch its own last attach announced. Handles are deliberately absent; they live in the session's two
directional maps. -/
structure LinkEndpoint where
  terminusAssociated : Bool
  life : LinkLife
  incompleteUnsettled : Bool

/-- One logical link. The flow state, the settlement negotiation, the in-progress delivery, the
transaction slot and the unsettled history belong to the link rather than the session, and the one
unsettled table is shared so the two handle spaces cannot disagree about one delivery. -/
structure Link where
  id : LinkId
  localEndpoint : LinkEndpoint
  remoteEndpoint : LinkEndpoint
  position : Option Position
  peerCount : Nat
  peerCredit : Nat
  senderSettleMode : Bool
  senderSettleUnsettled : Bool
  receiverSettleSecond : Bool
  delivery : Option WidenedDelivery
  deliveryTag : Option DeliveryTag
  deliveryFormat : Option Nat
  transactions : Option Layer
  unsettled : DeliveryTag → Option UnsettledDelivery
  nextDeliveryId : Nat

/-- A session: the restricted endpoint for its session-scope state, a stable registry keyed by
identity, the finite key index that makes that registry walkable for a handle-less frame, and one
handle map per endpoint's independent handle space. -/
structure WidenedSession where
  legacy : Endpoint
  links : LinkId → Option Link
  linkKeys : List LinkId
  localHandles : Nat → Option LinkId
  remoteHandles : Nat → Option LinkId

/-- The registry key is the record's own identity, so one slot is the only place a link of that name
and direction can exist. -/
def LinkNamesUnique (session : WidenedSession) : Prop :=
  ∀ (id : LinkId) (link : Link), session.links id = some link → link.id = id

/-- The finite key index names each and only each occupied registry slot, exactly once, so a
handle-less frame can traverse the registry without the index becoming a second source of state. -/
def RegistryKeysComplete (session : WidenedSession) : Prop :=
  session.linkKeys.Nodup ∧ ∀ id, id ∈ session.linkKeys ↔ ∃ link, session.links id = some link

/-- A mapped handle resolves to an attached endpoint; every attached endpoint has a handle in its
own directional space; and one endpoint cannot hold two handles at once. This is what a stale or
duplicated binding would falsify, which is why a detach that releases an endpoint releases its
handle in the same step. -/
def HandlesResolveLinks (session : WidenedSession) : Prop :=
  (∀ (handle : Nat) (id : LinkId), session.localHandles handle = some id →
    ∃ link, session.links id = some link ∧ link.localEndpoint.life = .attached) ∧
  (∀ (handle : Nat) (id : LinkId), session.remoteHandles handle = some id →
    ∃ link, session.links id = some link ∧ link.remoteEndpoint.life = .attached) ∧
  (∀ (id : LinkId) (link : Link), session.links id = some link →
    link.localEndpoint.life = .attached → ∃ handle, session.localHandles handle = some id) ∧
  (∀ (id : LinkId) (link : Link), session.links id = some link →
    link.remoteEndpoint.life = .attached → ∃ handle, session.remoteHandles handle = some id) ∧
  (∀ (leftHandle rightHandle : Nat) (id : LinkId),
    session.localHandles leftHandle = some id →
    session.localHandles rightHandle = some id → leftHandle = rightHandle) ∧
  (∀ (leftHandle rightHandle : Nat) (id : LinkId),
    session.remoteHandles leftHandle = some id →
    session.remoteHandles rightHandle = some id → leftHandle = rightHandle)

/-- The three invariants together, which every widened session a step produces satisfies. They are
properties of the state rather than optional proofs about it: a step that left a stale binding or a
key naming someone else's record would falsify one of them. -/
def WidenedSessionValid (session : WidenedSession) : Prop :=
  LinkNamesUnique session ∧ RegistryKeysComplete session ∧ HandlesResolveLinks session

/-! ## Identity and the two handle spaces -/

/-- The other end's role. -/
def oppositeRole : Role → Role
  | .sender => .receiver
  | .receiver => .sender

/-- The identity of the link an attach names: the name plus *our* role. The frame's `role` field
names the sender's endpoint, so a sent attach carries our role and a received one the peer's. -/
def identityOf (outbound : Bool) (name : String) (role : Role) : LinkId :=
  { name := name, localRole := if outbound then role else oppositeRole role }

/-- The peer's role in a link identity. -/
def peerRoleOf (id : LinkId) : Role := oppositeRole id.localRole

/-- The identity a handle names, in the direction the frame travels: our handles when the frame is
one we send, the peer's when it is one we receive. -/
def resolveHandle (session : WidenedSession) (outbound : Bool) (handle : Nat) : Option LinkId :=
  if outbound then session.localHandles handle else session.remoteHandles handle

/-- Bind a handle to an identity, dropping any binding that identity held in the same direction.
`HandlesResolveLinks` allows one active handle per identity in each direction, so a resume that
moves an endpoint onto a new handle releases the old one here. -/
def associate (handles : Nat → Option LinkId) (handle : Nat) (id : LinkId) : Nat → Option LinkId :=
  fun h => if h == handle then some id else if handles h == some id then none else handles h

/-- Release an identity's binding in one direction. -/
def release (handles : Nat → Option LinkId) (id : LinkId) : Nat → Option LinkId :=
  fun h => if handles h == some id then none else handles h

/-- The link record a peer's attach creates where this endpoint has none: neither endpoint
associated, no history, and the artifact's own life for a link whose termini exist without an
associated endpoint. -/
def blankLink (id : LinkId) : Link where
  id := id
  localEndpoint := ⟨false, .suspended, false⟩
  remoteEndpoint := ⟨false, .suspended, false⟩
  position := none
  peerCount := 0
  peerCredit := 0
  senderSettleMode := false
  senderSettleUnsettled := false
  receiverSettleSecond := false
  delivery := none
  deliveryTag := none
  deliveryFormat := none
  transactions := none
  unsettled := fun _ => none
  nextDeliveryId := 0

/-- Write a link record at its own key, which is the only slot it can occupy, so `LinkNamesUnique`
holds by construction. A key the session has not seen gains its one entry in `linkKeys` here and
never loses it, which is what `RegistryKeysComplete` needs of the index. -/
def putLink (session : WidenedSession) (link : Link) : WidenedSession :=
  { session with
      links := fun key => if key == link.id then some link else session.links key,
      linkKeys := if session.linkKeys.contains link.id then session.linkKeys
                  else session.linkKeys ++ [link.id] }

/-! ## The shared unsettled table -/

/-- One key's entry. -/
def setEntry (table : DeliveryTag → Option UnsettledDelivery) (key : DeliveryTag)
    (entry : UnsettledDelivery) : DeliveryTag → Option UnsettledDelivery :=
  fun k => if k == key then some entry else table k

/-- Drop one key. -/
def clearEntry (table : DeliveryTag → Option UnsettledDelivery) (key : DeliveryTag) :
    DeliveryTag → Option UnsettledDelivery :=
  fun k => if k == key then none else table k

/-! ## Reading the attach's two widening fields -/

/-- The map's keys, with `attach/field:unsettled.5`'s null-key prohibition checked: an absent or
null field reads `none`, a map reads its keys, and a null key in it is refused. A key that is not a
`binary` value is not a delivery tag and is not carried; the values are not read at all. -/
def unsettledKeyList : List (Value × Value) → Except Refusal (List DeliveryTag)
  | [] => .ok []
  | pair :: rest =>
    match pair.1 with
    | .null => .error (refuse invalidFieldCondition "malformed"
        "the attach's unsettled map carries a null key, and the map MUST NOT contain null valued keys")
    | key =>
      match octetsOf key with
      | some octets => (unsettledKeyList rest).map (fun keys => octets :: keys)
      | none => unsettledKeyList rest

/-- The attach's `unsettled` field: `none` where the field is absent or null, `some keys` where it
is a map its keys survived, and a refusal where a key is null. -/
def unsettledKeys (body : Value) : Except Refusal (Option (List DeliveryTag)) :=
  match valueOfField "attach" "unsettled" body with
  | none | some .null => .ok none
  | some (.map pairs) => (unsettledKeyList pairs).map (fun keys => some keys)
  | some _ => .ok none

/-- The latch an attach assigns: `attach/field:incomplete-unsettled`'s flag, false where the field is
absent or null. Assigned from *each* attach for the link, which is how a later attach with the flag
false lifts it. -/
def incompleteFlag (body : Value) : Bool :=
  booleanAtField "attach" "incomplete-unsettled" body

/-- Whether a field is present and not null, which is the reference's reading of "set". -/
def fieldPresent (typeName fieldName : String) (body : Value) : Bool :=
  match valueOfField typeName fieldName body with
  | some .null | none => false
  | some _ => true

/-- Refuse unless a condition holds. -/
def refuseUnless (ok : Bool) (reason : Refusal) : Except Refusal Unit :=
  if ok then .ok () else .error reason

/-! ## The delivery a transfer carries -/

/-- Whether the link's own unsettled table holds a delivery at this tag: `resume.2`'s refusal and
`resume.1`'s ignore are both this predicate, read once. A transfer that carries no tag at all holds
nothing, which is why the callers map over the tag rather than testing a lookup. -/
def resumable (link : Link) (tag : DeliveryTag) : Bool := (link.unsettled tag).isSome

/-- The delivery a transfer's own flags leave in progress: the settled flag accumulates over the
delivery's transfers, and `resumed` records whether the transfer that *began* it carried the resume
flag. -/
def deliveryStep (current : Option WidenedDelivery) (id : Nat) (settled resumed : Bool) :
    WidenedDelivery :=
  match current with
  | some delivery => { delivery with settled := delivery.settled || settled }
  | none => ⟨id, settled, resumed⟩

/-! ## The guards that read the link's negotiation and flow state -/

/-- `transfer/field:rcv-settle-mode.u1` with `.u2`'s exemption, at the link's negotiation. -/
def linkRcvSettleRefusal? (link : Link) (body : Value) (settled : Bool) : Option Refusal :=
  match (valueOfField "transfer" "rcv-settle-mode" body).bind numberOf with
  | none => none
  | some mode =>
    if settled || link.receiverSettleSecond then none
    else if some mode == ((declaredChoice "receiver-settle-mode" "second").bind String.toNat?) then
      some (refuse invalidFieldCondition "malformed"
        "the transfer sets rcv-settle-mode to the second choice, and the link negotiated the first choice")
    else none

/-- `transfer/field:settled.6`, at the link's negotiation, with `aborted`'s exemption. -/
def linkUnsettledSettleRefusal? (link : Link) (settled aborted : Bool) : Option Refusal :=
  if link.senderSettleUnsettled && settled && !aborted then
    some (refuse invalidFieldCondition "malformed"
      "the link negotiated the unsettled choice of sender-settle-mode, so the settled flag MUST be \
        false (or unset) on a transfer for a delivery unless the delivery is aborted")
  else none

/-- `flow/field:delivery-count`'s rule, at the link's roles and lives. -/
def linkFlowCountRefusal? (link : Link) (id : LinkId) (outbound : Bool) (body : Value) :
    Option Refusal :=
  let issuing := if outbound then id.localRole else peerRoleOf id
  let senderSeen := if outbound then link.remoteEndpoint.life == .attached
                    else link.localEndpoint.life == .attached
  let receiverBeforeSender := issuing == some Role.receiver && !senderSeen
  match valueOfField "flow" "delivery-count" body with
  | none =>
    if receiverBeforeSender then none
    else some (refuse invalidFieldCondition "malformed"
      "a flow that names the link MUST set its delivery-count, and this one omits it")
  | some value =>
    if receiverBeforeSender then
      some (refuse invalidFieldCondition "malformed"
        "the receiving link endpoint has not yet seen the initial attach frame from the sender, so \
          its flow MUST NOT set the delivery-count")
    else
      match link.position, numberOf value with
      | none, _ => none
      | some _, none => some (refuse invalidFieldCondition "malformed"
          "the flow's delivery-count is not an integer")
      | some current, some carried =>
        if carried == current.count then none
        else some (refuse invalidFieldCondition "malformed"
          "the flow's delivery-count is not this endpoint's last known value for the link")

/-- `links/doc:flow-control.u1`, `.u3` and `flow/field:link-credit.u1`: a flow from the link's sender
echoes the receiver's last known value and sets nothing. -/
def linkFlowCreditEchoRefusal? (link : Link) (id : LinkId) (outbound : Bool) (body : Value) :
    Option Refusal :=
  let issuing := if outbound then id.localRole else peerRoleOf id
  if issuing != some Role.sender then none
  else
    match link.position, (valueOfField "flow" "link-credit" body).bind numberOf with
    | some current, some credit =>
      if credit == current.credit then none
      else some (refuse invalidFieldCondition "malformed"
        "a flow from the link's sender carries a link-credit that is not this endpoint's last known \
          value for it")
    | _, _ => none

/-! ## The transaction layer's carriers, per link -/

/-- One transaction value, from the frame that carried it. -/
def linkStepTransaction (link : Link) (carrier : Carrier) (outbound : Bool) (value : Value)
    (settled : Bool) : Except Refusal Link := do
  match link.transactions with
  | none => return link
  | some layer =>
    match Transactions.step layer carrier outbound value settled with
    | .ok layer => return { link with transactions := some layer }
    | .error reason =>
      .error { condition := reason.condition, reasonClass := reason.reasonClass,
               text := reason.text, place := none, closes := false }

/-- The transaction layer's step for a transfer's payload. -/
def linkStepTransactionPayload (link : Link) (outbound : Bool) (payload : Octets)
    (settled : Bool) : Except Refusal Link := do
  match link.transactions with
  | none => return link
  | some _ =>
    match Message.bodyValue Message.Policy.empty payload with
    | .error _ => return link
    | .ok value => linkStepTransaction link .payload outbound value settled

/-- The transaction layer's step for a disposition's `state`. -/
def linkStepTransactionState (link : Link) (outbound : Bool) (body : Value) :
    Except Refusal Link :=
  match valueOfField "disposition" "state" body with
  | some state => linkStepTransaction link .state outbound state false
  | none => .ok link

/-- The control link's transaction layer, where the attach names a coordinator target. -/
def linkWithControlLink (link : Link) (outbound : Bool) (body : Value) : Link :=
  match (valueOfField "attach" "target" body).bind Transactions.coordinatorCapabilities with
  | none => link
  | some capabilities =>
    let layer := link.transactions.getD Layer.fresh
    { link with
        transactions := some (if outbound then { layer with own := capabilities }
                              else { layer with other := capabilities }) }

/-! ## The link each exchange leaves -/

/-- The link a sent attach leaves: our endpoint attached at the frame's handle, the position the
role and the initial count give it, and the settlement the attach negotiated. The peer's flow state
is reset, because the credit is the partner's to grant for this link, and the in-progress delivery
is cleared, because a link being established is not continuing one. -/
def linkAfterSentAttach (base : Link) (flag : Bool) (position : Option Position) (role : Role)
    (senderSettle senderUnsettled receiverSecond : Bool) : Link :=
  { base with
      localEndpoint := { base.localEndpoint with terminusAssociated := true, life := .attached, incompleteUnsettled := flag },
      position := position,
      peerCount := 0,
      peerCredit := 0,
      senderSettleMode := if role == Role.sender then senderSettle else base.senderSettleMode,
      senderSettleUnsettled := if role == Role.sender then senderUnsettled
                               else base.senderSettleUnsettled,
      receiverSettleSecond := if role == Role.receiver then receiverSecond
                              else base.receiverSettleSecond,
      delivery := none,
      deliveryTag := none,
      deliveryFormat := none }

/-- The link a received attach leaves: the peer's endpoint attached at the frame's handle, with the
peer's count set only where the partner is the link's sender and this endpoint its receiver, the
position surviving an attach that does not establish the link, and the settlement the attach
negotiated. -/
def linkAfterReceivedAttach (base : Link) (id : LinkId) (flag : Bool) (initialCount : Nat)
    (freshPosition : Option Position) (role : Role)
    (senderSettle senderUnsettled receiverSecond : Bool) : Link :=
  { base with
      remoteEndpoint := { base.remoteEndpoint with terminusAssociated := true, life := .attached, incompleteUnsettled := flag },
      peerCount := (if role == Role.sender && id.localRole == Role.receiver then initialCount
                    else base.peerCount),
      position := (if role == Role.sender || base.position.isSome then base.position
                   else freshPosition),
      senderSettleMode := if role == Role.sender then senderSettle else base.senderSettleMode,
      senderSettleUnsettled := if role == Role.sender then senderUnsettled
                               else base.senderSettleUnsettled,
      receiverSettleSecond := if role == Role.receiver then receiverSecond
                              else base.receiverSettleSecond,
      delivery := none,
      deliveryTag := none,
      deliveryFormat := none }

/-- The link a detach of one endpoint leaves. That endpoint's handle has been released by the caller,
the endpoint is destroyed or merely released, and the flow state it held goes with it. The unsettled
history is kept: `disposition.4` makes a delivery remain unsettled while the link is neither closed
nor detached with an error, and a resume exists precisely so a suspended link can be restored. Only
a detach carrying an error ends the link's history. -/
def linkAfterDetach (base : Link) (outbound closed withError : Bool) : Link :=
  if outbound then
    { base with
        localEndpoint := { base.localEndpoint with life := (if closed then .destroyed else .detached), incompleteUnsettled := false },
        position := none,
        peerCount := 0,
        peerCredit := 0,
        delivery := (if withError then none else base.delivery),
        deliveryTag := (if withError then none else base.deliveryTag),
        deliveryFormat := (if withError then none else base.deliveryFormat),
        unsettled := (if withError then fun _ => none else base.unsettled),
        transactions := base.transactions.map Layer.retiredAll }
  else
    { base with
        remoteEndpoint := { base.remoteEndpoint with life := (if closed then .destroyed else .detached), incompleteUnsettled := false },
        peerCount := 0,
        peerCredit := 0,
        delivery := (if withError then none else base.delivery),
        deliveryTag := (if withError then none else base.deliveryTag),
        deliveryFormat := (if withError then none else base.deliveryFormat),
        unsettled := (if withError then fun _ => none else base.unsettled),
        transactions := base.transactions.map Layer.retiredAll }

/-- The link a transfer leaves: the delivery it carries or completes, the tag and format recorded
with it, the sender's next id, and the credit or count the transfer moves. -/
def linkAfterTransfer (base : Link) (position : Option Position) (delivery : Option WidenedDelivery)
    (deliveryTag : Option DeliveryTag) (deliveryFormat : Option Nat) (nextDeliveryId : Nat)
    (unsettled : DeliveryTag → Option UnsettledDelivery) : Link :=
  { base with
      position := position,
      delivery := delivery,
      deliveryTag := deliveryTag,
      deliveryFormat := deliveryFormat,
      nextDeliveryId := nextDeliveryId,
      unsettled := unsettled }

/-- The session with its session-scope windows replaced. -/
def withWindows (session : WidenedSession) (windows : Windows) : WidenedSession :=
  { session with legacy := { session.legacy with windows := windows } }

/-- The session with its session-scope state replaced: what a refusal that places the peer in a state
leaves. -/
def withState (session : WidenedSession) (st : State) : WidenedSession :=
  { session with legacy := { session.legacy with state := st } }

/-- A widened session over a session-scope state, with no link registered and no handle bound: what a
corpus `session:<STATE>` start is. -/
def sessionOf (legacy : Endpoint) : WidenedSession :=
  { legacy := legacy, links := fun _ => none, linkKeys := [], localHandles := fun _ => none,
    remoteHandles := fun _ => none }

/-! ## The two placements -/

/-- The placement of a refusal the session raises before it reads the frame's own fields. A receive
it cannot process is answered by the END the section mandates, which the diagram draws as
`MAPPED --S:END(error)--> DISCARDING`, and a state that cannot send at all cannot issue the END. A
send's refusal is simply not taken. -/
def placedFor (endpoint : Endpoint) (outbound : Bool) (condition reasonClass text : String) :
    Refusal :=
  if outbound then refuse condition reasonClass text
  else
    { refuse condition reasonClass text with
        place := if endpoint.state == .mapped then some State.discarding else none }

/-- The same placement for a refusal a link rule raises. It differs in one way: a refusal that
mandates the *connection*'s close is not answered by an END, so it is passed through untouched. -/
def placeFor (endpoint : Endpoint) (outbound : Bool) (reason : Refusal) : Refusal :=
  if reason.closes || outbound then reason
  else
    { reason with
        place := if receiveAllowed endpoint.state then some State.discarding else reason.place }

/-! ## The attach exchange -/

/-- The attach exchange, widened. The handle rules come first, then the identity the name and role
name, then the three states the artifact distinguishes: an endpoint already *attached* must carry
its unsettled state (`links.5`); one *detached* still exists, so the map must be null
(`unsettled.6`); one *destroyed* can only be restored by a resume, which the map's presence is what
tells a resume request from a pipelined re-attach (`links.16`–`.18`). -/
def attachStep (session : WidenedSession) (outbound : Bool) (body : Value) :
    Except Refusal WidenedSession := do
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
  let name :=
    match valueOfField "attach" "name" body with
    | some (.string text) => text
    | some (.symbol text) => text
    | _ => ""
  let maxHandle := if outbound then session.legacy.peerHandleMax else session.legacy.handleMax
  refuseUnless (handle ≤ maxHandle)
    (closingRefuse wireCondition "limit"
      s!"handle {handle} is outside the range {maxHandle} that begin announced")
  -- `attach/field:handle.2` forbids a handle "used for other open links": the same link re-attaching
  -- on the handle it already holds is not another link, and it is the handle moving a resume that
  -- this check exists to catch
  let id := identityOf outbound name role
  let bound := resolveHandle session outbound handle
  refuseUnless (bound.isNone || bound == some id)
    (closingRefuse handleInUseCondition "illegalState"
      s!"handle {handle} is already associated with another link, and a handle MUST NOT be used \
        for other open links")
  let existing := session.links id
  let life : Option LinkLife :=
    existing.map (fun link => if outbound then link.localEndpoint.life
                             else link.remoteEndpoint.life)
  let keys ← unsettledKeys body
  let carriesMap := keys.isSome
  match life with
  | some .attached =>
    if outbound then
      refuseUnless carriesMap
        (refuse invalidFieldCondition "malformed"
          "an attach for a link whose terminus is already associated MUST carry its unsettled delivery state, and this one carries none")
  | some .detached =>
    refuseUnless (!carriesMap)
      (refuse invalidFieldCondition "malformed"
        "a re-attach MUST carry a null unsettled map: the link endpoint still exists, and the map is the resume's")
  | some .destroyed =>
    refuseUnless carriesMap
      (refuse errantLinkCondition "illegalState"
        "the link endpoint is destroyed, so this attach MUST resume the link and carry the unsettled state it resumes it with")
  | some .suspended => pure ()
  | none => pure ()
  let initialCount ←
    match (valueOfField "attach" "initial-delivery-count" body).bind numberOf with
    | some count => pure count
    | none =>
      if role == Role.sender then
        .error (refuse invalidFieldCondition "malformed"
          "a sender's attach MUST carry its initial delivery-count")
      else pure 0
  let sentBy := if role == Role.sender then Message.SentBy.sender else Message.SentBy.receiver
  match terminusRefusalOf sentBy "source" body with
  | some reason => .error reason
  | none => pure ()
  match terminusRefusalOf sentBy "target" body with
  | some reason => .error reason
  | none => pure ()
  let senderSettle :=
    (valueOfField "attach" "snd-settle-mode" body).bind numberOf ==
      ((declaredChoice "sender-settle-mode" "settled").bind String.toNat?)
  let senderUnsettled :=
    (valueOfField "attach" "snd-settle-mode" body).bind numberOf ==
      ((declaredChoice "sender-settle-mode" "unsettled").bind String.toNat?)
  let receiverSecond :=
    (valueOfField "attach" "rcv-settle-mode" body).bind numberOf ==
      ((declaredChoice "receiver-settle-mode" "second").bind String.toNat?)
  let freshPosition : Option Position :=
    match role with
    | Role.sender => some ⟨initialCount, 0⟩
    | Role.receiver => some ⟨0, 0⟩
  let base := existing.getD (blankLink id)
  let flag := incompleteFlag body
  if outbound then
    let session := { session with localHandles := associate session.localHandles handle id }
    return putLink session
      (linkWithControlLink (linkAfterSentAttach base flag freshPosition role senderSettle
        senderUnsettled receiverSecond) outbound body)
  else
    let session := { session with remoteHandles := associate session.remoteHandles handle id }
    return putLink session
      (linkWithControlLink (linkAfterReceivedAttach base id flag initialCount freshPosition role
        senderSettle senderUnsettled receiverSecond) outbound body)

/-! ## The flow exchange -/

/-- The flow's link half: the five field clauses a flow that names no handle must not carry, the
handle it must name, the delivery-count and link-credit it must agree with, and the credit the doc's
formula moves. -/
def flowLink (session : WidenedSession) (outbound : Bool) (body : Value) :
    Except Refusal WidenedSession := do
  if !fieldPresent "flow" "handle" body then
    let linkFields :=
      ["delivery-count", "link-credit", "available", "drain", "properties"].filter
        (fun field => fieldPresent "flow" field body)
    refuseUnless linkFields.isEmpty
      (refuse invalidFieldCondition "malformed"
        s!"a flow that sets no handle MUST NOT set {linkFields}")
    return session
  let handle ←
    match (valueOfField "flow" "handle" body).bind numberOf with
    | some handle => pure handle
    | none => .error (refuse invalidFieldCondition "malformed"
        "the flow's handle field is not an integer")
  let id ←
    match resolveHandle session outbound handle with
    | some id => pure id
    | none => .error (refuse unattachedHandleCondition "illegalState"
        s!"a flow names handle {handle}, and this endpoint has no link attached there")
  let link ←
    match session.links id with
    | some link => pure link
    | none => .error (refuse unattachedHandleCondition "illegalState"
        s!"a flow names handle {handle}, and this endpoint has no link attached there")
  match linkFlowCountRefusal? link id outbound body with
  | some reason => .error reason
  | none => pure ()
  match linkFlowCreditEchoRefusal? link id outbound body with
  | some reason => .error reason
  | none => pure ()
  if outbound then return session
  else
    let receivedCount :=
      ((valueOfField "flow" "delivery-count" body).bind numberOf).getD 0
    let receivedCredit :=
      ((valueOfField "flow" "link-credit" body).bind numberOf).getD 0
    if id.localRole == Role.sender then
      let position : Option Position :=
        match link.position with
        | some current =>
          some { current with
                   credit := Position.creditFor receivedCount receivedCredit current.count }
        | none => link.position
      return putLink session
        { link with position := position, peerCount := receivedCount, peerCredit := receivedCredit }
    else
      match link.position with
      | some current =>
        return putLink session
          { link with position := some { current with count := receivedCount },
                      peerCredit := receivedCredit }
      | none => return session

/-- The session a flow leaves: the `next-incoming-id` rule, the link's half, and the windows a
received flow adopts. -/
def flowStep (session : WidenedSession) (outbound : Bool) (body : Value) :
    Except Refusal WidenedSession := do
  let set := fieldPresent "flow" "next-incoming-id" body
  if set != session.legacy.peerBegun then
    .error (placedFor session.legacy outbound invalidFieldCondition "malformed"
      "a flow's next-incoming-id is set exactly when the partner's begin has arrived")
  let session ←
    match flowLink session outbound body with
    | .ok session => pure session
    | .error reason => .error (placeFor session.legacy outbound reason)
  if outbound then return session
  else
    let windows :=
      session.legacy.windows.afterReceivingFlow
        (← windowField "flow" "next-outgoing-id" body)
        (← windowField "flow" "incoming-window" body)
        (← windowField "flow" "outgoing-window" body)
        (match valueOfField "flow" "next-incoming-id" body with
         | some .null | none => none
         | some value => numberOf value)
    return withWindows session windows

/-! ## The detach exchange -/

/-- The detach exchange: a detach releases its endpoint's handle and its flow state, and keeps the
link's unsettled history unless it carries an error. The handle released is the one the frame names
in the direction it travels — our own space for a detach we send, the peer's for one we receive —
which is the same direction whose endpoint life moves, so the binding never survives the endpoint it
belongs to. A detach naming a handle this endpoint does not have is admitted and changes nothing,
which is the one frame the links section excepts from its rule about input for a detached endpoint. -/
def detachStep (session : WidenedSession) (outbound : Bool) (body : Value) :
    Except Refusal WidenedSession := do
  let named := (valueOfField "detach" "handle" body).bind numberOf
  match named.bind (fun handle => resolveHandle session outbound handle) with
  | none => return session
  | some id =>
    match session.links id with
    | none => return session
    | some link =>
      let closed := booleanAtField "detach" "closed" body
      let withError := fieldPresent "detach" "error" body
      if outbound then
        let session := { session with localHandles := release session.localHandles id }
        return putLink session (linkAfterDetach link true closed withError)
      else
        let session := { session with remoteHandles := release session.remoteHandles id }
        return putLink session (linkAfterDetach link false closed withError)

/-! ## The disposition exchange -/

/-- One link's share of a disposition: the delivery the link holds in progress is released when its
id lies in the named range, and the entry at that delivery's tag leaves the unsettled table, which
is `disposition.4`'s "the updated state MUST be applied". -/
def applyDisposition (session : WidenedSession) (link : Link) (first last : Nat) (settled : Bool) :
    WidenedSession :=
  if !settled then putLink session link
  else
    match link.delivery, link.deliveryTag with
    | some delivery, some tag =>
      if first ≤ delivery.id && delivery.id ≤ last then
        putLink session
          { link with delivery := none, deliveryTag := none, deliveryFormat := none,
                      unsettled := clearEntry link.unsettled tag }
      else putLink session link
    | _, _ => putLink session link

/-- The disposition exchange: `disposition.1`/`.2`'s directionality, the range `first`/`last` name,
and the settlement a disposition carries. A disposition declares no `handle` field, so the link it is
about is resolved through the registry's index: every registered link whose local role the frame's
`role` names, including links that are no longer attached, which is what `disposition.3` permits and
`disposition.4` then requires the state of. -/
def dispositionStep (session : WidenedSession) (outbound : Bool) (body : Value) :
    Except Refusal WidenedSession := do
  let role ←
    match (valueOfField "disposition" "role" body).bind Role.ofValue with
    | some role => pure role
    | none => .error (refuse invalidFieldCondition "malformed"
        "a disposition must carry a role the declared type names")
  let first ←
    match valueOfField "disposition" "first" body with
    | some value => pure ((numberOf value).getD 0)
    | none => pure 0
  let last ←
    match valueOfField "disposition" "last" body with
    | some value => pure ((numberOf value).getD 0)
    | none => pure first
  refuseUnless (first ≤ last)
    (refuse invalidFieldCondition "malformed"
      s!"the disposition's range runs from {first} to {last}, which is not a range")
  let targets :=
    (session.linkKeys.filter (fun key => key.localRole == role)).filterMap
      (fun key => (session.links key).map (fun link => (key, link)))
  refuseUnless (!targets.isEmpty)
    (refuse invalidFieldCondition "malformed"
      "the disposition names the deliveries of a role this session has no link of")
  let settled := booleanAtField "disposition" "settled" body
  let session :=
    targets.foldl (fun session target => applyDisposition session target.2 first last settled)
      session
  return (← targets.foldlM (fun session target =>
    match session.links target.1 with
    | some link =>
      match linkStepTransactionState link outbound body with
      | .ok link => pure (putLink session link)
      | .error reason => .error reason
    | none => pure session) session)

/-! ## The transfer exchange -/

/-- The transfer exchange's link half, widened: the frame's own fields, the credit it spends, the
delivery it carries, and the rules the widening adds —

* `links.23`, read after the credit gate: a tag already holding a *different* delivery is refused,
  while the same tag and the same id is a retransfer of one delivery;
* `transfer/field:resume.2`: a sent resumed transfer for a delivery not in the local table is
  refused;
* `transfer/field:resume.1`: a received one whose tag the table does not hold is *ignored* — the one
  place a step admits a frame and records nothing of it;
* `transfer/field:resume.3`: the resume flag is the first transfer's claim, so a continuation
  carrying it for a delivery that did not begin that way is refused;

and the incomplete-map latch: an endpoint whose peer announced an incomplete map may not be offered
a new delivery, and an endpoint that announced one of its own must answer a transfer without the
resume flag with a detach carrying an error. -/
def transferLink (session : WidenedSession) (outbound : Bool) (body : Value) :
    Except Refusal WidenedSession := do
  let handle ←
    match (valueOfField "transfer" "handle" body).bind numberOf with
    | some handle => pure handle
    | none => .error (refuse invalidFieldCondition "malformed"
        "a transfer must carry an integer handle")
  let id ←
    match resolveHandle session outbound handle with
    | some id => pure id
    | none => .error (refuse unattachedHandleCondition "illegalState"
        "a transfer names a handle this endpoint does not have attached")
  let link ←
    match session.links id with
    | some link => pure link
    | none => .error (refuse unattachedHandleCondition "illegalState"
        "a transfer names a handle this endpoint does not have attached")
  let sender := id.localRole == Role.sender
  refuseUnless (outbound == sender)
    (refuse illegalStateCondition "illegalState"
      s!"a transfer is the sender's frame, and this endpoint attached as \
        {(peerRoleOf id).label}")
  let continued := link.delivery.isSome
  let carriedId := (valueOfField "transfer" "delivery-id" body).bind numberOf
  let carriedTag := (valueOfField "transfer" "delivery-tag" body).bind octetsOf
  let carriedFormat := (valueOfField "transfer" "message-format" body).bind numberOf
  refuseUnless (deliveryTagInBounds body)
    (refuse invalidFieldCondition "malformed"
      "the transfer's delivery-tag carries more than the 32 octets of binary data the type allows")
  let deliveryId ←
    match carriedId with
    | some carried => pure carried
    | none =>
      match link.delivery with
      | some delivery => pure delivery.id
      | none => .error (refuse invalidFieldCondition "malformed"
          "the first transfer of a delivery MUST carry its delivery-id")
  refuseUnless (continued || (fieldPresent "transfer" "delivery-tag" body &&
      fieldPresent "transfer" "message-format" body))
    (refuse invalidFieldCondition "malformed"
      "a first transfer MUST carry its delivery-tag and message-format, which only a continuation \
        transfer may omit")
  let tag : Option DeliveryTag := if continued then link.deliveryTag else carriedTag
  let resume := booleanAtField "transfer" "resume" body
  let held := tag.map (fun key => resumable link key)
  if resume && held == some false && outbound then
    refuseUnless false
      (refuse invalidFieldCondition "malformed"
        "the sender MUST NOT send resumed transfers for deliveries not in its local unsettled map")
  if resume && held == some false && !outbound then
    return session
  if resume && continued then
    refuseUnless (link.delivery.map (fun delivery => delivery.resumed) == some true)
      (refuse invalidFieldCondition "malformed"
        "a resumed delivery spans more than one transfer performative, so the resume flag MUST be \
          set on the first transfer of the delivery")
  if outbound && !continued && !resume then
    refuseUnless (!link.remoteEndpoint.incompleteUnsettled)
      (refuse illegalStateCondition "illegalState"
        "an incomplete unsettled map was received for this link, so this endpoint MUST NOT send a \
          new delivery until it is complete")
  if !outbound && !resume then
    refuseUnless (!link.localEndpoint.incompleteUnsettled)
      (refuse illegalStateCondition "illegalState"
        "this endpoint sent an incomplete unsettled map, so it MUST detach with an error on a \
          transfer that does not set the resume flag")
  if continued then
    refuseUnless (carriedId.isNone || link.delivery.map (fun held => held.id) == some deliveryId)
      (refuse invalidFieldCondition "malformed"
        "the delivery-id of a continuation transfer differs from the delivery-id of the delivery it \
          continues, which is an error")
    refuseUnless (carriedTag.isNone || carriedTag == link.deliveryTag)
      (refuse invalidFieldCondition "malformed"
        "the delivery-tag of a continuation transfer differs from the delivery-tag of the delivery \
          it continues, which is an error")
    refuseUnless (carriedFormat.isNone || carriedFormat == link.deliveryFormat)
      (refuse invalidFieldCondition "malformed"
        "the message-format of a continuation transfer differs from the message-format of the \
          delivery it continues, which is an error")
  let settled := booleanAtField "transfer" "settled" body
  let aborted := booleanAtField "transfer" "aborted" body
  let more := !aborted && booleanAtField "transfer" "more" body
  let delivery : Except Refusal (Option WidenedDelivery) :=
    if aborted then pure none
    else if more then pure (some (deliveryStep link.delivery deliveryId settled resume))
    else
      let completed := deliveryStep link.delivery deliveryId settled resume
      if link.senderSettleMode && !completed.settled then
        .error (refuse invalidFieldCondition "malformed"
          "the negotiated settlement mode is the settled choice of sender-settle-mode, so a \
            delivery MUST be settled in at least one of its transfers")
      else pure none
  let delivery ← delivery
  let tagOut : Option DeliveryTag :=
    if delivery.isSome then (if continued then link.deliveryTag else carriedTag) else none
  let formatOut : Option Nat :=
    if delivery.isSome then (if continued then link.deliveryFormat else carriedFormat) else none
  let starting := !continued
  if sender && starting then
    match link.position with
    | some current =>
      refuseUnless (current.credit > 0)
        (refuse wireCondition "limit"
          "the link has no credit left: the sender has reached the receiver's delivery-limit")
    | none => pure ()
  -- `links.23`, after the flow-control gate: a link with no credit left cannot send the delivery at
  -- all, so the tag's own rule is read where the frame is one the link may send
  if !continued then
    match tag with
    | some key =>
      match link.unsettled key with
      | some held =>
        refuseUnless (held.deliveryId == deliveryId)
          (refuse invalidFieldCondition "malformed"
            "the delivery-tag is already held by another delivery, and a tag is unique among the \
              deliveries either end could still consider unsettled")
      | none => pure ()
    | none => pure ()
  let position : Option Position :=
    match link.position with
    | some current =>
      some { current with
               credit := if sender && starting then current.credit - 1 else current.credit,
               count := if starting then current.count + 1 else current.count }
    | none => link.position
  let table :=
    match tag with
    | none => link.unsettled
    | some key =>
      if settled || aborted then clearEntry link.unsettled key
      else
        setEntry link.unsettled key
          { deliveryId := deliveryId,
            localState := (link.unsettled key).bind (fun held => held.localState),
            remoteState := (link.unsettled key).bind (fun held => held.remoteState) }
  let nextDeliveryId := if outbound && starting then deliveryId + 1 else link.nextDeliveryId
  return putLink session
    (linkAfterTransfer link position delivery tagOut formatOut nextDeliveryId table)

/-- The session a transfer leaves, with the session-scope rules the restricted reading places around
it: the two windows a sent transfer is charged against, the settlement the transfer's own fields
carry, and the window the frame leaves. -/
def transferStep (session : WidenedSession) (outbound : Bool) (body : Value) (payload : Octets) :
    Except Refusal WidenedSession := do
  let handle := (valueOfField "transfer" "handle" body).bind numberOf
  let link? :=
    handle.bind (fun h => (resolveHandle session outbound h).bind (fun id => session.links id))
  let settled :=
    booleanAtField "transfer" "settled" body ||
      (match link? with
       | some link => (link.delivery.map (fun delivery => delivery.settled)).getD false
       | none => false)
  let aborted := booleanAtField "transfer" "aborted" body
  match link? with
  | some link =>
    match linkRcvSettleRefusal? link body settled with
    | some reason => .error (placeFor session.legacy outbound reason)
    | none =>
      match linkUnsettledSettleRefusal? link settled aborted with
      | some reason => .error (placeFor session.legacy outbound reason)
      | none => pure ()
  | none => pure ()
  if outbound then
    refuseUnless (session.legacy.windows.outgoing > 0)
      (placedFor session.legacy outbound windowViolationCondition "limit"
        "this session's outgoing window is exhausted, so it may not send another transfer")
    refuseUnless (session.legacy.windows.remoteIncoming > 0)
      (placedFor session.legacy outbound windowViolationCondition "limit"
        "the partner's incoming window is exhausted, so it can accept no further transfers")
    let session ←
      match transferLink session outbound body with
      | .ok session => pure session
      | .error reason => .error (placeFor session.legacy outbound reason)
    let session ←
      match handle.bind (fun h => (resolveHandle session outbound h).bind
          (fun id => session.links id)) with
      | some link =>
        match linkStepTransactionPayload link outbound payload settled with
        | .ok link => pure (putLink session link)
        | .error reason => .error (placeFor session.legacy outbound reason)
      | none => pure session
    return withWindows session (session.legacy.windows.afterSendingTransfer windowPolicy)
  else
    refuseUnless (session.legacy.windows.incoming > 0)
      (placedFor session.legacy outbound windowViolationCondition "limit"
        "this session's incoming window is exhausted, so it cannot receive another transfer")
    let session ←
      match transferLink session outbound body with
      | .ok session => pure session
      | .error reason => .error (placeFor session.legacy outbound reason)
    let session ←
      match handle.bind (fun h => (resolveHandle session outbound h).bind
          (fun id => session.links id)) with
      | some link =>
        match linkStepTransactionPayload link outbound payload settled with
        | .ok link => pure (putLink session link)
        | .error reason => .error (placeFor session.legacy outbound reason)
      | none => pure session
    return withWindows session
      (session.legacy.windows.afterReceivingTransfer session.legacy.windows.nextIncoming
        windowPolicy)

/-! ## The step -/

/-- **The widened session's step**: one frame, one direction, and the session it leaves. The prologue
is the restricted step's own — the DISCARDING short-circuit, the channel map, the state's permission
column and the mandatory fields, with the same two placements — because it is the same machine; what
follows is the link layer over the widened state. A frame this layer does not answer for is carried
rather than judged. -/
def step (session : WidenedSession) (outbound : Bool) (channel : Nat) (body : Value)
    (payload : Octets) : Except Refusal WidenedSession := do
  let legacy := session.legacy
  let frame := frameOf body
  let typeName :=
    match frame with
    | .begin => "begin" | .end => "end" | .attach => "attach" | .detach => "detach"
    | .flow => "flow" | .transfer => "transfer" | .other => ""
  -- DISCARDING discards what arrives until the peer's end, without looking at it
  if !outbound && legacy.state == .discarding && frame != .end then
    return session
  -- the begins are what map the channels, so they are the frames that arrive on a channel that is
  -- not mapped yet
  let mapped := if outbound then legacy.outgoing else legacy.incoming
  if frame != .begin && mapped != some channel then
    .error (refuse wireCondition "illegalState"
      s!"channel {channel} is not this session's {if outbound then "outgoing" else "incoming"} \
        channel, {mapped}")
  let allowed := frame == .begin ||
    (if outbound then sendAllowed legacy.state else receiveAllowed legacy.state)
  if !allowed then
    .error (placedFor legacy outbound illegalStateCondition "illegalState"
      s!"{legacy.state.label} does not let this session \
        {if outbound then "send" else "receive"} a {frame.label} frame")
  let missing := missingMandatory typeName body
  if !missing.isEmpty then
    .error (placedFor legacy outbound invalidFieldCondition "malformed"
      s!"the {typeName} performative does not carry {missing}, and the declared surface marks \
        it mandatory")
  match frame with
  | .begin =>
    let legacy ← takeBegin legacy outbound channel body
    return { session with legacy }
  | .end =>
    let withError := fieldPresent "end" "error" body
    return { session with legacy := afterEnd legacy outbound withError }
  | .attach =>
    match attachStep session outbound body with
    | .ok next => pure next
    | .error reason => .error (placeFor legacy outbound reason)
  | .detach =>
    match detachStep session outbound body with
    | .ok next => pure next
    | .error reason => .error (placeFor legacy outbound reason)
  | .flow => flowStep session outbound body
  | .transfer => transferStep session outbound body payload
  | .other =>
    if isDisposition body then
      match dispositionStep session outbound body with
      | .ok next => pure next
      | .error reason => .error (placeFor legacy outbound reason)
    else return session

end SpecAMQP.Ref.Protocol
