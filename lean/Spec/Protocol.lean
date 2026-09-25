/-
# The widened protocol step (`PLAN.md` §24 part 4)

The executable half of the widening. `Spec.WidenedState` declares the state — a stable link
registry keyed by identity, two directional handle maps, one shared unsettled table, and each
endpoint's own life and incomplete-map latch — and this module is where a frame moves it.

## What is here, and what is not

The session machine's prologue — the DISCARDING short-circuit, the channel map, the state's column
and the mandatory fields — is `Spec.Session.gate`, shared with the restricted single-link step so
the machine exists once. What this module owns is everything the widening adds or moves: the link
layer's rules, now that a session may hold more than one link and each link has two endpoint-local
handle spaces and one unsettled history.

`Spec.Session` keeps its own `step` and its own link rules unchanged. They are the *restricted*
model a session with exactly one link reaches: the frozen contracts in `Contracts/Settlement.lean`
and `Contracts/SessionCredit.lean` are stated over them and over `Session`'s single-link fields,
and those statements are part of the record rather than a second implementation to be kept in
step. The widened path never dispatches through them and never synchronizes their slots: the
registry is the only live representation of link state, and `legacy` is read for session-scope
state alone (`state`, `outgoing`, `incoming`, `peerBegun`, `windows`, `handleMax`,
`peerHandleMax`) and written for the same.

## The readings this module implements

* **Identity is the name plus *our* role.** An attach's `role` field names the *sender's* link
  endpoint, so a frame this endpoint sends names our role and one it receives names the peer's,
  and `identityOf` is the name plus our role in both cases. That is what lets both ends use handle
  zero and keeps two opposite-direction links of one name distinct.
* **Two handle spaces, one history.** `localHandles` and `remoteHandles` are separate, and a
  logical link has exactly one `unsettled` table, so the two spaces cannot drift into two accounts
  of one delivery.
* **The table is written by transfers and read by the rules that need it.** An entry appears when a
  transfer leaves a delivery unsettled, and it leaves when a disposition settles it, when a
  transfer settles it, or when an aborted transfer discards it. An attach's `unsettled` map is
  validated (its null keys are refused) and its keys are not merged: the map's values are delivery
  states, and `attach/field:unsettled.1`'s comparison of the local and remote states is a held
  comparison carried as a theorem (`Proofs/`), not a decision a step takes.
* **A handle-less frame is resolved through the registry's index.** `disposition` declares no
  `handle` field at all, so it is applied to every registered link whose local role the frame's
  `role` names — the order `linkKeys` carries is not observable and does not affect the result.
* **A detach releases an endpoint, not a link's history.** `disposition.4` makes a delivery stay
  unsettled while the link is neither closed nor detached with an error, so the flow state goes
  with the endpoint and the unsettled history does not.
-/

import Spec.WidenedState

namespace SpecAMQP.Spec.Protocol

open SpecAMQP.Harness (Octets)
open SpecAMQP.Spec.Codec (Value)
open SpecAMQP.Spec.Session
open SpecAMQP.Spec.Connection
  (choiceValue? fieldBool fieldValue fieldSet framingError invalidField valueBool valueNat
   valueOctets)
open SpecAMQP.Spec
  (DeliveryTag UnsettledDelivery WidenedDelivery LinkId LinkLife WidenedLinkEndpoint WidenedLink
   WidenedSession LinkNamesUnique RegistryKeysComplete UnsettledKeysComplete HandlesResolveLinks
   WidenedProtocolState WidenedProtocolStateValid)

/-! ## Link identity and the two handle spaces -/

/-- The other end's role. -/
def oppositeRole : LinkRole → LinkRole
  | .sender => .receiver
  | .receiver => .sender

/-- The other end's role is its own inverse, which is what makes `identityOf` involutive in the
direction a frame travels. -/
theorem oppositeRole_oppositeRole (role : LinkRole) : oppositeRole (oppositeRole role) = role := by
  cases role <;> rfl

/-- The identity of the link an attach names: the uninterpreted name plus *our* role. The frame's
`role` field names the sender's endpoint, so an attach this endpoint sends carries our role and one
it receives carries the peer's. -/
def identityOf (outbound : Bool) (name : String) (role : LinkRole) : LinkId :=
  { name := name, localRole := if outbound then role else oppositeRole role }

/-- The peer's role in a link identity. -/
def peerRoleOf (id : LinkId) : LinkRole := oppositeRole id.localRole

/-- The identity a handle names, in the direction the frame travels. -/
def resolveHandle (session : WidenedSession) (outbound : Bool) (handle : Nat) : Option LinkId :=
  if outbound then session.localHandles handle else session.remoteHandles handle

/-- Bind a handle to an identity, dropping any binding the identity held in that direction.
`HandlesResolveLinks` allows one active handle per identity and one identity per handle, so a
resume that moves an endpoint onto a new handle must release the old one in the same step. -/
def associate (handles : Nat → Option LinkId) (handle : Nat) (id : LinkId) : Nat → Option LinkId :=
  fun h => if h == handle then some id else if handles h == some id then none else handles h

/-- Release an identity's binding in one direction. -/
def release (handles : Nat → Option LinkId) (id : LinkId) : Nat → Option LinkId :=
  fun h => if handles h == some id then none else handles h

/-- The link record a peer's attach creates where this endpoint has none: no endpoint associated on
either side, and no history. `suspended` is the artifact's own word for a link whose termini exist
without an endpoint — "a link is said to be suspended if the termini exist, but have no associated
link endpoints" — and it is the only honest life for an endpoint this end has never attached. -/
def blankLink (id : LinkId) : WidenedLink where
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
  unsettledKeys := []
  nextDeliveryId := 0

/-- Write a link record at its own key, which is the only slot it can occupy: `LinkNamesUnique`
then holds by construction. A key the session has not seen gains its one entry in `linkKeys` here
and never loses it, which is what `RegistryKeysComplete` needs of the index. -/
def putLink (session : WidenedSession) (link : WidenedLink) : WidenedSession :=
  { session with
      links := fun key => if key == link.id then some link else session.links key,
      linkKeys := if session.linkKeys.contains link.id then session.linkKeys
                  else session.linkKeys ++ [link.id] }

/-! ## The shared unsettled table

One table keyed by `DeliveryTag`, with the two observations an in-doubt delivery is resolved from,
and `unsettledKeys`, the finite index of the tags the table holds. A transfer adds a key through
`setEntry` and drops one through `clearEntry`, and those are the only two things a step does to the
table; a `disposition` names neither a link nor a tag, so it walks that index to reach every entry
the delivery-id range it carries covers. -/

/-- One key's entry, with the link's finite index kept in step: a tag enters the index when the
table first holds it. The index is what makes the table walkable, which is what a `disposition` —
a frame that names no link and no tag — needs in order to reach a delivery the link no longer holds
in progress (`disposition.3`'s case). -/
def setEntry (link : WidenedLink) (key : DeliveryTag) (entry : UnsettledDelivery) : WidenedLink :=
  { link with
      unsettled := fun k => if k == key then some entry else link.unsettled k,
      unsettledKeys := if link.unsettledKeys.contains key then link.unsettledKeys
                       else key :: link.unsettledKeys }

/-- Drop one key, and its entry in the index with it. -/
def clearEntry (link : WidenedLink) (key : DeliveryTag) : WidenedLink :=
  { link with
      unsettled := fun k => if k == key then none else link.unsettled k,
      unsettledKeys := link.unsettledKeys.filter (fun k => k != key) }

/-! ## Reading the attach's two widening fields -/

/-- The `unsettled` field's keys, with `attach/field:unsettled.5`'s null-key prohibition checked:
`none` for an absent or null field, the map's keys when the field is a map, and a refusal when a key
is null. A key that is not a `binary` value is not a delivery tag and is not carried; the map's
*values* are not interpreted at all. -/
def unsettledKeyList : List (Value × Value) → Except Refusal (List DeliveryTag)
  | [] => .ok []
  | pair :: rest =>
    match pair.1 with
    | .null => .error (refusal invalidField "malformed" "the attach's unsettled map carries a null key, and the map MUST NOT contain null valued keys")
    | key =>
      match valueOctets key with
      | some octets => (unsettledKeyList rest).map (fun keys => ByteArray.mk octets :: keys)
      | none => unsettledKeyList rest

def unsettledKeys (body : Value) : Except Refusal (Option (List DeliveryTag)) :=
  match fieldValue "attach" "unsettled" body with
  | none | some .null => .ok none
  | some (.map pairs) => (unsettledKeyList pairs).map (fun keys => some keys)
  | some _ => .ok none

/-- The latch an attach sets: `attach/field:incomplete-unsettled`'s flag, false where the field is
absent. The flag is assigned from *each* attach for that link — which is how a later attach with the
flag false lifts the latch, `incomplete-unsettled.3`'s lift through its consequence. -/
def incompleteFlag (body : Value) : Bool := fieldBool "attach" "incomplete-unsettled" body

/-! ## The delivery a transfer carries -/

/-- Whether the link holds this delivery-tag in the unsettled state either end could still resolve.
`transfer/field:resume.1` and `.2` phrase this as "in its local unsettled map" and
`links/doc:resuming-deliveries.3`-`.5` as the deliveries only one end, or both ends, consider
unsettled; the widened step reads this predicate in both directions, which is what makes the three
clauses' obligations statable over one function rather than three paraphrases. -/
def resumable (link : WidenedLink) (tag : DeliveryTag) : Bool := (link.unsettled tag).isSome

/-- The delivery a transfer's own flags leave in progress: the settled flag accumulates over the
delivery's transfers (`settled.2`/`.3`), and `resumed` records whether the transfer that *began* the
delivery carried the resume flag, which is `resume.3`'s antecedent. -/
def deliveryStep (current : Option WidenedDelivery) (id : Nat) (settled resumed : Bool) :
    WidenedDelivery :=
  match current with
  | some delivery => { delivery with settled := delivery.settled || settled }
  | none => ⟨id, settled, resumed⟩

/-! ## The guards that read the link's negotiation -/

/-- `transfer/field:rcv-settle-mode.u1` with `.u2`'s exemption, at the link's negotiation. -/
def rcvSettleRefusal? (link : WidenedLink) (body : Value) (settled : Bool) : Option Refusal :=
  match (fieldValue "transfer" "rcv-settle-mode" body).bind valueNat with
  | none => none
  | some mode =>
    if settled || link.receiverSettleSecond then none
    else if some mode == ((choiceValue? "receiver-settle-mode" "second").bind String.toNat?) then
      some (refusal invalidField "malformed" "the transfer sets rcv-settle-mode to the second choice, and the link negotiated the first choice")
    else none

/-- `transfer/field:settled.6`, at the link's negotiation, with `aborted`'s exemption. -/
def unsettledSettleRefusal? (link : WidenedLink) (settled aborted : Bool) : Option Refusal :=
  if link.senderSettleUnsettled && settled && !aborted then
    some (refusal invalidField "malformed" "the link negotiated the unsettled choice of sender-settle-mode, so the settled flag MUST be false (or unset) on a transfer for a delivery unless the delivery is aborted")
  else none

/-- `flow/field:delivery-count`'s rule, at the link's roles and lives. -/
def flowCountRefusal? (link : WidenedLink) (outbound : Bool) (body : Value) : Option Refusal :=
  if !fieldSet "flow" "handle" body then none
  else
    let issuing := if outbound then link.id.localRole else peerRoleOf link.id
    let senderSeen := if outbound then link.remoteEndpoint.life == .attached
                      else link.localEndpoint.life == .attached
    let receiverBeforeSender := issuing == some LinkRole.receiver && !senderSeen
    match fieldValue "flow" "delivery-count" body with
    | none =>
      if receiverBeforeSender then none
      else some (refusal invalidField "malformed" "a flow that names the link MUST set its delivery-count, and this one omits it")
    | some value =>
      if receiverBeforeSender then
        some (refusal invalidField "malformed" "the receiving link endpoint has not yet seen the initial attach frame from the sender, so its flow MUST NOT set the delivery-count")
      else
        match link.position, valueNat value with
        | none, _ => none
        | some _, none => some (refusal invalidField "malformed" "the flow's delivery-count is not an integer")
        | some current, some carried =>
          if carried == current.deliveryCount then none
          else some (refusal invalidField "malformed" "the flow's delivery-count is not this endpoint's value for the link")

/-- `links/doc:flow-control.u1`, `.u3` and `flow/field:link-credit.u1`: a flow from the link's
sender echoes the receiver's last known value and sets nothing. -/
def flowCreditEchoRefusal? (link : WidenedLink) (outbound : Bool) (body : Value) : Option Refusal :=
  if !fieldSet "flow" "handle" body then none
  else
    let issuing := if outbound then link.id.localRole else peerRoleOf link.id
    if issuing != some LinkRole.sender then none
    else
      match link.position, (fieldValue "flow" "link-credit" body).bind valueNat with
      | some current, some credit =>
        if credit == current.credit then none
        else some (refusal invalidField "malformed" "a flow from the link's sender carries a link-credit that is not this endpoint's last known value")
      | _, _ => none

/-! ## The transaction layer's carriers, per link -/

/-- One transaction value, from the frame that carried it. -/
def linkStepTransaction (link : WidenedLink) (carrier : Transactions.Carrier) (outbound : Bool)
    (value : Value) (settled : Bool) : Except Refusal WidenedLink := do
  match link.transactions with
  | none => return link
  | some layer =>
    match Transactions.step layer carrier outbound value settled with
    | .ok layer => return { link with transactions := some layer }
    | .error reason =>
      .error ⟨reason.condition, reason.detail, none, false⟩

/-- The transaction layer's step for a transfer's payload. -/
def linkStepTransactionPayload (link : WidenedLink) (outbound : Bool) (payload : Octets)
    (settled : Bool) : Except Refusal WidenedLink := do
  match link.transactions with
  | none => return link
  | some _ =>
    match Message.bodyValue Message.Policy.empty payload with
    | .error _ => return link
    | .ok value => linkStepTransaction link .payload outbound value settled

/-- The transaction layer's step for a disposition's `state`. -/
def linkStepTransactionState (link : WidenedLink) (outbound : Bool) (body : Value) :
    Except Refusal WidenedLink :=
  match fieldValue "disposition" "state" body with
  | some state => linkStepTransaction link .state outbound state false
  | none => .ok link

/-- The control link's transaction layer, where the attach names a coordinator target. -/
def linkWithControlLink (link : WidenedLink) (outbound : Bool) (body : Value) : WidenedLink :=
  match (fieldValue "attach" "target" body).bind Transactions.coordinatorCapabilities with
  | none => link
  | some capabilities =>
    let layer := link.transactions.getD Transactions.Layer.fresh
    { link with
        transactions := some (if outbound then { layer with capabilities }
                              else { layer with peerCapabilities := capabilities }) }

/-! ## The link each exchange leaves -/

/-- The link a sent attach leaves: our endpoint attached at the frame's handle, the position the
role and initial count give it, and the settlement the attach negotiated. The peer's flow state is
reset — the credit is the partner's to grant for this link and the partner's count is its own
announcement — and the in-progress delivery is cleared, because a link being established is not
continuing one. -/
def linkAfterSentAttach (base : WidenedLink) (flag : Bool) (position : Option Position)
    (role : LinkRole) (senderSettle senderUnsettled receiverSecond : Bool) : WidenedLink :=
  { base with
      localEndpoint := { base.localEndpoint with terminusAssociated := true, life := .attached, incompleteUnsettled := flag },
      position := position,
      peerCount := 0,
      peerCredit := 0,
      senderSettleMode := if role == LinkRole.sender then senderSettle else base.senderSettleMode,
      senderSettleUnsettled := if role == LinkRole.sender then senderUnsettled
                               else base.senderSettleUnsettled,
      receiverSettleSecond := if role == LinkRole.receiver then receiverSecond
                              else base.receiverSettleSecond,
      delivery := none,
      deliveryTag := none,
      deliveryFormat := none }

/-- The link a received attach leaves: the peer's endpoint attached at the frame's handle, with the
flow state the legacy reading keeps — the peer's count is a quantity its owner announces, so a
received attach sets this endpoint's view of it only when the partner is the link's sender and this
endpoint is its receiver, and the position survives an attach that does not establish the link. -/
def linkAfterReceivedAttach (base : WidenedLink) (id : LinkId) (flag : Bool)
    (initialCount : Nat) (freshPosition : Option Position) (role : LinkRole)
    (senderSettle senderUnsettled receiverSecond : Bool) : WidenedLink :=
  { base with
      remoteEndpoint := { base.remoteEndpoint with terminusAssociated := true, life := .attached, incompleteUnsettled := flag },
      peerCount := (if role == LinkRole.sender && id.localRole == LinkRole.receiver then initialCount
                    else base.peerCount),
      position := (if role == LinkRole.sender || base.position.isSome then base.position
                   else freshPosition),
      senderSettleMode := if role == LinkRole.sender then senderSettle else base.senderSettleMode,
      senderSettleUnsettled := if role == LinkRole.sender then senderUnsettled
                               else base.senderSettleUnsettled,
      receiverSettleSecond := if role == LinkRole.receiver then receiverSecond
                              else base.receiverSettleSecond,
      delivery := none,
      deliveryTag := none,
      deliveryFormat := none }

/-- The link a detach of one endpoint leaves. That endpoint's handle has been released by the
caller, the endpoint is destroyed or merely released, and the flow state it held goes with it. The
unsettled history is *kept*: `disposition.4` makes a delivery remain unsettled while the link is
neither closed nor detached with an error, and a resume exists precisely so that a suspended link
can be restored. Only a detach carrying an error ends the link's history. -/
def linkAfterDetach (base : WidenedLink) (outbound closed withError : Bool) : WidenedLink :=
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
        unsettledKeys := (if withError then [] else base.unsettledKeys),
        transactions := base.transactions.map Transactions.Layer.retireAll }
  else
    { base with
        remoteEndpoint := { base.remoteEndpoint with life := (if closed then .destroyed else .detached), incompleteUnsettled := false },
        peerCount := 0,
        peerCredit := 0,
        delivery := (if withError then none else base.delivery),
        deliveryTag := (if withError then none else base.deliveryTag),
        deliveryFormat := (if withError then none else base.deliveryFormat),
        unsettled := (if withError then fun _ => none else base.unsettled),
        unsettledKeys := (if withError then [] else base.unsettledKeys),
        transactions := base.transactions.map Transactions.Layer.retireAll }

/-- The link a transfer leaves: the delivery it carries or completes, the identity recorded with
it, the sender's next id, and the credit or count the transfer moves. The unsettled table and its
index travel in `base`, because a transfer is what writes them. -/
def linkAfterTransfer (base : WidenedLink) (position : Option Position)
    (delivery : Option WidenedDelivery) (deliveryTag : Option DeliveryTag)
    (deliveryFormat : Option Nat) (nextDeliveryId : Nat) : WidenedLink :=
  { base with
      position := position,
      delivery := delivery,
      deliveryTag := deliveryTag,
      deliveryFormat := deliveryFormat,
      nextDeliveryId := nextDeliveryId }

/-- The session with its session-scope windows replaced. The window arithmetic lives on the
restricted session state, and this is the one place the widened step writes it. -/
def withWindows (session : WidenedSession) (windows : Windows) : WidenedSession :=
  { session with legacy := { session.legacy with windows } }

/-- The widened session with its session-scope state replaced: what a refusal that places the peer
in a state leaves. -/
def withState (session : WidenedSession) (st : State) : WidenedSession :=
  { session with legacy := { session.legacy with state := st } }

/-- A widened session over a session-scope state, with no link registered and no handle bound: what
a corpus `session:<STATE>` start is, and the only state the widened path begins from. -/
def sessionOf (legacy : Session) : WidenedSession where
  legacy := legacy
  links := fun _ => none
  linkKeys := []
  localHandles := fun _ => none
  remoteHandles := fun _ => none

/-! ## The attach exchange -/

/-- The attach exchange, widened. The handle rules come first (`attach/field:handle.1`/`.2` and
`begin/field:handle-max` in both directions), then the identity the name and role name, then the
three states the artifact distinguishes: an attach for a link whose end is already *associated* must
carry its unsettled delivery state (`links.5`); an endpoint that is *detached* still exists, so the
attach is a re-attach and its map MUST be null (`unsettled.6`); and an endpoint that is *destroyed*
can only be restored by a resume, which `links.16`-`.18` enforce by requiring the map a resume is
recognized by. -/
def attachStep (session : WidenedSession) (outbound : Bool) (body : Value) :
    Except Refusal WidenedSession := do
  let role ←
    match (fieldValue "attach" "role" body).bind LinkRole.ofValue with
    | some role => pure role
    | none => .error (refusal invalidField "malformed" "the attach must carry a role, and it must be one of the values the declared role type names")
  let handle ←
    match (fieldValue "attach" "handle" body).bind valueNat with
    | some handle => pure handle
    | none => .error (refusal invalidField "malformed" "the attach must carry an integer handle")
  let name :=
    match fieldValue "attach" "name" body with
    | some (.string text) => text
    | some (.symbol text) => text
    | _ => ""
  refuseUnless (handle ≤ (if outbound then session.legacy.peerHandleMax else session.legacy.handleMax))
    (closingRefusal framingError "limit" "the handle is outside the range the partner's begin declared it would accept")
  -- `attach/field:handle.2` forbids a handle "used for other open links": the same link re-attaching
  -- on the handle it already holds is not another link, and it is the handle moving a resume that
  -- this check exists to catch
  let id := identityOf outbound name role
  let bound := resolveHandle session outbound handle
  refuseUnless (bound.isNone || bound == some id)
    (closingRefusal handleInUse "illegalState" "the handle is already associated with another link, and a handle MUST NOT be used for other open links")
  let existing := session.links id
  let life : Option LinkLife :=
    existing.map (fun link => if outbound then link.localEndpoint.life else link.remoteEndpoint.life)
  let keys ← unsettledKeys body
  let carriesMap := keys.isSome
  match life with
  | some .attached =>
    if outbound then
      refuseUnless carriesMap
        (refusal invalidField "malformed" "an attach for a link whose terminus is already associated MUST carry its unsettled delivery state, and this one carries none")
  | some .detached =>
    refuseUnless (!carriesMap)
      (refusal invalidField "malformed" "a re-attach MUST carry a null unsettled map: the link endpoint still exists, and the map is the resume's")
  | some .destroyed =>
    refuseUnless carriesMap
      (refusal (sessionErrorCondition "errant-link") "illegalState" "the link endpoint is destroyed, so this attach MUST resume the link and carry the unsettled state it resumes it with")
  | some .suspended => pure ()
  | none => pure ()
  let initialCount ←
    match (fieldValue "attach" "initial-delivery-count" body).bind valueNat with
    | some count => pure count
    | none =>
      if role == LinkRole.sender then
        .error (refusal invalidField "malformed" "a sender's attach MUST carry its initial delivery-count")
      else pure 0
  let sentBy := if role == LinkRole.sender then Message.SendingEndpoint.sender
                else Message.SendingEndpoint.receiver
  refuseUnless ((terminusRefusalOf sentBy "source" body).isNone)
    ((terminusRefusalOf sentBy "source" body).getD
      (refusal invalidField "malformed" "the attach's source is not a valid terminus"))
  refuseUnless ((terminusRefusalOf sentBy "target" body).isNone)
    ((terminusRefusalOf sentBy "target" body).getD
      (refusal invalidField "malformed" "the attach's target is not a valid terminus"))
  let senderSettle :=
    (fieldValue "attach" "snd-settle-mode" body).bind valueNat ==
      ((choiceValue? "sender-settle-mode" "settled").bind String.toNat?)
  let senderUnsettled :=
    (fieldValue "attach" "snd-settle-mode" body).bind valueNat ==
      ((choiceValue? "sender-settle-mode" "unsettled").bind String.toNat?)
  let receiverSecond :=
    (fieldValue "attach" "rcv-settle-mode" body).bind valueNat ==
      ((choiceValue? "receiver-settle-mode" "second").bind String.toNat?)
  let freshPosition : Option Position :=
    match role with
    | LinkRole.sender => some ⟨initialCount, 0⟩
    | LinkRole.receiver => some ⟨0, 0⟩
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
handle it must name, the delivery-count and link-credit it must agree with, and the credit the
doc's formula moves. -/
def flowLink (session : WidenedSession) (outbound : Bool) (body : Value) :
    Except Refusal WidenedSession := do
  if !fieldSet "flow" "handle" body then
    let linkFields :=
      [("delivery-count", fieldSet "flow" "delivery-count" body),
       ("link-credit", fieldSet "flow" "link-credit" body),
       ("available", fieldSet "flow" "available" body),
       ("drain", fieldSet "flow" "drain" body),
       ("properties", fieldSet "flow" "properties" body)]
    let carried := (linkFields.filter (fun entry => entry.2)).map (fun entry => entry.1)
    refuseUnless carried.isEmpty
      (refusal invalidField "malformed" "a flow that does not set the handle MUST NOT set the link's fields")
    return session
  let handle ←
    match (fieldValue "flow" "handle" body).bind valueNat with
    | some handle => pure handle
    | none => .error (refusal invalidField "malformed" "the flow's handle field is not an integer")
  let id ←
    match resolveHandle session outbound handle with
    | some id => pure id
    | none => .error (refusal unattachedHandle "illegalState" "a flow names a handle this endpoint does not have attached")
  let link ←
    match session.links id with
    | some link => pure link
    | none => .error (refusal unattachedHandle "illegalState" "a flow names a handle this endpoint does not have attached")
  refuseUnless ((flowCountRefusal? link outbound body).isNone)
    ((flowCountRefusal? link outbound body).getD
      (refusal invalidField "malformed" "the flow's delivery-count is wrong"))
  refuseUnless ((flowCreditEchoRefusal? link outbound body).isNone)
    ((flowCreditEchoRefusal? link outbound body).getD
      (refusal invalidField "malformed" "the flow's link-credit is wrong"))
  if outbound then return session
  else
    let receivedCredit := ((fieldValue "flow" "link-credit" body).bind valueNat).getD 0
    let receivedCount := ((fieldValue "flow" "delivery-count" body).bind valueNat).getD 0
    if id.localRole == LinkRole.sender then
      let position : Option Position :=
        match link.position with
        | some current =>
          some { current with
                   credit := Position.creditFor receivedCount receivedCredit current.deliveryCount }
        | none => link.position
      return putLink session
        { link with position := position, peerCount := receivedCount, peerCredit := receivedCredit }
    else
      match link.position with
      | some current =>
        return putLink session
          { link with position := some { current with deliveryCount := receivedCount },
                      peerCredit := receivedCredit }
      | none => return session

/-- The session a flow leaves: the `next-incoming-id` rule, the link's half, and the windows a
received flow adopts. -/
def flowStep (session : WidenedSession) (outbound : Bool) (body : Value) :
    Except Refusal WidenedSession := do
  let set := fieldSet "flow" "next-incoming-id" body
  refuseUnless (set == session.legacy.peerBegun)
    (placed session.legacy outbound invalidField "malformed" "a flow's next-incoming-id must be set exactly when the partner's begin has arrived")
  let session ←
    match flowLink session outbound body with
    | .ok session => pure session
    | .error reason => .error (place session.legacy outbound reason)
  if outbound then return session
  else
    let windows :=
      session.legacy.windows.afterReceivingFlow
        (fieldNumber "flow" body "next-outgoing-id") (fieldNumber "flow" body "incoming-window")
        (fieldNumber "flow" body "outgoing-window")
        ((fieldValue "flow" "next-incoming-id" body).bind valueNat)
    return withWindows session windows

/-! ## The detach exchange -/

/-- The detach exchange: the handle rules, and the effect `link-handles` gives a detach — the handle
"remains in use until the link is detached", so a detach releases it and a later frame that names it
is refused with `unattached-handle`. A detach naming a handle this endpoint does not have is
admitted and changes nothing, which is the one frame the links section excepts from its rule about
input for a detached link endpoint. -/
def detachStep (session : WidenedSession) (outbound : Bool) (body : Value) :
    Except Refusal WidenedSession := do
  let named := (fieldValue "detach" "handle" body).bind valueNat
  match named.bind (fun handle => resolveHandle session outbound handle) with
  | none => return session
  | some id =>
    match session.links id with
    | none => return session
    | some link =>
      let closed := fieldBool "detach" "closed" body
      let withError := fieldSet "detach" "error" body
      if outbound then
        let session := { session with localHandles := release session.localHandles id }
        return putLink session (linkAfterDetach link true closed withError)
      else
        let session := { session with remoteHandles := release session.remoteHandles id }
        return putLink session (linkAfterDetach link false closed withError)

/-! ## The disposition exchange -/

/-- One link's share of a disposition: **every** unsettled entry whose delivery the range covers
leaves the table, and the link's in-progress delivery is released when it is one of them. The
traversal is exact because the link carries a finite index of the tags its table holds — which is
what lets a disposition reach a delivery the link no longer holds in progress, `disposition.3`'s
case, where the link is detached but the delivery is still live and `disposition.4` still requires
the updated state to be applied. -/
def applyDisposition (session : WidenedSession) (link : WidenedLink) (first last : Nat)
    (settled : Bool) : WidenedSession :=
  if !settled then putLink session link
  else
    let cleared :=
      link.unsettledKeys.foldl
        (fun carried tag =>
          match carried.unsettled tag with
          | some entry =>
            if first ≤ entry.deliveryId && entry.deliveryId ≤ last then clearEntry carried tag
            else carried
          | none => carried)
        link
    match cleared.delivery with
    | some delivery =>
      if first ≤ delivery.id && delivery.id ≤ last then
        putLink session { cleared with delivery := none, deliveryTag := none, deliveryFormat := none }
      else putLink session cleared
    | none => putLink session cleared

/-- The disposition exchange: `disposition.1`/`.2`'s directionality, the range `first`/`last` name,
and the settlement a disposition carries. A disposition declares no `handle` field, so the link it
is about is resolved through the registry's index: every registered link whose local role the
frame's `role` names, including links that are no longer attached, which is what `disposition.3`
permits and `disposition.4` then requires the state of. -/
def dispositionStep (session : WidenedSession) (outbound : Bool) (body : Value) :
    Except Refusal WidenedSession := do
  let role ←
    match (fieldValue "disposition" "role" body).bind LinkRole.ofValue with
    | some role => pure role
    | none => .error (refusal invalidField "malformed" "the disposition must carry a role, and it must be one of the values the declared role type names")
  let first ←
    match (fieldValue "disposition" "first" body).bind valueNat with
    | some first => pure first
    | none => pure 0
  let last ←
    match (fieldValue "disposition" "last" body).bind valueNat with
    | some last => pure last
    | none => pure first
  refuseUnless (first ≤ last)
    (refusal invalidField "malformed" "the disposition's range runs from a delivery to one before it, which is not a range")
  let targets :=
    (session.linkKeys.filter (fun id => id.localRole == role)).filterMap
      (fun id => (session.links id).map (fun link => (id, link)))
  refuseUnless (!targets.isEmpty)
    (refusal invalidField "malformed" "the disposition names the deliveries of a role this session has no link of")
  let settled := fieldBool "disposition" "settled" body
  let session := targets.foldl (fun session target => applyDisposition session target.2 first last settled) session
  let session ← targets.foldlM (fun session target =>
    match session.links target.1 with
    | some link =>
      match linkStepTransactionState link outbound body with
      | .ok link => pure (putLink session link)
      | .error reason => .error reason
    | none => pure session) session
  return session

/-! ## The transfer exchange -/

/-- The transfer exchange, widened: the frame's own fields, the credit it spends, the delivery it
carries, and the four rules the widening adds —

* `links.23`: a delivery-tag is unique among the deliveries either end could still consider
  unsettled, so a tag already holding a *different* delivery is refused while the same tag and the
  same id is a retransfer of one delivery;
* `transfer/field:resume.2`: the sender MUST NOT send a resumed transfer for a delivery not in its
  local unsettled map;
* `transfer/field:resume.1`: the receiver of one MUST ignore it, which is the one place a step
  admits a frame and records nothing of it. What is ignored is the *delivery*: the session-scope
  window accounting in `transferStep` still happens, because the frame arrived and the session's
  windows are the session machine's business rather than the link's;
* `transfer/field:resume.3`: the resume flag is the *first* transfer's claim, so a continuation
  carrying it for a delivery that did not begin that way is refused.

The incomplete-map latch is read here too: an endpoint that announced an incomplete unsettled map
may not be offered a new delivery (`incomplete-unsettled.1`/`.2`), and an endpoint that sent one must
answer a transfer without the resume flag (`incomplete-unsettled.1`'s receiving half). -/
def transferLink (session : WidenedSession) (outbound : Bool) (body : Value) :
    Except Refusal WidenedSession := do
  let handle ←
    match (fieldValue "transfer" "handle" body).bind valueNat with
    | some handle => pure handle
    | none => .error (refusal invalidField "malformed" "the transfer must carry an integer handle")
  let id ←
    match resolveHandle session outbound handle with
    | some id => pure id
    | none => .error (refusal unattachedHandle "illegalState" "a transfer names a handle this endpoint does not have attached")
  let link ←
    match session.links id with
    | some link => pure link
    | none => .error (refusal unattachedHandle "illegalState" "a transfer names a handle this endpoint does not have attached")
  let sender := id.localRole == LinkRole.sender
  refuseUnless (outbound == sender)
    (refusal illegalStateCondition "illegalState" "a transfer is the sender's frame, and this endpoint attached as the other role")
  let continued := link.delivery.isSome
  let carriedId := (fieldValue "transfer" "delivery-id" body).bind valueNat
  let carriedTag := (fieldValue "transfer" "delivery-tag" body).bind valueOctets
  let carriedFormat := (fieldValue "transfer" "message-format" body).bind valueNat
  refuseUnless (deliveryTagInBounds body)
    (refusal invalidField "malformed" "the transfer's delivery-tag carries more than the 32 octets of binary data the type allows")
  let deliveryId ←
    match carriedId with
    | some carried => pure carried
    | none =>
      match link.delivery with
      | some delivery => pure delivery.id
      | none => .error (refusal invalidField "malformed" "the first transfer of a delivery MUST carry its delivery-id")
  refuseUnless (continued || (fieldSet "transfer" "delivery-tag" body && fieldSet "transfer" "message-format" body))
    (refusal invalidField "malformed" "a first transfer MUST carry its delivery-tag and message-format, which only a continuation transfer may omit")
  let tag : Option DeliveryTag := if continued then link.deliveryTag else carriedTag.map ByteArray.mk
  let resume := fieldBool "transfer" "resume" body
  let held := tag.map (fun key => resumable link key)
  if resume && held == some false && outbound then
    refuseUnless false
      (refusal invalidField "malformed" "the sender MUST NOT send resumed transfers for deliveries not in its local unsettled map")
  if resume && held == some false && !outbound then
    return session
  if resume && continued then
    refuseUnless (link.delivery.map (fun delivery => delivery.resumed) == some true)
      (refusal invalidField "malformed" "a resumed delivery spans more than one transfer performative, so the resume flag MUST be set on the first transfer of the delivery")
  if outbound && !continued && !resume then
    refuseUnless (!link.remoteEndpoint.incompleteUnsettled)
      (refusal illegalStateCondition "illegalState" "an incomplete unsettled map was received for this link, so this endpoint MUST NOT send a new delivery until it is complete")
  if !outbound && !resume then
    refuseUnless (!link.localEndpoint.incompleteUnsettled)
      (refusal illegalStateCondition "illegalState" "this endpoint sent an incomplete unsettled map, so it MUST detach with an error on a transfer that does not set the resume flag")
  if continued then
    refuseUnless (carriedId.isNone || link.delivery.map (fun held => held.id) == carriedId)
      (refusal invalidField "malformed" "the delivery-id of a continuation transfer differs from the delivery-id of the delivery it continues, which is an error")
    refuseUnless (carriedTag.isNone || carriedTag == link.deliveryTag.map (fun tag => tag.data))
      (refusal invalidField "malformed" "the delivery-tag of a continuation transfer differs from the delivery-tag of the delivery it continues, which is an error")
    refuseUnless (carriedFormat.isNone || carriedFormat == link.deliveryFormat)
      (refusal invalidField "malformed" "the message-format of a continuation transfer differs from the message-format of the delivery it continues, which is an error")
  let settled := fieldBool "transfer" "settled" body
  let aborted := fieldBool "transfer" "aborted" body
  let more := !aborted && fieldBool "transfer" "more" body
  let delivery : Except Refusal (Option WidenedDelivery) :=
    if aborted then pure none
    else if more then pure (some (deliveryStep link.delivery deliveryId settled resume))
    else
      let completed := deliveryStep link.delivery deliveryId settled resume
      if link.senderSettleMode && !completed.settled then
        .error (refusal invalidField "malformed" "the negotiated settlement mode is the settled choice of sender-settle-mode, so a delivery MUST be settled in at least one of its transfers")
      else pure none
  let delivery ← delivery
  let tagOut : Option DeliveryTag :=
    if delivery.isSome then (if continued then link.deliveryTag else carriedTag.map ByteArray.mk)
    else none
  let formatOut : Option Nat :=
    if delivery.isSome then (if continued then link.deliveryFormat else carriedFormat) else none
  let starting := !continued
  if sender && starting then
    match link.position with
    | some current =>
      refuseUnless (current.credit > 0)
        (refusal framingError "limit" "the link has no credit left: the sender's delivery-count has reached the delivery-limit the receiver granted")
    | none => pure ()
  -- `links.23`, after the flow-control gate: a link with no credit left cannot send the delivery at
  -- all, and the corpus pins the credit's condition for exactly that frame, so the tag's own rule is
  -- read where the frame is one the link may send
  if !continued then
    match tag with
    | some key =>
      match link.unsettled key with
      | some held =>
        refuseUnless (held.deliveryId == deliveryId)
          (refusal invalidField "malformed" "the delivery-tag is already held by another delivery, and a tag is unique among the deliveries either end could still consider unsettled")
      | none => pure ()
    | none => pure ()
  let position : Option Position :=
    match link.position with
    | some current =>
      some { current with
               credit := if sender && starting then current.credit - 1 else current.credit,
               deliveryCount := if starting then current.deliveryCount + 1
                                else current.deliveryCount }
    | none => link.position
  let recorded :=
    match tag with
    | none => link
    | some key =>
      if settled || aborted then clearEntry link key
      else
        setEntry link key
          { deliveryId := deliveryId,
            localState := (link.unsettled key).bind (fun held => held.localState),
            remoteState := (link.unsettled key).bind (fun held => held.remoteState) }
  let nextDeliveryId := if outbound && starting then deliveryId + 1 else link.nextDeliveryId
  return putLink session
    (linkAfterTransfer recorded position delivery tagOut formatOut nextDeliveryId)

/-- The session a transfer leaves, with the session-scope rules the legacy reading places around it:
the two windows a sent transfer is charged against, the settlement the transfer's own fields carry,
and the window the frame leaves. -/
def transferStep (session : WidenedSession) (outbound : Bool) (body : Value) (payload : Octets) :
    Except Refusal WidenedSession := do
  let handle := (fieldValue "transfer" "handle" body).bind valueNat
  let link? := handle.bind (fun h => (resolveHandle session outbound h).bind (fun id => session.links id))
  let settled :=
    ((fieldValue "transfer" "settled" body).bind valueBool).getD
      ((link?.bind (fun link => link.delivery.map (fun delivery => delivery.settled))).getD false)
  let aborted := fieldBool "transfer" "aborted" body
  match link? with
  | some link =>
    match rcvSettleRefusal? link body settled with
    | some reason => .error (place session.legacy outbound reason)
    | none =>
      match unsettledSettleRefusal? link settled aborted with
      | some reason => .error (place session.legacy outbound reason)
      | none => pure ()
  | none => pure ()
  if outbound then
    refuseUnless (session.legacy.windows.outgoingWindow > 0)
      (placed session.legacy outbound windowViolation "limit" "this session's outgoing window is exhausted, so it may not send another transfer")
    refuseUnless (session.legacy.windows.remoteIncomingWindow > 0)
      (placed session.legacy outbound windowViolation "limit" "the partner's incoming window is exhausted, so it can accept no further transfers")
    let session ←
      match transferLink session outbound body with
      | .ok session => pure session
      | .error reason => .error (place session.legacy outbound reason)
    let session ←
      match handle.bind (fun h => (resolveHandle session outbound h).bind (fun id => session.links id)) with
      | some link =>
        match linkStepTransactionPayload link outbound payload settled with
        | .ok link => pure (putLink session link)
        | .error reason => .error (place session.legacy outbound reason)
      | none => pure session
    return withWindows session (session.legacy.windows.afterSendingTransfer startPolicy)
  else
    refuseUnless (session.legacy.windows.incomingWindow > 0)
      (placed session.legacy outbound windowViolation "limit" "this session's incoming window is exhausted, so it cannot receive another transfer")
    let session ←
      match transferLink session outbound body with
      | .ok session => pure session
      | .error reason => .error (place session.legacy outbound reason)
    let session ←
      match handle.bind (fun h => (resolveHandle session outbound h).bind (fun id => session.links id)) with
      | some link =>
        match linkStepTransactionPayload link outbound payload settled with
        | .ok link => pure (putLink session link)
        | .error reason => .error (place session.legacy outbound reason)
      | none => pure session
    return withWindows session (session.legacy.windows.afterReceivingTransfer session.legacy.windows.nextIncomingId startPolicy)

/-! ## The carriers of the ten clauses no corpus step can pin

Ten of §24's 26 clauses need a carrier that is not a vector: they require the endpoint to *emit* a
frame with a chosen content, to hold a comparison nothing reads, or to restrain a send the corpus
cannot ask for. Each declaration below is where that clause's meaning is written down, so the
obligations in `Proofs/WidenedClauses.lean` are stated over the step's own vocabulary rather than
over a paraphrase of it.

Which of them the step actually *reads* is part of the record, not an accident:

* `resumable` is read by `transferLink` in both directions (`resume.1`'s ignore, `resume.2`'s
  refusal), so the three `resuming-deliveries` clauses that are about which end holds a delivery are
  carried by the rule itself.
* `deliveryStep` is what records the resume claim, so `resuming-deliveries.8`'s state facet — that no
  continuation can make or unmake the claim — is a property of the step's own construction.
* `resolve`, `absentDeliveryState` and `reduce` are *not* read by any step, and that is the finding
  the corpus already records: a held comparison, an absence that is not evidence, and a reduction
  nothing triggers until an endpoint acts on it. They are declared here so the clauses have one place
  to be stated, and the theorem module says for each what it does and does not establish.

**Two of the ten are not carried at all, and are named here rather than shadowed.** `links.2`'s
second half ("the first attach MUST then be closed with a link error of «stolen»") and
`closing-a-link.2` ("the partner MUST signal that it has closed the link by reattaching and then
sending a closing detach") each oblige an endpoint to *emit* a frame with a chosen content. This
module's step has no output result — `step : WidenedSession → Bool → Nat → Value → Octets →
Except Refusal WidenedSession` — so nothing declared here can be a carrier for either: a refusal value
with the condition such a frame would name is not the frame, and stating one would be counting a
content shadow as the clause's carrier. The two stay unresolved obligations of the model's output
alphabet, which is what `PLAN.md` §24 part 4 item 3 says they are, and no theorem in
`Proofs/WidenedClauses.lean` claims them. -/

/-- The two observations `attach/field:unsettled.1` makes an endpoint compare for an in-doubt
delivery: the local and remote states it holds, or the fact that they differ. -/
inductive Doubt where
  /-- The two endpoint states are the same, and this is the state they agree on. -/
  | agreed (state : Option Message.DeliveryState)
  /-- The two endpoint states differ: the delivery is in doubt. -/
  | disputed
deriving Repr

/-- Whether two delivery states are the same, read through the state's own name. The delivery-state
type carries no decidable equality of its own — it holds an outcome record and a transaction-layer
state recorded unmodelled — and the corpus's vocabulary for a state *is* its name, which is what
`DeliveryState.name` gives. So the comparison `unsettled.1` asks for is decidable here without
being a second notion of state identity. -/
def sameState (left right : Option Message.DeliveryState) : Bool :=
  match left, right with
  | none, none => true
  | some left, some right => left.name == right.name
  | _, _ => false

/-- The comparison `attach/field:unsettled.1` asks for, over the one shared table: `none` for a tag
the link does not hold, the agreed state where the two observations agree, and `disputed` where they
differ. A function rather than a rule because the clause obliges the endpoints to compare, not to act
on a particular outcome. -/
def resolve (link : WidenedLink) (tag : DeliveryTag) : Option Doubt :=
  match link.unsettled tag with
  | none => none
  | some entry =>
    if sameState entry.localState entry.remoteState then some (.agreed entry.localState)
    else some .disputed

/-- The state a delivery's absence from the table may be read as: `none`, whether or not an
incomplete map was announced. This is `attach/field:incomplete-unsettled.u1`'s sentence as a
definition rather than as a default — there is no branch anywhere in the widened step that returns a
terminal state for an absent tag. -/
def absentDeliveryState (link : WidenedLink) (tag : DeliveryTag) :
    Option Message.DeliveryState :=
  match link.unsettled tag with
  | some entry => entry.localState
  | none => none

/-- The link after the two ends have reduced their unsettled state as far as they can and suspended:
each endpoint's incomplete-map latch is cleared and both lives are `suspended`, which is the state a
resume re-attempts from (`links/doc:resuming-deliveries.6`/`.7`). -/
def reduce (link : WidenedLink) : WidenedLink :=
  { link with
      localEndpoint := { link.localEndpoint with life := .suspended, incompleteUnsettled := false },
      remoteEndpoint := { link.remoteEndpoint with life := .suspended, incompleteUnsettled := false } }

/-! ## The step -/

/-- **The widened session's step**: one frame, one direction, and the session it leaves. The
prologue is `Spec.Session`'s own (`frameDiscarded`, `gate`), because it is the same machine; what
follows is the link layer over the widened state. A frame this layer does not answer for is carried
rather than judged, as in the restricted step. -/
def step (session : WidenedSession) (outbound : Bool) (channel : Nat) (body : Value)
    (payload : Octets) : Except Refusal WidenedSession := do
  if frameDiscarded session.legacy outbound body then
    return session
  let _ ← gate session.legacy outbound channel body
  match Performative.ofBody body with
  | .begin =>
    let legacy ← stepBegin session.legacy outbound channel body
    return { session with legacy }
  | .end => return { session with legacy := Session.afterEnd session.legacy outbound (fieldSet "end" "error" body) }
  | .attach =>
    match attachStep session outbound body with
    | .ok session => pure session
    | .error reason => .error (place session.legacy outbound reason)
  | .detach =>
    match detachStep session outbound body with
    | .ok session => pure session
    | .error reason => .error (place session.legacy outbound reason)
  | .flow => flowStep session outbound body
  | .transfer => transferStep session outbound body payload
  | .other =>
    if isDisposition body then
      match dispositionStep session outbound body with
      | .ok session => pure session
      | .error reason => .error (place session.legacy outbound reason)
    else return session

end SpecAMQP.Spec.Protocol
