import Spec.Session

/-!
# Dependency-neutral widened protocol state

This module freezes the widening's declaration-only state below `Contracts`, `Harness`, and `Impl`.
Executable steps over it live in `Spec.Protocol`; this file contains only state, identities, and
invariants. The placement keeps the handwritten specification independent of every consumer while
allowing the shipped core and the conformance contract to name exactly the same protocol state.

A logical link has two endpoint-local handle spaces. Both endpoints may use the same numeric handle,
and either may detach and later resume on a different one while the other handle remains mapped. The
stable registry is consequently keyed by link identity, while two directional maps resolve handles
to that identity. One logical-link record owns the shared unsettled history so the two handle spaces
cannot drift into two accounts of the same deliveries.
-/

namespace SpecAMQP.Spec

/-- A delivery tag is the binary key the link uses for unsettled delivery state. It has no null
constructor; null-key exclusion is therefore a property of the representation. -/
abbrev DeliveryTag := ByteArray

/-- The two observations that must be compared when a delivery is in doubt, plus the sender's id for
that delivery. One state would make the comparison obligation unstateable. -/
structure UnsettledDelivery where
  deliveryId : Nat
  localState : Option SpecAMQP.Spec.Message.DeliveryState
  remoteState : Option SpecAMQP.Spec.Message.DeliveryState

/-- A delivery currently crossing the link. `resumed` records whether its first transfer carried
the resume flag; a continuation that first claims resumption is observably different from a
continuation of a delivery whose first transfer already made that claim. -/
structure WidenedDelivery where
  id : Nat
  settled : Bool
  resumed : Bool
deriving Repr, BEq, DecidableEq

/-- A stable link identity: names are unique only among links of the same local direction. -/
structure LinkId where
  name : String
  localRole : SpecAMQP.Spec.Session.LinkRole
deriving Repr, BEq, DecidableEq

/-- The four lives distinguished by the attach rules. A detached endpoint remains a link endpoint;
a suspended or destroyed endpoint can only be restored by resume. -/
inductive LinkLife where
  | attached
  | detached
  | suspended
  | destroyed
deriving Repr, BEq, DecidableEq

/-- State belonging to one end of a logical link. `incompleteUnsettled` records that this endpoint's
last attach announced an incomplete unsettled map; the opposite endpoint reads that latch when it
considers a new or resumed delivery. Handles are deliberately absent and live in the directional
maps on `WidenedSession`. -/
structure WidenedLinkEndpoint where
  terminusAssociated : Bool
  life : LinkLife
  incompleteUnsettled : Bool

/-- One logical link. Local and remote endpoint lives are independent, but flow control, settlement
negotiation, the in-progress delivery, transaction-control state, and unsettled history belong to
the logical link rather than the session. The one unsettled table is shared: two records here would
permit the two handle spaces to disagree about one delivery. -/
structure WidenedLink where
  id : LinkId
  localEndpoint : WidenedLinkEndpoint
  remoteEndpoint : WidenedLinkEndpoint
  position : Option SpecAMQP.Spec.Session.Position
  peerCount : Nat
  peerCredit : Nat
  senderSettleMode : Bool
  senderSettleUnsettled : Bool
  receiverSettleSecond : Bool
  delivery : Option WidenedDelivery
  deliveryTag : Option DeliveryTag
  deliveryFormat : Option Nat
  transactions : Option SpecAMQP.Spec.Transactions.Layer
  unsettled : DeliveryTag → Option UnsettledDelivery
  nextDeliveryId : Nat

/-- A session with a stable link registry, its finite traversal index, and one handle map for each
endpoint's independent handle space. `legacy` retains the old restricted model for its frozen
contracts. The widened path uses its session-scope state but neither reads nor synchronizes its
single-link fields; `links` is the only live link-state representation. `linkKeys` makes that
functional registry walkable for handle-less session operations such as `disposition`; it carries
no state of its own and its order is not observable. -/
structure WidenedSession where
  legacy : SpecAMQP.Spec.Session.Session
  links : LinkId → Option WidenedLink
  linkKeys : List LinkId
  localHandles : Nat → Option LinkId
  remoteHandles : Nat → Option LinkId

/-- The registry key is the link record's identity. Because `LinkId` contains name and local role,
one function slot is the only place a link of that name and direction can exist. -/
def LinkNamesUnique (session : WidenedSession) : Prop :=
  ∀ (id : LinkId) (link : WidenedLink), session.links id = some link → link.id = id

/-- The finite key index contains each and only each occupied registry key, exactly once. This
licenses a session-scope operation to traverse a functional registry without making the index a
second source of link state. -/
def RegistryKeysComplete (session : WidenedSession) : Prop :=
  session.linkKeys.Nodup ∧
    ∀ id, id ∈ session.linkKeys ↔ ∃ link, session.links id = some link

/-- A mapped handle resolves to an attached endpoint; every attached endpoint has a handle in its
own directional space; and one endpoint cannot retain both its old and resumed handles. This
prevents stale handles, ghost attached endpoints, and duplicate directional bindings while still
allowing either endpoint to detach and resume on a new numeric handle independently. -/
def HandlesResolveLinks (session : WidenedSession) : Prop :=
  (∀ (handle : Nat) (id : LinkId), session.localHandles handle = some id →
    ∃ link, session.links id = some link ∧ link.localEndpoint.life = .attached) ∧
  (∀ (handle : Nat) (id : LinkId), session.remoteHandles handle = some id →
    ∃ link, session.links id = some link ∧ link.remoteEndpoint.life = .attached) ∧
  (∀ (id : LinkId) (link : WidenedLink), session.links id = some link →
    link.localEndpoint.life = .attached → ∃ handle, session.localHandles handle = some id) ∧
  (∀ (id : LinkId) (link : WidenedLink), session.links id = some link →
    link.remoteEndpoint.life = .attached → ∃ handle, session.remoteHandles handle = some id) ∧
  (∀ (leftHandle rightHandle : Nat) (id : LinkId),
    session.localHandles leftHandle = some id →
    session.localHandles rightHandle = some id → leftHandle = rightHandle) ∧
  (∀ (leftHandle rightHandle : Nat) (id : LinkId),
    session.remoteHandles leftHandle = some id →
    session.remoteHandles rightHandle = some id → leftHandle = rightHandle)

/-- The specification-side widened endpoint state. Sessions are indexed by channel; each session
owns stable logical links and two directional handle spaces. -/
structure WidenedProtocolState where
  connection : SpecAMQP.Spec.Connection.Endpoint
  sessions : Nat → Option WidenedSession

/-- Every stored session satisfies identity, finite-registry, and handle-resolution invariants.
They are part of the widened relation rather than optional proofs about states an endpoint may
nevertheless reach. -/
def WidenedProtocolStateValid (state : WidenedProtocolState) : Prop :=
  ∀ (channel : Nat) (session : WidenedSession),
    state.sessions channel = some session →
      LinkNamesUnique session ∧ RegistryKeysComplete session ∧ HandlesResolveLinks session


end SpecAMQP.Spec
