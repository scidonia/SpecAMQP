import Contracts.EndpointConformance
import Spec.Message
import Spec.Session

/-!
# The widened endpoint conformance contract

This module is parts 1 and 2 of `PLAN.md` §24. It freezes the state added by the widening, the
shape of the widened endpoint claim, and the statement that makes the new relation an extension of
the existing endpoint relation. It deliberately contains no implementation and no proof of either
claim. The later proof and acceptance modules must import this file; this file must not import them.

`Contracts.EndpointConformance` remains unchanged. Its `EndpointConforms` statement and R3 proof
continue to say exactly what they said before this module existed. The alphabet also remains
`Contracts.Conformance.Input` and `Output`: all 26 clauses decide frames already carried by that
alphabet, and need memory rather than a new event.

## Goal

Give the 26 `deferred:S4` clauses enough state to be stated without weakening the old endpoint
contract: multiple links, link identity and lifetime, local and remote unsettled state keyed by a
non-null delivery tag, the incomplete-map latch, and the sender's delivery record.

## Non-goals

* No step function, frame parser, writer, proof, acceptance theorem, or ledger promotion lands here.
* No routing, queue, address grammar, durability, application policy, or interpretation of link
  names is introduced.
* The relation does not hard-code an implementation function: `WidenedEndpointConforms` remains
  parameterized by two endpoints. Part 4 nevertheless makes the shipped-core choice recorded below,
  and must prove that endpoint meets this frozen relation.
* The ten clauses the current harness cannot observe are not represented as pretend vectors. They
  remain proof obligations or explicitly untestable obligations in part 4.

## Affected files and symbols

Parts 1 and 2 add only this module: `WidenedLink`, `WidenedSession`,
`WidenedProtocolState`, `WidenedImplementationState`, `WidenedEndpointRelation`,
`WidenedEndpointConforms`, and `WideningProjectsEndpointRelation`.

Part 3 moved the eleven scenarios into `scripts/gen-exchange-vectors.py` and its committed
`vectors/generated-exchanges.ndjson` output, then regenerated the planner manifest. The existing
`tests/contracts/s3_exchanges.sh` remains the boundary; no parallel runner was added.

Part 4 changes the session state and dispatch in `Spec.Session` and `Ref.Session`, their session
codecs where the attach and transfer fields enter, and adds proof and acceptance modules for the
two statements below. The selected one-core implementation target also changes `Impl.Core`; its
cutover obligations are recorded at the end.
`ledger/dispositions/part2-links.json`, `part2-performatives-link-state.json`, and
`unkeyed-normative.json`, plus generated coverage and the planner manifest, move only after their
carriers exist.

## The eight behaviours and their carriers

The ledger, not this summary, is authoritative for the text and hashes. The shorthand below is the
ledger anchor suffix. The 26 entries are partitioned once, with no duplicate counting:

1. **A link is named and identified** — `links.1`, `links.5`. Carried by `WidenedLink.name`,
   `WidenedLink.role`, `WidenedLink.terminusAssociated`, the multi-link table, and
   `LinkNamesUnique`.
2. **Detach, re-attach, and resume differ** — `links.2`, `.16`, `.17`, `.18`, and
   `closing-a-link.2`. Carried by identity plus `LinkLife`; the two MUST-emit rules are among the
   unpinnable ten below.
3. **The attach carries unsettled state** — `incomplete-unsettled.u1`, `unsettled.1`, `.5`, `.6`.
   Carried by `UnsettledDelivery` and `WidenedLink.unsettled`. A `DeliveryTag` is binary rather than
   optional, so a null key is unrepresentable; local and remote states are both retained so their
   comparison is stateable.
4. **An incomplete map latches the sender** — `incomplete-unsettled.1`, `.2`, `.3`. Carried by
   `WidenedLink.incompleteUnsettled`; the latch remains set until the detach and complete re-attach
   sequence lifts it.
5. **A delivery resumes** — `resuming-deliveries.2`, `.3`, `.4`, `.5`, `.8`, and
   `transfer/field:resume.1`, `.2`, `.3`. Carried by the unsettled table, each entry's
   `deliveryId`, and `nextDeliveryId`.
6. **Both ends reduce unsettled state** — `resuming-deliveries.6`, `.7`. The two endpoint states
   in each unsettled entry make the reduction stateable; both clauses are unpinnable at the current
   harness boundary.
7. **A delivery tag is unique while either end may consider it unsettled** — `links.23`. The
   function keyed by `DeliveryTag` makes this structural: one key denotes at most one entry.
8. **Settlement survives while its link does** — `disposition.4`. The unsettled entry is owned by
   a `WidenedLink`, and `LinkLife` states when that owner still exists.

The ten entries no corpus step can pin are: `links.2`, `closing-a-link.2`,
`incomplete-unsettled.u1`, `unsettled.1`, and `resuming-deliveries.3`, `.4`, `.5`, `.6`, `.7`,
`.8`. They require a chosen emission, a MUST-send, a restraint on sending, or an internal
comparison. Their nearest observable shadows are recorded in the vector plan below, but a shadow
is not a carrier for the clause itself.

## Part 3 plan: harness-boundary scenarios, failure first

The actor is the operator replaying the exchange corpus through `amqp-spec` and `amqp-ref`. The
boundary action is one corpus replay; the observable is each step's admitted/refused verdict,
condition, reason class, and resulting session state. No scenario calls a network, clock, model, or
filesystem outside the gate's temporary directory.

Promotion is complete: the exchange-vector generator carries the eleven authored inputs in
`vectors/generated-exchanges.ndjson`, with no second corpus convention. Before either model changed,
both artefacts were observed admitting every step whose expectation requires refusal; that named
assertion mismatch is retained as the failure-first evidence for each scenario:

| scenario | clauses pinned | expected pre-implementation failure |
|---|---|---|
| `staged-link-resume-sent-not-in-map` | `resume.2` | final send is admitted, not refused as malformed |
| `staged-link-resume-only-on-continuation` | `resume.3` | final receive is admitted, not refused as malformed |
| `staged-link-attach-unsettled-null-key` | `unsettled.5` | attach is admitted, not refused as malformed |
| `staged-link-second-attach-same-name` | `links.1`, `links.5` | second attach is admitted, not refused for the missing required state |
| `staged-link-pipelined-reattach` | `links.16`–`.18` | attach is admitted, not refused with the errant-link session condition |
| `staged-link-reattach-with-unsettled-map` | `unsettled.6` | re-attach is admitted, not refused as malformed |
| `staged-link-incomplete-map-latch` | `incomplete-unsettled.1`–`.3` | new delivery is admitted while the latch should refuse it |
| `staged-link-incomplete-map-receipt` | `incomplete-unsettled.1`, `.2`, `resume.1` | non-resumed receive is admitted, not refused as illegal state |
| `staged-link-resume-not-in-receiver-map` | `resume.1`, `resuming-deliveries.2` | the follow-up continuation is admitted, showing the resumed delivery was not ignored |
| `staged-link-duplicate-delivery-tag` | `links.23` | reused unsettled tag is admitted, not refused as malformed |
| `staged-disposition-after-detach` | `disposition.4` | the settled delivery can be resumed, so the final send is admitted rather than refused |

These eleven scenarios pin sixteen of the 26 clauses. Their notes name the nearest shadow for each
of the unpinnable ten and say that it is not coverage. The planner-authored expected verdicts were
present before either model changed; replay then produced the named assertion mismatches above.
Part 4 must satisfy those verdicts rather than changing them.

## Part 4 plan: a new implementation rung

1. Add the widened link/session state to both independent readings and to the existing
   `Impl.Core.State`, preserving the old state through explicit projections. Use one lookup/update
   convention in each tree. The old single-link fields leave `Impl.Core.State` as sources of truth
   at cutover; they are not retained and updated alongside the widened representation.
2. Implement the eight behaviours in dependency order: identity and lifetime; unsettled decoding
   and structural invariants; incomplete-map latch; resume checks; joint reduction; tag uniqueness;
   disposition lifetime. Keep the three §24 readings: field-rule failures are malformed,
   forbidden-moment failures are illegal-state, and the pipelined re-attach uses the artifact's
   errant-link session condition.
3. After each behaviour, rerun only its new scenario(s), recording the expected failure before and
   the passing observation after. For each of the unpinnable ten, add a theorem or place it on the
   interface's explicit untestable-obligation list; never count a shadow vector as its carrier.
4. Prove `WideningProjectsEndpointRelation` at exactly the type frozen below, then prove the widened
   `ConformsVia` instance for the existing `Impl.Core` endpoint. Add proof and acceptance modules
   rather than editing R3 or `Contracts.EndpointConformance`, and keep the original
   `EndpointConforms` statement proved at its own frozen type rather than merely recoverable through
   the projection.
5. Update all 26 ledger dispositions only when their carriers exist, classifying each as checked,
   structural, or still deferred. Regenerate the generated corpus, coverage, and
   `toolchain/spec-manifest.sha1` in the same accepted movement.
6. Acceptance is: all eleven scenarios pass in both artefacts with pinned conditions/classes; the
   widened acceptance module binds the existing `Impl.Core` endpoint; the projection and widened
   conformance statements are accepted at their frozen types; `EndpointConforms` remains proved at
   its unchanged type; the old R3 and R4 contracts stay green; package build, proof-integrity,
   ledger, generator-fidelity, citation, manifest, exchange, and wire-differential gates pass in the
   pinned shell with `LAKE_NO_CACHE=1`.

## Constraints and resolved decisions

* `EndpointConformance.lean` is extended only by importing it here; it is not edited.
* `Input` and `Output` are unchanged. The widening is state-only.
* A link name is an uninterpreted `String` and identity is name plus role.
* An unsettled entry stores both endpoint states and the sender's delivery id. The table key is a
  non-null binary delivery tag; key uniqueness and the null-key prohibition are structural.
* Link lifetime is explicit rather than inferred from handle presence, because attached, detached,
  suspended, and destroyed have different attach rules.
* The widened implementation relation ignores the stream inbox exactly as the old endpoint relation
  does.
* No compatibility alias, replacement of R3, descriptor literal, trusted declaration, or executable
  placeholder is permitted.

## Implementation target decision for part 4

There is one shipped core. Part 4 widens `Impl.Core.State` in place, proves
`WidenedEndpointConforms` for the existing `Impl.Core` endpoint, and uses
`WideningProjectsEndpointRelation` to preserve the old R3 claim.

A second implementation was considered and refused. It would isolate the current core, but would
leave two shipped-state shapes to keep in step — drift the differential could measure only after it
occurred rather than a single representation preventing it.

The choice creates two acceptance obligations. First, the statement in
`Contracts.EndpointConformance` remains proved at its own frozen type after cutover; being merely
recoverable through the projection is not enough. Second, the legacy single-link fields leave
`Impl.Core.State` as sources of truth rather than being updated beside the widened fields.

The ten clauses the harness cannot pin remain theorem obligations or entries on the explicit
untestable-obligation list. Their nearest shadow vectors remain useful evidence, but are never
coverage for those clauses.
-/

namespace SpecAMQP.Contracts

/-- A delivery tag is the binary key the link uses for unsettled delivery state. It has no null
constructor; null-key exclusion is therefore a property of the representation. -/
abbrev DeliveryTag := ByteArray

/-- The two observations that must be compared when a delivery is in doubt, plus the sender's id for
that delivery. One state would make `unsettled.1` unstateable. -/
structure UnsettledDelivery where
  deliveryId : Nat
  localState : Option SpecAMQP.Spec.Message.DeliveryState
  remoteState : Option SpecAMQP.Spec.Message.DeliveryState

/-- The four lives distinguished by the attach rules. A detached endpoint remains a link endpoint;
a suspended or destroyed endpoint can only be restored by resume. -/
inductive LinkLife where
  | attached
  | detached
  | suspended
  | destroyed

/-- The per-link state read by the 26 clauses, and no application or node state. -/
structure WidenedLink where
  name : String
  role : SpecAMQP.Spec.Session.LinkRole
  terminusAssociated : Bool
  life : LinkLife
  unsettled : DeliveryTag → Option UnsettledDelivery
  incompleteUnsettled : Bool
  nextDeliveryId : Nat

/-- A session with a handle-indexed table capable of holding more than one link. `legacy` is the old
session projection during cutover; part 4 removes its single-link fields as sources of truth rather
than updating two representations independently. -/
structure WidenedSession where
  legacy : SpecAMQP.Spec.Session.Session
  links : Nat → Option WidenedLink

/-- Link names identify at most one link of the same role. A resumed link may move to a new handle,
but a valid state cannot retain both the old and new handle entries. -/
def LinkNamesUnique (session : WidenedSession) : Prop :=
  ∀ (leftHandle rightHandle : Nat) (leftLink rightLink : WidenedLink),
    session.links leftHandle = some leftLink →
    session.links rightHandle = some rightLink →
    leftLink.role = rightLink.role →
    leftLink.name = rightLink.name →
    leftHandle = rightHandle

/-- The specification-side widened endpoint state. Sessions are indexed by channel; each session's
link table is independently indexed by handle. -/
structure WidenedProtocolState where
  connection : SpecAMQP.Spec.Connection.Endpoint
  sessions : Nat → Option WidenedSession

/-- Every stored session satisfies the link-name identity invariant. This is part of the widened
relation rather than an optional proof about a state the endpoint may nevertheless reach. -/
def WidenedProtocolStateValid (state : WidenedProtocolState) : Prop :=
  ∀ (channel : Nat) (session : WidenedSession),
    state.sessions channel = some session → LinkNamesUnique session

/-- The implementation-side shape mirrors `Impl.Core.State`: protocol state plus pending stream
input. The conformance relation intentionally ignores `inbox`. -/
structure WidenedImplementationState where
  protocol : WidenedProtocolState
  inbox : SpecAMQP.Harness.Octets

/-- The widened relation, in the same shape as the old relation `fun s i => i.conn = s`: the
implementation's protocol field is exactly the specification state, buffering is outside the
protocol step, and the link-name identity invariant holds in every related state. -/
def WidenedEndpointRelation
    (specification : WidenedProtocolState) (implementation : WidenedImplementationState) : Prop :=
  implementation.protocol = specification ∧ WidenedProtocolStateValid specification

/-- **The widened endpoint conforms.** This is the part-1 statement. A later acceptance module binds
its arguments to the selected specification and implementation endpoints and applies the proof at
exactly this type. -/
def WidenedEndpointConforms
    (specification : Endpoint WidenedProtocolState)
    (implementation : Endpoint WidenedImplementationState) : Prop :=
  ConformsVia WidenedEndpointRelation specification implementation

/-- Project widened specification state onto the state named by the frozen endpoint contract. -/
def projectSpecification (state : WidenedProtocolState) : SpecAMQP.Spec.Connection.Endpoint :=
  state.connection

/-- Project widened implementation state onto the state named by the frozen endpoint contract. -/
def projectImplementation (state : WidenedImplementationState) : SpecAMQP.Impl.Core.State :=
  { conn := state.protocol.connection, inbox := state.inbox }

/-- The fragment represented by the old endpoint rung: connection state and buffering, with no
widened session table on either side. -/
def OldEndpointFragment
    (specification : WidenedProtocolState) (implementation : WidenedImplementationState) : Prop :=
  (∀ channel, specification.sessions channel = none) ∧
    (∀ channel, implementation.protocol.sessions channel = none)

/-- **Projection theorem statement.** On the fragment the old endpoint reaches, the widened
relation agrees exactly with the old relation after projection. This proposition is frozen here;
part 4 proves it in a proof module and binds that proof in an acceptance module. -/
def WideningProjectsEndpointRelation : Prop :=
  ∀ (specification : WidenedProtocolState) (implementation : WidenedImplementationState),
    OldEndpointFragment specification implementation →
      (WidenedEndpointRelation specification implementation ↔
        (projectImplementation implementation).conn = projectSpecification specification)

end SpecAMQP.Contracts
