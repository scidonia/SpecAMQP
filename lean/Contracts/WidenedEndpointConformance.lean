import Contracts.EndpointConformance
import Spec.WidenedState

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
contract: stable logical-link identity, independent local and remote handle spaces and endpoint
lifetimes, one shared unsettled history, per-endpoint incomplete-map latches, and per-link flow,
settlement, transaction-control, and delivery state.

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

Parts 1 and 2 own a declaration module and this relation module. `Spec.WidenedState` is the
dependency-neutral state below every consumer: `LinkId`, `WidenedLinkEndpoint`, `WidenedLink`,
`WidenedSession`, `WidenedProtocolState`, `LinkNamesUnique`, `RegistryKeysComplete`, and
`HandlesResolveLinks`. This module aliases those public state names, aliases
`WidenedImplementationState` to `Impl.Core.State`, and freezes `WidenedEndpointRelation`,
`WidenedEndpointConforms`, and
`WideningProjectsEndpointRelation`.

Part 3 moved the eleven scenarios into `scripts/gen/slices.py` and its committed
`vectors/generated-exchanges.ndjson` output, then regenerated the planner manifest. The existing
`tests/contracts/s3_exchanges.sh` remains the boundary; no parallel runner was added.

Part 4 adds widened protocol dispatch in `Spec.Protocol` and `Ref.Protocol`, changes the session
codecs where the attach and transfer fields enter, and adds proof and acceptance modules for the
two statements below. The existing `Spec.Session` and `Ref.Session` link transitions remain only
the restricted model used by the frozen old contracts. The selected one-core target makes
`Impl.Core.State` exactly `WidenedImplementationState`; its cutover obligations are recorded at the
end. The 26 entries in
`ledger/dispositions/part2-links.json`, `part2-performatives-link-state.json`, and
`unkeyed-normative.json`, plus generated coverage and the planner manifest, move only after their
carriers exist.

## The eight behaviours and their carriers

The ledger, not this summary, is authoritative for the text and hashes. The shorthand below is the
ledger anchor suffix. The 26 entries are partitioned once, with no duplicate counting:

1. **A link is named and identified** — `links.1`, `links.5`. Carried structurally by `LinkId`
   (name plus local role), the stable `WidenedSession.links` registry, and its key-integrity law
   `LinkNamesUnique`. `linkKeys` is its complete, duplicate-free finite traversal index;
   `localHandles` and `remoteHandles` resolve the two independent handle spaces.
2. **Detach, re-attach, and resume differ** — `links.2`, `.16`, `.17`, `.18`, and
   `closing-a-link.2`. Carried by the local and remote `WidenedLinkEndpoint` lives plus the two
   handle maps; either endpoint can lose or change its handle while the logical link survives. The
   two MUST-emit rules are among the unpinnable ten below.
3. **The attach carries unsettled state** — `incomplete-unsettled.u1`, `unsettled.1`, `.5`, `.6`.
   Carried by `UnsettledDelivery` and the one shared `WidenedLink.unsettled` table. A `DeliveryTag`
   is binary rather than optional, so a null key is unrepresentable; local and remote states are
   retained in each entry so their comparison is stateable. There is deliberately no second table:
   the two handle spaces cannot drift into two histories the differential would never compare.
4. **An incomplete map latches the sender** — `incomplete-unsettled.1`, `.2`, `.3`. Carried
   separately on the local and remote `WidenedLinkEndpoint`; each latch remains set until that
   endpoint's detach and complete re-attach sequence lifts it.
5. **A delivery resumes** — `resuming-deliveries.2`, `.3`, `.4`, `.5`, `.8`, and
   `transfer/field:resume.1`, `.2`, `.3`. Carried by the shared unsettled table, each entry's
   `deliveryId`, `nextDeliveryId`, and the in-progress `WidenedDelivery.resumed` bit.
6. **Both ends reduce unsettled state** — `resuming-deliveries.6`, `.7`. The two endpoint states
   in each shared unsettled entry make the reduction stateable; both clauses are unpinnable at the
   current harness boundary.
7. **A delivery tag is unique while either end may consider it unsettled** — `links.23`. The one
   shared function keyed by `DeliveryTag` makes this structural: one key denotes at most one
   delivery, while retransfers carrying that delivery's same id and tag remain representable.
8. **Settlement survives while its link does** — `disposition.4`. The unsettled entry is owned by
   the stable logical-link record, and the two endpoint lives state when that owner still exists.
   Because a disposition carries a role and delivery-id range but no handle, it traverses every
   `linkKeys` entry whose `LinkId.localRole` matches, including links whose endpoint is detached.

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

The resume pair has an additional observable precondition. The conforming
`exchange-link-resume-on-first-transfer` and refusing `staged-link-resume-only-on-continuation`
first establish an ordinary unsettled delivery, destroy the peer endpoint without settling that
delivery, and resume the same logical link with the delivery in both directional unsettled maps.
Only then do they vary whether the first resumed transfer carries `resume=true`.
`staged-link-resume-not-in-receiver-map` deliberately omits that entry and remains the
counterexample: `resume.1` requires the receiver to ignore it. Before this contract correction,
payload-insensitive replay gave the conforming and absent-map scenarios identical protocol inputs
followed by opposite verdicts; that contradiction is the expected pre-correction failure, not an
implementation result to preserve.

One pre-existing positive credit scenario also needed its input corrected once tag uniqueness
became observable. `exchange-link-credit-regranted` had reused delivery zero's still-unsettled tag
for delivery one, while `staged-link-duplicate-delivery-tag` requires exactly that input to refuse.
The intervening flow grants credit but does not settle the first delivery. The credit scenario
therefore uses a distinct tag for delivery one and keeps its admitted verdict. Before that
correction, the correctly widened model refused it for `links.23`; that one-vector mismatch is the
expected pre-correction failure, not permission to weaken tag uniqueness.

The hand-authored transaction corpora had the same kind of latent one-link assumption: most vectors
used `txn-ctl` on one attach and `txn-ctrl` on its intended peer. The restricted model ignored
names; the widened registry correctly treated them as two links, so the following flow named a link
whose local endpoint had never attached. Eighteen of 36 transaction verdicts then failed per
artefact. Each mismatching structured send attach now uses the name already present in its peer's
valid encoded frame; no encoded frame bytes or length fields change. That mismatch is the expected
pre-correction failure; delivery-count remains a rule about the resolved link endpoint, not the
session.

The same transaction pass exposed one independent role error:
`txn-payload-on-a-link-that-is-not-a-control-link` attached both endpoints as receivers and then
expected this endpoint to receive a transfer. The widened direction check correctly refused it.
The peer attach is re-authored through the frame builder as the sender, with the sender's mandatory
initial delivery count; the scenario's non-control-link payload and admitted verdict are unchanged.
The pre-correction failure is the direction refusal, not permission for a link to have two
receivers.

## Part 4 plan: a new implementation rung

1. Add the dependency-neutral widened state to both independent readings and make
   `WidenedImplementationState` exactly `Impl.Core.State`. The core keeps its real `conn` and
   `inbox` fields, adds the channel-indexed sessions with an empty default for old literals, and
   exposes the computed `protocol` view the widened relation reads. Use one stable functional link
   registry, its complete duplicate-free `linkKeys` traversal index, two directional handle maps,
   and one shared unsettled history in each reading. The index carries no link state, is appended
   only on first registration, and is never removed or reordered. The old single-link fields remain
   only in the restricted legacy model that its frozen contracts quantify over. The widened codecs
   neither dispatch through nor synchronize those fields; the registry is their sole link-state
   source. With the contract written first, the old core has no widened `protocol` view; that
   unresolved exact-state binding is the expected pre-implementation failure. The coder closes it
   and must not add an adapter.
2. Implement the eight behaviours in dependency order: identity and lifetime; unsettled decoding
   and structural invariants; incomplete-map latch; resume checks; joint reduction; tag uniqueness;
   disposition lifetime. Keep the three §24 readings: field-rule failures are malformed,
   forbidden-moment failures are illegal-state, and the pipelined re-attach uses the artifact's
   errant-link session condition.
3. After each behaviour, rerun only its new scenario(s), recording the expected failure before and
   the passing observation after. Name all ten unpinnable obligations in `Proofs` and prove each
   state facet the widened model can state. A theorem about a comparison, reduction, or required
   condition is not proof that the endpoint emitted a required frame: keep every unrepresented
   action explicitly deferred, especially `links.2` and `closing-a-link.2`, whose emission is
   outside the widened protocol step's result. Never substitute a shadow vector, a tautological
   content constant, or a second untestable-obligation vocabulary for the full clause.
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
* A link identity is the uninterpreted name plus the local role. The registry key makes uniqueness
  by name and direction structural.
* Local and remote numeric handles occupy independent maps and resolve to the stable identity.
  `HandlesResolveLinks` forbids stale mappings and attached endpoints with no directional handle.
* `linkKeys` contains exactly the occupied registry keys with no duplicates. Its order has no
  protocol meaning. Handle-less disposition applies its delivery-id range to every registered link
  whose local role matches the frame role, even when that link endpoint is detached.
* One logical link owns one unsettled table. Local and remote delivery states are fields of the same
  entry, never separate histories.
* Flow control, settlement modes, transaction-control state, and the in-progress delivery are
  per-link quantities, not session-wide slots. `WidenedDelivery.resumed` records whether the first
  transfer made the resume claim.
* An unsettled entry stores both endpoint states and the sender's delivery id. The table key is a
  non-null binary delivery tag; tag uniqueness and the null-key prohibition are structural.
* Local and remote link lifetimes and incomplete-map latches are explicit, because the endpoints
  detach and resume independently.
* The widened implementation relation ignores the stream inbox exactly as the old endpoint relation
  does.
* No compatibility alias, replacement of R3, descriptor literal, trusted declaration, or executable
  placeholder is permitted.

## Implementation target decision for part 4

There is one shipped core. Part 4 makes `Impl.Core.State` exactly the dependency-neutral
`WidenedImplementationState`, proves `WidenedEndpointConforms` for the existing `Impl.Core`
endpoint, and uses `WideningProjectsEndpointRelation` to preserve the old R3 claim.

A second implementation was considered and refused. It would isolate the current core, but would
leave two shipped-state shapes to keep in step — drift the differential could measure only after it
occurred rather than a single representation preventing it.

The choice creates two acceptance obligations. First, the statement in
`Contracts.EndpointConformance` remains proved at its own frozen type after cutover; being merely
recoverable through the projection is not enough. Second, the legacy single-link fields remain
only as the state of the restricted model the old Settlement and SessionCredit contracts name.
They are neither read nor updated beside the widened registry on the shipped path.

The ten clauses the harness cannot pin remain named proof obligations. `Proofs` proves their
formalizable state facets and explicitly names every emission or action the widened protocol result
cannot represent; it does not count a required condition as the required output frame. Their nearest
shadow vectors remain useful evidence, but are never coverage or carriers for those full clauses.
-/

namespace SpecAMQP.Contracts

/-- State names are re-exported at the contract boundary without restating their representation. -/
abbrev DeliveryTag := SpecAMQP.Spec.DeliveryTag
abbrev UnsettledDelivery := SpecAMQP.Spec.UnsettledDelivery
abbrev WidenedDelivery := SpecAMQP.Spec.WidenedDelivery
abbrev LinkId := SpecAMQP.Spec.LinkId
abbrev LinkLife := SpecAMQP.Spec.LinkLife
abbrev WidenedLinkEndpoint := SpecAMQP.Spec.WidenedLinkEndpoint
abbrev WidenedLink := SpecAMQP.Spec.WidenedLink
abbrev WidenedSession := SpecAMQP.Spec.WidenedSession
abbrev LinkNamesUnique := SpecAMQP.Spec.LinkNamesUnique
abbrev RegistryKeysComplete := SpecAMQP.Spec.RegistryKeysComplete
abbrev HandlesResolveLinks := SpecAMQP.Spec.HandlesResolveLinks
abbrev WidenedProtocolState := SpecAMQP.Spec.WidenedProtocolState
abbrev WidenedProtocolStateValid := SpecAMQP.Spec.WidenedProtocolStateValid
abbrev WidenedImplementationState := SpecAMQP.Impl.Core.State


/-- The widened relation, in the same shape as the old relation `fun s i => i.conn = s`: the
implementation's protocol view is exactly the specification state, buffering is outside the
protocol step, and registry-key, finite-registry, and handle-resolution invariants hold in every
related state. -/
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
  state

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
