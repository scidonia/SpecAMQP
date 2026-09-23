import Contracts.Conformance
import Mathlib.Data.List.Basic
import Proofs.FrameConformance
import Ref.Connection
import Spec.Connection

/-!
# The connection layer's `Conforms` instance

`SpecAMQP.Contracts.Conformance` fixes what conformance means and says that the instances are between
this repository's two trees rather than against a downstream programme. `Proofs.FrameConformance` is
the frame layer's, where the subject is a codec. This module is the connection layer's, where the
subject is a *state machine*, and the two differ in three ways that matter.

## The mapping onto the interface's alphabet

`PLAN.md` §10 fixes three input channels, and the layer has something to say about each — which is
more than the frame layer did, because the frame layer had nothing behind two of them.

* **`Input.frame bytes` is the wire.** Octets arrive and the connection layer reads them:
  `Spec.Connection.step e false (.arriving bytes)`. The layer decodes header-versus-frame *itself*,
  and that is not a convenience — which of the two is due is the state's own question, and the state
  table's receive column is what answers it (`State.receiveClass`; `Ref.Connection.row .receivesHeader`
  on the other side). The frame layer's instance could take the direction as given because its subject
  is a codec; here the direction is the machine's business, so the octets are the input and nothing else
  is.
* **`Input.api call` is the endpoint's own application asking it to send.** This is the send direction,
  and the connection layer *can* be given it, where the frame layer could not: the layer's own
  vocabulary already carries the octets it writes — `Submission.frame channel octets body` and
  `Submission.header header` on the specification's side, `Offer.frame`/`Offer.header` on the
  reference's — and `Outcome.wrote`/the refusal's `reply` are the octets that go on the wire. So a call
  carries the octets to send and the layer answers with what it writes; no writer law is needed, which
  is the thing the frame layer's report named as missing for its own send direction. A call the layer
  cannot read — a header it does not speak, octets that are not a frame, a name that is not a send —
  is one the endpoint has no answer for, and both sides say so the same way.
* **`Input.tick` is time crossing, and this layer has nothing behind it.** Not an omission in the
  proof: `Submission` has no tick constructor, `step`'s dispatcher is total over header, frame and
  arriving only, and the field the artifact's timer clauses hang off — `open.idle-time-out` — is read
  nowhere in either tree (the generated field table carries it; neither layer consults it). Neither
  endpoint holds a timer, a threshold, or an expectation about the partner's timing, so both answer a
  tick with nothing, and the tie-back lemma below states that as a clause. An alphabet channel with
  nothing behind it is a scope statement, reported to the planner rather than papered over.

**What a step hands back.** On the specification's side `Spec.Connection.step` returns
`Except Refusal Outcome`; on the reference's `Ref.Connection.apply` returns `Except Refusal Peer`.
`Outcome` is the endpoint it left and the octets it wrote, and a refusal carries the protocol
condition, the reason class, where it leaves the peer and the octets it wrote while refusing. Those
are the observables, and each lands on the interface:

* the octets written are `Output.frame`, in order — which is where the connection layer differs from
  the frame layer's instance, because a refusal here *writes*: a failed header negotiation is
  answered with the peer's own header;
* the answer is `Output.api`: the state table's own name on an admitted step, and the protocol
  condition followed by the reason class on a refusal. The condition is in the answer because §10
  rule 5 makes the mandated error code part of the observable — an implementation that runs out of
  room is incorrect in a checked way, and *which* code it says is part of that — and the corpus pins
  it per refusal vector. The class is in the answer because the corpus compares it too
  (`Harness.reasonClassOf`), which is why it has to be a term on both sides rather than a token
  recovered from prose; see the note on the two interface changes below;
* the state the step leaves — including where a refusal places the peer, which the corpus pins as the
  state a refused step ends in — is the state, and `R` is what compares it.

The table's third column, the connection action, is not a separate output: it is a function of the
state (`State.action` agrees with `Ref.Connection.row`'s `.action` by the `action_eq` lemma below), and
the state is compared, so nothing is lost by not emitting it twice.

## The state, and what a step does to it

The state is the layer's own: `Spec.Connection.Endpoint` against `Ref.Connection.Peer`. The
specification's carries the table's state, the layer whose header exchange is in progress, the SASL
dialogue's stage, which end of it this peer is, the mechanisms announced, and the two sides'
frame-and-channel limits. The reference's carries the same six things under its own names. Both are
*real* state: a step hands back the endpoint it left, not a `Unit`, and the layer's remaining answers
depend on all six fields — which state a frame may be sent or received in, which layer's dispatch
runs, which SASL performative the dialogue is waiting for and from which end, whether an `init` names a
mechanism the partner announced, and whether a frame fits the limits in force (including the ones an
`open` installs).

## The relation

`R` is the statement that the reference's peer *is* the specification's endpoint under the layer's own
naming map: `refPeerOf s = i`, where `refPeerOf` maps the six fields by the table's own names
(`refState`), the protocol id (0 for AMQP, 3 for SASL), the dialogue's stage, which end announced the
mechanisms, and the limits. It is deliberately the *equality of the mapped record* and not a
conjunction of convenience clauses: each field is one the layer reads, so each is one the relation must
fix, and a relation that left any of them free would let the two sides answer the same input
differently.

* Drop `state` and the two machines may admit different frames, transition differently, and report
  different states.
* Drop the layer/protocol id and one may run the SASL dialogue while the other reads an AMQP
  performative, and a failed negotiation answers with the other layer's header.
* Drop the dialogue's stage and the SASL performative each is waiting for differs.
* Drop which end announced the mechanisms and `sasl-init`, `sasl-challenge`, `sasl-response` and
  `sasl-outcome` are each permitted in the wrong direction.
* Drop the announced mechanisms and an `init` naming a mechanism passes on one side and is refused on
  the other.
* Drop either side's limits and a frame one accepts is over the other's limit — and the limits an
  `open` installs are exactly what makes that observable later.

The relation is not vacuous: the initial states are related (by `refPeerOf_initial`), and the proof
below maintains all six fields across every step, which is what makes each clause load-bearing rather
than decorative.

## The choice, and the parameter

`choose` is the specification's own step: the singleton of `Spec.Connection.step`'s outcome, because
this layer's step is a function. That is not a convenience — it is what the layer *is*: `step` takes an
endpoint, a direction and a submission and returns `Except Refusal Outcome` with no policy argument and
no branching on one. The `MAY`s the artifact states around this layer (the empty frame that defeats an
idle timeout, which the frame layer's writer refuses to write; the frame-and-channel limits, which
arrive as `open`'s fields rather than as a free choice; and which peer closes first, which the table
fixes per row) do not reach `choose`, and there is therefore no policy parameter to name.

## What it rests on

The connection layer decides with the *body* of a performative — an `open`'s `max-frame-size` and
`channel-max`, the mandatory-field lists of `open` and `close`, a `sasl-mechanisms` frame's announced
mechanisms, a `sasl-init`'s mechanism, a `sasl-outcome`'s code, and a field's declared type against
the value the wire carried. The frame layer's instance needed none of that: it decides with a
descriptor, so its hypothesis (`ValueLayersAgree`) relates the two value layers only as far as the
declared type a descriptor names. This instance needs the two value layers to agree on what the body
*contains*, and that is the hypothesis named in the theorem below. It is a value-layer claim — the
shape a value layer's own `Conforms` instance would produce — and its proof belongs there.

Nothing weaker will do, and that is a fact about the layer rather than a preference: the four
`refuseUnless` guards and the limits an `open` installs all read a field, so a relation over the body's
descriptor alone would leave every one of them able to differ between the two sides.
-/

namespace SpecAMQP.Proofs

open SpecAMQP
open SpecAMQP.Contracts
open SpecAMQP.Harness (Octets toHex ofHex)
open SpecAMQP.Harness (Octets)

/-! #### 10_tables.lean -/

/-!
# The connection layers' tables, mapped

The value-free half of the connection layer's conformance instance: the maps from the
specification's `Spec.Connection` vocabulary to the reference implementation's
`Ref.Connection` vocabulary, and the lemmas that the two transcriptions of the Connection
State Table (picture 24) answer the same questions the same way.

The two tables are independent readings of the same picture — `Spec.Connection` writes each
row as two columns of *classes* (`SendClass`, `ReceiveClass`, `State.action`), `Ref.Connection`
writes each row as a record of what it admits (`Row`, `Ref.Connection.row`) — so nothing here
is a tautology: each lemma below compares a match on a specification function with a match on
the reference's own table, both of which are transcriptions of the artifact.

The maps are the identification the relation `R` of the conformance proof needs: which of the
reference's fourteen states a specification state *is*, which protocol id its layer is, where
the security layer's dialogue stands, which end of it the peer is, and the two sides' limits.
-/

/-! ## The state map -/

/-- The specification's state, in the reference's names: the table's own fourteen rows, read
twice. Both transcriptions use the artifact's names, so this is the identity on the table
rather than a correspondence invented here. -/

def refState : Spec.Connection.State → Ref.Connection.State
  | .start => .start
  | .hdrRcvd => .rcvHdr
  | .hdrSent => .sndHdr
  | .hdrExch => .bothHdr
  | .openRcvd => .rcvOpen
  | .openSent => .sndOpen
  | .openPipe => .pipeOpen
  | .closePipe => .pipeClose
  | .ocPipe => .pipeOc
  | .opened => .open
  | .closeRcvd => .rcvClose
  | .closeSent => .sndClose
  | .discarding => .discard
  | .end => .done

/-- The two tables spell a state's name the same way, in every state. -/

theorem refState_name (s : Spec.Connection.State) :
    Spec.Connection.State.name s = Ref.Connection.State.label (refState s) := by
  cases s <;> rfl

/-! ## The layer map -/

/-- The protocol id a layer is negotiated under, matching the two layers' own constants: the
transport section's zero for AMQP, the security section's three for SASL. -/

def refLayer : Spec.Connection.Layer → Nat
  | .amqp => 0
  | .sasl => 3

/-- The layer map agrees with the reference's SASL protocol id. -/

theorem refLayer_sasl (l : Spec.Connection.Layer) :
    (refLayer l == Ref.Connection.saslId) = (l == Spec.Connection.Layer.sasl) := by
  cases l <;> decide

/-- The layer map agrees with the reference's AMQP protocol id. -/

theorem refLayer_amqp (l : Spec.Connection.Layer) :
    (refLayer l == Ref.Connection.amqpId) = (l == Spec.Connection.Layer.amqp) := by
  cases l <;> decide

/-! ## The SASL dialogue -/

/-- Where the dialogue stands, in the reference's vocabulary.

A bijection, now that the specification's five positions are four: a successful outcome does not
leave the endpoint past the dialogue, it resets it to `.absent` on the AMQP layer, so there was never
a fifth position to map and the constructor that stood for one is gone. -/

def refPhase : Spec.Connection.SaslPhase → Ref.Connection.Sasl
  | .absent => .idle
  | .awaitingMechanisms => .wantsMechanisms
  | .mechanismsKnown => .wantsInit
  | .awaitingOutcome => .wantsOutcome

/-- Which end of the dialogue a peer is: the peer that announced the mechanisms is the server,
so the specification's role is the reference's `announcedBy`, with `some true` for the server
and `some false` for its partner, and `none` while no mechanisms have been announced. -/

def refRole : Option Spec.Connection.SaslRole → Option Bool
  | none => none
  | some .server => some true
  | some .client => some false

/-! ## The limits -/

/-- The two sides' limits: the reference names the same pair of numbers `frames` and
`channels` that the specification declares as an `open`'s `max-frame-size` and `channel-max`. -/

def refBounds : Spec.Connection.Limits → Ref.Connection.Bounds
  | ⟨maxFrameSize, channelMax⟩ => ⟨maxFrameSize, channelMax⟩

/-! ## The frame kinds -/

/-- What a frame is, in the reference's vocabulary: the two connection performatives, the
security layer's own frames, and everything the connection relays without deciding. -/

def refRoleKind : Spec.Connection.FrameRole → Ref.Connection.Kind
  | .open => .open
  | .close => .close
  | .sasl => .saslFrame
  | .other => .relayed

/-! ## The peer -/

/-- One endpoint, seen as the reference sees it: the same table state, the same protocol id,
the same place in the dialogue, the same end of it, the same announced mechanisms, and the
same two sides' limits. -/

def refPeerOf (e : Spec.Connection.Endpoint) : Ref.Connection.Peer :=
  ⟨refState e.state, refLayer e.layer, refPhase e.phase, refRole e.role, e.mechanisms,
   refBounds e.localLimits, refBounds e.remoteLimits⟩

/-- The two initial states are the same peer: START, in the AMQP layer, with no dialogue
begun, no mechanisms announced and the a priori limits on both sides. -/

theorem refPeerOf_initial :
    refPeerOf Spec.Connection.Endpoint.initial = Ref.Connection.Peer.new := by
  rfl

/-! ## The send column -/

/-- The table's legal-sends column, read the same way by both transcriptions: the class the
specification's column names is the case the reference's row admits, and the two frame classes
that admit frames are the row's two frame cases. The last clause is the reference's `-`: no
case of the row admits anything, which is what the specification's `.nothing` says.

The statement is a conjunction of five equations, one per column class, rather than one
equation over all five, because the reference's row is four flags and the class is one value;
the fifth says the reference's blank row (`-`) is exactly the negation of its four flags. -/

theorem sendColumn (s : Spec.Connection.State) :
    ((Spec.Connection.State.sendClass s == .header) =
      (Ref.Connection.row (refState s)).sendsHeader) ∧
    ((Spec.Connection.State.sendClass s == .open) =
      (Ref.Connection.row (refState s)).sendsOpen) ∧
    ((Spec.Connection.State.sendClass s == .anyFrame) =
      (Ref.Connection.row (refState s)).sendsAny) ∧
    ((Spec.Connection.State.sendClass s == .conforming) =
      (Ref.Connection.row (refState s)).sendsExpected) ∧
    ((Spec.Connection.State.sendClass s == .nothing) =
      (¬ ((Ref.Connection.row (refState s)).sendsHeader ∨
          (Ref.Connection.row (refState s)).sendsOpen ∨
          (Ref.Connection.row (refState s)).sendsAny ∨
          (Ref.Connection.row (refState s)).sendsExpected))) := by
  cases s <;> decide

/-! ## The receive column -/

/-- The table's legal-receives column, read the same way by both transcriptions, on the same
terms as `sendColumn`. The receive column has no `**` class, so there are four equations
rather than five. -/

theorem receiveColumn (s : Spec.Connection.State) :
    ((Spec.Connection.State.receiveClass s == .header) =
      (Ref.Connection.row (refState s)).receivesHeader) ∧
    ((Spec.Connection.State.receiveClass s == .open) =
      (Ref.Connection.row (refState s)).receivesOpen) ∧
    ((Spec.Connection.State.receiveClass s == .anyFrame) =
      (Ref.Connection.row (refState s)).receivesAny) ∧
    ((Spec.Connection.State.receiveClass s == .nothing) =
      (¬ ((Ref.Connection.row (refState s)).receivesHeader ∨
          (Ref.Connection.row (refState s)).receivesOpen ∨
          (Ref.Connection.row (refState s)).receivesAny))) := by
  cases s <;> decide

/-! ## What the two tables permit -/

/-- **A disagreement between the two transcriptions, and the reason this lemma is stated for
three roles rather than four.**

The equation below holds for every state and for the roles `open`, `close` and `other`. It
does *not* hold for `sasl`, and the two layers answer that case differently:

* `Spec.Connection.permitsSend s .sasl` asks the send column, which for the `*` and `**`
  classes answers `role != .open` — and `.sasl != .open` is `true`;
* `Ref.Connection.maySend (refState s) .saslFrame` answers `false` unconditionally, because a
  SASL performative belongs to the security layer's dialogue rather than to the AMQP layer's
  frame step.

A counterexample: `s = .opened` (`refState s = .open`), `r = .sasl`. The specification answers
`true` (`SendClass.anyFrame` admits anything that is not the peer's own `open`) and the
reference answers `false` (`Kind.saslFrame` is refused by the row). The disagreement holds in
every state whose send column is not `-`, `HDR` or `OPEN`: `.opened`, `.closeRcvd` and
`.discarding` (the `*` column) and `.openSent` and `.openPipe` (the `**` column); on the
receive side, `.openRcvd`, `.opened`, `.closeSent` and `.discarding` (the `*` column).

It is not observable in either layer, because both refuse a SASL frame *before* consulting the
column: `Spec.Connection.stepAmqpFrame` opens with `refuseUnless (role != .sasl)` and
`Ref.Connection.takeFrame` with `if kind == .saslFrame then .error …`. So the equation is
stated where it is used, under `hr : r ≠ .sasl`, with the hypothesis the two steps' successful
branches supply. -/

theorem permitsSend_eq (s : Spec.Connection.State) (r : Spec.Connection.FrameRole)
    (hr : r ≠ Spec.Connection.FrameRole.sasl) :
    Spec.Connection.permitsSend s r =
      Ref.Connection.maySend (refState s) (refRoleKind r) := by
  cases r <;> first | exact absurd rfl hr | (cases s <;> decide)

/-- Whether the table's receive column permits a role, read the same way by both
transcriptions. Stated under the same `hr : r ≠ .sasl` as `permitsSend_eq`, with the same
counterexample and the same reason: `Spec.Connection.permitsReceive` asks the `*` column's
`role != .open`, which is `true` for `.sasl`, while `Ref.Connection.mayReceive` answers `false`
for `Kind.saslFrame` in every state. Both layers refuse a SASL frame before the column is
consulted (`stepAmqpFrame`'s `refuseUnless (role != .sasl)`, `takeFrame`'s
`if kind == .saslFrame then .error …`). -/

theorem permitsReceive_eq (s : Spec.Connection.State) (r : Spec.Connection.FrameRole)
    (hr : r ≠ Spec.Connection.FrameRole.sasl) :
    Spec.Connection.permitsReceive s r =
      Ref.Connection.mayReceive (refState s) (refRoleKind r) := by
  cases r <;> first | exact absurd rfl hr | (cases s <;> decide)

/-! ## The action column -/

/-- The table's legal-connection-actions column: the action both transcriptions name, under
the name the table writes it. Both sides are blank exactly where the table's third column is
blank. -/

theorem action_eq (s : Spec.Connection.State) :
    (Spec.Connection.State.action s).map Spec.Connection.ConnAction.name =
      ((Ref.Connection.row (refState s)).action).map Ref.Connection.Action.label := by
  cases s <;> rfl

/-! ## The `open`/`close` transitions -/

/-- The endpoint a permitted `open` or `close` leaves, in the reference's state: the two
layers' transitions draw the same arrows to the same rows, including the `close`'s
error-triggered variant (DISCARDING) and the two rows where a close is the last thing written
(END). -/

theorem afterFrame_state (e : Spec.Connection.Endpoint) (outbound : Bool)
    (r : Spec.Connection.FrameRole) (d : Spec.Connection.Limits) :
    refState (Spec.Connection.Endpoint.afterFrame e outbound r d).state =
      (Ref.Connection.placed (refPeerOf e) outbound (refRoleKind r) (refBounds d)).state := by
  obtain ⟨state, layer, phase, role, mechanisms, localLimits, remoteLimits⟩ := e
  cases outbound <;> cases r <;> cases state <;> rfl

/-- And the limits the frame declared: a sent `open` declares this peer's own limits in both
layers, and a received one the partner's. -/

theorem afterFrame_localLimits (e : Spec.Connection.Endpoint) (outbound : Bool)
    (r : Spec.Connection.FrameRole) (d : Spec.Connection.Limits) :
    refBounds (Spec.Connection.Endpoint.afterFrame e outbound r d).localLimits =
      (Ref.Connection.placed (refPeerOf e) outbound (refRoleKind r) (refBounds d)).own := by
  obtain ⟨state, layer, phase, role, mechanisms, localLimits, remoteLimits⟩ := e
  cases outbound <;> cases r <;> cases state <;> rfl

/-- The same for the partner's limits. -/

theorem afterFrame_remoteLimits (e : Spec.Connection.Endpoint) (outbound : Bool)
    (r : Spec.Connection.FrameRole) (d : Spec.Connection.Limits) :
    refBounds (Spec.Connection.Endpoint.afterFrame e outbound r d).remoteLimits =
      (Ref.Connection.placed (refPeerOf e) outbound (refRoleKind r) (refBounds d)).partner := by
  obtain ⟨state, layer, phase, role, mechanisms, localLimits, remoteLimits⟩ := e
  cases outbound <;> cases r <;> cases state <;> rfl

/-! ## The header transitions -/

/-- The state a sent protocol header leaves, stated about the match expression `stepHeader`
writes inline so that `simp only [afterHeaderSend_state]` fires on the unfolded function: the
first header moves START to HDR_SENT and every other sending state to HDR_EXCH, and the
reference's `takeHeader` draws the same two arms — START to the reference's HDR_SENT, every
other sending state to its HDR_EXCH. -/

theorem afterHeaderSend_state (s : Spec.Connection.State) :
    refState (match s with | .start => .hdrSent | _ => .hdrExch) =
      (match refState s with | .start => .sndHdr | _ => .bothHdr) := by
  cases s <;> rfl

/-- The state a received protocol header leaves, stated about the match expression `stepHeader`
writes inline. The four states the diagram draws an arrow for — START, HDR_SENT, OPEN_PIPE and
OC_PIPE — and every other state, which a header leaves where it is. The two arms agree: the
reference's `takeHeader` writes START, HDR_SENT, OPEN_PIPE and OC_PIPE's images as its four
special arms and leaves the rest alone. -/

theorem afterHeaderReceive_state (s : Spec.Connection.State) :
    refState (match s with
      | .start => .hdrRcvd
      | .hdrSent => .hdrExch
      | .openPipe => .openSent
      | .ocPipe => .closePipe
      | other => other) =
      (match refState s with
        | .start => .rcvHdr
        | .sndHdr => .bothHdr
        | .pipeOpen => .sndOpen
        | .pipeOc => .pipeClose
        | other => other) := by
  cases s <;> rfl

/-! ## Entering the dialogue -/

/-- The endpoint a completed header exchange leaves, in the reference's vocabulary, whenever the
dialogue is not already past the point the reference would advance from.

Both layers put a SASL exchange that has exchanged both headers into the security layer's
dialogue, waiting for the server's mechanisms, and both leave an AMQP exchange alone. They
differ in *what* they ask: the specification asks whether the state is `HDR_EXCH`, and the
reference whether the state is both-header *and* its dialogue stage is still `.idle` — so in a
SASL-layer `HDR_EXCH` whose dialogue has already moved on, the specification would rewind the
stage to `awaitingMechanisms` while the reference leaves the later stage alone.

The hypothesis is exactly where the two agree: `refPhase e.phase` is `.idle` (the stage the
reference advances from) or `.wantsMechanisms` (already there, so the reference's unchanged
stage is the specification's); with any other stage the reference's answer is that other stage
and the specification's is `.wantsMechanisms`. `stepHeader` cannot reach the disagreeing
configuration — a header is refused in both layers unless the state's column is HDR, and a
SASL-layer `HDR_EXCH`'s columns are OPEN/OPEN — so nothing in either layer observes the
difference, but the functions differ as total functions and the lemma says so. -/

theorem afterHeaderExchange_agree (e : Spec.Connection.Endpoint) :
    refPeerOf (Spec.Connection.Endpoint.afterHeaderExchange e) =
      Ref.Connection.inDialogue (refPeerOf e) := by
  obtain ⟨state, layer, phase, role, mechanisms, localLimits, remoteLimits⟩ := e
  cases phase <;> cases layer <;> cases state <;> rfl

/-! ## Where a refusal leaves the peer -/

/-- A specification refusal, as the reference's: the same condition, the same octets written
while refusing, and the state it leaves the peer in. The reason class and the prose are blank
because `Ref.Connection.placeRefusal` never reads them — its `Refusal` carries them only so
that the corpus can render a diagnostic. -/

def refRefusalOf (r : Spec.Connection.Refusal) : Ref.Connection.Refusal :=
  ⟨r.condition, r.reasonClass, "", r.state.map refState, r.wrote⟩

/-- Both layers leave the peer in the same state when a refusal is placed: a refusal that
already says where it leaves the peer keeps it; a refused send moves nothing; a refused
receive in the layer that has not been established cuts the transport, and in the AMQP layer
closes with the error-triggered DISCARDING — unless the connection has already ended, where
END stands in both. -/

theorem placeRefusal_eq (e : Spec.Connection.Endpoint) (outbound : Bool)
    (r : Spec.Connection.Refusal) :
    (Spec.Connection.Refusal.withPlace e outbound r).state.map refState =
      (Ref.Connection.placeRefusal (refPeerOf e) outbound (refRefusalOf r)).place := by
  obtain ⟨state, layer, phase, role, mechanisms, localLimits, remoteLimits⟩ := e
  obtain ⟨condition, reasonClass, detail, place, wrote⟩ := r
  cases outbound <;> cases layer <;> cases state <;> cases place <;> rfl

/-! ## The octets the two layers agree on -/

/-- The protocol header's octets: the two layers write the same eight octets — the magic and
the four octets the layout gives the protocol id and the version — from the same parts, so a
negotiation compared octet for octet is a comparison of the same transcription of picture 11.
The two sides write the octets differently and the equality is proved rather than restated:
the specification names the octets through `ProtocolId.code` and `octet`, the reference
through `Header.octets`'s own `UInt8.ofNat (… % 256)`. -/

theorem headerOctets_eq (h : Spec.Connection.ProtocolHeader) :
    h.octets =
      Ref.Connection.Header.octets
        ⟨h.protocolId.code, h.version.major, h.version.minor, h.version.revision⟩ := by
  rfl

/-- The reference's triple and the specification's record are the same option, one `map`
apart: what both sides' `match` on the three constants produces. Private, because it is the
step `version_eq` takes rather than something a reader of the relation needs. -/

private theorem versionTriple (a b c : Option Nat) :
    (match a, b, c with
      | some x, some y, some z => some (⟨x, y, z⟩ : Spec.Connection.Version)
      | _, _, _ => none) =
      (match a, b, c with
        | some x, some y, some z => some (x, y, z)
        | _, _, _ => none).map
        (fun v : Nat × Nat × Nat => (⟨v.1, v.2.1, v.2.2⟩ : Spec.Connection.Version)) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- The version the artifact states for a layer, in the reference's shape: the specification's
`Version` record and the reference's `Nat × Nat × Nat` carry the same three numbers, both read
from the generated constant table rather than typed. -/

theorem version_eq (l : Spec.Connection.Layer) :
    Spec.Connection.Layer.version l =
      (Ref.Connection.statedVersion (refLayer l)).map
        (fun v => (⟨v.1, v.2.1, v.2.2⟩ : Spec.Connection.Version)) := by
  cases l <;> exact versionTriple _ _ _

/-! ## The disagreements between the two tables, proved -/

/-- The disagreement `permitsSend_eq` leaves out, proved as a counterexample: in `OPENED` — a
`*` row — the specification's send column admits a SASL role and the reference's row does
not. -/

private theorem permitsSend_sasl_disagrees :
    Spec.Connection.permitsSend Spec.Connection.State.opened
        Spec.Connection.FrameRole.sasl = true ∧
      Ref.Connection.maySend Ref.Connection.State.open Ref.Connection.Kind.saslFrame =
        false :=
  ⟨rfl, rfl⟩

/-- The same disagreement on the receive side: `OPENED`'s receive column is `*`. -/

private theorem permitsReceive_sasl_disagrees :
    Spec.Connection.permitsReceive Spec.Connection.State.opened
        Spec.Connection.FrameRole.sasl = true ∧
      Ref.Connection.mayReceive Ref.Connection.State.open Ref.Connection.Kind.saslFrame =
        false :=
  ⟨rfl, rfl⟩

/-! #### 20_values.lean -/

/-! ## The relation between the two value layers' values -/


mutual

/-- **What the connection layer reads of a body.** A relation between the specification's value type and
the reference's, strong enough for every question this layer asks of a decoded performative and no
stronger: whether a value is null, the number an integer carries in the width the wire used, the text a
symbol or string carries, the octets a binary or a floating-point payload carries, the element list a
compound value carries (elementwise, so the layer's field lookups agree at every index), the descriptor
a described value names, and the primitive type name a field's declared type is checked against.

The two value types are independent — they carry their integers in different widths (`Nat` against
`UInt8`…`UInt64`, `Int` against `Int8`…`Int64`) and their octets differently (`Octets`, an
`Array UInt8`, against `List UInt8` for `binary`) — so the numeric clauses are *round-trip equations in
the reference's width*, which is what makes the two layers' integer reads agree: `a = b.toNat` is
satisfiable only in the range the reference's width admits, which is the range a decoded value is in.

It is an inductive rather than a definition by pattern matching because its compound clauses recurse
through `List.Forall₂`, which no structural-recursion check can see — and an inductive is the honest
form for a relation anyway: there is no `False` clause, because the pairs it does not relate are simply
not in it.

The relation is the value layer's, and it is stated here rather than in the layer that consumes it
because the connection layer is the first that needs it: a frame layer decides with the declared type a
descriptor names, which is the *shape* of a body and not its contents. -/

inductive ValuesAgree : SpecAMQP.Spec.Codec.Value → SpecAMQP.Ref.Value → Prop where
  | null : ValuesAgree .null .null
  | boolean {a b : Bool} : a = b → ValuesAgree (.boolean a) (.boolean b)
  | ubyte {a : Nat} {b : UInt8} : a = b.toNat → ValuesAgree (.ubyte a) (.ubyte b)
  | ushort {a : Nat} {b : UInt16} : a = b.toNat → ValuesAgree (.ushort a) (.ushort b)
  | uint {a : Nat} {b : UInt32} : a = b.toNat → ValuesAgree (.uint a) (.uint b)
  | ulong {a : Nat} {b : UInt64} : a = b.toNat → ValuesAgree (.ulong a) (.ulong b)
  | byte {a : Int} {b : Int8} : a = b.toInt → ValuesAgree (.byte a) (.byte b)
  | short {a : Int} {b : Int16} : a = b.toInt → ValuesAgree (.short a) (.short b)
  | int {a : Int} {b : Int32} : a = b.toInt → ValuesAgree (.int a) (.int b)
  | long {a : Int} {b : Int64} : a = b.toInt → ValuesAgree (.long a) (.long b)
  | float {a b : SpecAMQP.Harness.Octets} : a = b → ValuesAgree (.float a) (.float b)
  | double {a b : SpecAMQP.Harness.Octets} : a = b → ValuesAgree (.double a) (.double b)
  | decimal32 {a b : SpecAMQP.Harness.Octets} : a = b → ValuesAgree (.decimal32 a) (.decimal32 b)
  | decimal64 {a b : SpecAMQP.Harness.Octets} : a = b → ValuesAgree (.decimal64 a) (.decimal64 b)
  | decimal128 {a b : SpecAMQP.Harness.Octets} : a = b → ValuesAgree (.decimal128 a) (.decimal128 b)
  | char {a : Nat} {b : UInt32} : a = b.toNat → ValuesAgree (.char a) (.char b)
  | timestamp {a : Int} {b : Int64} : a = b.toInt → ValuesAgree (.timestamp a) (.timestamp b)
  | uuid {a b : SpecAMQP.Harness.Octets} : a = b → ValuesAgree (.uuid a) (.uuid b)
  | binary {a : SpecAMQP.Harness.Octets} {b : List UInt8} : a.toList = b →
    ValuesAgree (.binary a) (.binary b)
  | string {a b : String} : a = b → ValuesAgree (.string a) (.string b)
  | symbol {a b : String} : a = b → ValuesAgree (.symbol a) (.symbol b)
  | list {xs : List SpecAMQP.Spec.Codec.Value} {ys : List SpecAMQP.Ref.Value} :
    List.Forall₂ ValuesAgree xs ys → ValuesAgree (.list xs) (.list ys)
  | map {ps : List (SpecAMQP.Spec.Codec.Value × SpecAMQP.Spec.Codec.Value)}
      {qs : List (SpecAMQP.Ref.Value × SpecAMQP.Ref.Value)} :
    List.Forall₂ PairAgree ps qs → ValuesAgree (.map ps) (.map qs)
  | array {ca cb : UInt8} {xs : List SpecAMQP.Spec.Codec.Value}
      {ys : List SpecAMQP.Ref.Value} :
    ca = cb → List.Forall₂ ValuesAgree xs ys → ValuesAgree (.array ca xs) (.array cb ys)
  | described {da va : SpecAMQP.Spec.Codec.Value} {db vb : SpecAMQP.Ref.Value} :
    ValuesAgree da db → ValuesAgree va vb → ValuesAgree (.described da va) (.described db vb)

/-- Two pairs of values that agree, one component at a time: what a map's entries agree means. It is
declared mutually with `ValuesAgree` because a lambda in a nested position would carry a local variable,
which the kernel refuses. -/

inductive PairAgree : SpecAMQP.Spec.Codec.Value × SpecAMQP.Spec.Codec.Value →
    SpecAMQP.Ref.Value × SpecAMQP.Ref.Value → Prop where
  | mk {a : SpecAMQP.Spec.Codec.Value} {b : SpecAMQP.Spec.Codec.Value}
      {c : SpecAMQP.Ref.Value} {d : SpecAMQP.Ref.Value} :
    ValuesAgree a c → ValuesAgree b d → PairAgree (a, b) (c, d)
end

/-- Two optional values that agree, or are both absent: what a field lookup answers on each side. -/

inductive OptionAgree : Option SpecAMQP.Spec.Codec.Value → Option SpecAMQP.Ref.Value → Prop where
  | none : OptionAgree none none
  | some {a : SpecAMQP.Spec.Codec.Value} {b : SpecAMQP.Ref.Value} :
    ValuesAgree a b → OptionAgree (some a) (some b)

/-! #### 25_hypothesis.lean -/

/-! ## The hypothesis, and what the two readers answer -/

/-- Two frames as the connection layer reads them: the layout and the frame type agree (up to the two
layers' naming), and the bodies agree under `ValuesAgree` — strictly more than the frame layer's own

instance needed, because a frame layer decides with the descriptor a body names while a connection layer
decides with the body's *fields*. -/

structure FramesAgree (frame : SpecAMQP.Spec.Frame.Frame)
    (other : SpecAMQP.Ref.Frame.Frame) : Prop where
  doff : frame.doff = other.doff
  kind : refKind frame.frameType = other.kind
  channel : frame.channel = other.channel
  extended : frame.extended = other.extended
  payload : frame.payload = other.payload
  body : ∀ (sb : SpecAMQP.Spec.Codec.Value) (rb : SpecAMQP.Ref.Value),
    frame.body = some sb → other.body = some rb → ValuesAgree sb rb
  bodyNone : frame.body = none ↔ other.body = none

/-- **The hypothesis this instance rests on.** The two frame readers answer the same buffer alike in the
two ways that matter here: the frames they read agree as `FramesAgree` says, and the refusals they raise
agree in the class each names. `ValuesAgree` inside `FramesAgree` is the value layer's claim — the shape
a value-layer instance would produce — and its proof belongs there; what this instance adds to the frame
layer's own hypothesis is exactly the body's contents, which is exactly what this layer consults and the
frame layer does not. -/

abbrev ReadersAgree : Prop :=
  ∀ bytes : Octets,
    (∀ (rframe : SpecAMQP.Ref.Frame.Frame) (used : Nat),
        SpecAMQP.Ref.Frame.readFrame bytes = .ok (rframe, used) →
        ∃ (sframe : SpecAMQP.Spec.Frame.Frame) (consumed : Nat),
          SpecAMQP.Spec.Frame.readFrame bytes = .ok (sframe, consumed) ∧
          consumed = used ∧ FramesAgree sframe rframe) ∧
    (∀ failure : SpecAMQP.Ref.Frame.Refusal,
        SpecAMQP.Ref.Frame.readFrame bytes = .error failure →
        ∃ refusal : SpecAMQP.Spec.Frame.Refusal,
          SpecAMQP.Spec.Frame.readFrame bytes = .error refusal ∧
          refusal.reasonClass = failure.reasonClass)

/-- The hypothesis as the frame layer states its own, which is the projection of `FramesAgree` the frame
layer's relation needs: two frames the connection layer cannot tell apart are two frames whose bodies
the frame layer reads the same way. -/

theorem FramesAgree.toFrameAgrees {frame : SpecAMQP.Spec.Frame.Frame}
    {other : SpecAMQP.Ref.Frame.Frame} (h : FramesAgree frame other)
    (hview : ∀ (a : SpecAMQP.Spec.Codec.Value) (b : SpecAMQP.Ref.Value),
      ValuesAgree a b → specBodyView a = refBodyView b) :
    FrameAgrees frame other := by
  refine ⟨h.doff, h.kind, h.channel, h.extended, ?_, h.payload⟩
  cases hb : frame.body with
  | none =>
    have hother : other.body = none := h.bodyNone.mp hb
    simp only [hother, Option.map_none]
  | some sb =>
    cases hc : other.body with
    | none => exact absurd (h.bodyNone.mpr hc) (by rw [hb]; simp)
    | some rb =>
      simp only [hc, Option.map_some, Option.some.injEq]
      exact hview sb rb (h.body sb rb hb hc)

/-- **The frame layer's own obligation is a consequence of this instance's hypothesis**, not a second
assumption: whatever the reference's frame reader answers for a buffer, the specification's answers with
a frame related by the frame layer's own `FrameAgrees`, or refuses with the same class. That is
`AnswerMatched`, which is what the frame layer's instance consumes. -/

theorem readersAgree_answer_matched (h : ReadersAgree)
    (hview : ∀ (a : SpecAMQP.Spec.Codec.Value) (b : SpecAMQP.Ref.Value),
      ValuesAgree a b → specBodyView a = refBodyView b) (bytes : Octets) :
    AnswerMatched (SpecAMQP.Spec.Frame.readFrame bytes) (SpecAMQP.Ref.Frame.readFrame bytes) :=
  ⟨fun other used hok =>
      let ⟨frame, consumed, hread, hcount, hagrees⟩ := (h bytes).1 other used hok
      ⟨frame, consumed, hread, hcount, hagrees.toFrameAgrees hview⟩,
   (h bytes).2⟩

/-! ## What the two layers' frame readers answer in the form the connection layer uses -/

/-- The classed reader and the rendered one accept the same frames and refuse the same ones: the
rendered form is the classed one with each refusal's class folded into its message, so a claim about one
is a claim about the other. -/

theorem spec_readFrame_ok_iff (bytes : Octets) (frame : SpecAMQP.Spec.Frame.Frame) (consumed : Nat) :
    SpecAMQP.Spec.Frame.decodeFrame bytes = .ok (frame, consumed) ↔
      SpecAMQP.Spec.Frame.readFrame bytes = .ok (frame, consumed) := by
  unfold SpecAMQP.Spec.Frame.decodeFrame
  cases h : SpecAMQP.Spec.Frame.readFrame bytes <;> simp [h, Except.mapError]

/-- And a refusal, with the class the frame layer named. -/

theorem spec_decodeFrame_error_iff (bytes : Octets) (message : String) :
    SpecAMQP.Spec.Frame.decodeFrame bytes = .error message ↔
      ∃ refusal : SpecAMQP.Spec.Frame.Refusal,
        SpecAMQP.Spec.Frame.readFrame bytes = .error refusal ∧ refusal.message = message := by
  unfold SpecAMQP.Spec.Frame.decodeFrame
  cases h : SpecAMQP.Spec.Frame.readFrame bytes <;> simp [h, Except.mapError]

/-- The reference's, on the same terms. -/

theorem ref_readFrame_ok_iff (bytes : Octets) (frame : SpecAMQP.Ref.Frame.Frame) (used : Nat) :
    SpecAMQP.Ref.Frame.decodeFrame bytes = .ok (frame, used) ↔
      SpecAMQP.Ref.Frame.readFrame bytes = .ok (frame, used) := by
  unfold SpecAMQP.Ref.Frame.decodeFrame
  cases h : SpecAMQP.Ref.Frame.readFrame bytes <;> simp [h, Except.mapError]

/-- And its refusal. -/

theorem ref_decodeFrame_error_iff (bytes : Octets) (message : String) :
    SpecAMQP.Ref.Frame.decodeFrame bytes = .error message ↔
      ∃ failure : SpecAMQP.Ref.Frame.Refusal,
        SpecAMQP.Ref.Frame.readFrame bytes = .error failure ∧ failure.message = message := by
  unfold SpecAMQP.Ref.Frame.decodeFrame
  cases h : SpecAMQP.Ref.Frame.readFrame bytes <;> simp [h, Except.mapError]

/-! #### 30_header.lean -/

/-!
# The two protocol-header readers agree

`Spec.Connection.decodeHeader` and `Ref.Connection.readHeader` both read the eight-octet
protocol header the layout picture (picture 11) draws — width, magic, protocol id, version —
and the connection layer's `Conforms` proof needs them to be the same reader. This module
proves that, as a theorem rather than as a differential over a corpus.

## The two vocabularies

The two trees share no definition, so the proof first fixes the vocabulary the comparison is
written in:

* `refProtoId` is the reference's numbering of the specification's `ProtocolId`, and
  `refProtoId_code` says it *is* the specification's own `code` — the three assignments
  (0 AMQP, 2 TLS, 3 SASL) are the artifact's, not each tree's;
* `speaksId_iff` says the reference speaks exactly the ids zero and three, which is where the
  two readers' accept sets are compared, and `speaks_of_code`/`speaks_of_code_layer` turn "the
  reference speaks it" into the specification's `ProtocolId`, its `layer?` and a version;
* `ofCode_eq_none_iff` says the ids the specification's protocol-id check declines are exactly
  the ids other than zero, two and three — the same set the reference declines, split
  differently: the specification by whether an id is assigned and then by whether its layer is
  spoken, the reference by whether it speaks the id;
* `statedVersion_eq` says the version the reference states for an id is the version the
  specification states for the layer that id selects: one constant table (`constantNat` and
  `constantNumber` are the same function), read by each tree's own name for it.

## The branch lemmas

Each reader answers branch by branch, and each branch is its own theorem in the layer's own
vocabulary — the specification's `decodeHeader` checks width, magic, protocol id, layer and
version in that order, and so does the reference's `readHeader`. The refusal theorems are
stated as `∃ r, … = .error r` rather than as a bare `isError`, so that the refusal is a term a
later edit can pin: `Spec.Connection.Refusal` gains its `reasonClass` field in a sibling
change, and the class conjunct belongs on these statements rather than on the agreement.

## The agreement

`refHeader_matched` chains the branch facts: every header the reference reads is a header the
specification reads, with the same protocol id, the same three version octets and the octets
the layout draws; and every buffer the reference refuses is a buffer the specification refuses.
The two readers keep their checks in the same order and draw the same line, so the case split
over the reference's questions lands each branch on the specification's matching branch.
-/

/-! ## The vocabulary the two readers are compared in -/

/-- The reference's numbering of the specification's protocol ids: the three assignments are
the artifact's (zero AMQP, two TLS, three SASL). -/

def refProtoId : SpecAMQP.Spec.Connection.ProtocolId → Nat
  | .amqp => 0
  | .tls => 2
  | .sasl => 3

/-- The map is the specification's own `code`, so the specification's name for a protocol id and
the reference's number for it are the same number. -/

theorem refProtoId_code (p : SpecAMQP.Spec.Connection.ProtocolId) : p.code = refProtoId p := by
  cases p <;> rfl

/-- The reference speaks exactly the two ids AMQP and SASL: protocol id two is assigned by the
artifact to TLS and is not spoken here. -/

theorem speaksId_iff (n : Nat) : SpecAMQP.Ref.Connection.speaksId n = true ↔ n = 0 ∨ n = 3 := by
  unfold SpecAMQP.Ref.Connection.speaksId SpecAMQP.Ref.Connection.amqpId
    SpecAMQP.Ref.Connection.saslId
  rw [Bool.or_eq_true]
  simp only [beq_iff_eq]

/-- An id the reference speaks names a protocol id in the specification's enumeration, and the
numbering the reference uses for that id is the id itself. -/

theorem speaks_of_code (n : Nat) (h : SpecAMQP.Ref.Connection.speaksId n = true) :
    ∃ p : SpecAMQP.Spec.Connection.ProtocolId,
      SpecAMQP.Spec.Connection.ProtocolId.ofCode n = some p ∧ refProtoId p = n := by
  rw [speaksId_iff] at h
  rcases h with rfl | rfl
  · exact ⟨.amqp, rfl, rfl⟩
  · exact ⟨.sasl, rfl, rfl⟩

/-- An id the reference speaks selects a layer in the specification's sense: the only id whose
protocol id the specification declines is two, and the reference does not speak it either. -/

theorem speaks_of_code_layer (n : Nat) (h : SpecAMQP.Ref.Connection.speaksId n = true) :
    ∃ p l, SpecAMQP.Spec.Connection.ProtocolId.ofCode n = some p ∧ p.layer? = some l ∧
      refProtoId p = n := by
  obtain ⟨p, hp, hpr⟩ := speaks_of_code n h
  cases p with
  | amqp => exact ⟨.amqp, .amqp, hp, rfl, hpr⟩
  | sasl => exact ⟨.sasl, .sasl, hp, rfl, hpr⟩
  | tls =>
    exfalso
    rw [speaksId_iff] at h
    have hn : n = 2 := by rw [← hpr]; rfl
    rw [hn] at h
    omega

/-- The ids the specification's protocol-id check declines are the ids other than zero, two and
three: the two refusals cover the same set, split differently. -/

theorem ofCode_eq_none_iff (n : Nat) :
    SpecAMQP.Spec.Connection.ProtocolId.ofCode n = none ↔ n ≠ 0 ∧ n ≠ 2 ∧ n ≠ 3 := by
  by_cases h0 : n = 0
  · subst n
    simp [SpecAMQP.Spec.Connection.ProtocolId.ofCode, SpecAMQP.Spec.Connection.ProtocolId.code]
  by_cases h2 : n = 2
  · subst n
    simp [SpecAMQP.Spec.Connection.ProtocolId.ofCode, SpecAMQP.Spec.Connection.ProtocolId.code]
  by_cases h3 : n = 3
  · subst n
    simp [SpecAMQP.Spec.Connection.ProtocolId.ofCode, SpecAMQP.Spec.Connection.ProtocolId.code]
  · simp [SpecAMQP.Spec.Connection.ProtocolId.ofCode, SpecAMQP.Spec.Connection.ProtocolId.code,
      h0, h2, h3]

/-- The three named constants as a triple, read one way and read the other: the specification's
`versionOf` writes the version out of the table's three entries, and the reference's
`statedVersion` hands the triple back and lets the caller write it — the same table either way. -/

private theorem triple_map_eq (A B C : Option Nat) :
    (match A, B, C with
     | some a, some b, some c => some (⟨a, b, c⟩ : SpecAMQP.Spec.Connection.Version)
     | _, _, _ => none) =
    ((match A, B, C with
      | some a, some b, some c => some (a, b, c)
      | _, _, _ => none) : Option (Nat × Nat × Nat)).map
      (fun v => (⟨v.1, v.2.1, v.2.2⟩ : SpecAMQP.Spec.Connection.Version)) := by
  cases A <;> cases B <;> cases C <;> rfl

/-- The version the reference states for a protocol id is the version the specification states
for the layer that id selects: one constant table, read by each tree's own name for it. -/

theorem statedVersion_eq (p : SpecAMQP.Spec.Connection.ProtocolId)
    (l : SpecAMQP.Spec.Connection.Layer) (h : p.layer? = some l) :
    SpecAMQP.Spec.Connection.Layer.version l =
      (SpecAMQP.Ref.Connection.statedVersion (refProtoId p)).map
        (fun v => (⟨v.1, v.2.1, v.2.2⟩ : SpecAMQP.Spec.Connection.Version)) := by
  cases p with
  | amqp =>
    cases h
    exact triple_map_eq _ _ _
  | sasl =>
    cases h
    exact triple_map_eq _ _ _
  | tls => cases h

/-! ## The specification's reader, branch by branch -/

/-- A buffer shorter than the header is `truncated`, whatever it holds. -/

theorem spec_decodeHeader_short (bytes : Octets)
    (h : bytes.size < SpecAMQP.Spec.Connection.headerOctets) :
    ∃ r, SpecAMQP.Spec.Connection.decodeHeader bytes = .error r :=
  ⟨_, by unfold SpecAMQP.Spec.Connection.decodeHeader; rw [if_pos h]⟩

/-- A buffer long enough that does not begin with the magic is `malformed`. -/

theorem spec_decodeHeader_malformed (bytes : Octets)
    (h₁ : ¬ bytes.size < SpecAMQP.Spec.Connection.headerOctets)
    (h₂ : bytes.extract 0 4 != SpecAMQP.Spec.Connection.magic) :
    ∃ r, SpecAMQP.Spec.Connection.decodeHeader bytes = .error r :=
  ⟨_, by unfold SpecAMQP.Spec.Connection.decodeHeader; rw [if_neg h₁, if_pos h₂]⟩

/-- A protocol id octet no artifact assigns is `unsupported`. -/

theorem spec_decodeHeader_unknown_id (bytes : Octets)
    (h₁ : ¬ bytes.size < SpecAMQP.Spec.Connection.headerOctets)
    (h₂ : ¬ bytes.extract 0 4 != SpecAMQP.Spec.Connection.magic)
    (h₃ : SpecAMQP.Spec.Connection.ProtocolId.ofCode
      (SpecAMQP.Spec.Connection.beAt bytes 4 1) = none) :
    ∃ r, SpecAMQP.Spec.Connection.decodeHeader bytes = .error r :=
  ⟨_, by
    unfold SpecAMQP.Spec.Connection.decodeHeader
    rw [if_neg h₁, if_neg h₂]
    simp only [h₃]
    rfl⟩

/-- A protocol id the artifact assigns to a layer this peer does not speak — TLS — is
`unsupported`. -/

theorem spec_decodeHeader_unspoken_layer (bytes : Octets)
    (h₁ : ¬ bytes.size < SpecAMQP.Spec.Connection.headerOctets)
    (h₂ : ¬ bytes.extract 0 4 != SpecAMQP.Spec.Connection.magic)
    (p : SpecAMQP.Spec.Connection.ProtocolId)
    (hp : SpecAMQP.Spec.Connection.ProtocolId.ofCode
      (SpecAMQP.Spec.Connection.beAt bytes 4 1) = some p)
    (h₃ : p.layer? = none) :
    ∃ r, SpecAMQP.Spec.Connection.decodeHeader bytes = .error r :=
  ⟨_, by
    unfold SpecAMQP.Spec.Connection.decodeHeader
    rw [if_neg h₁, if_neg h₂]
    simp only [hp, h₃]
    rfl⟩

/-- A header whose version octets are not the version the constant table states for the layer
that id selects is `unsupported`. -/

theorem spec_decodeHeader_unsupported_version (bytes : Octets)
    (h₁ : ¬ bytes.size < SpecAMQP.Spec.Connection.headerOctets)
    (h₂ : ¬ bytes.extract 0 4 != SpecAMQP.Spec.Connection.magic)
    (p : SpecAMQP.Spec.Connection.ProtocolId)
    (hp : SpecAMQP.Spec.Connection.ProtocolId.ofCode
      (SpecAMQP.Spec.Connection.beAt bytes 4 1) = some p)
    (l : SpecAMQP.Spec.Connection.Layer) (hl : p.layer? = some l)
    (v : SpecAMQP.Spec.Connection.Version) (hv : SpecAMQP.Spec.Connection.Layer.version l = some v)
    (hne : ¬ (⟨SpecAMQP.Spec.Connection.beAt bytes 5 1, SpecAMQP.Spec.Connection.beAt bytes 6 1,
      SpecAMQP.Spec.Connection.beAt bytes 7 1⟩ : SpecAMQP.Spec.Connection.Version) = v) :
    ∃ r, SpecAMQP.Spec.Connection.decodeHeader bytes = .error r :=
  ⟨_, by
    unfold SpecAMQP.Spec.Connection.decodeHeader
    rw [if_neg h₁, if_neg h₂]
    simp only [hp, hl, hv]
    rw [if_neg hne]⟩

/-- A layer whose version the constant table does not state at all is `unsupported`. -/

theorem spec_decodeHeader_no_version (bytes : Octets)
    (h₁ : ¬ bytes.size < SpecAMQP.Spec.Connection.headerOctets)
    (h₂ : ¬ bytes.extract 0 4 != SpecAMQP.Spec.Connection.magic)
    (p : SpecAMQP.Spec.Connection.ProtocolId)
    (hp : SpecAMQP.Spec.Connection.ProtocolId.ofCode
      (SpecAMQP.Spec.Connection.beAt bytes 4 1) = some p)
    (l : SpecAMQP.Spec.Connection.Layer) (hl : p.layer? = some l)
    (h : SpecAMQP.Spec.Connection.Layer.version l = none) :
    ∃ r, SpecAMQP.Spec.Connection.decodeHeader bytes = .error r :=
  ⟨_, by
    unfold SpecAMQP.Spec.Connection.decodeHeader
    rw [if_neg h₁, if_neg h₂]
    simp only [hp, hl, h]
    rfl⟩

/-- A header for a layer this peer speaks whose version is the stated one is read, and the header
it answers is the protocol id and the version the octets name. -/

theorem spec_decodeHeader_ok (bytes : Octets)
    (h₁ : ¬ bytes.size < SpecAMQP.Spec.Connection.headerOctets)
    (h₂ : ¬ bytes.extract 0 4 != SpecAMQP.Spec.Connection.magic)
    (p : SpecAMQP.Spec.Connection.ProtocolId)
    (hp : SpecAMQP.Spec.Connection.ProtocolId.ofCode
      (SpecAMQP.Spec.Connection.beAt bytes 4 1) = some p)
    (l : SpecAMQP.Spec.Connection.Layer) (hl : p.layer? = some l)
    (v : SpecAMQP.Spec.Connection.Version) (hv : SpecAMQP.Spec.Connection.Layer.version l = some v)
    (hveq : v = ⟨SpecAMQP.Spec.Connection.beAt bytes 5 1, SpecAMQP.Spec.Connection.beAt bytes 6 1,
      SpecAMQP.Spec.Connection.beAt bytes 7 1⟩) :
    SpecAMQP.Spec.Connection.decodeHeader bytes = .ok ⟨p, v⟩ := by
  unfold SpecAMQP.Spec.Connection.decodeHeader
  rw [if_neg h₁, if_neg h₂]
  simp only [hp, hl, hv]
  rw [hveq, if_pos rfl]

/-! ## The reference's reader, branch by branch -/

/-- A buffer shorter than the header is `truncated`, whatever it holds. -/

theorem ref_readHeader_short (bytes : Octets)
    (h : bytes.size < SpecAMQP.Ref.Connection.headerWidth) :
    ∃ r, SpecAMQP.Ref.Connection.readHeader bytes = .error r :=
  ⟨_, by unfold SpecAMQP.Ref.Connection.readHeader; rw [if_pos h]⟩

/-- A buffer long enough that does not begin with the magic is `malformed`. -/

theorem ref_readHeader_malformed (bytes : Octets)
    (h₁ : ¬ bytes.size < SpecAMQP.Ref.Connection.headerWidth)
    (h₂ : bytes.extract 0 4 != SpecAMQP.Ref.Connection.magic) :
    ∃ r, SpecAMQP.Ref.Connection.readHeader bytes = .error r :=
  ⟨_, by unfold SpecAMQP.Ref.Connection.readHeader; rw [if_neg h₁, if_pos h₂]⟩

/-- A protocol id the reference does not speak — anything but zero and three — is
`unsupported`. -/

theorem ref_readHeader_unspeaking (bytes : Octets)
    (h₁ : ¬ bytes.size < SpecAMQP.Ref.Connection.headerWidth)
    (h₂ : ¬ bytes.extract 0 4 != SpecAMQP.Ref.Connection.magic)
    (h₃ : SpecAMQP.Ref.Connection.speaksId (SpecAMQP.Ref.Connection.field bytes 4 1) = false) :
    ∃ r, SpecAMQP.Ref.Connection.readHeader bytes = .error r :=
  ⟨_, by
    unfold SpecAMQP.Ref.Connection.readHeader
    rw [if_neg h₁, if_neg h₂]
    rw [if_pos (by simp [h₃])]⟩

/-- A protocol id the reference speaks whose version the constant table does not state is
`unsupported`. -/

theorem ref_readHeader_no_version (bytes : Octets)
    (h₁ : ¬ bytes.size < SpecAMQP.Ref.Connection.headerWidth)
    (h₂ : ¬ bytes.extract 0 4 != SpecAMQP.Ref.Connection.magic)
    (h₃ : SpecAMQP.Ref.Connection.speaksId (SpecAMQP.Ref.Connection.field bytes 4 1) = true)
    (h : SpecAMQP.Ref.Connection.statedVersion (SpecAMQP.Ref.Connection.field bytes 4 1) = none) :
    ∃ r, SpecAMQP.Ref.Connection.readHeader bytes = .error r :=
  ⟨_, by
    unfold SpecAMQP.Ref.Connection.readHeader
    rw [if_neg h₁, if_neg h₂, if_neg (by simp [h₃])]
    simp only [h]
    rfl⟩

/-- The version refusal with the table's triple destructured. The reference's reader matches the
stated version as a triple, so this is the form the refusal is proved in; the theorem below is the
same statement with the triple left whole, which is the form the version it read is compared in. -/

private theorem ref_readHeader_version_abc (bytes : Octets)
    (h₁ : ¬ bytes.size < SpecAMQP.Ref.Connection.headerWidth)
    (h₂ : ¬ bytes.extract 0 4 != SpecAMQP.Ref.Connection.magic)
    (h₃ : SpecAMQP.Ref.Connection.speaksId (SpecAMQP.Ref.Connection.field bytes 4 1) = true)
    (a b c : Nat)
    (hv : SpecAMQP.Ref.Connection.statedVersion (SpecAMQP.Ref.Connection.field bytes 4 1) =
      some (a, b, c))
    (hacc : ¬ (SpecAMQP.Ref.Connection.field bytes 5 1 == a &&
      SpecAMQP.Ref.Connection.field bytes 6 1 == b &&
      SpecAMQP.Ref.Connection.field bytes 7 1 == c) = true) :
    ∃ r, SpecAMQP.Ref.Connection.readHeader bytes = .error r :=
  ⟨_, by
    unfold SpecAMQP.Ref.Connection.readHeader
    rw [if_neg h₁, if_neg h₂, if_neg (by simp [h₃])]
    simp only [hv]
    exact if_neg hacc⟩

/-- A header whose version octets are not the stated version is `unsupported`. -/

theorem ref_readHeader_version (bytes : Octets)
    (h₁ : ¬ bytes.size < SpecAMQP.Ref.Connection.headerWidth)
    (h₂ : ¬ bytes.extract 0 4 != SpecAMQP.Ref.Connection.magic)
    (h₃ : SpecAMQP.Ref.Connection.speaksId (SpecAMQP.Ref.Connection.field bytes 4 1) = true)
    (v : Nat × Nat × Nat)
    (hv : SpecAMQP.Ref.Connection.statedVersion (SpecAMQP.Ref.Connection.field bytes 4 1) = some v)
    (hacc : ¬ (SpecAMQP.Ref.Connection.field bytes 5 1 == v.1 &&
      SpecAMQP.Ref.Connection.field bytes 6 1 == v.2.1 &&
      SpecAMQP.Ref.Connection.field bytes 7 1 == v.2.2) = true) :
    ∃ r, SpecAMQP.Ref.Connection.readHeader bytes = .error r := by
  rcases v with ⟨a, b, c⟩
  have hacc' : ¬ (SpecAMQP.Ref.Connection.field bytes 5 1 == a &&
      SpecAMQP.Ref.Connection.field bytes 6 1 == b &&
      SpecAMQP.Ref.Connection.field bytes 7 1 == c) = true := hacc
  exact ref_readHeader_version_abc bytes h₁ h₂ h₃ a b c hv hacc'

/-- A header for a protocol id the reference speaks whose three version octets are the stated
version is read, and what it reads is the four octets the layout draws. The version octets are
read *into* the header before the comparison, so the header's `major` is the buffer's fifth
octet, its `minor` the sixth and its `revision` the seventh. -/

theorem ref_readHeader_ok (bytes : Octets)
    (h₁ : ¬ bytes.size < SpecAMQP.Ref.Connection.headerWidth)
    (h₂ : ¬ bytes.extract 0 4 != SpecAMQP.Ref.Connection.magic)
    (h₃ : SpecAMQP.Ref.Connection.speaksId (SpecAMQP.Ref.Connection.field bytes 4 1) = true)
    (v : Nat × Nat × Nat)
    (hv : SpecAMQP.Ref.Connection.statedVersion (SpecAMQP.Ref.Connection.field bytes 4 1) = some v)
    (hacc : (SpecAMQP.Ref.Connection.field bytes 5 1 == v.1 &&
      SpecAMQP.Ref.Connection.field bytes 6 1 == v.2.1 &&
      SpecAMQP.Ref.Connection.field bytes 7 1 == v.2.2) = true) :
    SpecAMQP.Ref.Connection.readHeader bytes =
      .ok ⟨SpecAMQP.Ref.Connection.field bytes 4 1, SpecAMQP.Ref.Connection.field bytes 5 1,
           SpecAMQP.Ref.Connection.field bytes 6 1, SpecAMQP.Ref.Connection.field bytes 7 1⟩ := by
  rcases v with ⟨a, b, c⟩
  have hacc' : (SpecAMQP.Ref.Connection.field bytes 5 1 == a &&
      SpecAMQP.Ref.Connection.field bytes 6 1 == b &&
      SpecAMQP.Ref.Connection.field bytes 7 1 == c) = true := hacc
  unfold SpecAMQP.Ref.Connection.readHeader
  rw [if_neg h₁, if_neg h₂, if_neg (by simp [h₃])]
  simp only [hv]
  exact if_pos hacc'

/-! ## The agreement -/

/-- Every header the reference reads is a header the specification reads, with the same protocol
id, the same three version octets and the octets the layout draws; and every buffer the reference
refuses the specification refuses. The two readers ask the same questions in the same order, and
the accept sets are the same set — `speaks_of_code_layer` and `statedVersion_eq` are where the two
trees' numbering and constant tables are shown to be one — so the case split over the reference's
questions lands each branch on the specification's matching branch. -/

theorem refHeader_matched (bytes : Octets) :
    (∀ h, SpecAMQP.Ref.Connection.readHeader bytes = .ok h →
      ∃ h' : SpecAMQP.Spec.Connection.ProtocolHeader,
        SpecAMQP.Spec.Connection.decodeHeader bytes = .ok h' ∧
        h'.protocolId.code = h.protocolId ∧ h'.version.major = h.major ∧
        h'.version.minor = h.minor ∧ h'.version.revision = h.revision ∧
        h'.octets = SpecAMQP.Ref.Connection.Header.octets h) ∧
    (∀ r, SpecAMQP.Ref.Connection.readHeader bytes = .error r →
      ∃ r', SpecAMQP.Spec.Connection.decodeHeader bytes = .error r') := by
  constructor
  · intro hdr hok
    have hw : ¬ bytes.size < SpecAMQP.Ref.Connection.headerWidth := by
      intro hlt
      obtain ⟨r', hr'⟩ := ref_readHeader_short bytes hlt
      exact absurd (hr'.symm.trans hok) (by simp)
    have hm : ¬ bytes.extract 0 4 != SpecAMQP.Ref.Connection.magic := by
      intro hmal
      obtain ⟨r', hr'⟩ := ref_readHeader_malformed bytes hw hmal
      exact absurd (hr'.symm.trans hok) (by simp)
    have hs : SpecAMQP.Ref.Connection.speaksId (SpecAMQP.Ref.Connection.field bytes 4 1) = true := by
      by_contra hns
      have hsf : SpecAMQP.Ref.Connection.speaksId
          (SpecAMQP.Ref.Connection.field bytes 4 1) = false := by
        cases hb : SpecAMQP.Ref.Connection.speaksId (SpecAMQP.Ref.Connection.field bytes 4 1) <;>
          simp_all
      obtain ⟨r', hr'⟩ := ref_readHeader_unspeaking bytes hw hm hsf
      exact absurd (hr'.symm.trans hok) (by simp)
    have hsome : ∃ w, SpecAMQP.Ref.Connection.statedVersion
        (SpecAMQP.Ref.Connection.field bytes 4 1) = some w := by
      by_contra hno
      have hnone : SpecAMQP.Ref.Connection.statedVersion
          (SpecAMQP.Ref.Connection.field bytes 4 1) = none := by
        cases hc : SpecAMQP.Ref.Connection.statedVersion
            (SpecAMQP.Ref.Connection.field bytes 4 1) with
        | none => rfl
        | some w => exact absurd ⟨w, hc⟩ hno
      obtain ⟨r', hr'⟩ := ref_readHeader_no_version bytes hw hm hs hnone
      exact absurd (hr'.symm.trans hok) (by simp)
    obtain ⟨v, hv⟩ := hsome
    have hacc : (SpecAMQP.Ref.Connection.field bytes 5 1 == v.1 &&
        SpecAMQP.Ref.Connection.field bytes 6 1 == v.2.1 &&
        SpecAMQP.Ref.Connection.field bytes 7 1 == v.2.2) = true := by
      by_contra hnac
      obtain ⟨r', hr'⟩ := ref_readHeader_version bytes hw hm hs v hv hnac
      exact absurd (hr'.symm.trans hok) (by simp)
    have hh : hdr = ⟨SpecAMQP.Ref.Connection.field bytes 4 1,
        SpecAMQP.Ref.Connection.field bytes 5 1, SpecAMQP.Ref.Connection.field bytes 6 1,
        SpecAMQP.Ref.Connection.field bytes 7 1⟩ := by
      have hr' := ref_readHeader_ok bytes hw hm hs v hv hacc
      exact (Except.ok.inj (hr'.symm.trans hok)).symm
    subst hdr
    obtain ⟨p, l, hp, hl, hpr⟩ :=
      speaks_of_code_layer (SpecAMQP.Ref.Connection.field bytes 4 1) hs
    have hpc : p.code = SpecAMQP.Ref.Connection.field bytes 4 1 := by
      rw [refProtoId_code p, hpr]
    have htab : (⟨v.1, v.2.1, v.2.2⟩ : SpecAMQP.Spec.Connection.Version) =
        ⟨SpecAMQP.Ref.Connection.field bytes 5 1, SpecAMQP.Ref.Connection.field bytes 6 1,
         SpecAMQP.Ref.Connection.field bytes 7 1⟩ := by
      have hc := hacc
      rw [Bool.and_eq_true, Bool.and_eq_true] at hc
      simp only [beq_iff_eq] at hc
      rw [← hc.1.1, ← hc.1.2, ← hc.2]
    have hvL : SpecAMQP.Spec.Connection.Layer.version l = some
        (⟨SpecAMQP.Spec.Connection.beAt bytes 5 1, SpecAMQP.Spec.Connection.beAt bytes 6 1,
          SpecAMQP.Spec.Connection.beAt bytes 7 1⟩ : SpecAMQP.Spec.Connection.Version) := by
      rw [statedVersion_eq p l hl, hpr, hv]
      exact congrArg some htab
    refine ⟨⟨p, ⟨SpecAMQP.Spec.Connection.beAt bytes 5 1, SpecAMQP.Spec.Connection.beAt bytes 6 1,
        SpecAMQP.Spec.Connection.beAt bytes 7 1⟩⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact spec_decodeHeader_ok bytes hw hm p hp l hl _ hvL rfl
    · exact hpc
    · rfl
    · rfl
    · rfl
    · unfold SpecAMQP.Spec.Connection.ProtocolHeader.octets SpecAMQP.Ref.Connection.Header.octets
      rw [hpc]
      rfl
  · intro r herr
    by_cases hw : bytes.size < SpecAMQP.Ref.Connection.headerWidth
    · exact spec_decodeHeader_short bytes hw
    · by_cases hm : bytes.extract 0 4 != SpecAMQP.Ref.Connection.magic
      · exact spec_decodeHeader_malformed bytes hw hm
      · by_cases hs : SpecAMQP.Ref.Connection.speaksId (SpecAMQP.Ref.Connection.field bytes 4 1) = true
        · cases hsv : SpecAMQP.Ref.Connection.statedVersion
              (SpecAMQP.Ref.Connection.field bytes 4 1) with
          | none =>
            obtain ⟨p, l, hp, hl, hpr⟩ :=
              speaks_of_code_layer (SpecAMQP.Ref.Connection.field bytes 4 1) hs
            have hvn : SpecAMQP.Spec.Connection.Layer.version l = none := by
              rw [statedVersion_eq p l hl, hpr, hsv]
              rfl
            exact spec_decodeHeader_no_version bytes hw hm p hp l hl hvn
          | some v =>
            by_cases hacc : (SpecAMQP.Ref.Connection.field bytes 5 1 == v.1 &&
                SpecAMQP.Ref.Connection.field bytes 6 1 == v.2.1 &&
                SpecAMQP.Ref.Connection.field bytes 7 1 == v.2.2) = true
            · exfalso
              have hr' := ref_readHeader_ok bytes hw hm hs v hsv hacc
              exact absurd (herr.symm.trans hr') (by simp)
            · obtain ⟨p, l, hp, hl, hpr⟩ :=
                speaks_of_code_layer (SpecAMQP.Ref.Connection.field bytes 4 1) hs
              have hne : ¬ ((⟨SpecAMQP.Spec.Connection.beAt bytes 5 1,
                  SpecAMQP.Spec.Connection.beAt bytes 6 1,
                  SpecAMQP.Spec.Connection.beAt bytes 7 1⟩ : SpecAMQP.Spec.Connection.Version) =
                    ⟨v.1, v.2.1, v.2.2⟩) := by
                intro heq
                injection heq with h1 h2 h3
                have h1' : SpecAMQP.Ref.Connection.field bytes 5 1 = v.1 := h1
                have h2' : SpecAMQP.Ref.Connection.field bytes 6 1 = v.2.1 := h2
                have h3' : SpecAMQP.Ref.Connection.field bytes 7 1 = v.2.2 := h3
                apply hacc
                rw [h1', h2', h3']
                simp
              have hvtab : SpecAMQP.Spec.Connection.Layer.version l =
                  some (⟨v.1, v.2.1, v.2.2⟩ : SpecAMQP.Spec.Connection.Version) := by
                rw [statedVersion_eq p l hl, hpr, hsv]
                rfl
              exact spec_decodeHeader_unsupported_version bytes hw hm p hp l hl
                (⟨v.1, v.2.1, v.2.2⟩ : SpecAMQP.Spec.Connection.Version) hvtab hne
        · have hn : ¬ (SpecAMQP.Ref.Connection.field bytes 4 1 = 0 ∨
              SpecAMQP.Ref.Connection.field bytes 4 1 = 3) := by
            intro hc
            have htrue : SpecAMQP.Ref.Connection.speaksId
                (SpecAMQP.Ref.Connection.field bytes 4 1) = true := (speaksId_iff _).mpr hc
            exact hs htrue
          by_cases h2 : SpecAMQP.Ref.Connection.field bytes 4 1 = 2
          · have hft : SpecAMQP.Spec.Connection.ProtocolId.ofCode
                (SpecAMQP.Spec.Connection.beAt bytes 4 1) =
                some SpecAMQP.Spec.Connection.ProtocolId.tls := by
              rw [show SpecAMQP.Spec.Connection.beAt bytes 4 1 = 2 from h2]
              rfl
            exact spec_decodeHeader_unspoken_layer bytes hw hm
              SpecAMQP.Spec.Connection.ProtocolId.tls hft rfl
          · have hfn : SpecAMQP.Spec.Connection.ProtocolId.ofCode
                (SpecAMQP.Spec.Connection.beAt bytes 4 1) = none := by
              rw [show SpecAMQP.Spec.Connection.beAt bytes 4 1 =
                SpecAMQP.Ref.Connection.field bytes 4 1 from rfl, ofCode_eq_none_iff]
              exact ⟨fun h => hn (Or.inl h), h2, fun h => hn (Or.inr h)⟩
            exact spec_decodeHeader_unknown_id bytes hw hm hfn

/-! #### 40_endpoints.lean -/

/-! ## The api channel, and what each endpoint reads out of it -/

/-- The name an api call must carry to be a send. -/

def sendName : String := "send"

/-- The api call that asks an endpoint to send octets.

The interface's `ApiCall` carries strings and the wire is octets, so a call carries the octets
hex-encoded, and both endpoints read the argument with the *same* harness decoder — so the octets are
one term on both sides rather than two decoders' readings of one string. What the layer then writes is
the octets it was handed, because that is what its own vocabulary says: `Submission.frame` and
`Offer.frame` carry the octets the caller's encoder produced, and the layer's answer is those octets. -/

def sendCall (octets : Octets) : ApiCall :=
  { name := sendName, arguments := [toHex octets] }

/-- The octets a call asks the endpoint to send, or `none` for a call that is not a send. -/

def callOctets (call : ApiCall) : Option Octets :=
  if call.name = sendName then
    match call.arguments with
    | arg :: _ => match ofHex arg with
      | .ok octets => some octets
      | .error _ => none
    | [] => none
  else none

/-- The api channel is live: this call is read as a send of exactly these octets. A witness rather than
a general inverse, because an interpretation that answered `none` to every call would make the send
direction vacuous — what the theorem needs of the decoder is only that both endpoints run the *same*
one, which is why the harness's decoder is shared. -/

theorem callOctets_sendCall (octets : Octets) (h : ofHex (toHex octets) = .ok octets) :
    callOctets (sendCall octets) = some octets := by
  show (match ofHex (toHex octets) with
        | .ok received => some received
        | .error _ => none) = some octets
  rw [h]

/-- The submission the specification's endpoint reads out of a call.

Octets that begin the way a protocol header does are the header they are — a protocol header is not a
frame, so a call carrying one can only mean that — and anything else is a frame, which the endpoint's
own frame layer reads, because the layer needs the channel and the body to decide whether to send it.
A header this peer does not speak, or octets that are not a frame, are a call the endpoint has no
answer for rather than a step: this is the reading `Spec.ConnectionCodec.submissionOf` already applies
to a send step in the corpus, and it is applied here for the same reason. -/

def specSubmissionOf (call : ApiCall) : Option SpecAMQP.Spec.Connection.Submission :=
  match callOctets call with
  | none => none
  | some octets =>
    if SpecAMQP.Spec.Connection.headerShaped octets then
      match SpecAMQP.Spec.Connection.decodeHeader octets with
      | .ok header => some (.header header)
      | .error _ => none
    else
      match SpecAMQP.Spec.Frame.decodeFrame octets with
      | .ok (frame, _) => some (.frame frame.channel octets frame.body)
      | .error _ => none

/-- The offer the reference's endpoint reads out of the same call. -/

def refOfferOf (call : ApiCall) : Option SpecAMQP.Ref.Connection.Offer :=
  match callOctets call with
  | none => none
  | some octets =>
    if SpecAMQP.Ref.Connection.looksLikeHeader octets then
      match SpecAMQP.Ref.Connection.readHeader octets with
      | .ok header => some (.header header)
      | .error _ => none
    else
      match SpecAMQP.Ref.Frame.decodeFrame octets with
      | .ok (frame, _) => some (.frame frame.channel octets frame.body)
      | .error _ => none

/-! ## What an endpoint hands back, and the two endpoints -/

/-- The interface's bytes, from the specification's octets.

`Contracts.Conformance` carries the wire as `ByteArray` — `Input.frame` and `Output.frame` both take
one — while the connection layer's octets are `Harness.Octets`, which is `Array UInt8`; they are
different types, and this is the first instance to put anything on the `frame` channel. The two
functions are `ByteArray.mk` and `ByteArray.data`, which are `rfl`-inverses of each other, so nothing
is copied and nothing is decided here: every byte the layer writes reaches the interface unchanged.
Both endpoints convert with the *same* pair, which is what makes an output comparison a comparison of
the layer's own octets rather than of two renderings of them. -/

def toBytes (octets : Octets) : ByteArray := ByteArray.mk octets

/-- The specification's octets, from the interface's bytes. -/

def toOctets (bytes : ByteArray) : Octets := bytes.data

/-- The two conversions are inverses, which is the whole of what the instance needs of them. -/

theorem toOctets_toBytes (octets : Octets) : toOctets (toBytes octets) = octets := rfl

/-- And in the other direction, which is the direction an input takes. -/

theorem toBytes_toOctets (bytes : ByteArray) : toBytes (toOctets bytes) = bytes := rfl

/-- The octets written, on the wire, as the interface carries them. -/

def wireOutput (wrote : List Octets) : List Output := wrote.map (fun octets => Output.frame (toBytes octets))

/-- The answer to a call the endpoint took: the state table's own name, which is the one thing both
layers name the same way and the one the corpus pins. -/

def tookAnswer (stateName : String) : Output := Output.api ⟨stateName, true⟩

/-- The answer to a refusal: the protocol condition, then the reason class. Both are interface —
§10 rule 5 makes the mandated error code part of the observable, and the corpus compares the class as
well as the condition — and neither is recoverable from the other. The class is a term on both sides,
which is why it can be compared at all. -/

def refusedAnswer (condition reasonClass : String) : List Output :=
  [Output.api ⟨condition, false⟩, Output.api ⟨reasonClass, false⟩]

/-- The specification's answer to one step, as the pair the interface returns. The refusal a step
returns is already placed — `Spec.Connection.step` applies `Refusal.withPlace` before answering — so
this only has to move the endpoint's state to where the refusal left it. -/

def specAnswerOf (s : SpecAMQP.Spec.Connection.Endpoint)
    (answer : Except SpecAMQP.Spec.Connection.Refusal SpecAMQP.Spec.Connection.Outcome) :
    SpecAMQP.Spec.Connection.Endpoint × List Output :=
  match answer with
  | .ok outcome => (outcome.endpoint, wireOutput outcome.wrote ++ [tookAnswer outcome.endpoint.state.name])
  | .error reason =>
    ({ s with state := reason.state.getD s.state },
      wireOutput reason.wrote ++ refusedAnswer reason.condition reason.reasonClass)

/-- The octets the reference's answer writes, from the offer it was given: the layer's own vocabulary
says the caller supplies them, and `apply` returns the peer alone, so this is where the wire comes from
on that side. It is exactly the same list the specification's layer builds internally — including the one
case that is not "the octets I was handed when I am sending": a frame with no body is admitted writing
nothing in either direction, on both sides, so a send of an empty frame puts no octets on the wire. What
checks this list is the simulation below, which compares it against the octets the specification's own
`Outcome` reports. -/

def refOfferWrote (outbound : Bool) (offer : SpecAMQP.Ref.Connection.Offer) : List Octets :=
  match offer with
  | .header header => if outbound then [header.octets] else []
  | .frame _ _ none => []
  | .frame _ octets (some _) => if outbound then [octets] else []
  | .arrives _ => []

/-- The reference's answer to one step, as the same pair. -/

def refAnswerOf (i : SpecAMQP.Ref.Connection.Peer) (outbound : Bool)
    (offer : SpecAMQP.Ref.Connection.Offer)
    (answer : Except SpecAMQP.Ref.Connection.Refusal SpecAMQP.Ref.Connection.Peer) :
    SpecAMQP.Ref.Connection.Peer × List Output :=
  match answer with
  | .ok peer => (peer, wireOutput (refOfferWrote outbound offer) ++ [tookAnswer peer.state.label])
  | .error reason =>
    ({ i with state := reason.place.getD i.state },
      wireOutput reason.reply ++ refusedAnswer reason.condition reason.reasonClass)

/-- The specification's answer to one arriving buffer, in the layer's own terms. -/

def specArriving (s : SpecAMQP.Spec.Connection.Endpoint) (bytes : Octets) :
    SpecAMQP.Spec.Connection.Endpoint × List Output :=
  specAnswerOf s (SpecAMQP.Spec.Connection.step s false (.arriving bytes))

/-- The specification's answer to one submission it is asked to send. -/

def specSending (s : SpecAMQP.Spec.Connection.Endpoint)
    (sub : SpecAMQP.Spec.Connection.Submission) :
    SpecAMQP.Spec.Connection.Endpoint × List Output :=
  specAnswerOf s (SpecAMQP.Spec.Connection.step s true sub)

/-- The reference's answer to one arriving buffer. -/

def refArriving (i : SpecAMQP.Ref.Connection.Peer) (bytes : Octets) :
    SpecAMQP.Ref.Connection.Peer × List Output :=
  refAnswerOf i false (.arrives bytes) (SpecAMQP.Ref.Connection.apply i false (.arrives bytes))

/-- The reference's answer to one offer it is asked to send. -/

def refSending (i : SpecAMQP.Ref.Connection.Peer) (offer : SpecAMQP.Ref.Connection.Offer) :
    SpecAMQP.Ref.Connection.Peer × List Output :=
  refAnswerOf i true offer (SpecAMQP.Ref.Connection.apply i true offer)

/-- The specification's step over the interface's alphabet: an arriving buffer is the layer's own
question to answer, a call that reads as a send is one it is asked to take, a call it cannot read is one
it has no answer for, and a tick is time crossing with nothing behind it in this layer. -/

def specConnStep (s : SpecAMQP.Spec.Connection.Endpoint) (inp : Input) :
    Option (SpecAMQP.Spec.Connection.Endpoint × List Output) :=
  match inp with
  | .frame bytes => some (specArriving s (toOctets bytes))
  | .api call => (specSubmissionOf call).map (specSending s)
  | .tick _ => none

/-- The reference's step over the same alphabet, the same way. -/

def refConnStep (i : SpecAMQP.Ref.Connection.Peer) (inp : Input) :
    Option (SpecAMQP.Ref.Connection.Peer × List Output) :=
  match inp with
  | .frame bytes => some (refArriving i (toOctets bytes))
  | .api call => (refOfferOf call).map (refSending i)
  | .tick _ => none

/-- The specification as an endpoint: every permitted outcome is the layer's own step's outcome and
nothing else, because this layer's step is a function of endpoint, direction and submission — there is
no policy argument and no branch on one, so there is no `MAY` for `choose` to be a set of. -/

def specConn : Endpoint SpecAMQP.Spec.Connection.Endpoint where
  init := SpecAMQP.Spec.Connection.Endpoint.initial
  step := specConnStep
  choose := fun s inp => {out | specConnStep s inp = some out}

/-- The reference as an endpoint. `ConformsVia` never consults an implementation's `choose` — an
implementation has none — which is why the field is empty here rather than a second set that could
drift from the specification's. -/

def refConn : Endpoint SpecAMQP.Ref.Connection.Peer where
  init := SpecAMQP.Ref.Connection.Peer.new
  step := refConnStep
  choose := fun _ _ => ∅

/-- **The relation.** The reference's peer *is* the specification's endpoint under the layer's own naming
map: the state table's state, the protocol layer, the dialogue's stage, which end announced the
mechanisms, the announced mechanisms, and the two sides' limits. It is an equality of the mapped record
rather than a conjunction of clauses because every field is one the layer reads, and a relation that
would leave any of them free would let the two sides answer the same input differently. -/

def RConn (s : SpecAMQP.Spec.Connection.Endpoint) (i : SpecAMQP.Ref.Connection.Peer) : Prop :=
  refPeerOf s = i

/-! #### 60_tieback.lean -/

/-! ## The tie-back: what the endpoint permits is the layer's step -/

/-- A member of `choose` is a step the endpoint takes, which is what defines `choose` rather than a
coincidence about it. -/

theorem specConnection_choose_member (s : SpecAMQP.Spec.Connection.Endpoint) (inp : Input)
    (out : SpecAMQP.Spec.Connection.Endpoint × List Output) :
    out ∈ specConn.choose s inp ↔ specConn.step s inp = some out := Iff.rfl

/-- **The tie-back, in the layer's own vocabulary.**

An outcome the endpoint permits is exactly the connection layer's own step's answer: an arriving buffer
answered with an endpoint and the state it left in, or a call read as a submission and answered the
same way, or a refusal whose condition, class, placement and octets are the layer's own. It is stated
against `Spec.Connection.step` — the layer's transition relation, whose `Outcome` and `Refusal` are what
a caller and the corpus see — rather than against the endpoint's wrapper, because a `choose` tied only
to its own wrapper is a proof about a relation the specification does not have.

The last arm is the one a widened `choose` breaks: a tick crossing is not a step this layer takes — it
has no timer and no threshold behind it — so nothing is permitted, and a `choose` of `Set.univ` would
permit every outcome there. -/

theorem specConnection_choose_is_the_step (s : SpecAMQP.Spec.Connection.Endpoint) (inp : Input)
    (s' : SpecAMQP.Spec.Connection.Endpoint) (outs : List Output) :
    (s', outs) ∈ specConn.choose s inp ↔
      match inp with
      | .frame bytes =>
        (∃ outcome : SpecAMQP.Spec.Connection.Outcome,
            SpecAMQP.Spec.Connection.step s false (.arriving (toOctets bytes)) = .ok outcome ∧
            s' = outcome.endpoint ∧
            outs = wireOutput outcome.wrote ++ [tookAnswer outcome.endpoint.state.name]) ∨
        (∃ reason : SpecAMQP.Spec.Connection.Refusal,
            SpecAMQP.Spec.Connection.step s false (.arriving (toOctets bytes)) = .error reason ∧
            s' = { s with state := reason.state.getD s.state } ∧
            outs = wireOutput reason.wrote ++ refusedAnswer reason.condition reason.reasonClass)
      | .api call =>
        ∃ sub : SpecAMQP.Spec.Connection.Submission,
          specSubmissionOf call = some sub ∧
          ((∃ outcome : SpecAMQP.Spec.Connection.Outcome,
              SpecAMQP.Spec.Connection.step s true sub = .ok outcome ∧
              s' = outcome.endpoint ∧
              outs = wireOutput outcome.wrote ++ [tookAnswer outcome.endpoint.state.name]) ∨
           (∃ reason : SpecAMQP.Spec.Connection.Refusal,
              SpecAMQP.Spec.Connection.step s true sub = .error reason ∧
              s' = { s with state := reason.state.getD s.state } ∧
              outs = wireOutput reason.wrote ++
                refusedAnswer reason.condition reason.reasonClass))
      | .tick _ => False := by
  rw [specConnection_choose_member]
  unfold specConn specConnStep
  dsimp only []
  cases inp with
  | frame bytes =>
    cases h : SpecAMQP.Spec.Connection.step s false (.arriving (toOctets bytes)) with
    | ok outcome => simp only [h, specArriving, specAnswerOf]; grind
    | error reason => simp only [h, specArriving, specAnswerOf]; grind
  | api call =>
    cases h : specSubmissionOf call with
    | none => simp [h]
    | some sub =>
      cases hstep : SpecAMQP.Spec.Connection.step s true sub with
      | ok outcome => simp only [h, hstep, Option.map_some, specSending, specAnswerOf]; grind
      | error reason => simp only [h, hstep, Option.map_some, specSending, specAnswerOf]; grind
  | tick t => simp

/-- A tick is not a step this layer takes: the tie-back's last arm, stated on its own so that a widened
`choose` is a failing theorem rather than a comment. -/

theorem specConnection_no_tick (s : SpecAMQP.Spec.Connection.Endpoint) (t : Tick)
    (out : SpecAMQP.Spec.Connection.Endpoint × List Output) :
    out ∉ specConn.choose s (.tick t) := by
  rw [specConnection_choose_is_the_step]
  simp

/-! #### 70_step_answers.lean -/

/-!
# What a step answers, and what each step slice needs of the two bodies

The composition below compares one step's answer on the two sides. Three step slices prove that
comparison — one per dispatch the layer has (`stepHeader`, `stepAmqpFrame`, `stepSaslFrame`) — and
each is stated against the vocabulary here, so that the slices are independent of the value relation
and the composition is where the relation is discharged.

`AnswersMatch` is the comparison: what the specification answered, what the reference answered, and
what makes them the same answer. It is stated over the two layers' *step* functions — the guards
this module's dispatcher has not yet added — so the header exchange, the AMQP frame and the SASL
dialogue are each proved on their own.

`FrameCorresponds` and `SaslCorresponds` are what each slice needs of the two bodies, field by field:
each is a question the slice's guards ask, and proving them from `ValuesAgree` is the value slice's
deliverable, discharged at the point of use rather than assumed inside the slices.
-/

/-- **One step's answer, paired.** What the specification answered, what the reference answered, and
what makes them the same answer: the states are related, the octets written agree, and a refusal agrees
in the condition it names, in the reason class it names, in where it leaves the peer, and in the octets
it writes. The class is here rather than recovered from the detail because it is what the corpus
compares, and both layers carry it as a field.

The write list is a parameter rather than the specification's own, because the two sides learn it
differently: `Spec.Connection.step` *returns* the octets it wrote, while `Ref.Connection.apply` returns
the peer alone and the reference's wrapper supplies the octets the caller handed over. Stating it as a
parameter is what makes the two comparable and puts the wrapper's own definition of the reference's
writes in the composition, where `refOfferWrote` lives. -/

def AnswersMatch (so : Except Spec.Connection.Refusal Spec.Connection.Outcome)
    (ro : Except Ref.Connection.Refusal Ref.Connection.Peer) (wrote : List Octets) : Prop :=
  (∀ out, so = .ok out →
      ∃ i', ro = .ok i' ∧ refPeerOf out.endpoint = i' ∧ out.wrote = wrote) ∧
  (∀ r', ro = .error r' →
      ∃ r, so = .error r ∧ r.condition = r'.condition ∧ r.reasonClass = r'.reasonClass ∧
        r.state.map refState = r'.place ∧ r.wrote = r'.reply)

/-- **The vacuity is asymmetric, in the direction that matters.** The two conjuncts are keyed in
opposite directions — the first on the specification accepting, the second on the reference refusing —
so an answer the specification refuses and the reference accepts satisfies the relation however the
two answers differ: both antecedents are false. This is that fact, and it is the reason a step slice's
`isOk` agreement is part of the composition's vocabulary rather than a convenience. -/

theorem answersMatch_of_spec_refuses (r : Spec.Connection.Refusal) (i' : Ref.Connection.Peer)
    (wrote : List Octets) : AnswersMatch (.error r) (.ok i') wrote :=
  ⟨fun out hout => absurd hout (by simp), fun r' hr' => absurd hr' (by simp)⟩

/-- And the other mismatch is not vacuous: a specification that accepts demands that the reference
accept, so a reference that refuses while the specification accepts fails the relation outright. -/

theorem not_answersMatch_of_ref_refuses (out : Spec.Connection.Outcome)
    (r' : Ref.Connection.Refusal) (wrote : List Octets) :
    ¬ AnswersMatch (.ok out) (.error r') wrote := by
  intro h
  obtain ⟨i', hro, _⟩ := h.1 out rfl
  exact absurd hro (by simp)

/-- What the AMQP-layer frame step needs of the two bodies and the two endpoints: every question its
guards ask, answered the same way on both sides. The two column fields carry the hypothesis the two
guards supply — the AMQP step refuses a SASL role before the column is consulted, on both sides — which
is exactly where `permitsSend_eq` and `permitsReceive_eq` are stated. -/

structure FrameCorresponds (s : Spec.Connection.Endpoint) (i : Ref.Connection.Peer)
    (outbound : Bool) (sbody : Spec.Codec.Value) (rbody : Ref.Value) : Prop where
  /-- the frame's role, which decides which dispatch runs and which performatives the state admits -/
  role : refRoleKind (Spec.Connection.roleOfBody sbody) = Ref.Connection.kindOfBody rbody
  /-- the table's send column, asked of the state the frame would be sent from -/
  send : Spec.Connection.roleOfBody sbody ≠ Spec.Connection.FrameRole.sasl →
    Spec.Connection.permitsSend s.state (Spec.Connection.roleOfBody sbody) =
      Ref.Connection.maySend i.state (Ref.Connection.kindOfBody rbody)
  /-- and its receive column -/
  receive : Spec.Connection.roleOfBody sbody ≠ Spec.Connection.FrameRole.sasl →
    Spec.Connection.permitsReceive s.state (Spec.Connection.roleOfBody sbody) =
      Ref.Connection.mayReceive i.state (Ref.Connection.kindOfBody rbody)
  /-- the declared surface's mandatory-field rule, for the two performatives this layer reads itself -/
  mandatoryOpen : Spec.Connection.missingMandatory "open" sbody =
    Ref.Connection.missingMandatory "open" rbody
  mandatoryClose : Spec.Connection.missingMandatory "close" sbody =
    Ref.Connection.missingMandatory "close" rbody
  /-- the limits the frame's size and channel are measured against -/
  limits : refBounds (Spec.Connection.limitsFor s outbound) =
    Ref.Connection.boundsFor i outbound
  /-- the limits an `open` declares: both read them, and they agree -/
  declaredOk : ∀ (l : Spec.Connection.Limits) (m : Ref.Connection.Bounds),
    Spec.Connection.openLimits sbody = .ok l →
      Ref.Connection.openBounds rbody = .ok m → refBounds l = m
  declaredShape : (∃ l, Spec.Connection.openLimits sbody = .ok l) ↔
    (∃ m, Ref.Connection.openBounds rbody = .ok m)

/-- What the SASL step needs of the two bodies: the performative each names, the fields the
dialogue reads, and the field-value rules the arms enforce. The five name fields are equalities of the
two *readings* rather than of two names, because the two layers ask the question differently — one
matches the declared type's name against its five performatives, the other returns the name and the arm
compares it.

Three groups rather than one, because the arms ask three kinds of question. The five `mandatory…`
fields are the declared surface's mandatory rule, asked of each performative's own type name — the same
rule `FrameCorresponds` carries for `open` and `close`. `codeOk` and `codeShape` are the `sasl-outcome`'s
code, read through the declared-type check rather than through the value's shape, so they are the
`Except`-shaped pair `FrameCorresponds.declaredOk`/`declaredShape` are for the `open`'s limits.
`additionalData` is whether the artifact's "this field is not set" holds of the failure outcome. The
`code` name question needs no field: the two layers name a declared code with the same function. -/

structure SaslCorresponds (s : Spec.Connection.Endpoint) (i : Ref.Connection.Peer)
    (sbody : Spec.Codec.Value) (rbody : Ref.Value) : Prop where
  mechanisms : (Spec.Connection.SaslFrame.ofBody sbody == .mechanisms) =
    (Ref.Connection.saslName rbody == "sasl-mechanisms")
  init : (Spec.Connection.SaslFrame.ofBody sbody == .init) =
    (Ref.Connection.saslName rbody == "sasl-init")
  challenge : (Spec.Connection.SaslFrame.ofBody sbody == .challenge) =
    (Ref.Connection.saslName rbody == "sasl-challenge")
  response : (Spec.Connection.SaslFrame.ofBody sbody == .response) =
    (Ref.Connection.saslName rbody == "sasl-response")
  outcome : (Spec.Connection.SaslFrame.ofBody sbody == .outcome) =
    (Ref.Connection.saslName rbody == "sasl-outcome")
  declared : Spec.Connection.symbolsOf
      ((Spec.Connection.fieldValue "sasl-mechanisms" "sasl-server-mechanisms" sbody).getD
        .null) =
    Ref.Connection.symbolList
      ((Ref.Connection.valueOfField "sasl-mechanisms" "sasl-server-mechanisms" rbody).getD
        .null)
  chosen : (match Spec.Connection.fieldValue "sasl-init" "mechanism" sbody with
      | some (.symbol t) => t
      | _ => "") =
    (match Ref.Connection.valueOfField "sasl-init" "mechanism" rbody with
      | some (.symbol t) => t
      | _ => "")
  /-- the declared surface's mandatory rule, for the mechanisms the dialogue begins with -/
  mandatoryMechanisms : Spec.Connection.missingMandatory "sasl-mechanisms" sbody =
    Ref.Connection.missingMandatory "sasl-mechanisms" rbody
  /-- the same, for the init that chooses a mechanism -/
  mandatoryInit : Spec.Connection.missingMandatory "sasl-init" sbody =
    Ref.Connection.missingMandatory "sasl-init" rbody
  /-- the same, for the server's challenge -/
  mandatoryChallenge : Spec.Connection.missingMandatory "sasl-challenge" sbody =
    Ref.Connection.missingMandatory "sasl-challenge" rbody
  /-- the same, for the client's response -/
  mandatoryResponse : Spec.Connection.missingMandatory "sasl-response" sbody =
    Ref.Connection.missingMandatory "sasl-response" rbody
  /-- the same, for the outcome that closes the dialogue -/
  mandatoryOutcome : Spec.Connection.missingMandatory "sasl-outcome" sbody =
    Ref.Connection.missingMandatory "sasl-outcome" rbody
  /-- the outcome's code, read through the declared type both layers check first: the two reads agree
  on the number they carry -/
  codeOk : ∀ (n m : Nat), Spec.Connection.intField "sasl-outcome" "code" sbody = .ok n →
    Ref.Connection.integerField "sasl-outcome" "code" rbody = .ok m → n = m
  /-- and they either both read a code or both refuse -/
  codeShape : (∃ n, Spec.Connection.intField "sasl-outcome" "code" sbody = .ok n) ↔
    (∃ m, Ref.Connection.integerField "sasl-outcome" "code" rbody = .ok m)
  /-- whether the failure outcome sets the field the artifact says an unsuccessful outcome leaves
  unset -/
  additionalData : Spec.Connection.fieldSet "sasl-outcome" "additional-data" sbody =
    Ref.Connection.declaredFieldSet "sasl-outcome" "additional-data" rbody

/-! #### 40_value_bundles.lean -/

/-!
# What the connection layer reads of a body, preserved

The value slice: the relation `ValuesAgree` above is what the connection layer's decisions rest on, and
this section is the set of facts that make it usable — one read per lemma, each of the questions the
two layers' guards ask of a body, answered the same way on both sides.

It is a section of this module rather than a module of its own because `ValuesAgree` is declared here:
the relation is the connection layer's own hypothesis (a value layer's instance would produce it), and
its consequences are stated where the structure the layers are compared with is, so that the discharges
below can project them without a second module boundary.
-/

theorem pairAgree_iff (p : SpecAMQP.Spec.Codec.Value × SpecAMQP.Spec.Codec.Value)
    (q : SpecAMQP.Ref.Value × SpecAMQP.Ref.Value) :
    PairAgree p q ↔ (ValuesAgree p.1 q.1 ∧ ValuesAgree p.2 q.2) := by
  constructor
  · intro hp
    cases hp with
    | mk h1 h2 => exact ⟨h1, h2⟩
  · intro hp
    exact .mk hp.1 hp.2

/-- The `map` clause's relation is elementwise agreement of the pairs' components, in wire
order. -/
theorem forall₂_pairAgree_iff :
    (ps : List (SpecAMQP.Spec.Codec.Value × SpecAMQP.Spec.Codec.Value)) →
    (qs : List (SpecAMQP.Ref.Value × SpecAMQP.Ref.Value)) →
    (List.Forall₂ PairAgree ps qs ↔
      List.Forall₂ (fun p q => ValuesAgree p.1 q.1 ∧ ValuesAgree p.2 q.2) ps qs)
  | [], [] => Iff.intro (fun _ => .nil) (fun _ => .nil)
  | [], _ :: _ => Iff.intro (fun h => nomatch h) (fun h => nomatch h)
  | _ :: _, [] => Iff.intro (fun h => nomatch h) (fun h => nomatch h)
  | _ :: _, _ :: _ => by
    rw [List.forall₂_cons, List.forall₂_cons]
    constructor
    · intro hp
      exact ⟨(pairAgree_iff _ _).mp hp.1, (forall₂_pairAgree_iff _ _).mp hp.2⟩
    · intro hp
      exact ⟨(pairAgree_iff _ _).mpr hp.1, (forall₂_pairAgree_iff _ _).mpr hp.2⟩

/-- The index lemma the item read needs, abstractly over the relation: elementwise-related
lists have related elements at every index, either direction, and one runs out exactly
where the other does.

The forward direction lifts the specification's element read to the reference's; the
backward direction is what a layer needs when it inspects an element it chose; the run-out
agreement is what makes "no element here" the same fact on both sides, which is the
precondition of the trailing-null rule every field lookup rests on. -/
theorem forall₂_index {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) :
    (∀ (i : Nat) (x : α), xs[i]? = some x → ∃ y, ys[i]? = some y ∧ R x y) ∧
    (∀ (i : Nat) (y : β), ys[i]? = some y → ∃ x, xs[i]? = some x ∧ R x y) ∧
    (∀ i : Nat, (xs[i]? = none) ↔ (ys[i]? = none)) := by
  induction h with
  | nil => refine ⟨?_, ?_, ?_⟩ <;> simp
  | cons hr ht ih =>
    refine ⟨?_, ?_, ?_⟩
    · intro i x hx
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero] at hx
        rw [Option.some.injEq] at hx
        rw [← hx]
        exact ⟨_, rfl, hr⟩
      | succ i =>
        simp only [List.getElem?_cons_succ] at hx
        obtain ⟨y, hy, hry⟩ := ih.1 i x hx
        exact ⟨y, by simpa using hy, hry⟩
    · intro i y hy
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero] at hy
        rw [Option.some.injEq] at hy
        rw [← hy]
        exact ⟨_, rfl, hr⟩
      | succ i =>
        simp only [List.getElem?_cons_succ] at hy
        obtain ⟨x, hx, hrx⟩ := ih.2.1 i y hy
        exact ⟨x, by simpa using hx, hrx⟩
    · intro i
      cases i with
      | zero => simp
      | succ i => simpa using ih.2.2 i

/-- Agreement decides null-ness: the field read treats a null field as unset, so the two
sides must call the same values null. -/
theorem ValuesAgree.null_iff {a : SpecAMQP.Spec.Codec.Value} {b : SpecAMQP.Ref.Value}
    (h : ValuesAgree a b) : (a = .null) ↔ (b = .null) := by
  cases h <;> simp

/-- The primitive type name both layers spell: `typeName` on the specification's side,
`primitiveName` on the reference's. Both `fieldTypeRefusal?` and `integerField` compare a
value's name with the field's declared type, so the names agreeing is what makes the
refusal fire on both sides or on neither. -/
theorem ValuesAgree.typeName_eq {a : SpecAMQP.Spec.Codec.Value} {b : SpecAMQP.Ref.Value}
    (h : ValuesAgree a b) :
    SpecAMQP.Spec.Codec.typeName a = SpecAMQP.Ref.Connection.primitiveName b := by
  cases h <;> rfl

/-- The integer number both layers read: `valueNat` reads every unsigned width and
`numberOf` every integer width, and the clauses keep them equal, so an `open`'s
`max-frame-size` and `channel-max` and a SASL outcome's `code` are the same number on
both sides. -/
theorem ValuesAgree.number_eq {a : SpecAMQP.Spec.Codec.Value} {b : SpecAMQP.Ref.Value}
    (h : ValuesAgree a b) :
    SpecAMQP.Spec.Connection.valueNat a = SpecAMQP.Ref.Connection.numberOf b := by
  cases h <;>
    first
      | rfl
      | simp_all [SpecAMQP.Spec.Connection.valueNat, SpecAMQP.Ref.Connection.numberOf]

/-- The symbolic payload of a value, on the specification's side. A definition rather than
a `match` written into each statement: a `match` whose discriminant is a variable of the
statement's own context makes Lean generalise the hypothesis that depends on it, and the
statement's type then carries that hypothesis inside the `match`, which no caller can use
without knowing the elaboration's shape. -/
private def specSymbol? : SpecAMQP.Spec.Codec.Value → Option String
  | .symbol t => some t
  | _ => none

/-- The symbolic payload of a value, on the reference's side. -/
private def refSymbol? : SpecAMQP.Ref.Value → Option String
  | .symbol t => some t
  | _ => none

/-- Agreement decides the symbolic payload: the read that takes the text of a `symbol` and
nothing of every other value gets the same answer on both sides, so the two sides are
symbols of the same text or non-symbols together. -/
theorem ValuesAgree.symbol_eq {a : SpecAMQP.Spec.Codec.Value} {b : SpecAMQP.Ref.Value}
    (h : ValuesAgree a b) : specSymbol? a = refSymbol? b := by
  cases h <;>
    first
      | rfl
      | simp_all [specSymbol?, refSymbol?]

/-- The symbolic payload as *text*, the projection the SASL `mechanism` read makes. -/
private def specSymbolText : SpecAMQP.Spec.Codec.Value → String
  | .symbol t => t
  | _ => ""

/-- The same, on the reference's side. -/
private def refSymbolText : SpecAMQP.Ref.Value → String
  | .symbol t => t
  | _ => ""

/-- Agreement decides the symbolic text as well as the symbolic payload. -/
theorem ValuesAgree.symbolText_eq {a : SpecAMQP.Spec.Codec.Value} {b : SpecAMQP.Ref.Value}
    (h : ValuesAgree a b) : specSymbolText a = refSymbolText b := by
  cases h <;>
    first
      | rfl
      | simp_all [specSymbolText, refSymbolText]

/-- `filterMap` of two elementwise-related lists, for any two projections that agree on
related elements. This is what turns elementwise agreement of the body's items into the
symbol list a `multiple` field carries. -/
private theorem filterMap_forall₂ {α β γ : Type} {R : α → β → Prop} {f : α → Option γ}
    {g : β → Option γ} {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys)
    (hp : ∀ x y, R x y → f x = g y) : xs.filterMap f = ys.filterMap g := by
  induction h with
  | nil => rfl
  | cons hr ht ih =>
    rw [List.filterMap_cons, List.filterMap_cons, hp _ _ hr]
    split <;> simp [ih]

/-- The symbol list a `multiple` field carries — a SASL mechanisms announcement, or an
array of symbols — read by `symbolsOf` and `symbolList`. -/
theorem ValuesAgree.symbols_eq {a : SpecAMQP.Spec.Codec.Value} {b : SpecAMQP.Ref.Value}
    (h : ValuesAgree a b) :
    SpecAMQP.Spec.Connection.symbolsOf a = SpecAMQP.Ref.Connection.symbolList b := by
  cases h
  case symbol heq =>
    simp only [SpecAMQP.Spec.Connection.symbolsOf, SpecAMQP.Ref.Connection.symbolList, heq]
  case list hfa =>
    exact filterMap_forall₂ hfa (fun x y hxy => ValuesAgree.symbol_eq hxy)
  case array heq hfa =>
    exact filterMap_forall₂ hfa (fun x y hxy => ValuesAgree.symbol_eq hxy)
  all_goals rfl

/-- Elementwise agreement of the items a described body holds. -/
private theorem described_items_forall₂ {d : SpecAMQP.Spec.Codec.Value}
    {db : SpecAMQP.Ref.Value} {v : SpecAMQP.Spec.Codec.Value} {w : SpecAMQP.Ref.Value}
    (h : ValuesAgree v w) :
    List.Forall₂ ValuesAgree (SpecAMQP.Spec.Connection.itemsOf (.described d v))
      (SpecAMQP.Ref.Connection.fieldList (.described db w)) := by
  cases h
  case list hfa => exact hfa
  all_goals exact .nil

/-- The item lists of two agreeing values agree elementwise. -/
private theorem items_forall₂ {a : SpecAMQP.Spec.Codec.Value} {b : SpecAMQP.Ref.Value}
    (h : ValuesAgree a b) :
    List.Forall₂ ValuesAgree (SpecAMQP.Spec.Connection.itemsOf a)
      (SpecAMQP.Ref.Connection.fieldList b) := by
  cases h
  case described hd hv => exact described_items_forall₂ hv
  all_goals exact .nil

/-- The element list read by index, both directions, plus the run-out agreement: a
`multiple` field's items and every field lookup by declared index read this. -/
theorem ValuesAgree.items_eq {a : SpecAMQP.Spec.Codec.Value} {b : SpecAMQP.Ref.Value}
    (h : ValuesAgree a b) :
    (∀ (i : Nat) (x : SpecAMQP.Spec.Codec.Value),
        (SpecAMQP.Spec.Connection.itemsOf a)[i]? = some x →
        ∃ y, (SpecAMQP.Ref.Connection.fieldList b)[i]? = some y ∧ ValuesAgree x y) ∧
    (∀ (i : Nat) (y : SpecAMQP.Ref.Value),
        (SpecAMQP.Ref.Connection.fieldList b)[i]? = some y →
        ∃ x, (SpecAMQP.Spec.Connection.itemsOf a)[i]? = some x ∧ ValuesAgree x y) ∧
    (∀ i : Nat, ((SpecAMQP.Spec.Connection.itemsOf a)[i]? = none) ↔
        ((SpecAMQP.Ref.Connection.fieldList b)[i]? = none)) :=
  forall₂_index (items_forall₂ h)

/-- Agreement at any index of two elementwise-related lists, as the optional value the
index carries. -/
private theorem optionAgree_get? {xs : List SpecAMQP.Spec.Codec.Value}
    {ys : List SpecAMQP.Ref.Value} (h : List.Forall₂ ValuesAgree xs ys) (i : Nat) :
    OptionAgree xs[i]? ys[i]? := by
  obtain ⟨hl, hr, hn⟩ := forall₂_index h
  by_cases hx : xs[i]? = none
  · rw [hx, (hn i).mp hx]
    exact .none
  · obtain ⟨x, hx'⟩ := Option.ne_none_iff_exists'.mp hx
    obtain ⟨y, hy, hxy⟩ := hl i x hx'
    rw [hx', hy]
    exact .some hxy

/-- The two layers' `if` on a declared field's index: the specification asks `1 ≤ index`
and the reference asks `index == 0`, which are the same test, and both branches are the
same choice between the field's value and "unset". -/
private theorem optionAgree_index_ite (i : Nat) {P : Option SpecAMQP.Spec.Codec.Value}
    {Q : Option SpecAMQP.Ref.Value} (hPQ : OptionAgree P Q) :
    OptionAgree (if 1 ≤ i then P else none) (if i == 0 then none else Q) := by
  by_cases h0 : i = 0
  · rw [h0]
    exact .none
  · have h1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr h0
    rw [if_pos h1, if_neg (fun hc => h0 (beq_iff_eq.mp hc))]
    exact hPQ

/-- The field read: `fieldValue` on the specification's side and `valueOfField` on the
reference's, looked up in the same generated field table (`fieldOf` is `declaredField`, by
`rfl`, so the declared index is the same) at the same declared index. An `open`'s limits,
a `close`'s fields, and every SASL field read this. -/
theorem ValuesAgree.fieldValue_eq {a : SpecAMQP.Spec.Codec.Value} {b : SpecAMQP.Ref.Value}
    (h : ValuesAgree a b) (owner field : String) :
    OptionAgree (SpecAMQP.Spec.Connection.fieldValue owner field a)
      (SpecAMQP.Ref.Connection.valueOfField owner field b) := by
  simp only [SpecAMQP.Spec.Connection.fieldValue, SpecAMQP.Ref.Connection.valueOfField,
    show SpecAMQP.Spec.Connection.fieldOf owner field =
      SpecAMQP.Ref.Connection.declaredField owner field from rfl]
  rcases hd : SpecAMQP.Ref.Connection.declaredField owner field with _ | fld
  · exact .none
  · exact optionAgree_index_ite fld.index (optionAgree_get? (items_forall₂ h) (fld.index - 1))

/-- Whether a field lookup found a value that is not null, on the specification's side:
`false` for an absent field and for a null one, which is the rule `fieldSet` spells out. -/
private def specSetFlag? : Option SpecAMQP.Spec.Codec.Value → Bool
  | some .null | none => false
  | some _ => true

/-- The same test, on the reference's side. -/
private def refSetFlag? : Option SpecAMQP.Ref.Value → Bool
  | some .null | none => false
  | some _ => true

/-- The name the reference's filter emits for a field: the field's declared name when the
lookup found nothing or found null, and nothing otherwise. -/
private def refFieldName? (nm : String) : Option SpecAMQP.Ref.Value → Option String
  | some .null | none => some nm
  | some _ => none

/-- The `unset` test each layer's mandatory-field filter makes of a field lookup: the
specification's `!fieldSet` and the predicate the reference's own filter spells out are
the same test.

Stated over the optional results themselves rather than over `fieldSet`/`valueOfField`
applied to a value: the generated equation lemma for `fieldSet` has `fieldValue`'s own
match inlined into it, so a dependent case split on the lookup's result cannot see the
lookup term in the goal. -/
private theorem optionAgree_unset {P : Option SpecAMQP.Spec.Codec.Value}
    {Q : Option SpecAMQP.Ref.Value} (h : OptionAgree P Q) :
    specSetFlag? P = refSetFlag? Q := by
  cases h with
  | none => rfl
  | some hxy => cases hxy <;> rfl

/-- The per-field equality of the two mandatory-field filters: a field the declared
surface marks mandatory and the performative does not set is missing on both sides, and no
other field is. -/
private theorem optionAgree_mandatory_filter {P : Option SpecAMQP.Spec.Codec.Value}
    {Q : Option SpecAMQP.Ref.Value} (h : OptionAgree P Q) (mand : Bool) (nm : String) :
    (if mand && ! specSetFlag? P then some nm else none)
      = (if ! mand then none else refFieldName? nm Q) := by
  cases h with
  | none => by_cases hm : mand <;> simp [hm, specSetFlag?, refFieldName?]
  | some hxy =>
      cases hxy <;> (by_cases hm : mand <;> simp [hm, specSetFlag?, refFieldName?])

/-- The per-field equality of the two mandatory-field filters, read off the lookup the two
layers share. -/
private theorem mandatory_filter_eq {a : SpecAMQP.Spec.Codec.Value}
    {b : SpecAMQP.Ref.Value} (h : ValuesAgree a b) (owner : String)
    (fld : SpecAMQP.Generated.Oasis.FieldDecl) :
    (if fld.mandatory && ! SpecAMQP.Spec.Connection.fieldSet owner fld.name a then
        some fld.name else none)
      = (if ! fld.mandatory then none
         else match SpecAMQP.Ref.Connection.valueOfField owner fld.name b with
              | some .null | none => some fld.name
              | some _ => none) := by
  rw [show SpecAMQP.Spec.Connection.fieldSet owner fld.name a =
        specSetFlag? (SpecAMQP.Spec.Connection.fieldValue owner fld.name a) from rfl]
  rw [show (match SpecAMQP.Ref.Connection.valueOfField owner fld.name b with
            | some .null | none => some fld.name
            | some _ => none)
        = refFieldName? fld.name (SpecAMQP.Ref.Connection.valueOfField owner fld.name b)
      from rfl]
  exact optionAgree_mandatory_filter (ValuesAgree.fieldValue_eq h owner fld.name)
    fld.mandatory fld.name

/-- `filterMap` congruence, pointwise. -/
private theorem filterMap_congr' {γ δ : Type} {l : List γ} {f g : γ → Option δ}
    (hf : ∀ x ∈ l, f x = g x) : l.filterMap f = l.filterMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx : f x = g x := hf x (by simp)
    have hxs : ∀ y ∈ xs, f y = g y := fun y hy => hf y (by simp [hy])
    rw [List.filterMap_cons, List.filterMap_cons, hx]
    split <;> simp [ih hxs]

/-- The mandatory-field lists the connection layer refuses an `open` or a `close` for: the
same fields, in the same table order, on both sides. -/
theorem ValuesAgree.mandatory_eq {a : SpecAMQP.Spec.Codec.Value} {b : SpecAMQP.Ref.Value}
    (h : ValuesAgree a b) (owner : String) :
    SpecAMQP.Spec.Connection.missingMandatory owner a =
      SpecAMQP.Ref.Connection.missingMandatory owner b := by
  simp only [SpecAMQP.Spec.Connection.missingMandatory,
    SpecAMQP.Ref.Connection.missingMandatory,
    show SpecAMQP.Spec.Connection.pathOf owner = SpecAMQP.Ref.Connection.anchorOf owner
      from rfl]
  rcases hp : SpecAMQP.Ref.Connection.anchorOf owner with _ | path
  · rfl
  · exact filterMap_congr' (fun fld _ => mandatory_filter_eq h owner fld)

/-- An integer field read the same way on both sides, up to the refusal payloads the two
layers spell differently. The two reads check the same things in a different order — the
specification refuses a wrongly-typed value before it reads a number, the reference reads
the number first — so the proof splits on the declared field, on the index the two layers
share, on the item the index carries, and on the declared primitive type, and compares the
two reads' branch conditions there through `typeName`/`primitiveName` and
`valueNat`/`numberOf`. -/
private theorem intField_toOption_eq {a : SpecAMQP.Spec.Codec.Value} {b : SpecAMQP.Ref.Value}
    (h : ValuesAgree a b) (owner field : String) :
    (SpecAMQP.Spec.Connection.intField owner field a).toOption =
      (SpecAMQP.Ref.Connection.integerField owner field b).toOption := by
  have hitems := items_forall₂ h
  have hf : SpecAMQP.Spec.Connection.fieldOf owner field =
      SpecAMQP.Ref.Connection.declaredField owner field := rfl
  have hdflt : SpecAMQP.Spec.Connection.fieldDefault owner field =
      SpecAMQP.Ref.Connection.declaredDefault owner field := rfl
  have hpd : ∀ t, SpecAMQP.Spec.Connection.primitiveOf t =
      SpecAMQP.Ref.Connection.primitiveOfDeclared t := fun _ => rfl
  simp only [SpecAMQP.Spec.Connection.intField, SpecAMQP.Ref.Connection.integerField,
    SpecAMQP.Spec.Connection.fieldTypeRefusal?, SpecAMQP.Spec.Connection.fieldValue,
    SpecAMQP.Ref.Connection.valueOfField, hf, hdflt, hpd]
  rcases hd : SpecAMQP.Ref.Connection.declaredField owner field with _ | fld
  · dsimp only
    cases hdd : SpecAMQP.Ref.Connection.declaredDefault owner field <;> rfl
  · dsimp only
    by_cases hidx : 1 ≤ fld.index
    · have hbeq : (fld.index == 0) = false := by
        rw [beq_eq_false_iff_ne]
        omega
      have hfalse : ¬ ((fld.index == 0) = true) := by
        rw [hbeq]
        simp
      rw [if_pos hidx, if_neg hfalse]
      generalize hP : (SpecAMQP.Spec.Connection.itemsOf a)[fld.index - 1]? = P
      generalize hQ : (SpecAMQP.Ref.Connection.fieldList b)[fld.index - 1]? = Q
      have hPQ : OptionAgree P Q := by
        rw [← hP, ← hQ]
        exact optionAgree_get? hitems (fld.index - 1)
      cases hPQ with
      | none => cases hdd : SpecAMQP.Ref.Connection.declaredDefault owner field <;> rfl
      | @some x y hxy =>
        have hTN : SpecAMQP.Spec.Codec.typeName x = SpecAMQP.Ref.Connection.primitiveName y :=
          ValuesAgree.typeName_eq hxy
        have hVN : SpecAMQP.Spec.Connection.valueNat x =
            SpecAMQP.Ref.Connection.numberOf y := ValuesAgree.number_eq hxy
        by_cases hx : x = .null
        · have hy : y = .null := (ValuesAgree.null_iff hxy).mp hx
          rw [hx, hy]
          cases hdd : SpecAMQP.Ref.Connection.declaredDefault owner field <;> rfl
        · have hy : y ≠ .null := fun hy' => hx ((ValuesAgree.null_iff hxy).mpr hy')
          -- Neither item is null, so both reads take their non-null branch: simplifying
          -- with the two facts above turns each item match into the read of the item.
          simp only []
          cases hD : SpecAMQP.Ref.Connection.primitiveOfDeclared fld.typeName with
          | none =>
            dsimp only
            cases hnum : SpecAMQP.Ref.Connection.numberOf y <;>
              cases hnat : SpecAMQP.Spec.Connection.valueNat x <;>
              simp_all [Except.toOption]
          | some declared =>
            rw [hTN]
            dsimp only
            by_cases hc : (SpecAMQP.Ref.Connection.primitiveName y == declared) = true
            · rw [if_pos hc]
              dsimp only
              cases hnum : SpecAMQP.Ref.Connection.numberOf y <;>
                cases hnat : SpecAMQP.Spec.Connection.valueNat x <;>
                simp_all [Except.toOption]
            · rw [if_neg hc]
              dsimp only
              cases hnum : SpecAMQP.Ref.Connection.numberOf y <;> simp_all [Except.toOption]
    · have h0 : fld.index = 0 := by omega
      rw [h0]
      cases hdd : SpecAMQP.Ref.Connection.declaredDefault owner field <;> rfl

/-- The limits an `open` declares on the specification's side, as the two field reads that
produce them: both fields must be integers of their declared type for limits to exist. -/
private theorem openLimits_ok_iff {body : SpecAMQP.Spec.Codec.Value}
    {l : SpecAMQP.Spec.Connection.Limits} :
    SpecAMQP.Spec.Connection.openLimits body = .ok l ↔
      SpecAMQP.Spec.Connection.intField "open" "max-frame-size" body = .ok l.maxFrameSize ∧
      SpecAMQP.Spec.Connection.intField "open" "channel-max" body = .ok l.channelMax := by
  constructor
  · intro hl
    rcases h1 : SpecAMQP.Spec.Connection.intField "open" "max-frame-size" body with err | mfs
    · have hred : SpecAMQP.Spec.Connection.openLimits body =
          .error err := by
        rw [SpecAMQP.Spec.Connection.openLimits, h1]
        rfl
      rw [hred] at hl
      exact absurd hl (by simp)
    · rcases h2 : SpecAMQP.Spec.Connection.intField "open" "channel-max" body with err | cm
      · have hred : SpecAMQP.Spec.Connection.openLimits body =
            .error err := by
          rw [SpecAMQP.Spec.Connection.openLimits, h1, h2]
          rfl
        rw [hred] at hl
        exact absurd hl (by simp)
      · have hred : SpecAMQP.Spec.Connection.openLimits body =
            .ok ⟨mfs, cm⟩ := by
          rw [SpecAMQP.Spec.Connection.openLimits, h1, h2]
          rfl
        rw [hred] at hl
        injection hl with hl
        rw [← hl]
        exact ⟨rfl, rfl⟩
  · intro ⟨h1, h2⟩
    rw [SpecAMQP.Spec.Connection.openLimits, h1, h2]
    rfl

/-- The limits an `open` declares on the reference's side, as the same two field reads. -/
private theorem openBounds_ok_iff {body : SpecAMQP.Ref.Value}
    {m : SpecAMQP.Ref.Connection.Bounds} :
    SpecAMQP.Ref.Connection.openBounds body = .ok m ↔
      SpecAMQP.Ref.Connection.integerField "open" "max-frame-size" body = .ok m.frames ∧
      SpecAMQP.Ref.Connection.integerField "open" "channel-max" body = .ok m.channels := by
  constructor
  · intro hm
    rcases h1 : SpecAMQP.Ref.Connection.integerField "open" "max-frame-size" body with err | mfs
    · have hred : SpecAMQP.Ref.Connection.openBounds body =
          .error err := by
        rw [SpecAMQP.Ref.Connection.openBounds, h1]
        rfl
      rw [hred] at hm
      exact absurd hm (by simp)
    · rcases h2 : SpecAMQP.Ref.Connection.integerField "open" "channel-max" body with err | cm
      · have hred : SpecAMQP.Ref.Connection.openBounds body =
            .error err := by
          rw [SpecAMQP.Ref.Connection.openBounds, h1, h2]
          rfl
        rw [hred] at hm
        exact absurd hm (by simp)
      · have hred : SpecAMQP.Ref.Connection.openBounds body =
            .ok ⟨mfs, cm⟩ := by
          rw [SpecAMQP.Ref.Connection.openBounds, h1, h2]
          rfl
        rw [hred] at hm
        injection hm with hm
        rw [← hm]
        exact ⟨rfl, rfl⟩
  · intro ⟨h1, h2⟩
    rw [SpecAMQP.Ref.Connection.openBounds, h1, h2]
    rfl

/-- The limits an `open` frame declares: both layers accept exactly the `open`s whose two
integer fields are integers of their declared types, and the `Bounds` the reference reads
is the `Limits` the specification read. -/
theorem ValuesAgree.openLimits_shape {a : SpecAMQP.Spec.Codec.Value} {b : SpecAMQP.Ref.Value}
    (h : ValuesAgree a b) :
    ((∃ l, SpecAMQP.Spec.Connection.openLimits a = .ok l) ↔
       (∃ m, SpecAMQP.Ref.Connection.openBounds b = .ok m)) ∧
    (∀ l m, SpecAMQP.Spec.Connection.openLimits a = .ok l →
       SpecAMQP.Ref.Connection.openBounds b = .ok m →
       SpecAMQP.Ref.Connection.Bounds.mk m.frames m.channels =
         ⟨l.maxFrameSize, l.channelMax⟩) := by
  have hmfs := intField_toOption_eq h "open" "max-frame-size"
  have hcm := intField_toOption_eq h "open" "channel-max"
  have some_eq {α β : Type} {x : α} {e : Except β α} (he : e.toOption = some x) :
      e = .ok x := by
    cases e with
    | error err => simp [Except.toOption] at he
    | ok y =>
      have hy : y = x := Option.some.inj (by simpa only [Except.toOption] using he)
      subst hy
      rfl
  constructor
  · constructor
    · intro ⟨l, hl⟩
      obtain ⟨h1, h2⟩ := openLimits_ok_iff.mp hl
      have h3 : SpecAMQP.Ref.Connection.integerField "open" "max-frame-size" b =
          .ok l.maxFrameSize := some_eq (by rw [← hmfs, h1]; rfl)
      have h4 : SpecAMQP.Ref.Connection.integerField "open" "channel-max" b =
          .ok l.channelMax := some_eq (by rw [← hcm, h2]; rfl)
      exact ⟨⟨l.maxFrameSize, l.channelMax⟩, openBounds_ok_iff.mpr ⟨h3, h4⟩⟩
    · intro ⟨m, hm⟩
      obtain ⟨h1, h2⟩ := openBounds_ok_iff.mp hm
      have h3 : SpecAMQP.Spec.Connection.intField "open" "max-frame-size" a =
          .ok m.frames := some_eq (by rw [hmfs, h1]; rfl)
      have h4 : SpecAMQP.Spec.Connection.intField "open" "channel-max" a =
          .ok m.channels := some_eq (by rw [hcm, h2]; rfl)
      exact ⟨⟨m.frames, m.channels⟩, openLimits_ok_iff.mpr ⟨h3, h4⟩⟩
  · intro l m hl hm
    obtain ⟨h1, h2⟩ := openLimits_ok_iff.mp hl
    obtain ⟨h3, h4⟩ := openBounds_ok_iff.mp hm
    have e1 : l.maxFrameSize = m.frames := by
      have hsome := hmfs
      rw [h1, h3] at hsome
      exact Option.some.inj (by simpa only [Except.toOption] using hsome)
    have e2 : l.channelMax = m.channels := by
      have hsome := hcm
      rw [h2, h4] at hsome
      exact Option.some.inj (by simpa only [Except.toOption] using hsome)
    rw [← e1, ← e2]

/-- The symbol list a `multiple` field carries, at the lookup's own result, on the
specification's side: `symbolsOf` of the value found, or of the null value an absent field
stands for. A definition rather than a `match` in the statement, because a match whose
discriminant is a statement variable makes Lean carry the hypothesis that depends on it
into the statement's type. -/
private def specSymbolsOfOption : Option SpecAMQP.Spec.Codec.Value → List String
  | some v => SpecAMQP.Spec.Connection.symbolsOf v
  | none => SpecAMQP.Spec.Connection.symbolsOf .null

/-- The same, on the reference's side. -/
private def refSymbolsOfOption : Option SpecAMQP.Ref.Value → List String
  | some v => SpecAMQP.Ref.Connection.symbolList v
  | none => SpecAMQP.Ref.Connection.symbolList .null

private theorem specSymbolsOfOption_getD (P : Option SpecAMQP.Spec.Codec.Value) :
    SpecAMQP.Spec.Connection.symbolsOf (P.getD .null) = specSymbolsOfOption P := by
  cases P <;> rfl

private theorem refSymbolsOfOption_getD (Q : Option SpecAMQP.Ref.Value) :
    SpecAMQP.Ref.Connection.symbolList (Q.getD .null) = refSymbolsOfOption Q := by
  cases Q <;> rfl

private theorem optionAgree_symbolsOfOption {P : Option SpecAMQP.Spec.Codec.Value}
    {Q : Option SpecAMQP.Ref.Value} (h : OptionAgree P Q) :
    specSymbolsOfOption P = refSymbolsOfOption Q := by
  cases h with
  | none => rfl
  | some hxy => exact ValuesAgree.symbols_eq hxy

/-- The mechanisms a peer announces, which the SASL dialogue compares before an init. -/
theorem ValuesAgree.mechanisms_eq {a : SpecAMQP.Spec.Codec.Value} {b : SpecAMQP.Ref.Value}
    (h : ValuesAgree a b) :
    SpecAMQP.Spec.Connection.symbolsOf
        ((SpecAMQP.Spec.Connection.fieldValue "sasl-mechanisms"
          "sasl-server-mechanisms" a).getD .null) =
      SpecAMQP.Ref.Connection.symbolList
        ((SpecAMQP.Ref.Connection.valueOfField "sasl-mechanisms"
          "sasl-server-mechanisms" b).getD .null) := by
  rw [specSymbolsOfOption_getD, refSymbolsOfOption_getD]
  exact optionAgree_symbolsOfOption
    (ValuesAgree.fieldValue_eq h "sasl-mechanisms" "sasl-server-mechanisms")

/-- The `mechanism` read's projection: the text of a symbol, and the empty string where the
field is unset or is not a symbol. -/
private def specSymbolText? : Option SpecAMQP.Spec.Codec.Value → String
  | some (.symbol t) => t
  | _ => ""

/-- The same, on the reference's side. -/
private def refSymbolText? : Option SpecAMQP.Ref.Value → String
  | some (.symbol t) => t
  | _ => ""

private theorem optionAgree_symbolText? {P : Option SpecAMQP.Spec.Codec.Value}
    {Q : Option SpecAMQP.Ref.Value} (h : OptionAgree P Q) :
    specSymbolText? P = refSymbolText? Q := by
  cases h with
  | none => rfl
  | some hxy => cases hxy <;> simp_all [specSymbolText?, refSymbolText?]

/-- The mechanism an init chooses, which the dialogue checks against the announced list. -/
theorem ValuesAgree.mechanism_eq {a : SpecAMQP.Spec.Codec.Value} {b : SpecAMQP.Ref.Value}
    (h : ValuesAgree a b) :
    (match SpecAMQP.Spec.Connection.fieldValue "sasl-init" "mechanism" a with
      | some (.symbol t) => t | _ => "") =
    (match SpecAMQP.Ref.Connection.valueOfField "sasl-init" "mechanism" b with
      | some (.symbol t) => t | _ => "") := by
  rw [show (match SpecAMQP.Spec.Connection.fieldValue "sasl-init" "mechanism" a with
            | some (.symbol t) => t | _ => "") =
        specSymbolText? (SpecAMQP.Spec.Connection.fieldValue "sasl-init" "mechanism" a)
      from rfl]
  rw [show (match SpecAMQP.Ref.Connection.valueOfField "sasl-init" "mechanism" b with
            | some (.symbol t) => t | _ => "") =
        refSymbolText? (SpecAMQP.Ref.Connection.valueOfField "sasl-init" "mechanism" b)
      from rfl]
  exact optionAgree_symbolText? (ValuesAgree.fieldValue_eq h "sasl-init" "mechanism")

/-- The outcome code read, at the lookup's own result. -/
private def specCodeOfOption (o : Option SpecAMQP.Spec.Codec.Value) : Option Nat :=
  o.bind SpecAMQP.Spec.Connection.valueNat

/-- The same, on the reference's side. -/
private def refCodeOfOption (o : Option SpecAMQP.Ref.Value) : Option Nat :=
  o.bind SpecAMQP.Ref.Connection.numberOf

private theorem optionAgree_codeOfOption {P : Option SpecAMQP.Spec.Codec.Value}
    {Q : Option SpecAMQP.Ref.Value} (h : OptionAgree P Q) :
    specCodeOfOption P = refCodeOfOption Q := by
  cases h with
  | none => rfl
  | some hxy => exact ValuesAgree.number_eq hxy

/-- The code a SASL outcome carries, which decides whether the security layer is
established. -/
theorem ValuesAgree.outcomeCode_eq {a : SpecAMQP.Spec.Codec.Value} {b : SpecAMQP.Ref.Value}
    (h : ValuesAgree a b) :
    (SpecAMQP.Spec.Connection.fieldValue "sasl-outcome" "code" a).bind
        SpecAMQP.Spec.Connection.valueNat =
      (SpecAMQP.Ref.Connection.valueOfField "sasl-outcome" "code" b).bind
        SpecAMQP.Ref.Connection.numberOf := by
  exact optionAgree_codeOfOption (ValuesAgree.fieldValue_eq h "sasl-outcome" "code")

/-- The declared type a body's descriptor names, which decides the frame's role. Both
layers search the generated type table for the descriptor they read, and the searches
agree: the integer form is compared as a `Nat` against the artifact's `domain:code`, and
the symbolic form against the descriptor's own declared name. -/
theorem ValuesAgree.descriptor_eq {da : SpecAMQP.Spec.Codec.Value} {db : SpecAMQP.Ref.Value}
    (h : ValuesAgree da db) :
    SpecAMQP.Spec.Frame.typeOfDescriptor da =
      SpecAMQP.Ref.Frame.typeOfDescriptor db := by
  cases h
  case ulong heq =>
    simp only [SpecAMQP.Spec.Frame.typeOfDescriptor, SpecAMQP.Ref.Frame.typeOfDescriptor, heq]
    rfl
  case symbol heq =>
    simp only [SpecAMQP.Spec.Frame.typeOfDescriptor, SpecAMQP.Ref.Frame.typeOfDescriptor, heq]
    rfl
  all_goals rfl

/-- The type a body's descriptor names, on the specification's side. -/
private def specBodyType? :
    SpecAMQP.Spec.Codec.Value → Option SpecAMQP.Generated.Oasis.TypeDecl
  | .described descriptor _ => SpecAMQP.Spec.Frame.typeOfDescriptor descriptor
  | _ => none

/-- The two layers' body-type readings agree: `Spec.Frame.typeOfDescriptor` at the body's
descriptor and the reference's `bodyType` are the same search. Both resolve an integer
descriptor against the artifact's `domain:code`, and both resolve a symbolic descriptor
against the descriptor's *declared* name (`amqp:open:list`) — the name the declared
surface records in `descriptor.name`. That last clause is what makes the role and SASL-name
reads below agree; matching a bare type name instead would resolve only bodies no
conforming writer produces. -/
theorem ValuesAgree.bodyType_eq {a : SpecAMQP.Spec.Codec.Value} {b : SpecAMQP.Ref.Value}
    (h : ValuesAgree a b) :
    specBodyType? a = SpecAMQP.Ref.Connection.bodyType b := by
  cases h
  case described hd hv =>
    cases hd <;>
      first
        | rfl
        | (rename_i heq
           simp only [specBodyType?, SpecAMQP.Ref.Connection.bodyType,
             SpecAMQP.Spec.Frame.typeOfDescriptor, SpecAMQP.Ref.Frame.typeOfDescriptor, heq]
           rfl)
  all_goals rfl

/-- The role the specification's connection layer gives a resolved body type. -/
private def specRoleOfType :
    Option SpecAMQP.Generated.Oasis.TypeDecl → SpecAMQP.Spec.Connection.FrameRole
  | some decl =>
    if decl.name == "open" then .open
    else if decl.name == "close" then .close
    else if decl.provides.contains "sasl-frame" then .sasl
    else .other
  | none => .other

/-- The kind the reference's connection layer gives a resolved body type. The clauses are
in `Ref.Connection.kindOfBody`'s own order — `none` first — so that `refKindOfType` at the
body's type is *definitionally* what `kindOfBody` computes at the body, which is what
`kindOfBody_described` needs. -/
private def refKindOfType :
    Option SpecAMQP.Generated.Oasis.TypeDecl → SpecAMQP.Ref.Connection.Kind
  | none => .relayed
  | some decl =>
    if decl.name == "open" then .open
    else if decl.name == "close" then .close
    else if decl.provides.contains "sasl-frame" then .saslFrame
    else .relayed

private theorem roleOfType_open (O : Option SpecAMQP.Generated.Oasis.TypeDecl) :
    (specRoleOfType O == SpecAMQP.Spec.Connection.FrameRole.open) =
      (refKindOfType O == SpecAMQP.Ref.Connection.Kind.open) := by
  cases O with
  | none => rfl
  | some decl =>
    cases h1 : decl.name == "open" <;> cases h2 : decl.name == "close" <;>
      cases h3 : decl.provides.contains "sasl-frame" <;>
        simp_all [specRoleOfType, refKindOfType] <;> decide

private theorem roleOfType_close (O : Option SpecAMQP.Generated.Oasis.TypeDecl) :
    (specRoleOfType O == SpecAMQP.Spec.Connection.FrameRole.close) =
      (refKindOfType O == SpecAMQP.Ref.Connection.Kind.close) := by
  cases O with
  | none => rfl
  | some decl =>
    cases h1 : decl.name == "open" <;> cases h2 : decl.name == "close" <;>
      cases h3 : decl.provides.contains "sasl-frame" <;>
        simp_all [specRoleOfType, refKindOfType] <;> decide

private theorem roleOfType_sasl (O : Option SpecAMQP.Generated.Oasis.TypeDecl) :
    (specRoleOfType O == SpecAMQP.Spec.Connection.FrameRole.sasl) =
      (refKindOfType O == SpecAMQP.Ref.Connection.Kind.saslFrame) := by
  cases O with
  | none => rfl
  | some decl =>
    cases h1 : decl.name == "open" <;> cases h2 : decl.name == "close" <;>
      cases h3 : decl.provides.contains "sasl-frame" <;>
        simp_all [specRoleOfType, refKindOfType] <;> decide

/-- The SASL performative the specification's connection layer gives a resolved body
type. -/
private def specSaslOfType :
    Option SpecAMQP.Generated.Oasis.TypeDecl → SpecAMQP.Spec.Connection.SaslFrame
  | some decl =>
    if decl.name == "sasl-mechanisms" then .mechanisms
    else if decl.name == "sasl-init" then .init
    else if decl.name == "sasl-challenge" then .challenge
    else if decl.name == "sasl-response" then .response
    else if decl.name == "sasl-outcome" then .outcome
    else .other
  | none => .other

/-- The name the reference's connection layer gives a resolved body type. -/
private def refSaslNameOfType : Option SpecAMQP.Generated.Oasis.TypeDecl → String
  | some decl => decl.name
  | none => ""

private theorem saslOfType_mechanisms (O : Option SpecAMQP.Generated.Oasis.TypeDecl) :
    (specSaslOfType O == SpecAMQP.Spec.Connection.SaslFrame.mechanisms) =
      (refSaslNameOfType O == "sasl-mechanisms") := by
  cases O with
  | none => rfl
  | some decl =>
    rcases eq_or_ne decl.name "sasl-mechanisms" with h | h
    · simp only [specSaslOfType, refSaslNameOfType]
      rw [h]
      rfl
    · rcases eq_or_ne decl.name "sasl-init" with h2 | h2
      · simp only [specSaslOfType, refSaslNameOfType]
        rw [h2]
        rfl
      · rcases eq_or_ne decl.name "sasl-challenge" with h3 | h3
        · simp only [specSaslOfType, refSaslNameOfType]
          rw [h3]
          rfl
        · rcases eq_or_ne decl.name "sasl-response" with h4 | h4
          · simp only [specSaslOfType, refSaslNameOfType]
            rw [h4]
            rfl
          · rcases eq_or_ne decl.name "sasl-outcome" with h5 | h5
            · simp only [specSaslOfType, refSaslNameOfType]
              rw [h5]
              rfl
            · simp only [specSaslOfType, refSaslNameOfType]
              rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr h2,
                beq_eq_false_iff_ne.mpr h3, beq_eq_false_iff_ne.mpr h4,
                beq_eq_false_iff_ne.mpr h5]
              rfl

private theorem saslOfType_init (O : Option SpecAMQP.Generated.Oasis.TypeDecl) :
    (specSaslOfType O == SpecAMQP.Spec.Connection.SaslFrame.init) =
      (refSaslNameOfType O == "sasl-init") := by
  cases O with
  | none => rfl
  | some decl =>
    rcases eq_or_ne decl.name "sasl-mechanisms" with h | h
    · simp only [specSaslOfType, refSaslNameOfType]
      rw [h]
      rfl
    · rcases eq_or_ne decl.name "sasl-init" with h2 | h2
      · simp only [specSaslOfType, refSaslNameOfType]
        rw [h2]
        rfl
      · rcases eq_or_ne decl.name "sasl-challenge" with h3 | h3
        · simp only [specSaslOfType, refSaslNameOfType]
          rw [h3]
          rfl
        · rcases eq_or_ne decl.name "sasl-response" with h4 | h4
          · simp only [specSaslOfType, refSaslNameOfType]
            rw [h4]
            rfl
          · rcases eq_or_ne decl.name "sasl-outcome" with h5 | h5
            · simp only [specSaslOfType, refSaslNameOfType]
              rw [h5]
              rfl
            · simp only [specSaslOfType, refSaslNameOfType]
              rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr h2,
                beq_eq_false_iff_ne.mpr h3, beq_eq_false_iff_ne.mpr h4,
                beq_eq_false_iff_ne.mpr h5]
              rfl

private theorem saslOfType_challenge (O : Option SpecAMQP.Generated.Oasis.TypeDecl) :
    (specSaslOfType O == SpecAMQP.Spec.Connection.SaslFrame.challenge) =
      (refSaslNameOfType O == "sasl-challenge") := by
  cases O with
  | none => rfl
  | some decl =>
    rcases eq_or_ne decl.name "sasl-mechanisms" with h | h
    · simp only [specSaslOfType, refSaslNameOfType]
      rw [h]
      rfl
    · rcases eq_or_ne decl.name "sasl-init" with h2 | h2
      · simp only [specSaslOfType, refSaslNameOfType]
        rw [h2]
        rfl
      · rcases eq_or_ne decl.name "sasl-challenge" with h3 | h3
        · simp only [specSaslOfType, refSaslNameOfType]
          rw [h3]
          rfl
        · rcases eq_or_ne decl.name "sasl-response" with h4 | h4
          · simp only [specSaslOfType, refSaslNameOfType]
            rw [h4]
            rfl
          · rcases eq_or_ne decl.name "sasl-outcome" with h5 | h5
            · simp only [specSaslOfType, refSaslNameOfType]
              rw [h5]
              rfl
            · simp only [specSaslOfType, refSaslNameOfType]
              rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr h2,
                beq_eq_false_iff_ne.mpr h3, beq_eq_false_iff_ne.mpr h4,
                beq_eq_false_iff_ne.mpr h5]
              rfl

private theorem saslOfType_response (O : Option SpecAMQP.Generated.Oasis.TypeDecl) :
    (specSaslOfType O == SpecAMQP.Spec.Connection.SaslFrame.response) =
      (refSaslNameOfType O == "sasl-response") := by
  cases O with
  | none => rfl
  | some decl =>
    rcases eq_or_ne decl.name "sasl-mechanisms" with h | h
    · simp only [specSaslOfType, refSaslNameOfType]
      rw [h]
      rfl
    · rcases eq_or_ne decl.name "sasl-init" with h2 | h2
      · simp only [specSaslOfType, refSaslNameOfType]
        rw [h2]
        rfl
      · rcases eq_or_ne decl.name "sasl-challenge" with h3 | h3
        · simp only [specSaslOfType, refSaslNameOfType]
          rw [h3]
          rfl
        · rcases eq_or_ne decl.name "sasl-response" with h4 | h4
          · simp only [specSaslOfType, refSaslNameOfType]
            rw [h4]
            rfl
          · rcases eq_or_ne decl.name "sasl-outcome" with h5 | h5
            · simp only [specSaslOfType, refSaslNameOfType]
              rw [h5]
              rfl
            · simp only [specSaslOfType, refSaslNameOfType]
              rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr h2,
                beq_eq_false_iff_ne.mpr h3, beq_eq_false_iff_ne.mpr h4,
                beq_eq_false_iff_ne.mpr h5]
              rfl

private theorem saslOfType_outcome (O : Option SpecAMQP.Generated.Oasis.TypeDecl) :
    (specSaslOfType O == SpecAMQP.Spec.Connection.SaslFrame.outcome) =
      (refSaslNameOfType O == "sasl-outcome") := by
  cases O with
  | none => rfl
  | some decl =>
    rcases eq_or_ne decl.name "sasl-mechanisms" with h | h
    · simp only [specSaslOfType, refSaslNameOfType]
      rw [h]
      rfl
    · rcases eq_or_ne decl.name "sasl-init" with h2 | h2
      · simp only [specSaslOfType, refSaslNameOfType]
        rw [h2]
        rfl
      · rcases eq_or_ne decl.name "sasl-challenge" with h3 | h3
        · simp only [specSaslOfType, refSaslNameOfType]
          rw [h3]
          rfl
        · rcases eq_or_ne decl.name "sasl-response" with h4 | h4
          · simp only [specSaslOfType, refSaslNameOfType]
            rw [h4]
            rfl
          · rcases eq_or_ne decl.name "sasl-outcome" with h5 | h5
            · simp only [specSaslOfType, refSaslNameOfType]
              rw [h5]
              rfl
            · simp only [specSaslOfType, refSaslNameOfType]
              rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr h2,
                beq_eq_false_iff_ne.mpr h3, beq_eq_false_iff_ne.mpr h4,
                beq_eq_false_iff_ne.mpr h5]
              rfl

/-- The connection layer's role read at the level of the declared type: the specification's
`roleOfBody` at a described body is the type-level role of the type its descriptor names. -/
private theorem roleOfBody_described (d v : SpecAMQP.Spec.Codec.Value) :
    SpecAMQP.Spec.Connection.roleOfBody (.described d v) =
      specRoleOfType (specBodyType? (.described d v)) := rfl

/-- The reference's kind read at the level of the declared type. -/
private theorem kindOfBody_described (d v : SpecAMQP.Ref.Value) :
    SpecAMQP.Ref.Connection.kindOfBody (.described d v) =
      refKindOfType (SpecAMQP.Ref.Connection.bodyType (.described d v)) := rfl

/-- The role the layer branches on: an `open`. -/
theorem ValuesAgree.role_open_iff {a : SpecAMQP.Spec.Codec.Value} {b : SpecAMQP.Ref.Value}
    (h : ValuesAgree a b) :
    (SpecAMQP.Spec.Connection.roleOfBody a == SpecAMQP.Spec.Connection.FrameRole.open) =
      (SpecAMQP.Ref.Connection.kindOfBody b == SpecAMQP.Ref.Connection.Kind.open) := by
  cases h
  case described hd hv =>
    rw [roleOfBody_described, kindOfBody_described,
      ← ValuesAgree.bodyType_eq (ValuesAgree.described hd hv)]
    exact roleOfType_open _
  all_goals rfl

/-- The role the layer branches on: a `close`. -/
theorem ValuesAgree.role_close_iff {a : SpecAMQP.Spec.Codec.Value} {b : SpecAMQP.Ref.Value}
    (h : ValuesAgree a b) :
    (SpecAMQP.Spec.Connection.roleOfBody a == SpecAMQP.Spec.Connection.FrameRole.close) =
      (SpecAMQP.Ref.Connection.kindOfBody b == SpecAMQP.Ref.Connection.Kind.close) := by
  cases h
  case described hd hv =>
    rw [roleOfBody_described, kindOfBody_described,
      ← ValuesAgree.bodyType_eq (ValuesAgree.described hd hv)]
    exact roleOfType_close _
  all_goals rfl

/-- The role the layer branches on: a SASL performative, which is what sends the frame to
the security layer's dialogue rather than to the table. -/
theorem ValuesAgree.role_sasl_iff {a : SpecAMQP.Spec.Codec.Value} {b : SpecAMQP.Ref.Value}
    (h : ValuesAgree a b) :
    (SpecAMQP.Spec.Connection.roleOfBody a == SpecAMQP.Spec.Connection.FrameRole.sasl) =
      (SpecAMQP.Ref.Connection.kindOfBody b == SpecAMQP.Ref.Connection.Kind.saslFrame) := by
  cases h
  case described hd hv =>
    rw [roleOfBody_described, kindOfBody_described,
      ← ValuesAgree.bodyType_eq (ValuesAgree.described hd hv)]
    exact roleOfType_sasl _
  all_goals rfl

/-- The SASL performative read at the level of the declared type. -/
private theorem saslOfBody_described (d v : SpecAMQP.Spec.Codec.Value) :
    SpecAMQP.Spec.Connection.SaslFrame.ofBody (.described d v) =
      specSaslOfType (specBodyType? (.described d v)) := rfl

/-- The reference's SASL name read at the level of the declared type. -/
private theorem saslName_described (d v : SpecAMQP.Ref.Value) :
    SpecAMQP.Ref.Connection.saslName (.described d v) =
      refSaslNameOfType (SpecAMQP.Ref.Connection.bodyType (.described d v)) := rfl

/-- The SASL performative each name denotes: `sasl-mechanisms`. -/
theorem ValuesAgree.sasl_mechanisms_iff {a : SpecAMQP.Spec.Codec.Value}
    {b : SpecAMQP.Ref.Value} (h : ValuesAgree a b) :
    (SpecAMQP.Spec.Connection.SaslFrame.ofBody a ==
      SpecAMQP.Spec.Connection.SaslFrame.mechanisms) =
    (SpecAMQP.Ref.Connection.saslName b == "sasl-mechanisms") := by
  cases h
  case described hd hv =>
    rw [saslOfBody_described, saslName_described,
      ← ValuesAgree.bodyType_eq (ValuesAgree.described hd hv)]
    exact saslOfType_mechanisms _
  all_goals rfl

/-- The SASL performative each name denotes: `sasl-init`. -/
theorem ValuesAgree.sasl_init_iff {a : SpecAMQP.Spec.Codec.Value} {b : SpecAMQP.Ref.Value}
    (h : ValuesAgree a b) :
    (SpecAMQP.Spec.Connection.SaslFrame.ofBody a ==
      SpecAMQP.Spec.Connection.SaslFrame.init) =
    (SpecAMQP.Ref.Connection.saslName b == "sasl-init") := by
  cases h
  case described hd hv =>
    rw [saslOfBody_described, saslName_described,
      ← ValuesAgree.bodyType_eq (ValuesAgree.described hd hv)]
    exact saslOfType_init _
  all_goals rfl

/-- The SASL performative each name denotes: `sasl-challenge`. -/
theorem ValuesAgree.sasl_challenge_iff {a : SpecAMQP.Spec.Codec.Value}
    {b : SpecAMQP.Ref.Value} (h : ValuesAgree a b) :
    (SpecAMQP.Spec.Connection.SaslFrame.ofBody a ==
      SpecAMQP.Spec.Connection.SaslFrame.challenge) =
    (SpecAMQP.Ref.Connection.saslName b == "sasl-challenge") := by
  cases h
  case described hd hv =>
    rw [saslOfBody_described, saslName_described,
      ← ValuesAgree.bodyType_eq (ValuesAgree.described hd hv)]
    exact saslOfType_challenge _
  all_goals rfl

/-- The SASL performative each name denotes: `sasl-response`. -/
theorem ValuesAgree.sasl_response_iff {a : SpecAMQP.Spec.Codec.Value}
    {b : SpecAMQP.Ref.Value} (h : ValuesAgree a b) :
    (SpecAMQP.Spec.Connection.SaslFrame.ofBody a ==
      SpecAMQP.Spec.Connection.SaslFrame.response) =
    (SpecAMQP.Ref.Connection.saslName b == "sasl-response") := by
  cases h
  case described hd hv =>
    rw [saslOfBody_described, saslName_described,
      ← ValuesAgree.bodyType_eq (ValuesAgree.described hd hv)]
    exact saslOfType_response _
  all_goals rfl

/-- The SASL performative each name denotes: `sasl-outcome`. -/
theorem ValuesAgree.sasl_outcome_iff {a : SpecAMQP.Spec.Codec.Value}
    {b : SpecAMQP.Ref.Value} (h : ValuesAgree a b) :
    (SpecAMQP.Spec.Connection.SaslFrame.ofBody a ==
      SpecAMQP.Spec.Connection.SaslFrame.outcome) =
    (SpecAMQP.Ref.Connection.saslName b == "sasl-outcome") := by
  cases h
  case described hd hv =>
    rw [saslOfBody_described, saslName_described,
      ← ValuesAgree.bodyType_eq (ValuesAgree.described hd hv)]
    exact saslOfType_outcome _
  all_goals rfl

/-! #### 75_step_slices.lean -/

/-!
# The AMQP-layer frame step, matched

The first of the three step slices: whatever the reference's frame step answers for a decoded AMQP
performative, the specification's answers the same thing, given the correspondence between the two
bodies that the value slice's bundles produce (`FrameCorresponds`). The walk is over the reference's own
decision tree — the layer, the table's column, the `open`'s channel rule, the mandatory-field rule, and
the limits in force — each guard discharged by the lemma that says the two transcriptions of the table
answer it the same way.
-/

private theorem spec_fieldTypeRefusal_shape (owner fieldName : String)
    (body : SpecAMQP.Spec.Codec.Value) {reason : SpecAMQP.Spec.Connection.Refusal}
    (h : SpecAMQP.Spec.Connection.fieldTypeRefusal? owner fieldName body = some reason) :
    ∃ prose, reason = SpecAMQP.Spec.Connection.fieldRefusal "malformed" prose := by
  unfold SpecAMQP.Spec.Connection.fieldTypeRefusal? at h
  repeat' split at h
  all_goals
    first
      | exact ⟨_, by simpa using h.symm⟩
      | simp_all

/-- The specification's `intField` refuses only through the declared `invalid-field` / `malformed`
rule, whatever its own checks were; the SASL step's code read needs this shape, so it is stated here
rather than private. -/
theorem spec_intField_shape (owner fieldName : String)
    (body : SpecAMQP.Spec.Codec.Value) {r : SpecAMQP.Spec.Connection.Refusal}
    (h : SpecAMQP.Spec.Connection.intField owner fieldName body = .error r) :
    ∃ prose, r = SpecAMQP.Spec.Connection.fieldRefusal "malformed" prose := by
  cases hft : SpecAMQP.Spec.Connection.fieldTypeRefusal? owner fieldName body with
  | some reason =>
    obtain ⟨prose, hp⟩ := spec_fieldTypeRefusal_shape owner fieldName body hft
    unfold SpecAMQP.Spec.Connection.intField at h
    simp only [hft] at h
    cases h
    exact ⟨prose, hp⟩
  | none =>
    unfold SpecAMQP.Spec.Connection.intField at h
    simp only [hft] at h
    repeat' split at h
    all_goals
      first
        | exact ⟨_, by simpa using h.symm⟩
        | simp_all

private theorem spec_openLimits_shape (body : SpecAMQP.Spec.Codec.Value)
    {r : SpecAMQP.Spec.Connection.Refusal}
    (h : SpecAMQP.Spec.Connection.openLimits body = .error r) :
    ∃ prose, r = SpecAMQP.Spec.Connection.fieldRefusal "malformed" prose := by
  unfold SpecAMQP.Spec.Connection.openLimits at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  cases h1 : SpecAMQP.Spec.Connection.intField "open" "max-frame-size" body with
  | error e =>
    simp only [h1] at h
    obtain ⟨prose, hp⟩ := spec_intField_shape "open" "max-frame-size" body h1
    cases h
    exact ⟨prose, hp⟩
  | ok v =>
    simp only [h1] at h
    cases h2 : SpecAMQP.Spec.Connection.intField "open" "channel-max" body with
    | error e =>
      simp only [h2] at h
      obtain ⟨prose, hp⟩ := spec_intField_shape "open" "channel-max" body h2
      cases h
      exact ⟨prose, hp⟩
    | ok w =>
      simp only [h2] at h
      simp at h

theorem ref_integerField_shape (typeName fieldName : String) (body : SpecAMQP.Ref.Value)
    {r : SpecAMQP.Ref.Connection.Refusal}
    (h : SpecAMQP.Ref.Connection.integerField typeName fieldName body = .error r) :
    ∃ prose, r = SpecAMQP.Ref.Connection.refuseWith
      SpecAMQP.Ref.Connection.invalidFieldCondition "malformed" prose := by
  unfold SpecAMQP.Ref.Connection.integerField at h
  repeat' split at h
  all_goals
    first
      | exact ⟨_, by simpa using h.symm⟩
      | simp_all

private theorem ref_openBounds_shape (body : SpecAMQP.Ref.Value)
    {r : SpecAMQP.Ref.Connection.Refusal}
    (h : SpecAMQP.Ref.Connection.openBounds body = .error r) :
    ∃ prose, r = SpecAMQP.Ref.Connection.refuseWith
      SpecAMQP.Ref.Connection.invalidFieldCondition "malformed" prose := by
  unfold SpecAMQP.Ref.Connection.openBounds at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  cases h1 : SpecAMQP.Ref.Connection.integerField "open" "max-frame-size" body with
  | error e =>
    simp only [h1] at h
    obtain ⟨prose, hp⟩ := ref_integerField_shape "open" "max-frame-size" body h1
    cases h
    exact ⟨prose, hp⟩
  | ok v =>
    simp only [h1] at h
    cases h2 : SpecAMQP.Ref.Connection.integerField "open" "channel-max" body with
    | error e =>
      simp only [h2] at h
      obtain ⟨prose, hp⟩ := ref_integerField_shape "open" "channel-max" body h2
      cases h
      exact ⟨prose, hp⟩
    | ok w =>
      simp only [h2] at h
      simp at h

/-- The AMQP-layer frame step, matched: whatever the reference answers, the specification answers
the same thing, leaving related states and writing the same octets. -/
theorem stepAmqpFrame_matched
    (s : SpecAMQP.Spec.Connection.Endpoint) (i : SpecAMQP.Ref.Connection.Peer)
    (hR : refPeerOf s = i) (outbound : Bool) (channel size : Nat)
    (sbody : SpecAMQP.Spec.Codec.Value) (rbody : SpecAMQP.Ref.Value) (wrote : Octets)
    (hc : FrameCorresponds s i outbound sbody rbody)
    (hafter : ∀ (d : SpecAMQP.Spec.Connection.Limits),
      refPeerOf (SpecAMQP.Spec.Connection.Endpoint.afterFrame s outbound
        (SpecAMQP.Spec.Connection.roleOfBody sbody) d) =
      SpecAMQP.Ref.Connection.placed i outbound (SpecAMQP.Ref.Connection.kindOfBody rbody)
        (refBounds d))
    : AnswersMatch
        (SpecAMQP.Spec.Connection.stepAmqpFrame s outbound channel size sbody wrote)
        (SpecAMQP.Ref.Connection.takeFrame i outbound channel size rbody)
        (if outbound then [wrote] else []) := by
  subst i
  unfold SpecAMQP.Spec.Connection.stepAmqpFrame SpecAMQP.Spec.Connection.refuseUnless
    SpecAMQP.Ref.Connection.takeFrame
  have hkind : SpecAMQP.Ref.Connection.kindOfBody rbody =
      refRoleKind (SpecAMQP.Spec.Connection.roleOfBody sbody) := hc.role.symm
  have hb1 : ((SpecAMQP.Ref.Connection.kindOfBody rbody ==
        SpecAMQP.Ref.Connection.Kind.saslFrame) = true) ↔
      ¬ ((SpecAMQP.Spec.Connection.roleOfBody sbody !=
        SpecAMQP.Spec.Connection.FrameRole.sasl) = true) := by
    rw [hkind]
    cases h : SpecAMQP.Spec.Connection.roleOfBody sbody <;> decide
  by_cases h1 : (SpecAMQP.Spec.Connection.roleOfBody sbody !=
      SpecAMQP.Spec.Connection.FrameRole.sasl) = true
  · have hne : SpecAMQP.Spec.Connection.roleOfBody sbody ≠
        SpecAMQP.Spec.Connection.FrameRole.sasl := by
      intro hh
      rw [hh] at h1
      exact absurd h1 (by decide)
    have hr1 : ¬ ((SpecAMQP.Ref.Connection.kindOfBody rbody ==
        SpecAMQP.Ref.Connection.Kind.saslFrame) = true) := fun hh => hb1.mp hh h1
    try simp only []
    rw (config := { transparency := .default }) [if_pos h1]
    rw (config := { transparency := .default }) [if_neg hr1]
    try simp only []
    have hb2 : (if outbound = true then
          SpecAMQP.Ref.Connection.maySend (refPeerOf s).state
            (SpecAMQP.Ref.Connection.kindOfBody rbody)
        else
          SpecAMQP.Ref.Connection.mayReceive (refPeerOf s).state
            (SpecAMQP.Ref.Connection.kindOfBody rbody))
        = (if outbound = true then
          SpecAMQP.Spec.Connection.permitsSend s.state
            (SpecAMQP.Spec.Connection.roleOfBody sbody)
        else
          SpecAMQP.Spec.Connection.permitsReceive s.state
            (SpecAMQP.Spec.Connection.roleOfBody sbody)) := by
      by_cases hout : outbound = true
      · simp only [if_pos hout]
        exact (hc.send hne).symm
      · simp only [if_neg hout]
        exact (hc.receive hne).symm
    by_cases h2 : (if outbound = true then
          SpecAMQP.Spec.Connection.permitsSend s.state
            (SpecAMQP.Spec.Connection.roleOfBody sbody)
        else
          SpecAMQP.Spec.Connection.permitsReceive s.state
            (SpecAMQP.Spec.Connection.roleOfBody sbody)) = true
    · have hr2 : ¬ ((!(if outbound = true then
            SpecAMQP.Ref.Connection.maySend (refPeerOf s).state
              (SpecAMQP.Ref.Connection.kindOfBody rbody)
          else
            SpecAMQP.Ref.Connection.mayReceive (refPeerOf s).state
              (SpecAMQP.Ref.Connection.kindOfBody rbody))) = true) := by
        rw [hb2, h2]
        decide
      try simp only []
      rw (config := { transparency := .default }) [if_pos h2]
      rw (config := { transparency := .default }) [if_neg hr2]
      try simp only []
      have hb3 : ((SpecAMQP.Ref.Connection.kindOfBody rbody ==
            SpecAMQP.Ref.Connection.Kind.open && channel != 0) = true) ↔
          ¬ ((SpecAMQP.Spec.Connection.roleOfBody sbody !=
            SpecAMQP.Spec.Connection.FrameRole.open || channel == 0) = true) := by
        rw [hkind]
        cases h : SpecAMQP.Spec.Connection.roleOfBody sbody <;>
          (by_cases hch : channel = 0 <;>
            first
              | (simp only [hch]
                 decide)
              | (have hc0 : (channel == 0) = false := by simpa using hch
                 have hc1 : (channel != 0) = true := by simpa using hch
                 simp only [hc0, hc1]
                 decide))
      by_cases h3 : (SpecAMQP.Spec.Connection.roleOfBody sbody !=
          SpecAMQP.Spec.Connection.FrameRole.open || channel == 0) = true
      · have hr3 : ¬ ((SpecAMQP.Ref.Connection.kindOfBody rbody ==
            SpecAMQP.Ref.Connection.Kind.open && channel != 0) = true) :=
          fun hh => hb3.mp hh h3
        try simp only []
        rw (config := { transparency := .default }) [if_pos h3]
        rw (config := { transparency := .default }) [if_neg hr3]
        try simp only []
        have hb4 : ((!(match SpecAMQP.Ref.Connection.kindOfBody rbody with
              | SpecAMQP.Ref.Connection.Kind.open =>
                SpecAMQP.Ref.Connection.missingMandatory "open" rbody
              | SpecAMQP.Ref.Connection.Kind.close =>
                SpecAMQP.Ref.Connection.missingMandatory "close" rbody
              | x => []).isEmpty) = true) ↔
            ¬ ((match SpecAMQP.Spec.Connection.roleOfBody sbody with
              | SpecAMQP.Spec.Connection.FrameRole.open =>
                SpecAMQP.Spec.Connection.missingMandatory "open" sbody
              | SpecAMQP.Spec.Connection.FrameRole.close =>
                SpecAMQP.Spec.Connection.missingMandatory "close" sbody
              | x => []).isEmpty = true) := by
          rw [hkind]
          cases h : SpecAMQP.Spec.Connection.roleOfBody sbody
          · simp only [refRoleKind, ← hc.mandatoryOpen]
            by_cases hh : (SpecAMQP.Spec.Connection.missingMandatory "open" sbody).isEmpty =
                true
            · simp only [hh]
              decide
            · have hb : (SpecAMQP.Spec.Connection.missingMandatory "open" sbody).isEmpty =
                  false := Bool.eq_false_iff.mpr hh
              simp only [hb]
              decide
          · simp only [refRoleKind, ← hc.mandatoryClose]
            by_cases hh : (SpecAMQP.Spec.Connection.missingMandatory "close" sbody).isEmpty =
                true
            · simp only [hh]
              decide
            · have hb : (SpecAMQP.Spec.Connection.missingMandatory "close" sbody).isEmpty =
                  false := Bool.eq_false_iff.mpr hh
              simp only [hb]
              decide
          · simp only [refRoleKind]
            decide
          · simp only [refRoleKind]
            decide
        by_cases h4 : (match SpecAMQP.Spec.Connection.roleOfBody sbody with
              | SpecAMQP.Spec.Connection.FrameRole.open =>
                SpecAMQP.Spec.Connection.missingMandatory "open" sbody
              | SpecAMQP.Spec.Connection.FrameRole.close =>
                SpecAMQP.Spec.Connection.missingMandatory "close" sbody
              | x => []).isEmpty = true
        · have hr4 : ¬ ((!(match SpecAMQP.Ref.Connection.kindOfBody rbody with
                | SpecAMQP.Ref.Connection.Kind.open =>
                  SpecAMQP.Ref.Connection.missingMandatory "open" rbody
                | SpecAMQP.Ref.Connection.Kind.close =>
                  SpecAMQP.Ref.Connection.missingMandatory "close" rbody
                | x => []).isEmpty) = true) := fun hh => hb4.mp hh h4
          try simp only []
          rw (config := { transparency := .default }) [if_pos h4]
          rw (config := { transparency := .default }) [if_neg hr4]
          try simp only []
          have hb5 : (size > (SpecAMQP.Ref.Connection.boundsFor (refPeerOf s) outbound).frames) ↔
              ¬ (decide (size ≤
                (SpecAMQP.Spec.Connection.limitsFor s outbound).maxFrameSize) = true) := by
            rw [← hc.limits]
            simp only [decide_eq_true_eq]
            exact ⟨fun hh => Nat.not_le.mpr hh, fun hh => Nat.lt_of_not_le hh⟩
          by_cases h5 : decide (size ≤
              (SpecAMQP.Spec.Connection.limitsFor s outbound).maxFrameSize) = true
          · have hr5 : ¬ (size >
                (SpecAMQP.Ref.Connection.boundsFor (refPeerOf s) outbound).frames) :=
              fun hh => hb5.mp hh h5
            try simp only []
            rw (config := { transparency := .default }) [if_pos h5]
            rw (config := { transparency := .default }) [if_neg hr5]
            try simp only []
            have hb6 : (channel >
                  (SpecAMQP.Ref.Connection.boundsFor (refPeerOf s) outbound).channels) ↔
                ¬ (decide (channel ≤
                  (SpecAMQP.Spec.Connection.limitsFor s outbound).channelMax) = true) := by
              rw [← hc.limits]
              simp only [decide_eq_true_eq]
              exact ⟨fun hh => Nat.not_le.mpr hh, fun hh => Nat.lt_of_not_le hh⟩
            by_cases h6 : decide (channel ≤
                (SpecAMQP.Spec.Connection.limitsFor s outbound).channelMax) = true
            · have hr6 : ¬ (channel >
                  (SpecAMQP.Ref.Connection.boundsFor (refPeerOf s) outbound).channels) :=
                fun hh => hb6.mp hh h6
              try simp only []
              rw (config := { transparency := .default }) [if_pos h6]
              rw (config := { transparency := .default }) [if_neg hr6]
              try simp only []
              have hb7 : (SpecAMQP.Ref.Connection.kindOfBody rbody ==
                    SpecAMQP.Ref.Connection.Kind.open) =
                  (SpecAMQP.Spec.Connection.roleOfBody sbody ==
                    SpecAMQP.Spec.Connection.FrameRole.open) := by
                rw [hkind]
                cases h : SpecAMQP.Spec.Connection.roleOfBody sbody <;> decide
              by_cases h7 : (SpecAMQP.Spec.Connection.roleOfBody sbody ==
                  SpecAMQP.Spec.Connection.FrameRole.open) = true
              · have hr7 : (SpecAMQP.Ref.Connection.kindOfBody rbody ==
                    SpecAMQP.Ref.Connection.Kind.open) = true := by
                  rw [hb7]
                  exact h7
                try simp only []
                rw (config := { transparency := .default }) [if_pos h7]
                rw (config := { transparency := .default }) [if_pos hr7]
                try simp only []
                cases hl : SpecAMQP.Spec.Connection.openLimits sbody with
                | ok l =>
                  obtain ⟨m, hm⟩ := hc.declaredShape.mp ⟨l, hl⟩
                  simp only [hm, bind, Except.bind, pure, Except.pure]
                  rw [← hc.declaredOk l m hl hm]
                  constructor
                  · intro out hout
                    cases hout
                    exact ⟨_, rfl, hafter l, rfl⟩
                  · intro r' hr'
                    cases hr'
                | error e =>
                  obtain ⟨prose, he⟩ := spec_openLimits_shape sbody hl
                  have hnone : ¬ ∃ m, SpecAMQP.Ref.Connection.openBounds rbody = .ok m := by
                    intro hh
                    obtain ⟨l, hl'⟩ := hc.declaredShape.mpr hh
                    rw [hl] at hl'
                    cases hl'
                  cases hm : SpecAMQP.Ref.Connection.openBounds rbody with
                  | ok m => exact absurd ⟨m, hm⟩ hnone
                  | error e' =>
                    obtain ⟨prose', he'⟩ := ref_openBounds_shape rbody hm
                    try simp only [bind, Except.bind, pure, Except.pure]
                    constructor
                    · intro out hout
                      cases hout
                    · intro r' hr'
                      cases hr'
                      rw [he, he']
                      exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
              · have hr7 : ¬ ((SpecAMQP.Ref.Connection.kindOfBody rbody ==
                    SpecAMQP.Ref.Connection.Kind.open) = true) := by
                  rw [hb7]
                  exact fun hh => h7 hh
                try simp only []
                rw (config := { transparency := .default }) [if_neg h7]
                rw (config := { transparency := .default }) [if_neg hr7]
                try simp only []
                constructor
                · intro out hout
                  cases hout
                  exact ⟨_, rfl, hafter SpecAMQP.Spec.Connection.Limits.aPriori, rfl⟩
                · intro r' hr'
                  cases hr'
            · have hr6 : (channel >
                  (SpecAMQP.Ref.Connection.boundsFor (refPeerOf s) outbound).channels) :=
                hb6.mpr h6
              try simp only []
              rw (config := { transparency := .default }) [if_neg h6]
              rw (config := { transparency := .default }) [if_pos hr6]
              try simp only []
              constructor
              · intro out hout
                cases hout
              · intro r' hr'
                cases hr'
                exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
          · have hr5 : (size >
                (SpecAMQP.Ref.Connection.boundsFor (refPeerOf s) outbound).frames) :=
              hb5.mpr h5
            try simp only []
            rw (config := { transparency := .default }) [if_neg h5]
            rw (config := { transparency := .default }) [if_pos hr5]
            try simp only []
            constructor
            · intro out hout
              cases hout
            · intro r' hr'
              cases hr'
              exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
        · have hr4 : ((!(match SpecAMQP.Ref.Connection.kindOfBody rbody with
                | SpecAMQP.Ref.Connection.Kind.open =>
                  SpecAMQP.Ref.Connection.missingMandatory "open" rbody
                | SpecAMQP.Ref.Connection.Kind.close =>
                  SpecAMQP.Ref.Connection.missingMandatory "close" rbody
                | x => []).isEmpty) = true) := hb4.mpr h4
          try simp only []
          rw (config := { transparency := .default }) [if_neg h4]
          rw (config := { transparency := .default }) [if_pos hr4]
          try simp only []
          constructor
          · intro out hout
            cases hout
          · intro r' hr'
            cases hr'
            exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
      · have hr3 : ((SpecAMQP.Ref.Connection.kindOfBody rbody ==
            SpecAMQP.Ref.Connection.Kind.open && channel != 0) = true) := hb3.mpr h3
        try simp only []
        rw (config := { transparency := .default }) [if_neg h3]
        rw (config := { transparency := .default }) [if_pos hr3]
        try simp only []
        constructor
        · intro out hout
          cases hout
        · intro r' hr'
          cases hr'
          exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
    · have hr2 : ((!(if outbound = true then
            SpecAMQP.Ref.Connection.maySend (refPeerOf s).state
              (SpecAMQP.Ref.Connection.kindOfBody rbody)
          else
            SpecAMQP.Ref.Connection.mayReceive (refPeerOf s).state
              (SpecAMQP.Ref.Connection.kindOfBody rbody))) = true) := by
        rw [hb2]
        rw [Bool.eq_false_iff.mpr h2]
        decide
      try simp only []
      rw (config := { transparency := .default }) [if_neg h2]
      rw (config := { transparency := .default }) [if_pos hr2]
      try simp only []
      constructor
      · intro out hout
        cases hout
      · intro r' hr'
        cases hr'
        exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
  · have hr1 : ((SpecAMQP.Ref.Connection.kindOfBody rbody ==
        SpecAMQP.Ref.Connection.Kind.saslFrame) = true) := hb1.mpr h1
    try simp only []
    rw (config := { transparency := .default }) [if_neg h1]
    rw (config := { transparency := .default }) [if_pos hr1]
    try simp only []
    constructor
    · intro out hout
      cases hout
    · intro r' hr'
      cases hr'
      exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

/-! #### 80_composition.lean -/

/-! ## The correspondence between the two layers' submissions, and the composition -/

/-- The submissions that stand for the same step: the same octets carrying the same frame, with bodies
the connection layer reads the same way, or the same protocol header. -/

def SubmissionsCorrespond (sub : SpecAMQP.Spec.Connection.Submission)
    (offer : SpecAMQP.Ref.Connection.Offer) : Prop :=
  match sub, offer with
  | .header sh, .header rh =>
    sh.protocolId.code = rh.protocolId ∧ sh.version.major = rh.major ∧
      sh.version.minor = rh.minor ∧ sh.version.revision = rh.revision
  | .frame ch octets (some sbody), .frame ch' octets' (some rbody) =>
    ch = ch' ∧ octets = octets' ∧ ValuesAgree sbody rbody
  | .frame ch octets none, .frame ch' octets' none => ch = ch' ∧ octets = octets'
  | .arriving a, .arrives b => a = b
  | _, _ => False

/-- One step's answer as the pair the interface returns, compared in the relation: the states are
related, and the outputs are the same sequence. -/

def PairMatches (so : SpecAMQP.Spec.Connection.Endpoint × List Output)
    (ro : SpecAMQP.Ref.Connection.Peer × List Output) : Prop :=
  refPeerOf so.1 = ro.1 ∧ so.2 = ro.2

/-- The step question, at the level both sides answer it: what the specification answers to a
submission, the reference answers to the corresponding one.

The readers' agreement is a parameter of the proposition rather than of the theorem that proves it,
because the arriving case *needs* it: the octets of an arriving buffer become a body on each side
independently, and only `ReadersAgree` says the two bodies are the same body. A `StepAgrees` that left
it out would be the same proposition for every hypothesis, and its arriving case would be a claim about
two readers nothing has related. -/

def StepAgrees : Prop :=
  ∀ (h : ReadersAgree) (s : SpecAMQP.Spec.Connection.Endpoint) (i : SpecAMQP.Ref.Connection.Peer)
    (hR : refPeerOf s = i) (outbound : Bool)
    (sub : SpecAMQP.Spec.Connection.Submission) (offer : SpecAMQP.Ref.Connection.Offer),
    SubmissionsCorrespond sub offer →
    PairMatches (specAnswerOf s (SpecAMQP.Spec.Connection.step s outbound sub))
      (refAnswerOf i outbound offer (SpecAMQP.Ref.Connection.apply i outbound offer))

theorem frameSubmission_of_ref (h : ReadersAgree) (octets : Octets)
    (rframe : SpecAMQP.Ref.Frame.Frame) (used : Nat)
    (hdec : SpecAMQP.Ref.Frame.decodeFrame octets = .ok (rframe, used)) :
    ∃ (sframe : SpecAMQP.Spec.Frame.Frame) (consumed : Nat),
      SpecAMQP.Spec.Frame.decodeFrame octets = .ok (sframe, consumed) ∧
      SubmissionsCorrespond (.frame sframe.channel octets sframe.body)
        (.frame rframe.channel octets rframe.body) := by
  obtain ⟨sframe, consumed, hread, _, hagrees⟩ :=
    (h octets).1 rframe used ((ref_readFrame_ok_iff octets rframe used).mp hdec)
  refine ⟨sframe, consumed, (spec_readFrame_ok_iff octets sframe consumed).mpr hread, ?_⟩
  cases hsb : sframe.body with
  | none =>
    have hrb : rframe.body = none := hagrees.bodyNone.mp hsb
    simp only [SubmissionsCorrespond, hsb, hrb]
    exact ⟨hagrees.channel, trivial⟩
  | some sb =>
    cases hrb : rframe.body with
    | none => exact absurd (hagrees.bodyNone.mpr hrb) (by rw [hsb]; simp)
    | some rb =>
      simp only [SubmissionsCorrespond, hsb, hrb]
      exact ⟨hagrees.channel, trivial, hagrees.body sb rb hsb hrb⟩

/-- The submission the reference reads out of a call is one the specification reads as the same step:
both wrappers ask the same questions of the same octets, so a call one endpoint can read is a call both
can, and they read it as the same step.

The frame half is above, and it is what the value relation and the frame readers' agreement carry: the
channel and the body's contents are the whole of what `SubmissionsCorrespond` asks of a frame. The header
half is the header readers' agreement, which the header slice proves as `refHeader_matched`. -/

theorem submissionsCorrespond_of_call (h : ReadersAgree) (call : ApiCall) :
    ∀ offer, refOfferOf call = some offer →
      ∃ sub, specSubmissionOf call = some sub ∧ SubmissionsCorrespond sub offer := by
  intro offer hoffer
  unfold refOfferOf at hoffer
  cases hoctets : callOctets call with
  | none => exact absurd hoffer (by simp [hoctets])
  | some octets =>
    simp only [hoctets] at hoffer
    by_cases hshape : SpecAMQP.Ref.Connection.looksLikeHeader octets = true
    · -- a protocol header: each endpoint reads it with its own reader, and the header slice proves
      -- the reference's answer is one the specification's reader also gives, octet for octet
      cases hdec : SpecAMQP.Ref.Connection.readHeader octets with
      | error r => exact absurd hoffer (by simp [hshape, hdec])
      | ok rh =>
        simp only [hshape, if_true, hdec, Option.some.injEq] at hoffer
        subst hoffer
        obtain ⟨sh, hsh, hp, hv1, hv2, hv3, _⟩ := (refHeader_matched octets).1 rh hdec
        have hshapeSpec : SpecAMQP.Spec.Connection.headerShaped octets = true := hshape
        refine ⟨.header sh, ?_, ?_⟩
        · simp only [specSubmissionOf, hoctets, hshapeSpec, if_true, hsh, Option.some.injEq]
        · simp only [SubmissionsCorrespond, hp, hv1, hv2, hv3]
          exact ⟨trivial, trivial, trivial, trivial⟩
    · have hshapeF : SpecAMQP.Ref.Connection.looksLikeHeader octets = false := by
        simpa using hshape
      cases hdec : SpecAMQP.Ref.Frame.decodeFrame octets with
      | error message => exact absurd hoffer (by simp [hshapeF, hdec])
      | ok answer =>
        obtain ⟨rframe, used⟩ := answer
        simp only [hshapeF, Bool.false_eq_true, if_false, hdec, Option.some.injEq] at hoffer
        subst hoffer
        obtain ⟨sframe, consumed, hdecS, hcorr⟩ :=
          frameSubmission_of_ref h octets rframe used hdec
        have hshapeSpecF : SpecAMQP.Spec.Connection.headerShaped octets = false := hshapeF
        refine ⟨.frame sframe.channel octets sframe.body, ?_, hcorr⟩
        simp only [specSubmissionOf, hoctets, hshapeSpecF, Bool.false_eq_true, if_false, hdecS,
          Option.some.injEq]

/-- The receive direction: whatever the reference answers for an arriving buffer, the specification
answers the same. The layer decodes header-versus-frame itself — the state's receive column is what says
which is due — so this is where the two readers' agreement enters the connection layer. -/


private theorem ownHeader_eq_none (n : Nat)
    (h : Ref.Connection.statedVersion n = none) :
    Ref.Connection.ownHeader n = none := by
  unfold Ref.Connection.ownHeader
  rw [h]

/-- And where the table states the three numbers, the reference's own header is them: the header
refuses nothing and names the id it was asked about. -/

private theorem ownHeader_eq_some (n a b c : Nat)
    (h : Ref.Connection.statedVersion n = some (a, b, c)) :
    Ref.Connection.ownHeader n = some (⟨n, a, b, c⟩ : Ref.Connection.Header) := by
  unfold Ref.Connection.ownHeader
  rw [h]

/-- The version the reference states for a layer is `none` exactly where the specification's table
states none for it: `version_eq` with the `none` read off. -/

private theorem version_statedVersion_none (l : Spec.Connection.Layer)
    (h : Spec.Connection.Layer.version l = none) :
    Ref.Connection.statedVersion (refLayer l) = none := by
  have hv := version_eq l
  rw [h] at hv
  cases hs : Ref.Connection.statedVersion (refLayer l) with
  | none => rfl
  | some w => rw [hs] at hv; simp at hv

/-- And where the specification states a version, the reference states the same three numbers: the
record is the triple, read out. -/

private theorem version_statedVersion_some (l : Spec.Connection.Layer)
    (v : Spec.Connection.Version) (h : Spec.Connection.Layer.version l = some v) :
    Ref.Connection.statedVersion (refLayer l) = some (v.major, v.minor, v.revision) := by
  have hv := version_eq l
  rw [h] at hv
  cases hs : Ref.Connection.statedVersion (refLayer l) with
  | none => rw [hs] at hv; simp at hv
  | some w =>
    rw [hs] at hv
    rcases w with ⟨a, b, c⟩
    simp only [Option.map_some, Option.some.injEq] at hv
    subst hv
    rfl

/-- The layer map is the specification's own `code` on the protocol id the layer carries, which is
what lets a negotiated layer be compared with the protocol id octet the reference records. -/

private theorem refLayer_protocolId_code (l : Spec.Connection.Layer) :
    refLayer l = (Spec.Connection.Layer.protocolId l).code := by
  cases l <;> rfl

/-- The protocol id the reference speaks, as the specification's own layer: an id whose protocol id
selects a layer is one the reference speaks, and the reference's numbering for that layer is the
specification's own. -/

private theorem speaks_of_layer (p : Spec.Connection.ProtocolId) (l : Spec.Connection.Layer)
    (h : p.layer? = some l) :
    Ref.Connection.speaksId p.code = true ∧ refLayer l = refProtoId p := by
  cases p <;> cases l <;>
    simp_all [Spec.Connection.ProtocolId.layer?, Spec.Connection.ProtocolId.code,
      Ref.Connection.speaksId, Ref.Connection.amqpId, Ref.Connection.saslId, refLayer, refProtoId]

/-- And an id whose protocol id selects no layer is one the reference does not speak: TLS is the only
such octet, and the reference does not speak it either. -/

private theorem not_speaks_of_no_layer (p : Spec.Connection.ProtocolId)
    (h : p.layer? = none) : Ref.Connection.speaksId p.code = false := by
  cases p <;>
    simp_all [Spec.Connection.ProtocolId.layer?, Spec.Connection.ProtocolId.code,
      Ref.Connection.speaksId, Ref.Connection.amqpId, Ref.Connection.saslId]

/-- The specification's reply when its table states a version for the layer: its own header for it. -/

private theorem negotiationReply_ok_shape (l : Spec.Connection.Layer)
    (v : Spec.Connection.Version) (h : Spec.Connection.Layer.version l = some v) :
    Spec.Connection.negotiationReply l = .ok ⟨l.protocolId, v⟩ := by
  unfold Spec.Connection.negotiationReply
  rw [h]

/-- And when the table states none: an `unsupported` refusal, there being no header to answer with. -/

private theorem negotiationReply_error_shape (l : Spec.Connection.Layer)
    (h : Spec.Connection.Layer.version l = none) :
    ∃ detail, Spec.Connection.negotiationReply l =
      .error (Spec.Connection.refusal "unsupported" detail) :=
  ⟨_, by unfold Spec.Connection.negotiationReply; rw [h]⟩

/-- Which header a layer's negotiation answers with, and whether it answers at all: the reply is the
layer's own header — the protocol id the layer carries and the three numbers the constant table states
for it — and the two sides agree that there is one to answer with. The three version conjuncts are the
same numbers under the two trees' names, and the octets conjunct is `headerOctets_eq`: the reply is
compared octet for octet, which is what the corpus's header vector does. -/

theorem negotiationReply_matched (l : Spec.Connection.Layer) :
    (∀ h, Spec.Connection.negotiationReply l = .ok h →
      ∃ h' : Ref.Connection.Header, Ref.Connection.ownHeader (refLayer l) = some h' ∧
        h'.protocolId = h.protocolId.code ∧ h'.major = h.version.major ∧
        h'.minor = h.version.minor ∧ h'.revision = h.version.revision ∧ h'.octets = h.octets) ∧
    ((Spec.Connection.negotiationReply l).isOk = (Ref.Connection.ownHeader (refLayer l)).isSome) := by
  cases hv : Spec.Connection.Layer.version l with
  | none =>
    have hsv := version_statedVersion_none l hv
    have hoh := ownHeader_eq_none (refLayer l) hsv
    constructor
    · intro h hok
      obtain ⟨detail, hd⟩ := negotiationReply_error_shape l hv
      rw [hd] at hok
      cases hok
    · rw [Spec.Connection.negotiationReply, hv, hoh]
      rfl
  | some v =>
    have hsv := version_statedVersion_some l v hv
    have hoh := ownHeader_eq_some (refLayer l) v.major v.minor v.revision hsv
    have hnr := negotiationReply_ok_shape l v hv
    constructor
    · intro h hok
      rw [hnr] at hok
      cases hok
      refine ⟨⟨refLayer l, v.major, v.minor, v.revision⟩, hoh, ?_, ?_, ?_, ?_, ?_⟩
      · exact refLayer_protocolId_code l
      · rfl
      · rfl
      · rfl
      · rw [headerOctets_eq ⟨Spec.Connection.Layer.protocolId l, v⟩,
          refLayer_protocolId_code l]
    · rw [hnr, hoh]
      rfl

/-! ## The readers' refusals, class by class -/

/-- The reference's reader in its shortening branch, the class pinned: a buffer shorter than the
header is refused as `truncated`, whatever prose the refusal carries. -/

private theorem ref_readHeader_short_class (bytes : Octets)
    (h : bytes.size < Ref.Connection.headerWidth) :
    ∃ text, Ref.Connection.readHeader bytes =
      .error (Ref.Connection.refuse "truncated" text) :=
  ⟨_, by unfold Ref.Connection.readHeader; rw [if_pos h]⟩

/-- The specification's reader in the same branch, the same class. -/

private theorem spec_decodeHeader_short_class (bytes : Octets)
    (h : bytes.size < Spec.Connection.headerOctets) :
    ∃ detail, Spec.Connection.decodeHeader bytes =
      .error (Spec.Connection.refusal "truncated" detail) :=
  ⟨_, by unfold Spec.Connection.decodeHeader; rw [if_pos h]⟩

/-- The reference's reader on a buffer that does not begin with the magic: `malformed`. -/

private theorem ref_readHeader_malformed_class (bytes : Octets)
    (h₁ : ¬ bytes.size < Ref.Connection.headerWidth)
    (h₂ : bytes.extract 0 4 != Ref.Connection.magic) :
    ∃ text, Ref.Connection.readHeader bytes =
      .error (Ref.Connection.refuse "malformed" text) :=
  ⟨_, by unfold Ref.Connection.readHeader; rw [if_neg h₁, if_pos h₂]⟩

/-- And the specification's reader on the same buffer. -/

private theorem spec_decodeHeader_malformed_class (bytes : Octets)
    (h₁ : ¬ bytes.size < Spec.Connection.headerOctets)
    (h₂ : bytes.extract 0 4 != Spec.Connection.magic) :
    ∃ detail, Spec.Connection.decodeHeader bytes =
      .error (Spec.Connection.refusal "malformed" detail) :=
  ⟨_, by unfold Spec.Connection.decodeHeader; rw [if_neg h₁, if_pos h₂]⟩

/-- Every refusal the reference's reader raises once past its width and magic checks is an
`unsupported`: the id it does not speak, the version the table does not state and the version that is
not the stated one are one class, as the register reads them, so no branch analysis is needed to pin
it. -/

private theorem ref_readHeader_past_magic_class (bytes : Octets)
    (h₁ : ¬ bytes.size < Ref.Connection.headerWidth)
    (h₂ : ¬ bytes.extract 0 4 != Ref.Connection.magic)
    (r : Ref.Connection.Refusal)
    (h : Ref.Connection.readHeader bytes = .error r) :
    ∃ text, r = Ref.Connection.refuse "unsupported" text := by
  unfold Ref.Connection.readHeader at h
  rw [if_neg h₁, if_neg h₂] at h
  repeat' (first | split at h | simp only [] at h)
  all_goals
    first
      | exact ⟨_, by simpa using h.symm⟩
      | simp_all

/-- And every refusal the specification's reader raises past the same two checks is an `unsupported`,
for the same reason: the id it does not know, the layer it does not speak, the version it does not
state and the version that is not the stated one are one class. -/

private theorem spec_decodeHeader_past_magic_class (bytes : Octets)
    (h₁ : ¬ bytes.size < Spec.Connection.headerOctets)
    (h₂ : ¬ bytes.extract 0 4 != Spec.Connection.magic)
    (r : Spec.Connection.Refusal)
    (h : Spec.Connection.decodeHeader bytes = .error r) :
    ∃ detail, r = Spec.Connection.refusal "unsupported" detail := by
  unfold Spec.Connection.decodeHeader at h
  rw [if_neg h₁, if_neg h₂] at h
  repeat' (first | split at h | simp only [] at h)
  all_goals
    first
      | exact ⟨_, by simpa using h.symm⟩
      | simp_all

/-- The two readers' refusals agree in the condition they name and in the reason class they name, not
just in whether there is one. `refHeader_matched`'s refusal half says the specification refuses
exactly where the reference does; this says the refusal is the same refusal as far as the endpoint
publishes it — the artifact's condition and the register's class — and that is what the corpus's
header vectors compare.

The case split is over the reference's own decision tree, as `refHeader_matched`'s was, but coarser:
the width check and the magic check are each one class on both sides, and *every* branch past them is
`unsupported` on both sides, so the two branches the reference splits further — the id it does not
speak and the version it cannot accept — need no case at all. -/

theorem refHeader_refusal_class (bytes : Octets) :
    ∀ r, Ref.Connection.readHeader bytes = .error r →
      ∃ r' : Spec.Connection.Refusal,
        Spec.Connection.decodeHeader bytes = .error r' ∧
        r'.condition = r.condition ∧ r'.reasonClass = r.reasonClass := by
  intro r herr
  by_cases hw : bytes.size < Ref.Connection.headerWidth
  · obtain ⟨text, ht⟩ := ref_readHeader_short_class bytes hw
    obtain ⟨detail, hd⟩ := spec_decodeHeader_short_class bytes hw
    rw [ht] at herr
    have hr : r = Ref.Connection.refuse "truncated" text := (Except.error.inj herr).symm
    rw [hr]
    exact ⟨Spec.Connection.refusal "truncated" detail, hd, rfl, rfl⟩
  · by_cases hm : bytes.extract 0 4 != Ref.Connection.magic
    · obtain ⟨text, ht⟩ := ref_readHeader_malformed_class bytes hw hm
      obtain ⟨detail, hd⟩ := spec_decodeHeader_malformed_class bytes hw hm
      rw [ht] at herr
      have hr : r = Ref.Connection.refuse "malformed" text := (Except.error.inj herr).symm
      rw [hr]
      exact ⟨Spec.Connection.refusal "malformed" detail, hd, rfl, rfl⟩
    · obtain ⟨text, ht⟩ := ref_readHeader_past_magic_class bytes hw hm r herr
      obtain ⟨rs, hrs⟩ := (refHeader_matched bytes).2 r herr
      obtain ⟨detail, hd⟩ := spec_decodeHeader_past_magic_class bytes hw hm rs hrs
      have hd' : Spec.Connection.decodeHeader bytes =
          .error (Spec.Connection.refusal "unsupported" detail) := by rw [hrs, hd]
      rw [ht]
      exact ⟨Spec.Connection.refusal "unsupported" detail, hd', rfl, rfl⟩

/-! ## The refusal a failed negotiation leaves -/

/-- The two layers' refusals, compared as the endpoint compares them: the condition each names, the
reason class each names, where each leaves the peer — the specification's state under the layer's own
naming map — and what each writes while refusing. Both conjuncts are needed because a failed
negotiation answers in one of two ways: with the peer's own header and the close the table draws to
END, or with nothing at all where the artifact states no version for the layer, which is the case the
second conjunct is for. -/

def RefusalsMatch (so : Except Spec.Connection.Refusal Spec.Connection.Refusal)
    (ro : Except Ref.Connection.Refusal Ref.Connection.Refusal) : Prop :=
  (∀ fixed, so = .ok fixed → ∃ fixed' : Ref.Connection.Refusal, ro = .ok fixed' ∧
     fixed.condition = fixed'.condition ∧ fixed.reasonClass = fixed'.reasonClass ∧
     fixed.state.map refState = fixed'.place ∧ fixed.wrote = fixed'.reply) ∧
  (∀ r', ro = .error r' → ∃ r : Spec.Connection.Refusal, so = .error r ∧
     r.condition = r'.condition ∧ r.reasonClass = r'.reasonClass ∧
     r.state.map refState = r'.place ∧ r.wrote = r'.reply)

/-- The specification's answer to a failed negotiation when there is a reply header to answer with:
the reply's octets and the close to END, with the refusing refusal's condition and class carried
through. -/

private theorem headerFailure_ok_shape (l : Spec.Connection.Layer) (r : Spec.Connection.Refusal)
    (hdr : Spec.Connection.ProtocolHeader)
    (h : Spec.Connection.negotiationReply l = .ok hdr) :
    Spec.Connection.headerFailure l r =
      .ok { r with state := some Spec.Connection.State.end, wrote := [hdr.octets] } := by
  unfold Spec.Connection.headerFailure
  rw [h]
  rfl

/-- And when there is none, the reply's own refusal is the answer. -/

private theorem headerFailure_error_shape (l : Spec.Connection.Layer) (r : Spec.Connection.Refusal)
    (e : Spec.Connection.Refusal) (h : Spec.Connection.negotiationReply l = .error e) :
    Spec.Connection.headerFailure l r = .error e := by
  unfold Spec.Connection.headerFailure
  rw [h]
  rfl

/-- The reference's answer, in the same two shapes: the reply's octets and the close to the
reference's DONE, or the reply's own refusal. -/

private theorem headerRefusal_ok_shape (n : Nat) (r : Ref.Connection.Refusal)
    (hdr : Ref.Connection.Header) (h : Ref.Connection.ownHeader n = some hdr) :
    Ref.Connection.headerRefusal n r =
      .ok { r with place := some Ref.Connection.State.done, reply := [hdr.octets] } := by
  unfold Ref.Connection.headerRefusal
  rw [h]

/-- And the reference's refusal when it has no header to answer with. -/

private theorem headerRefusal_error_shape (n : Nat) (r : Ref.Connection.Refusal)
    (h : Ref.Connection.ownHeader n = none) :
    ∃ text, Ref.Connection.headerRefusal n r =
      .error (Ref.Connection.refuse "unsupported" text) :=
  ⟨_, by unfold Ref.Connection.headerRefusal; rw [h]⟩

/-- A failed header negotiation, answered the same way on the two sides. The answer carries the reply
header — the same header on both sides, by `negotiationReply_matched` — and the close the table draws:
the specification to END, the reference to the reference's DONE, which is the same row. The refusing
refusal keeps its condition and class, and its place and writes come from the answer rather than from
the refusal, which is why the two are hypotheses.

Where the artifact states no version for the layer the two sides agree at the other end: there is no
header to answer with, so both refuse `unsupported`, writing nothing and moving nothing, and the second
conjunct of `RefusalsMatch` is discharged by the refusals' own class instead of by a reply. -/

theorem headerFailure_matched (s : Spec.Connection.Endpoint)
    (i : Ref.Connection.Peer) (hR : refPeerOf s = i) (r : Spec.Connection.Refusal)
    (r' : Ref.Connection.Refusal) (hcond : r.condition = r'.condition)
    (hcls : r.reasonClass = r'.reasonClass) :
    RefusalsMatch (Spec.Connection.headerFailure s.layer r)
      (Ref.Connection.headerRefusal i.protocolId r') := by
  subst i
  rw [show (refPeerOf s).protocolId = refLayer s.layer from rfl]
  cases hv : Spec.Connection.Layer.version s.layer with
  | none =>
    have hsv := version_statedVersion_none s.layer hv
    have hown := ownHeader_eq_none (refLayer s.layer) hsv
    obtain ⟨detail, hnr⟩ := negotiationReply_error_shape s.layer hv
    obtain ⟨text, hhr⟩ := headerRefusal_error_shape (refLayer s.layer) r' hown
    rw [headerFailure_error_shape s.layer r (Spec.Connection.refusal "unsupported" detail) hnr, hhr]
    constructor
    · intro fixed hok
      cases hok
    · intro r'' herr
      have hsub : r'' = Ref.Connection.refuse "unsupported" text := (Except.error.inj herr).symm
      rw [hsub]
      exact ⟨Spec.Connection.refusal "unsupported" detail, rfl, rfl, rfl, rfl, rfl⟩
  | some v =>
    have hsv := version_statedVersion_some s.layer v hv
    have hown := ownHeader_eq_some (refLayer s.layer) v.major v.minor v.revision hsv
    have hnr := negotiationReply_ok_shape s.layer v hv
    obtain ⟨h', hh', hp, hmaj, hmin, hrev, hoct⟩ :=
      (negotiationReply_matched s.layer).1 ⟨Spec.Connection.Layer.protocolId s.layer, v⟩ hnr
    rw [headerFailure_ok_shape s.layer r ⟨Spec.Connection.Layer.protocolId s.layer, v⟩ hnr,
      headerRefusal_ok_shape (refLayer s.layer) r' h' hh']
    constructor
    · intro fixed hok
      cases hok
      refine ⟨{ r' with place := some Ref.Connection.State.done, reply := [h'.octets] },
        rfl, ?_, ?_, ?_, ?_⟩
      · exact hcond
      · exact hcls
      · rfl
      · exact congrArg (fun octets => [octets]) hoct.symm
    · intro r'' herr
      cases herr

/-- And the two answers to a failed negotiation are the same *shape*: both refuse, or both answer
with a header. `RefusalsMatch`'s conjuncts are implications, so on their own they would be satisfied by
one side refusing while the other answers; this is the clause that rules it out, and it is the same two
cases as `headerFailure_matched` with the payloads dropped — the layer has a stated version, so both
sides answer with their own header, or it has none, so both refuse `unsupported`. -/

theorem headerFailure_shapes (s : Spec.Connection.Endpoint) (i : Ref.Connection.Peer)
    (hR : refPeerOf s = i) (r : Spec.Connection.Refusal) (r' : Ref.Connection.Refusal) :
    (Spec.Connection.headerFailure s.layer r).isOk =
      (Ref.Connection.headerRefusal i.protocolId r').isOk := by
  subst i
  rw [show (refPeerOf s).protocolId = refLayer s.layer from rfl]
  cases hv : Spec.Connection.Layer.version s.layer with
  | none =>
    have hsv := version_statedVersion_none s.layer hv
    have hown := ownHeader_eq_none (refLayer s.layer) hsv
    obtain ⟨detail, hnr⟩ := negotiationReply_error_shape s.layer hv
    obtain ⟨text, hhr⟩ := headerRefusal_error_shape (refLayer s.layer) r' hown
    rw [headerFailure_error_shape s.layer r (Spec.Connection.refusal "unsupported" detail) hnr, hhr]
    rfl
  | some v =>
    have hsv := version_statedVersion_some s.layer v hv
    have hown := ownHeader_eq_some (refLayer s.layer) v.major v.minor v.revision hsv
    have hnr := negotiationReply_ok_shape s.layer v hv
    rw [headerFailure_ok_shape s.layer r ⟨Spec.Connection.Layer.protocolId s.layer, v⟩ hnr,
      headerRefusal_ok_shape (refLayer s.layer) r'
        ⟨refLayer s.layer, v.major, v.minor, v.revision⟩ hown]
    rfl

/-! ## The header step -/

/-- The header step, both answers compared and the two answers known to be the same shape. The first
conjunct is the payload comparison the composition needs; the second is the same walk with the
payloads dropped, and it is what rules out the vacuous reading of the first — the two sides cannot
answer with different shapes, because the walk lands every guard the same way.

The walk is over the reference's own decision tree: the protocol id it speaks (`speaksId` against the
specification's `ProtocolId.layer?`, which `speaks_of_layer` and `not_speaks_of_no_layer` carry both
ways), the table's column for the direction (`sendColumn`/`receiveColumn`), and the layer check each
direction makes once the exchange has begun — asked as "is this the layer the exchange is in" on the
specification's side and as "is this the id the exchange records" on the reference's, the two being
one question because the layer and the id are one number (`refLayer_protocolId_code`). The two
directions differ in what the check's refusal does: a header that has already crossed cannot be
un-crossed, so the receive side ends the connection, while the send side refuses the offer with the
frame condition and moves nothing.

The guards are aligned by rewriting each side's *conditions* to literals rather than by eliminating
the `if`s: each guard's condition is a distinct closed-once-rewritten Boolean term, so a `rw` on it
fires on exactly the guard it names, where an `if`-elimination would have to pick between the two
sides' `if`s and the nested ones inside the branch it is walking. What is left after the conditions are
literals is definitional, so each leaf closes by reduction: the refusals agree by `rfl`, and so does
the state the accepted step leaves. -/

private theorem refState_beq_start (st : Spec.Connection.State) :
    (refState st == Ref.Connection.State.start) = (st == Spec.Connection.State.start) := by
  cases st <;> rfl

private theorem refState_ne_start (st : Spec.Connection.State) :
    (refState st != Ref.Connection.State.start) = (st != Spec.Connection.State.start) := by
  cases st <;> rfl

private theorem refPeerOf_ne_start (s : Spec.Connection.Endpoint) :
    ((refPeerOf s).state != Ref.Connection.State.start) =
      (s.state != Spec.Connection.State.start) := by
  rw [show (refPeerOf s).state = refState s.state from rfl, refState_ne_start]

private theorem refPeerOf_protocolId_ne (s : Spec.Connection.Endpoint) (n : Nat) :
    (n != (refPeerOf s).protocolId) = (n != refLayer s.layer) := by
  rw [show (refPeerOf s).protocolId = refLayer s.layer from rfl]

private theorem refState_hdrSent (st : Spec.Connection.State) :
    refState (if st == Spec.Connection.State.start then Spec.Connection.State.hdrSent
              else Spec.Connection.State.hdrExch) =
      (if refState st == Ref.Connection.State.start then Ref.Connection.State.sndHdr
       else Ref.Connection.State.bothHdr) := by
  rw [refState_beq_start st]
  by_cases h : (st == Spec.Connection.State.start) = true
  · rw [h]
    rfl
  · rw [Bool.eq_false_iff.mpr h]
    rfl

private theorem refState_recv (st : Spec.Connection.State) :
    refState (match st with
      | .start => .hdrRcvd | .hdrSent => .hdrExch | .openPipe => .openSent
      | .ocPipe => .closePipe | other => other) =
      (match refState st with
        | .start => .rcvHdr | .sndHdr => .bothHdr | .pipeOpen => .sndOpen
        | .pipeOc => .pipeClose | other => other) := by
  cases st <;> rfl

private theorem refPeerOf_update (s : Spec.Connection.Endpoint) (st : Spec.Connection.State)
    (l : Spec.Connection.Layer) :
    refPeerOf { s with state := st, layer := l } =
      { refPeerOf s with state := refState st, protocolId := refLayer l } := rfl

private theorem refLayer_bne (a b : Spec.Connection.Layer) :
    (refLayer a != refLayer b) = (!(a == b)) := by
  cases a <;> cases b <;> rfl

private theorem hdrPeer_recv_eq (s : Spec.Connection.Endpoint) (l : Spec.Connection.Layer) :
    refPeerOf (Spec.Connection.Endpoint.afterHeaderExchange
        { s with state := (match s.state with
            | .start => .hdrRcvd | .hdrSent => .hdrExch | .openPipe => .openSent
            | .ocPipe => .closePipe | other => other), layer := l }) =
      Ref.Connection.inDialogue
        { refPeerOf s with
          state := (match (refPeerOf s).state with
            | .start => .rcvHdr | .sndHdr => .bothHdr | .pipeOpen => .sndOpen
            | .pipeOc => .pipeClose | other => other),
          protocolId := refLayer l } := by
  rw [afterHeaderExchange_agree, refPeerOf_update]
  try simp only []
  rw [refState_recv]
  try simp only []
  rfl

private theorem stepHeader_matched_aux (s : Spec.Connection.Endpoint) (i : Ref.Connection.Peer)
    (hR : refPeerOf s = i) (outbound : Bool) (sh : Spec.Connection.ProtocolHeader)
    (rh : Ref.Connection.Header) (hcode : sh.protocolId.code = rh.protocolId)
    (hmajor : sh.version.major = rh.major) (hminor : sh.version.minor = rh.minor)
    (hrev : sh.version.revision = rh.revision) :
    AnswersMatch (Spec.Connection.stepHeader s outbound sh)
        (Ref.Connection.takeHeader i outbound rh) (if outbound then [sh.octets] else []) ∧
      ((Spec.Connection.stepHeader s outbound sh).isOk =
        (Ref.Connection.takeHeader i outbound rh).isOk) := by
  have _hmajor := hmajor
  have _hminor := hminor
  have _hrev := hrev
  subst i
  rcases rh with ⟨rid, rmaj, rmin, rrev⟩
  rw [show rid = sh.protocolId.code from hcode.symm]
  unfold Spec.Connection.stepHeader Spec.Connection.refuseUnless Ref.Connection.takeHeader
  cases hlp : sh.protocolId.layer?
  · have hsp := not_speaks_of_no_layer sh.protocolId hlp
    try simp only [bind, Except.bind, pure, Except.pure]
    try simp only []
    rw [hsp]
    refine ⟨?_, rfl⟩
    constructor
    · intro out hout
      cases hout
    · intro r' hr'
      cases hr'
      exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
  · rename_i l
    obtain ⟨hsp, hlay⟩ := speaks_of_layer sh.protocolId l hlp
    have hlay' : refLayer l = sh.protocolId.code := hlay.trans (refProtoId_code sh.protocolId)
    try simp only [bind, Except.bind, pure, Except.pure]
    try simp only []
    rw [hsp]
    by_cases hout : outbound = true
    · rw [hout]
      by_cases hg : (s.state.sendClass == Spec.Connection.SendClass.header) = true
      · have hrg : (Ref.Connection.row (refPeerOf s).state).sendsHeader = true := by
          rw [show (refPeerOf s).state = refState s.state from rfl, ← (sendColumn s.state).1]
          exact hg
        rw [hg, hrg]
        by_cases hst : (s.state != Spec.Connection.State.start) = true
        · rw [refPeerOf_ne_start, hst]
          by_cases hml : (l == s.layer) = true
          · rw [refPeerOf_protocolId_ne s sh.protocolId.code, ← hlay', refLayer_bne, hml]
            refine ⟨?_, rfl⟩
            constructor
            · intro out hout'
              cases hout'
              refine ⟨_, rfl, ?_, rfl⟩
              rw [afterHeaderExchange_agree, refPeerOf_update, refState_hdrSent, hlay']
              try simp only []
              rfl
            · intro r' hr'
              cases hr'
          · rw [refPeerOf_protocolId_ne s sh.protocolId.code, ← hlay', refLayer_bne,
              Bool.eq_false_iff.mpr hml]
            refine ⟨?_, rfl⟩
            constructor
            · intro out hout'
              cases hout'
            · intro r' hr'
              cases hr'
              exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
        · rw [refPeerOf_ne_start, Bool.eq_false_iff.mpr hst]
          refine ⟨?_, rfl⟩
          constructor
          · intro out hout'
            cases hout'
            refine ⟨_, rfl, ?_, rfl⟩
            rw [afterHeaderExchange_agree, refPeerOf_update, refState_hdrSent, hlay']
            try simp only []
            rfl
          · intro r' hr'
            cases hr'
      · have hrf : (Ref.Connection.row (refPeerOf s).state).sendsHeader = false := by
          rw [show (refPeerOf s).state = refState s.state from rfl, ← (sendColumn s.state).1]
          exact Bool.eq_false_iff.mpr hg
        rw [Bool.eq_false_iff.mpr hg, hrf]
        refine ⟨?_, rfl⟩
        constructor
        · intro out hout'
          cases hout'
        · intro r' hr'
          cases hr'
          exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
    · rw [Bool.eq_false_iff.mpr hout]
      by_cases hr : (s.state.receiveClass == Spec.Connection.ReceiveClass.header) = true
      · have hrr : (Ref.Connection.row (refPeerOf s).state).receivesHeader = true := by
          rw [show (refPeerOf s).state = refState s.state from rfl, ← (receiveColumn s.state).1]
          exact hr
        rw [hr, hrr]
        by_cases hst : (s.state != Spec.Connection.State.start) = true
        · rw [refPeerOf_ne_start, hst]
          by_cases hml : (l == s.layer) = true
          · rw [refPeerOf_protocolId_ne s sh.protocolId.code, ← hlay', refLayer_bne, hml]
            refine ⟨?_, rfl⟩
            constructor
            · intro out hout'
              cases hout'
              refine ⟨_, rfl, ?_, rfl⟩
              exact hdrPeer_recv_eq s l
            · intro r' hr'
              cases hr'
          · rw [refPeerOf_protocolId_ne s sh.protocolId.code, ← hlay', refLayer_bne,
              Bool.eq_false_iff.mpr hml]
            refine ⟨?_, rfl⟩
            constructor
            · intro out hout'
              cases hout'
            · intro r' hr'
              cases hr'
              exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
        · rw [refPeerOf_ne_start, Bool.eq_false_iff.mpr hst, ← hlay']
          refine ⟨?_, rfl⟩
          constructor
          · intro out hout'
            cases hout'
            refine ⟨_, rfl, ?_, rfl⟩
            exact hdrPeer_recv_eq s l
          · intro r' hr'
            cases hr'
      · have hrf : (Ref.Connection.row (refPeerOf s).state).receivesHeader = false := by
          rw [show (refPeerOf s).state = refState s.state from rfl, ← (receiveColumn s.state).1]
          exact Bool.eq_false_iff.mpr hr
        rw [Bool.eq_false_iff.mpr hr, hrf]
        refine ⟨?_, rfl⟩
        constructor
        · intro out hout'
          cases hout'
        · intro r' hr'
          cases hr'
          exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

/-- The header step, matched: whatever the reference answers to an offered or arriving header, the
specification answers the same thing — related states, the octets the layout draws, and a refusal
agreeing in condition, class, place and writes. Both directions of `outbound` are covered, and so is
the layer check each direction makes once the exchange has begun: a header that names the other layer
is the table's header-mismatch row, which ends the connection on a received header and refuses the
offer on a sent one. -/

theorem stepHeader_matched (s : Spec.Connection.Endpoint) (i : Ref.Connection.Peer)
    (hR : refPeerOf s = i) (outbound : Bool) (sh : Spec.Connection.ProtocolHeader)
    (rh : Ref.Connection.Header) (hcode : sh.protocolId.code = rh.protocolId)
    (hmajor : sh.version.major = rh.major) (hminor : sh.version.minor = rh.minor)
    (hrev : sh.version.revision = rh.revision) :
    AnswersMatch (Spec.Connection.stepHeader s outbound sh)
      (Ref.Connection.takeHeader i outbound rh) (if outbound then [sh.octets] else []) :=
  (stepHeader_matched_aux s i hR outbound sh rh hcode hmajor hminor hrev).1

/-- And the two answers are the same *shape*: the step either succeeds on both sides or refuses on
both. `AnswersMatch`'s conjuncts are implications, so on their own they would be satisfied by a
specification that refuses while the reference accepts; this is the clause that rules that out, and it
is the same walk as `stepHeader_matched` with the payloads dropped — each leaf lands on two errors or
two successes, where `rfl` closes the goal. -/

theorem stepHeader_shapes (s : Spec.Connection.Endpoint) (i : Ref.Connection.Peer)
    (hR : refPeerOf s = i) (outbound : Bool) (sh : Spec.Connection.ProtocolHeader)
    (rh : Ref.Connection.Header) (hcode : sh.protocolId.code = rh.protocolId)
    (hmajor : sh.version.major = rh.major) (hminor : sh.version.minor = rh.minor)
    (hrev : sh.version.revision = rh.revision) :
    (Spec.Connection.stepHeader s outbound sh).isOk =
      (Ref.Connection.takeHeader i outbound rh).isOk :=
  (stepHeader_matched_aux s i hR outbound sh rh hcode hmajor hminor hrev).2
theorem stepAmqpFrame_shapes (s : SpecAMQP.Spec.Connection.Endpoint)
    (i : SpecAMQP.Ref.Connection.Peer) (hR : refPeerOf s = i) (outbound : Bool)
    (channel size : Nat) (sbody : SpecAMQP.Spec.Codec.Value) (rbody : SpecAMQP.Ref.Value)
    (wrote : Octets) (hc : FrameCorresponds s i outbound sbody rbody)
    (hafter : ∀ (d : SpecAMQP.Spec.Connection.Limits),
      refPeerOf (SpecAMQP.Spec.Connection.Endpoint.afterFrame s outbound
        (SpecAMQP.Spec.Connection.roleOfBody sbody) d) =
      SpecAMQP.Ref.Connection.placed i outbound (SpecAMQP.Ref.Connection.kindOfBody rbody)
        (refBounds d)) :
    (SpecAMQP.Spec.Connection.stepAmqpFrame s outbound channel size sbody wrote).isOk =
      (SpecAMQP.Ref.Connection.takeFrame i outbound channel size rbody).isOk := by
  subst i
  unfold SpecAMQP.Spec.Connection.stepAmqpFrame SpecAMQP.Spec.Connection.refuseUnless
    SpecAMQP.Ref.Connection.takeFrame
  have hkind : SpecAMQP.Ref.Connection.kindOfBody rbody =
      refRoleKind (SpecAMQP.Spec.Connection.roleOfBody sbody) := hc.role.symm
  have hb1 : ((SpecAMQP.Ref.Connection.kindOfBody rbody ==
        SpecAMQP.Ref.Connection.Kind.saslFrame) = true) ↔
      ¬ ((SpecAMQP.Spec.Connection.roleOfBody sbody !=
        SpecAMQP.Spec.Connection.FrameRole.sasl) = true) := by
    rw [hkind]
    cases h : SpecAMQP.Spec.Connection.roleOfBody sbody <;> decide
  by_cases h1 : (SpecAMQP.Spec.Connection.roleOfBody sbody !=
      SpecAMQP.Spec.Connection.FrameRole.sasl) = true
  · have hne : SpecAMQP.Spec.Connection.roleOfBody sbody ≠
        SpecAMQP.Spec.Connection.FrameRole.sasl := by
      intro hh
      rw [hh] at h1
      exact absurd h1 (by decide)
    have hr1 : ¬ ((SpecAMQP.Ref.Connection.kindOfBody rbody ==
        SpecAMQP.Ref.Connection.Kind.saslFrame) = true) := fun hh => hb1.mp hh h1
    try simp only []
    rw (config := { transparency := .default }) [if_pos h1]
    rw (config := { transparency := .default }) [if_neg hr1]
    try simp only []
    have hb2 : (if outbound = true then
          SpecAMQP.Ref.Connection.maySend (refPeerOf s).state
            (SpecAMQP.Ref.Connection.kindOfBody rbody)
        else
          SpecAMQP.Ref.Connection.mayReceive (refPeerOf s).state
            (SpecAMQP.Ref.Connection.kindOfBody rbody))
        = (if outbound = true then
          SpecAMQP.Spec.Connection.permitsSend s.state
            (SpecAMQP.Spec.Connection.roleOfBody sbody)
        else
          SpecAMQP.Spec.Connection.permitsReceive s.state
            (SpecAMQP.Spec.Connection.roleOfBody sbody)) := by
      by_cases hout : outbound = true
      · simp only [if_pos hout]
        exact (hc.send hne).symm
      · simp only [if_neg hout]
        exact (hc.receive hne).symm
    by_cases h2 : (if outbound = true then
          SpecAMQP.Spec.Connection.permitsSend s.state
            (SpecAMQP.Spec.Connection.roleOfBody sbody)
        else
          SpecAMQP.Spec.Connection.permitsReceive s.state
            (SpecAMQP.Spec.Connection.roleOfBody sbody)) = true
    · have hr2 : ¬ ((!(if outbound = true then
            SpecAMQP.Ref.Connection.maySend (refPeerOf s).state
              (SpecAMQP.Ref.Connection.kindOfBody rbody)
          else
            SpecAMQP.Ref.Connection.mayReceive (refPeerOf s).state
              (SpecAMQP.Ref.Connection.kindOfBody rbody))) = true) := by
        rw [hb2, h2]
        decide
      try simp only []
      rw (config := { transparency := .default }) [if_pos h2]
      rw (config := { transparency := .default }) [if_neg hr2]
      try simp only []
      have hb3 : ((SpecAMQP.Ref.Connection.kindOfBody rbody ==
            SpecAMQP.Ref.Connection.Kind.open && channel != 0) = true) ↔
          ¬ ((SpecAMQP.Spec.Connection.roleOfBody sbody !=
            SpecAMQP.Spec.Connection.FrameRole.open || channel == 0) = true) := by
        rw [hkind]
        cases h : SpecAMQP.Spec.Connection.roleOfBody sbody <;>
          (by_cases hch : channel = 0 <;>
            first
              | (simp only [hch]
                 decide)
              | (have hc0 : (channel == 0) = false := by simpa using hch
                 have hc1 : (channel != 0) = true := by simpa using hch
                 simp only [hc0, hc1]
                 decide))
      by_cases h3 : (SpecAMQP.Spec.Connection.roleOfBody sbody !=
          SpecAMQP.Spec.Connection.FrameRole.open || channel == 0) = true
      · have hr3 : ¬ ((SpecAMQP.Ref.Connection.kindOfBody rbody ==
            SpecAMQP.Ref.Connection.Kind.open && channel != 0) = true) :=
          fun hh => hb3.mp hh h3
        try simp only []
        rw (config := { transparency := .default }) [if_pos h3]
        rw (config := { transparency := .default }) [if_neg hr3]
        try simp only []
        have hb4 : ((!(match SpecAMQP.Ref.Connection.kindOfBody rbody with
              | SpecAMQP.Ref.Connection.Kind.open =>
                SpecAMQP.Ref.Connection.missingMandatory "open" rbody
              | SpecAMQP.Ref.Connection.Kind.close =>
                SpecAMQP.Ref.Connection.missingMandatory "close" rbody
              | x => []).isEmpty) = true) ↔
            ¬ ((match SpecAMQP.Spec.Connection.roleOfBody sbody with
              | SpecAMQP.Spec.Connection.FrameRole.open =>
                SpecAMQP.Spec.Connection.missingMandatory "open" sbody
              | SpecAMQP.Spec.Connection.FrameRole.close =>
                SpecAMQP.Spec.Connection.missingMandatory "close" sbody
              | x => []).isEmpty = true) := by
          rw [hkind]
          cases h : SpecAMQP.Spec.Connection.roleOfBody sbody
          · simp only [refRoleKind, ← hc.mandatoryOpen]
            by_cases hh : (SpecAMQP.Spec.Connection.missingMandatory "open" sbody).isEmpty =
                true
            · simp only [hh]
              decide
            · have hb : (SpecAMQP.Spec.Connection.missingMandatory "open" sbody).isEmpty =
                  false := Bool.eq_false_iff.mpr hh
              simp only [hb]
              decide
          · simp only [refRoleKind, ← hc.mandatoryClose]
            by_cases hh : (SpecAMQP.Spec.Connection.missingMandatory "close" sbody).isEmpty =
                true
            · simp only [hh]
              decide
            · have hb : (SpecAMQP.Spec.Connection.missingMandatory "close" sbody).isEmpty =
                  false := Bool.eq_false_iff.mpr hh
              simp only [hb]
              decide
          · simp only [refRoleKind]
            decide
          · simp only [refRoleKind]
            decide
        by_cases h4 : (match SpecAMQP.Spec.Connection.roleOfBody sbody with
              | SpecAMQP.Spec.Connection.FrameRole.open =>
                SpecAMQP.Spec.Connection.missingMandatory "open" sbody
              | SpecAMQP.Spec.Connection.FrameRole.close =>
                SpecAMQP.Spec.Connection.missingMandatory "close" sbody
              | x => []).isEmpty = true
        · have hr4 : ¬ ((!(match SpecAMQP.Ref.Connection.kindOfBody rbody with
                | SpecAMQP.Ref.Connection.Kind.open =>
                  SpecAMQP.Ref.Connection.missingMandatory "open" rbody
                | SpecAMQP.Ref.Connection.Kind.close =>
                  SpecAMQP.Ref.Connection.missingMandatory "close" rbody
                | x => []).isEmpty) = true) := fun hh => hb4.mp hh h4
          try simp only []
          rw (config := { transparency := .default }) [if_pos h4]
          rw (config := { transparency := .default }) [if_neg hr4]
          try simp only []
          have hb5 : (size > (SpecAMQP.Ref.Connection.boundsFor (refPeerOf s) outbound).frames) ↔
              ¬ (decide (size ≤
                (SpecAMQP.Spec.Connection.limitsFor s outbound).maxFrameSize) = true) := by
            rw [← hc.limits]
            simp only [decide_eq_true_eq]
            exact ⟨fun hh => Nat.not_le.mpr hh, fun hh => Nat.lt_of_not_le hh⟩
          by_cases h5 : decide (size ≤
              (SpecAMQP.Spec.Connection.limitsFor s outbound).maxFrameSize) = true
          · have hr5 : ¬ (size >
                (SpecAMQP.Ref.Connection.boundsFor (refPeerOf s) outbound).frames) :=
              fun hh => hb5.mp hh h5
            try simp only []
            rw (config := { transparency := .default }) [if_pos h5]
            rw (config := { transparency := .default }) [if_neg hr5]
            try simp only []
            have hb6 : (channel >
                  (SpecAMQP.Ref.Connection.boundsFor (refPeerOf s) outbound).channels) ↔
                ¬ (decide (channel ≤
                  (SpecAMQP.Spec.Connection.limitsFor s outbound).channelMax) = true) := by
              rw [← hc.limits]
              simp only [decide_eq_true_eq]
              exact ⟨fun hh => Nat.not_le.mpr hh, fun hh => Nat.lt_of_not_le hh⟩
            by_cases h6 : decide (channel ≤
                (SpecAMQP.Spec.Connection.limitsFor s outbound).channelMax) = true
            · have hr6 : ¬ (channel >
                  (SpecAMQP.Ref.Connection.boundsFor (refPeerOf s) outbound).channels) :=
                fun hh => hb6.mp hh h6
              try simp only []
              rw (config := { transparency := .default }) [if_pos h6]
              rw (config := { transparency := .default }) [if_neg hr6]
              try simp only []
              have hb7 : (SpecAMQP.Ref.Connection.kindOfBody rbody ==
                    SpecAMQP.Ref.Connection.Kind.open) =
                  (SpecAMQP.Spec.Connection.roleOfBody sbody ==
                    SpecAMQP.Spec.Connection.FrameRole.open) := by
                rw [hkind]
                cases h : SpecAMQP.Spec.Connection.roleOfBody sbody <;> decide
              by_cases h7 : (SpecAMQP.Spec.Connection.roleOfBody sbody ==
                  SpecAMQP.Spec.Connection.FrameRole.open) = true
              · have hr7 : (SpecAMQP.Ref.Connection.kindOfBody rbody ==
                    SpecAMQP.Ref.Connection.Kind.open) = true := by
                  rw [hb7]
                  exact h7
                try simp only []
                rw (config := { transparency := .default }) [if_pos h7]
                rw (config := { transparency := .default }) [if_pos hr7]
                try simp only []
                cases hl : SpecAMQP.Spec.Connection.openLimits sbody with
                | ok l =>
                  obtain ⟨m, hm⟩ := hc.declaredShape.mp ⟨l, hl⟩
                  rw [hm]
                  rfl
                | error e =>
                  have hnone : ¬ ∃ m, SpecAMQP.Ref.Connection.openBounds rbody = .ok m := by
                    intro hh
                    obtain ⟨l, hl'⟩ := hc.declaredShape.mpr hh
                    rw [hl] at hl'
                    cases hl'
                  cases hm : SpecAMQP.Ref.Connection.openBounds rbody with
                  | ok m => exact absurd ⟨m, hm⟩ hnone
                  | error e' => rfl
              · have hr7 : ¬ ((SpecAMQP.Ref.Connection.kindOfBody rbody ==
                    SpecAMQP.Ref.Connection.Kind.open) = true) := by
                  rw [hb7]
                  exact fun hh => h7 hh
                try simp only []
                rw (config := { transparency := .default }) [if_neg h7]
                rw (config := { transparency := .default }) [if_neg hr7]
                rfl
            · have hr6 : (channel >
                  (SpecAMQP.Ref.Connection.boundsFor (refPeerOf s) outbound).channels) :=
                hb6.mpr h6
              try simp only []
              rw (config := { transparency := .default }) [if_neg h6]
              rw (config := { transparency := .default }) [if_pos hr6]
              rfl
          · have hr5 : (size >
                (SpecAMQP.Ref.Connection.boundsFor (refPeerOf s) outbound).frames) :=
              hb5.mpr h5
            try simp only []
            rw (config := { transparency := .default }) [if_neg h5]
            rw (config := { transparency := .default }) [if_pos hr5]
            rfl
        · have hr4 : ((!(match SpecAMQP.Ref.Connection.kindOfBody rbody with
                | SpecAMQP.Ref.Connection.Kind.open =>
                  SpecAMQP.Ref.Connection.missingMandatory "open" rbody
                | SpecAMQP.Ref.Connection.Kind.close =>
                  SpecAMQP.Ref.Connection.missingMandatory "close" rbody
                | x => []).isEmpty) = true) := hb4.mpr h4
          try simp only []
          rw (config := { transparency := .default }) [if_neg h4]
          rw (config := { transparency := .default }) [if_pos hr4]
          rfl
      · have hr3 : ((SpecAMQP.Ref.Connection.kindOfBody rbody ==
            SpecAMQP.Ref.Connection.Kind.open && channel != 0) = true) := hb3.mpr h3
        try simp only []
        rw (config := { transparency := .default }) [if_neg h3]
        rw (config := { transparency := .default }) [if_pos hr3]
        rfl
    · have hr2 : ((!(if outbound = true then
            SpecAMQP.Ref.Connection.maySend (refPeerOf s).state
              (SpecAMQP.Ref.Connection.kindOfBody rbody)
          else
            SpecAMQP.Ref.Connection.mayReceive (refPeerOf s).state
              (SpecAMQP.Ref.Connection.kindOfBody rbody))) = true) := by
        rw [hb2]
        rw [Bool.eq_false_iff.mpr h2]
        decide
      try simp only []
      rw (config := { transparency := .default }) [if_neg h2]
      rw (config := { transparency := .default }) [if_pos hr2]
      rfl
  · have hr1 : ((SpecAMQP.Ref.Connection.kindOfBody rbody ==
        SpecAMQP.Ref.Connection.Kind.saslFrame) = true) := hb1.mpr h1
    try simp only []
    rw (config := { transparency := .default }) [if_neg h1]
    rw (config := { transparency := .default }) [if_pos hr1]
    rfl
section SaslStep

-- The SASL arm's walk is one long term (the guards of four positions and four performatives),
-- so it needs a larger elaboration budget than the default; the section keeps that and the two
-- linter relaxations to the arm rather than applying them to the whole module.
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

private theorem answers_of_error {r : Spec.Connection.Refusal} {r' : Ref.Connection.Refusal}
    {w : List Octets} (hcond : r.condition = r'.condition)
    (hclass : r.reasonClass = r'.reasonClass) (hplace : r.state.map refState = r'.place)
    (hwrote : r.wrote = r'.reply) : AnswersMatch (.error r) (.error r') w := by
  constructor
  · intro out h
    cases h
  · intro r'' hr
    rw [Except.error.injEq] at hr
    subst hr
    exact ⟨r, rfl, hcond, hclass, hplace, hwrote⟩

/-- A permitted step, on both sides: `AnswersMatch`'s first conjunct fires with the endpoint the step
left, related to the reference's peer by `refPeerOf`, and the octets the specification answered with
are the writs the frame was written with. -/

private theorem answers_of_ok {out : Spec.Connection.Outcome} {i : Ref.Connection.Peer}
    (h : refPeerOf out.endpoint = i) : AnswersMatch (.ok out) (.ok i) out.wrote := by
  constructor
  · intro o ho
    rw [Except.ok.injEq] at ho
    subst ho
    exact ⟨i, rfl, h, rfl⟩
  · intro r' hr
    cases hr

/-! ## What the two guard vocabularies need of each other -/

/-- The two spellings of "this list is non-empty": the reference counts a list to zero, the
specification asks whether it is empty, and the two questions are each other's answer. -/

private theorem not_empty_length (l : List String) : (!l.isEmpty) = !(l.length == 0) := by
  cases l with
  | nil => rfl
  | cons a t => rfl

/-- The announced-mechanism guard: the specification refuses a `sasl-mechanisms` frame that
announces nothing through `isEmpty`, the reference through `length == 0`, and the two lists are the
same list (the hypothesis), so the two guards are the same guard. -/

private theorem announced_guard {announced offered : List String} (h : announced = offered) :
    (!announced.isEmpty) = !(offered.length == 0) := by
  rw [h, not_empty_length]

/-- A predicate that holds, whose negation therefore does not. This is the shape every refusal
"unless" guard has against the reference's "if … then refuse": the reference's condition is the
negation of the specification's, and this is that fact, for a `Bool` that is true. -/

private theorem not_not_true {a : Bool} (h : a = true) : ¬ ((!a) = true) := by
  rw [h]
  exact Bool.false_ne_true

/-- And the same fact the other way: a predicate that fails has a true negation. -/

private theorem not_true_of_not {a : Bool} (h : ¬ (a = true)) : (!a) = true := by
  rw [Bool.eq_false_iff.mpr h]
  rfl

/-- The `sasl-init`'s direction guard. The specification asks whether the sender is *not* the end
that announced the mechanisms — one disjunction over the two directions and the role — and the
reference asks whether the announcer is this same side — one equation against the direction. The
role is the one the mechanisms arm installed, so the two questions are the same question. -/

private theorem init_guard (role : Option Spec.Connection.SaslRole) (outbound : Bool) :
    ((outbound && role == some Spec.Connection.SaslRole.server) ||
        (!outbound && role == some Spec.Connection.SaslRole.client)) =
      (refRole role == some outbound) := by
  cases role with
  | none => cases outbound <;> rfl
  | some r => cases r <;> cases outbound <;> rfl

/-- The outcome arm's "this peer is the server" test: the specification compares its role against
`server`, the reference compares which end announced the mechanisms against `true`, and the role *is*
which end announced. -/

private theorem role_server (role : Option Spec.Connection.SaslRole) :
    (role == some Spec.Connection.SaslRole.server) = (refRole role == some true) := by
  cases role with
  | none => rfl
  | some r => cases r <;> rfl

/-- The role the mechanisms arm installs, read back: the peer that sent the mechanisms is the
server, which is the reference's `announcedBy := some outbound`. -/

private theorem refRole_ofBool (b : Bool) :
    refRole (if b then some Spec.Connection.SaslRole.server
        else some Spec.Connection.SaslRole.client) = some b := by
  cases b <;> rfl

/-- The two layers read a successful outcome's code from the same generated choice table, so the
`ok` code is one number on both sides. -/

private theorem saslOk_eq_successCode :
    Spec.Connection.saslOk = Ref.Connection.successCode := rfl

/-- And they name a code from the same table too, for the same reason. -/

private theorem saslCodeName_eq_declaredCodeName :
    Spec.Connection.saslCodeName = Ref.Connection.declaredCodeName := rfl

/-- A successful outcome establishes the layer: both sides reset to a fresh peer — the
specification to an endpoint that begins again on the AMQP layer, the reference to `Peer.new` — and
`refPeerOf` maps one onto the other. -/

private theorem refPeerOf_established :
    refPeerOf { Spec.Connection.Endpoint.initial with state := .start, layer := .amqp, phase := .absent, role := none, mechanisms := [], localLimits := Spec.Connection.Limits.aPriori, remoteLimits := Spec.Connection.Limits.aPriori } = Ref.Connection.Peer.new := rfl

/-! ## The step -/

/-- **The SASL dialogue's answers agree, and in the same shape.** The walk over the reference's own
decision tree, carrying both halves of the claim at once: what each side answered (the `AnswersMatch`
conjunct), and that both answered about the same side of `Except` (the `isOk` conjunct). The two
halves are one induction because they are decided by the same guards — a leaf that fixes the refusal
also fixes the shape, and a leaf whose guards disagree would fail the `isOk` half rather than pass
vacuously as `AnswersMatch` alone would. -/

theorem stepSaslFrame_pair (s : Spec.Connection.Endpoint) (i : Ref.Connection.Peer)
    (hR : refPeerOf s = i) (outbound : Bool) (size : Nat)
    (sbody : Spec.Codec.Value) (rbody : Ref.Value) (wrote : Octets)
    (hc : SaslCorresponds s i sbody rbody) :
    AnswersMatch (Spec.Connection.stepSaslFrame s outbound size sbody wrote)
        (Ref.Connection.takeSasl i outbound size rbody) (if outbound then [wrote] else []) ∧
      (Spec.Connection.stepSaslFrame s outbound size sbody wrote).isOk =
        (Ref.Connection.takeSasl i outbound size rbody).isOk := by
  subst i
  unfold Spec.Connection.stepSaslFrame Spec.Connection.refuseUnlessComplete
    Ref.Connection.takeSasl Ref.Connection.refuseUnlessComplete
  simp only [Spec.Connection.refuseUnless]
  try dsimp only []
  by_cases hsz : size ≤ Spec.Connection.minMaxFrameSize
  · have hszd : decide (size ≤ Spec.Connection.minMaxFrameSize) = true := decide_eq_true hsz
    have hszr : ¬ (size > Ref.Connection.minMaxFrameSize) := Nat.not_lt.mpr hsz
    rw (config := { transparency := .default }) [if_pos hszd]
    rw (config := { transparency := .default }) [if_neg hszr]
    try simp only [bind, Except.bind, pure, Except.pure]
    obtain ⟨sst, slay, sph, srole, smech, sll, srl⟩ := s

    cases sph with
    | absent =>
      -- the dialogue has not begun: both sides refuse it the same way and move nothing
      try dsimp only [refPhase]
      exact ⟨answers_of_error rfl rfl rfl rfl, rfl⟩
    | awaitingMechanisms =>
      -- the mechanisms arm: the performative, its mandatory fields, the announced list, the role
      try dsimp only [refPhase]
      rw (config := { transparency := .default }) [hc.mechanisms]
      by_cases h1 : (Ref.Connection.saslName rbody == "sasl-mechanisms") = true
      · rw (config := { transparency := .default }) [if_pos h1]
        rw (config := { transparency := .default }) [if_neg (not_not_true h1)]
        try simp only [bind, Except.bind, pure, Except.pure]
        rw (config := { transparency := .default }) [hc.mandatoryMechanisms]
        by_cases h2 : (Ref.Connection.missingMandatory "sasl-mechanisms" rbody).isEmpty = true
        · rw (config := { transparency := .default }) [if_pos h2]
          try rw (config := { transparency := .default }) [if_pos h2]
          try simp only [bind, Except.bind, pure, Except.pure]
          rw (config := { transparency := .default }) [announced_guard hc.declared]
          by_cases h3 : ((Ref.Connection.symbolList
                ((Ref.Connection.valueOfField "sasl-mechanisms" "sasl-server-mechanisms"
                  rbody).getD Ref.Value.null)).length == 0) = true
          · rw (config := { transparency := .default }) [if_neg (not_not_true h3)]
            rw (config := { transparency := .default }) [if_pos h3]
            try simp only [bind, Except.bind, pure, Except.pure]
            exact ⟨answers_of_error rfl rfl rfl rfl, rfl⟩
          · rw (config := { transparency := .default }) [if_pos (not_true_of_not h3)]
            rw (config := { transparency := .default }) [if_neg h3]
            try simp only [bind, Except.bind, pure, Except.pure]
            refine ⟨answers_of_ok ?_, rfl⟩
            simp only [refPeerOf, refPhase, refRole_ofBool, hc.declared]
        · rw (config := { transparency := .default }) [if_neg h2]
          try rw (config := { transparency := .default }) [if_neg h2]
          try simp only [bind, Except.bind, pure, Except.pure]
          exact ⟨answers_of_error rfl rfl rfl rfl, rfl⟩
      · rw (config := { transparency := .default }) [if_neg h1]
        rw (config := { transparency := .default }) [if_pos (not_true_of_not h1)]
        try simp only [bind, Except.bind, pure, Except.pure]
        exact ⟨answers_of_error rfl rfl rfl rfl, rfl⟩
    | mechanismsKnown =>
      -- the init arm: the performative, its mandatory fields, whose turn it is, the mechanism
      try dsimp only [refPhase]
      rw (config := { transparency := .default }) [hc.init]
      by_cases h1 : (Ref.Connection.saslName rbody == "sasl-init") = true
      · rw (config := { transparency := .default }) [if_pos h1]
        rw (config := { transparency := .default }) [if_neg (not_not_true h1)]
        try simp only [bind, Except.bind, pure, Except.pure]
        rw (config := { transparency := .default }) [hc.mandatoryInit]
        by_cases h2 : (Ref.Connection.missingMandatory "sasl-init" rbody).isEmpty = true
        · rw (config := { transparency := .default }) [if_pos h2]
          try rw (config := { transparency := .default }) [if_pos h2]
          try simp only [bind, Except.bind, pure, Except.pure]
          rw (config := { transparency := .default }) [← init_guard srole outbound]
          by_cases h3 : ((outbound && srole == some Spec.Connection.SaslRole.server) ||
              (!outbound && srole == some Spec.Connection.SaslRole.client)) = true
          · rw (config := { transparency := .default }) [if_neg (not_not_true h3)]
            rw (config := { transparency := .default }) [if_pos h3]
            try simp only [bind, Except.bind, pure, Except.pure]
            exact ⟨answers_of_error rfl rfl rfl rfl, rfl⟩
          · rw (config := { transparency := .default }) [if_pos (not_true_of_not h3)]
            rw (config := { transparency := .default }) [if_neg h3]
            try simp only [bind, Except.bind, pure, Except.pure]
            -- the two layers read the init's mechanism with their own accessor, and the two reads
            -- are `hc.chosen`; the membership test is carried across that equation rather than by
            -- rewriting either body, because the two `match` bodies elaborate to distinct (if
            -- definitionally equal) auxiliary matchers and so cannot be found by `rw`
            have hcont : (smech.contains
                  (match Spec.Connection.fieldValue "sasl-init" "mechanism" sbody with
                    | some (.symbol t) => t
                    | _ => "")) =
                (smech.contains
                  (match Ref.Connection.valueOfField "sasl-init" "mechanism" rbody with
                    | some (.symbol t) => t
                    | _ => "")) :=
              congrArg (fun mechanism => smech.contains mechanism) hc.chosen
            by_cases h4 : (smech.contains
                (match Spec.Connection.fieldValue "sasl-init" "mechanism" sbody with
                  | some (.symbol t) => t
                  | _ => "")) = true
            · have h4' : (smech.contains
                    (match Ref.Connection.valueOfField "sasl-init" "mechanism" rbody with
                      | some (.symbol t) => t
                      | _ => "")) = true := by
                rw [← hcont]
                exact h4
              rw (config := { transparency := .default }) [if_pos h4]
              rw (config := { transparency := .default }) [if_neg (not_not_true h4')]
              try simp only [bind, Except.bind, pure, Except.pure]
              refine ⟨answers_of_ok ?_, rfl⟩
              simp only [refPeerOf, refPhase]
            · have h4' : ¬ ((smech.contains
                    (match Ref.Connection.valueOfField "sasl-init" "mechanism" rbody with
                      | some (.symbol t) => t
                      | _ => "")) = true) := by
                rw [← hcont]
                exact h4
              rw (config := { transparency := .default }) [if_neg h4]
              rw (config := { transparency := .default }) [if_pos (not_true_of_not h4')]
              try simp only [bind, Except.bind, pure, Except.pure]
              exact ⟨answers_of_error rfl rfl rfl rfl, rfl⟩
        · rw (config := { transparency := .default }) [if_neg h2]
          try rw (config := { transparency := .default }) [if_neg h2]
          try simp only [bind, Except.bind, pure, Except.pure]
          exact ⟨answers_of_error rfl rfl rfl rfl, rfl⟩
      · rw (config := { transparency := .default }) [if_neg h1]
        rw (config := { transparency := .default }) [if_pos (not_true_of_not h1)]
        try simp only [bind, Except.bind, pure, Except.pure]
        exact ⟨answers_of_error rfl rfl rfl rfl, rfl⟩
    | awaitingOutcome =>
      -- the outcome position: the challenge, the response, the outcome performative, its direction,
      -- its mandatory fields, the code it carries and what a failed outcome leaves
      try dsimp only [refPhase]
      rw (config := { transparency := .default }) [hc.challenge]
      rw (config := { transparency := .default }) [hc.response]
      rw (config := { transparency := .default }) [hc.outcome]
      rw (config := { transparency := .default }) [role_server srole]
      by_cases h1 : (Ref.Connection.saslName rbody == "sasl-challenge") = true
      · rw (config := { transparency := .default }) [if_pos h1]
        try rw (config := { transparency := .default }) [if_pos h1]
        try simp only [bind, Except.bind, pure, Except.pure]
        by_cases h2 : (outbound == (refRole srole == some true)) = true
        · rw (config := { transparency := .default }) [if_pos h2]
          rw (config := { transparency := .default }) [if_neg (not_not_true h2)]
          try simp only [bind, Except.bind, pure, Except.pure]
          rw (config := { transparency := .default }) [hc.mandatoryChallenge]
          by_cases h3 : (Ref.Connection.missingMandatory "sasl-challenge" rbody).isEmpty = true
          · rw (config := { transparency := .default }) [if_pos h3]
            try rw (config := { transparency := .default }) [if_pos h3]
            try simp only [bind, Except.bind, pure, Except.pure]
            refine ⟨answers_of_ok ?_, rfl⟩
            rfl
          · rw (config := { transparency := .default }) [if_neg h3]
            try rw (config := { transparency := .default }) [if_neg h3]
            try simp only [bind, Except.bind, pure, Except.pure]
            exact ⟨answers_of_error rfl rfl rfl rfl, rfl⟩
        · rw (config := { transparency := .default }) [if_neg h2]
          rw (config := { transparency := .default }) [if_pos (not_true_of_not h2)]
          try simp only [bind, Except.bind, pure, Except.pure]
          exact ⟨answers_of_error rfl rfl rfl rfl, rfl⟩
      · rw (config := { transparency := .default }) [if_neg h1]
        try rw (config := { transparency := .default }) [if_neg h1]
        try simp only [bind, Except.bind, pure, Except.pure]
        by_cases h4 : (Ref.Connection.saslName rbody == "sasl-response") = true
        · rw (config := { transparency := .default }) [if_pos h4]
          try rw (config := { transparency := .default }) [if_pos h4]
          try simp only [bind, Except.bind, pure, Except.pure]
          by_cases h5 : (outbound == (refRole srole == some true)) = true
          · rw (config := { transparency := .default }) [if_neg (not_not_true h5)]
            rw (config := { transparency := .default }) [if_pos h5]
            try simp only [bind, Except.bind, pure, Except.pure]
            exact ⟨answers_of_error rfl rfl rfl rfl, rfl⟩
          · rw (config := { transparency := .default }) [if_pos (not_true_of_not h5)]
            rw (config := { transparency := .default }) [if_neg h5]
            try simp only [bind, Except.bind, pure, Except.pure]
            rw (config := { transparency := .default }) [hc.mandatoryResponse]
            by_cases h6 : (Ref.Connection.missingMandatory "sasl-response" rbody).isEmpty = true
            · rw (config := { transparency := .default }) [if_pos h6]
              try rw (config := { transparency := .default }) [if_pos h6]
              try simp only [bind, Except.bind, pure, Except.pure]
              refine ⟨answers_of_ok ?_, rfl⟩
              rfl
            · rw (config := { transparency := .default }) [if_neg h6]
              try rw (config := { transparency := .default }) [if_neg h6]
              try simp only [bind, Except.bind, pure, Except.pure]
              exact ⟨answers_of_error rfl rfl rfl rfl, rfl⟩
        · rw (config := { transparency := .default }) [if_neg h4]
          try rw (config := { transparency := .default }) [if_neg h4]
          try simp only [bind, Except.bind, pure, Except.pure]
          by_cases h7 : (Ref.Connection.saslName rbody == "sasl-outcome") = true
          · rw (config := { transparency := .default }) [if_pos h7]
            rw (config := { transparency := .default }) [if_neg (not_not_true h7)]
            try simp only [bind, Except.bind, pure, Except.pure]
            by_cases h8 : (outbound == (refRole srole == some true)) = true
            · rw (config := { transparency := .default }) [if_pos h8]
              rw (config := { transparency := .default }) [if_neg (not_not_true h8)]
              try simp only [bind, Except.bind, pure, Except.pure]
              rw (config := { transparency := .default }) [hc.mandatoryOutcome]
              by_cases h9 : (Ref.Connection.missingMandatory "sasl-outcome" rbody).isEmpty = true
              · rw (config := { transparency := .default }) [if_pos h9]
                try rw (config := { transparency := .default }) [if_pos h9]
                try simp only [bind, Except.bind, pure, Except.pure]
                cases hread : Spec.Connection.intField "sasl-outcome" "code" sbody with
                | error e =>
                  have hnone : ¬ ∃ m,
                      Ref.Connection.integerField "sasl-outcome" "code" rbody = .ok m := by
                    intro hh
                    obtain ⟨n, hn⟩ := hc.codeShape.mpr hh
                    rw [hread] at hn
                    cases hn
                  cases hread2 : Ref.Connection.integerField "sasl-outcome" "code" rbody with
                  | error e' =>
                    obtain ⟨prose, he⟩ := spec_intField_shape "sasl-outcome" "code" sbody hread
                    obtain ⟨prose', he'⟩ :=
                      ref_integerField_shape "sasl-outcome" "code" rbody hread2
                    try simp only [bind, Except.bind, pure, Except.pure]
                    rw [he, he']
                    exact ⟨answers_of_error rfl rfl rfl rfl, rfl⟩
                  | ok code => exact absurd ⟨code, hread2⟩ hnone
                | ok code =>
                  cases hread2 : Ref.Connection.integerField "sasl-outcome" "code" rbody with
                  | error e' =>
                    obtain ⟨m, hm⟩ := hc.codeShape.mp ⟨code, hread⟩
                    rw [hread2] at hm
                    cases hm
                  | ok code' =>
                    try simp only [bind, Except.bind, pure, Except.pure]
                    rw (config := { transparency := .default }) [hc.codeOk code code' hread hread2]
                    rw (config := { transparency := .default }) [saslCodeName_eq_declaredCodeName]
                    by_cases h10 : (Ref.Connection.declaredCodeName code').isSome = true
                    · rw (config := { transparency := .default }) [if_pos h10]
                      rw (config := { transparency := .default }) [if_neg (not_not_true h10)]
                      try simp only [bind, Except.bind, pure, Except.pure]
                      rw (config := { transparency := .default }) [saslOk_eq_successCode]
                      by_cases h11 : (code' == Ref.Connection.successCode) = true
                      · rw (config := { transparency := .default }) [if_pos h11]
                        try rw (config := { transparency := .default }) [if_pos h11]
                        try simp only [bind, Except.bind, pure, Except.pure]
                        refine ⟨answers_of_ok ?_, rfl⟩
                        exact refPeerOf_established
                      · rw (config := { transparency := .default }) [if_neg h11]
                        try rw (config := { transparency := .default }) [if_neg h11]
                        try simp only [bind, Except.bind, pure, Except.pure]
                        rw (config := { transparency := .default }) [hc.additionalData]
                        by_cases h12 :
                            (Ref.Connection.declaredFieldSet "sasl-outcome" "additional-data"
                              rbody) = true
                        · -- an unsuccessful outcome that sets additional-data
                          rw (config := { transparency := .default }) [if_neg (not_not_true h12)]
                          rw (config := { transparency := .default }) [if_pos h12]
                          try simp only [bind, Except.bind, pure, Except.pure]
                          exact ⟨answers_of_error rfl rfl rfl rfl, rfl⟩
                        · -- an unsuccessful outcome, well formed: both sides refuse it, and the
                          -- class is the code's own declared name
                          rw (config := { transparency := .default }) [if_pos (not_true_of_not h12)]
                          rw (config := { transparency := .default }) [if_neg h12]
                          try simp only [bind, Except.bind, pure, Except.pure]
                          rw (config := { transparency := .default }) [Spec.Connection.saslFailure,
                            Ref.Connection.saslFailure]
                          exact ⟨answers_of_error rfl rfl rfl rfl, rfl⟩
                    · rw (config := { transparency := .default }) [if_neg h10]
                      rw (config := { transparency := .default }) [if_pos (not_true_of_not h10)]
                      try simp only [bind, Except.bind, pure, Except.pure]
                      exact ⟨answers_of_error rfl rfl rfl rfl, rfl⟩
              · rw (config := { transparency := .default }) [if_neg h9]
                try rw (config := { transparency := .default }) [if_neg h9]
                try simp only [bind, Except.bind, pure, Except.pure]
                exact ⟨answers_of_error rfl rfl rfl rfl, rfl⟩
            · rw (config := { transparency := .default }) [if_neg h8]
              rw (config := { transparency := .default }) [if_pos (not_true_of_not h8)]
              try simp only [bind, Except.bind, pure, Except.pure]
              exact ⟨answers_of_error rfl rfl rfl rfl, rfl⟩
          · rw (config := { transparency := .default }) [if_neg h7]
            rw (config := { transparency := .default }) [if_pos (not_true_of_not h7)]
            try simp only [bind, Except.bind, pure, Except.pure]
            exact ⟨answers_of_error rfl rfl rfl rfl, rfl⟩
  · -- the frame is over the layer's own limit: both sides refuse it and write nothing
    have hszd : decide (size ≤ Spec.Connection.minMaxFrameSize) = false :=
      decide_eq_false_iff_not.mpr hsz
    have hszr : size > Ref.Connection.minMaxFrameSize := Nat.lt_of_not_le hsz
    rw (config := { transparency := .default }) [if_neg (Bool.eq_false_iff.mp hszd)]
    rw (config := { transparency := .default }) [if_pos hszr]
    try simp only [bind, Except.bind, pure, Except.pure]
    exact ⟨answers_of_error rfl rfl rfl rfl, rfl⟩

/-- **The SASL dialogue's answers agree.** Whatever the reference answers to one SASL performative —
a refused step, a state the dialogue advanced to, or the layer established — the specification
answers the same thing: the refusal's condition, reason class, placement and octets, or a state the
relation `refPeerOf` maps onto the reference's, with the octets the frame was written with. -/

theorem stepSaslFrame_matched (s : Spec.Connection.Endpoint) (i : Ref.Connection.Peer)
    (hR : refPeerOf s = i) (outbound : Bool) (size : Nat)
    (sbody : Spec.Codec.Value) (rbody : Ref.Value) (wrote : Octets)
    (hc : SaslCorresponds s i sbody rbody) :
    AnswersMatch (Spec.Connection.stepSaslFrame s outbound size sbody wrote)
      (Ref.Connection.takeSasl i outbound size rbody) (if outbound then [wrote] else []) :=
  (stepSaslFrame_pair s i hR outbound size sbody rbody wrote hc).1

/-- **And the two answers are the same shape.** `AnswersMatch`'s two conjuncts are implications, so
they say nothing when one side refuses and the other accepts; this is the half that rules that out,
and it is what the composition needs to compare the two answers as one answer rather than as a
vacuous relation between two. -/

theorem stepSaslFrame_shapes (s : Spec.Connection.Endpoint) (i : Ref.Connection.Peer)
    (hR : refPeerOf s = i) (outbound : Bool) (size : Nat)
    (sbody : Spec.Codec.Value) (rbody : Ref.Value) (wrote : Octets)
    (hc : SaslCorresponds s i sbody rbody) :
    (Spec.Connection.stepSaslFrame s outbound size sbody wrote).isOk =
      (Ref.Connection.takeSasl i outbound size rbody).isOk :=
  (stepSaslFrame_pair s i hR outbound size sbody rbody wrote hc).2

end SaslStep

theorem refBounds_mk (l : Spec.Connection.Limits) :
    refBounds l = ⟨l.maxFrameSize, l.channelMax⟩ := by
  cases l with
  | mk maxFrameSize channelMax => rfl

/-- The reference's a priori condition is the specification's `**` class: an `if` on the
`Bool` test `class == .conforming` is the same choice as a match on the class. -/

theorem if_conforming_eq (c : Spec.Connection.SendClass) (X Y : Ref.Connection.Bounds) :
    (if (c == Spec.Connection.SendClass.conforming) then X else Y) =
      (match c with | .conforming => X | _ => Y) := by
  cases c <;> rfl

/-- The limits a frame is measured against, read the same way by both layers. -/

theorem limitsFor_eq (e : Spec.Connection.Endpoint) (outbound : Bool) :
    refBounds (Spec.Connection.limitsFor e outbound) =
      Ref.Connection.boundsFor (refPeerOf e) outbound := by
  have hcol := (sendColumn e.state).2.2.2.1
  cases outbound with
  | false => rfl
  | true =>
    rw [show Ref.Connection.boundsFor (refPeerOf e) true =
        (if (Ref.Connection.row (refState e.state)).sendsExpected then
          Ref.Connection.Bounds.aPriori else refBounds e.remoteLimits) from rfl]
    rw [show Spec.Connection.limitsFor e true =
        (match e.state.sendClass with
          | .conforming => Spec.Connection.Limits.aPriori
          | _ => e.remoteLimits) from rfl]
    rw [← hcol, if_conforming_eq]
    cases hc : e.state.sendClass <;> rfl

/-! ### The role

`roleOfBody` and `kindOfBody` agree. The three bundle lemmas `role_open_iff`, `role_close_iff` and
`role_sasl_iff` are equalities of two `Bool` tests rather than of the two reads, so the proof cases
both reads down to constructors: the matching pairs are `rfl`, and every mismatched pair is ruled
out by the test both layers make of the role that mismatches. -/

/-- `kindOfBody` never answers `.header`: the reference's kind is one of the four the body's
declared type resolves to, and a protocol header is not one of them. -/

theorem kindOfBody_ne_header (b : Ref.Value) :
    Ref.Connection.kindOfBody b ≠ Ref.Connection.Kind.header := by
  intro h
  simp only [Ref.Connection.kindOfBody] at h
  split at h
  · exact absurd h (by decide)
  · split_ifs at h

/-- The frame's role, read the same way by both layers. -/

theorem ValuesAgree.roleKind_eq {a : Spec.Codec.Value} {b : Ref.Value} (h : ValuesAgree a b) :
    refRoleKind (Spec.Connection.roleOfBody a) = Ref.Connection.kindOfBody b := by
  cases hk : Ref.Connection.kindOfBody b <;>
    cases hr : Spec.Connection.roleOfBody a <;>
    first
      | rfl
      | exact absurd (ValuesAgree.role_open_iff h) (by rw [hr, hk]; decide)
      | exact absurd (ValuesAgree.role_close_iff h) (by rw [hr, hk]; decide)
      | exact absurd (ValuesAgree.role_sasl_iff h) (by rw [hr, hk]; decide)
      | exact absurd hk (kindOfBody_ne_header b)

/-! ### Whether a field is set

`fieldSet` and `declaredFieldSet` are the same test of the same lookup, so the pair is the
`OptionAgree` of the two lookups read as a `Bool`. -/

/-- Whether a lookup found a value that is not null, on the specification's side. -/

private theorem optionAgree_setFlag {P : Option Spec.Codec.Value} {Q : Option Ref.Value}
    (h : OptionAgree P Q) : specSetFlag? P = refSetFlag? Q := by
  cases h with
  | none => rfl
  | some hxy => cases hxy <;> rfl

/-- Whether a field is present and not null, read the same way by both layers: the
artifact's "this field is not set" is the same fact on both sides. -/

theorem ValuesAgree.fieldSet_eq {a : Spec.Codec.Value} {b : Ref.Value} (h : ValuesAgree a b)
    (owner field : String) :
    Spec.Connection.fieldSet owner field a = Ref.Connection.declaredFieldSet owner field b := by
  rw [show Spec.Connection.fieldSet owner field a =
        specSetFlag? (Spec.Connection.fieldValue owner field a) from rfl]
  rw [show Ref.Connection.declaredFieldSet owner field b =
        refSetFlag? (Ref.Connection.valueOfField owner field b) from rfl]
  exact optionAgree_setFlag (ValuesAgree.fieldValue_eq h owner field)

/-! ### An integer field read through the declared type

The two reads check the same things in a different order — the specification refuses a wrongly
typed value before it reads a number, the reference reads the number first — so the discharge is
stated as the two reads' `toOption`, which is the same value on both sides, and the `Except`-shaped
facts `codeOk` and `codeShape` follow from it.

`ValuesAgree.intField_toOption_eq` restates the module's private `intField_toOption_eq`, which the
discharges below cannot see across the module boundary; it is stated on the public `items_eq`
rather than on a `Forall₂` of the item lists. -/

/-- Agreement at any index of two values' item lists, as the optional value the index carries. -/

private theorem optionAgree_items_at {a : Spec.Codec.Value} {b : Ref.Value}
    (h : ValuesAgree a b) (i : Nat) :
    OptionAgree (Spec.Connection.itemsOf a)[i]? (Ref.Connection.fieldList b)[i]? := by
  obtain ⟨hl, hr, hn⟩ := ValuesAgree.items_eq h
  by_cases hx : (Spec.Connection.itemsOf a)[i]? = none
  · rw [hx, (hn i).mp hx]
    exact .none
  · obtain ⟨x, hx'⟩ := Option.ne_none_iff_exists'.mp hx
    obtain ⟨y, hy, hxy⟩ := hl i x hx'
    rw [hx', hy]
    exact .some hxy

/-- The two layers' `if` on a declared field's index: the specification asks `1 ≤ index` and the
reference asks `index == 0`, which are the same test, and both branches are the same choice
between the field's value and "unset". -/

theorem ValuesAgree.intField_toOption_eq {a : Spec.Codec.Value} {b : Ref.Value}
    (h : ValuesAgree a b) (owner field : String) :
    (Spec.Connection.intField owner field a).toOption =
      (Ref.Connection.integerField owner field b).toOption := by
  have hf : Spec.Connection.fieldOf owner field = Ref.Connection.declaredField owner field := rfl
  have hdflt : Spec.Connection.fieldDefault owner field =
      Ref.Connection.declaredDefault owner field := rfl
  have hpd : ∀ t, Spec.Connection.primitiveOf t = Ref.Connection.primitiveOfDeclared t :=
    fun _ => rfl
  simp only [Spec.Connection.intField, Ref.Connection.integerField,
    Spec.Connection.fieldTypeRefusal?, Spec.Connection.fieldValue,
    Ref.Connection.valueOfField, hf, hdflt, hpd]
  rcases hd : Ref.Connection.declaredField owner field with _ | fld
  · dsimp only
    cases hdd : Ref.Connection.declaredDefault owner field <;> rfl
  · dsimp only
    by_cases hidx : 1 ≤ fld.index
    · have hbeq : (fld.index == 0) = false := by
        rw [beq_eq_false_iff_ne]
        omega
      have hfalse : ¬ ((fld.index == 0) = true) := by
        rw [hbeq]
        simp
      rw [if_pos hidx, if_neg hfalse]
      generalize hP : (Spec.Connection.itemsOf a)[fld.index - 1]? = P
      generalize hQ : (Ref.Connection.fieldList b)[fld.index - 1]? = Q
      have hPQ : OptionAgree P Q := by
        rw [← hP, ← hQ]
        exact optionAgree_items_at h (fld.index - 1)
      cases hPQ with
      | none => cases hdd : Ref.Connection.declaredDefault owner field <;> rfl
      | @some x y hxy =>
        have hTN : Spec.Codec.typeName x = Ref.Connection.primitiveName y :=
          ValuesAgree.typeName_eq hxy
        have hVN : Spec.Connection.valueNat x = Ref.Connection.numberOf y :=
          ValuesAgree.number_eq hxy
        by_cases hx : x = .null
        · have hy : y = .null := (ValuesAgree.null_iff hxy).mp hx
          rw [hx, hy]
          cases hdd : Ref.Connection.declaredDefault owner field <;> rfl
        · have hy : y ≠ .null := fun hy' => hx ((ValuesAgree.null_iff hxy).mpr hy')
          simp only []
          cases hD : Ref.Connection.primitiveOfDeclared fld.typeName with
          | none =>
            dsimp only
            cases hnum : Ref.Connection.numberOf y <;>
              cases hnat : Spec.Connection.valueNat x <;>
              simp_all [Except.toOption]
          | some declared =>
            rw [hTN]
            dsimp only
            by_cases hc : (Ref.Connection.primitiveName y == declared) = true
            · rw [if_pos hc]
              dsimp only
              cases hnum : Ref.Connection.numberOf y <;>
                cases hnat : Spec.Connection.valueNat x <;>
                simp_all [Except.toOption]
            · rw [if_neg hc]
              dsimp only
              cases hnum : Ref.Connection.numberOf y <;> simp_all [Except.toOption]
    · have h0 : fld.index = 0 := by omega
      rw [h0]
      cases hdd : Ref.Connection.declaredDefault owner field <;> rfl

/-- A read that is an `ok` is the read whose `toOption` is that `some`. -/

private theorem ok_of_toOption_eq_some {α β : Type} {e : Except β α} {x : α}
    (h : e.toOption = some x) : e = .ok x := by
  cases e with
  | error err => simp [Except.toOption] at h
  | ok y =>
    have h' : some y = some x := by simpa [Except.toOption] using h
    have hy : y = x := Option.some.inj h'
    rw [hy]

/-- The outcome code's two reads agree on the number they carry. -/

theorem ValuesAgree.outcomeCode_ok_eq {a : Spec.Codec.Value} {b : Ref.Value}
    (h : ValuesAgree a b) (n m : Nat)
    (hn : Spec.Connection.intField "sasl-outcome" "code" a = .ok n)
    (hm : Ref.Connection.integerField "sasl-outcome" "code" b = .ok m) : n = m := by
  have hto := ValuesAgree.intField_toOption_eq h "sasl-outcome" "code"
  rw [hn, hm] at hto
  have h' : some n = some m := by simpa [Except.toOption] using hto
  exact Option.some.inj h'

/-- And they either both read a code or both refuse. -/

theorem ValuesAgree.outcomeCode_shape {a : Spec.Codec.Value} {b : Ref.Value}
    (h : ValuesAgree a b) :
    (∃ n, Spec.Connection.intField "sasl-outcome" "code" a = .ok n) ↔
      (∃ m, Ref.Connection.integerField "sasl-outcome" "code" b = .ok m) := by
  have hto := ValuesAgree.intField_toOption_eq h "sasl-outcome" "code"
  constructor
  · intro ⟨n, hn⟩
    refine ⟨n, ok_of_toOption_eq_some ?_⟩
    rw [← hto]
    exact congrArg Except.toOption hn
  · intro ⟨m, hm⟩
    refine ⟨m, ok_of_toOption_eq_some ?_⟩
    rw [hto]
    exact congrArg Except.toOption hm

/-! ### The limits an `open` declares, in the pair's own order -/

/-- The two layers read the same `open` limits: the `Bounds` the reference read is the `Limits`
the specification read. -/

theorem ValuesAgree.openLimits_agree {a : Spec.Codec.Value} {b : Ref.Value}
    (h : ValuesAgree a b) (l : Spec.Connection.Limits) (m : Ref.Connection.Bounds)
    (hl : Spec.Connection.openLimits a = .ok l)
    (hm : Ref.Connection.openBounds b = .ok m) : refBounds l = m := by
  rw [refBounds_mk, ← (ValuesAgree.openLimits_shape h).2 l m hl hm]

/-! ### The two discharges -/

/-- Every question the AMQP-layer frame step's guards ask of the two bodies, answered the same way
on both sides. -/

theorem frameCorresponds_of_valuesAgree (s : Spec.Connection.Endpoint) (i : Ref.Connection.Peer)
    (hR : refPeerOf s = i) (outbound : Bool) (sbody : Spec.Codec.Value) (rbody : Ref.Value)
    (h : ValuesAgree sbody rbody) : FrameCorresponds s i outbound sbody rbody where
  role := ValuesAgree.roleKind_eq h
  send := fun hne => by
    rw [permitsSend_eq s.state (Spec.Connection.roleOfBody sbody) hne,
      ValuesAgree.roleKind_eq h]
    rw [show refState s.state = (refPeerOf s).state from rfl, hR]
  receive := fun hne => by
    rw [permitsReceive_eq s.state (Spec.Connection.roleOfBody sbody) hne,
      ValuesAgree.roleKind_eq h]
    rw [show refState s.state = (refPeerOf s).state from rfl, hR]
  mandatoryOpen := ValuesAgree.mandatory_eq h "open"
  mandatoryClose := ValuesAgree.mandatory_eq h "close"
  limits := by rw [limitsFor_eq s outbound, hR]
  declaredOk := ValuesAgree.openLimits_agree h
  declaredShape := (ValuesAgree.openLimits_shape h).1

/-- Every question the SASL step's guards ask of the two bodies, answered the same way on both
sides. The peer parameters are the slice's, which this discharge does not consult: a SASL
performative's questions are asked of the bodies alone. -/
theorem saslCorresponds_of_valuesAgree (s : Spec.Connection.Endpoint) (i : Ref.Connection.Peer)
    (hR : refPeerOf s = i) (sbody : Spec.Codec.Value) (rbody : Ref.Value)
    (h : ValuesAgree sbody rbody) : SaslCorresponds s i sbody rbody where
  mechanisms := ValuesAgree.sasl_mechanisms_iff h
  init := ValuesAgree.sasl_init_iff h
  challenge := ValuesAgree.sasl_challenge_iff h
  response := ValuesAgree.sasl_response_iff h
  outcome := ValuesAgree.sasl_outcome_iff h
  declared := ValuesAgree.mechanisms_eq h
  chosen := ValuesAgree.mechanism_eq h
  mandatoryMechanisms := ValuesAgree.mandatory_eq h "sasl-mechanisms"
  mandatoryInit := ValuesAgree.mandatory_eq h "sasl-init"
  mandatoryChallenge := ValuesAgree.mandatory_eq h "sasl-challenge"
  mandatoryResponse := ValuesAgree.mandatory_eq h "sasl-response"
  mandatoryOutcome := ValuesAgree.mandatory_eq h "sasl-outcome"
  codeOk := ValuesAgree.outcomeCode_ok_eq h
  codeShape := ValuesAgree.outcomeCode_shape h
  additionalData := ValuesAgree.fieldSet_eq h "sasl-outcome" "additional-data"
theorem framingError_eq : Spec.Connection.framingError = Ref.Connection.wireCondition := rfl

theorem illegalState_eq : Spec.Connection.illegalState = Ref.Connection.stateCondition := rfl

/-! ## Two refusals that say the same thing, and where placing them leaves the peer -/

def RefusalsAgree (r : Spec.Connection.Refusal) (r' : Ref.Connection.Refusal) : Prop :=
  r.condition = r'.condition ∧ r.reasonClass = r'.reasonClass ∧
    r.state.map refState = r'.place ∧ r.wrote = r'.reply

theorem placement_agrees (s : Spec.Connection.Endpoint) (i : Ref.Connection.Peer)
    (hR : refPeerOf s = i) (outbound : Bool) (r : Spec.Connection.Refusal)
    (r' : Ref.Connection.Refusal) (h : RefusalsAgree r r') :
    RefusalsAgree (Spec.Connection.Refusal.withPlace s outbound r)
      (Ref.Connection.placeRefusal i outbound r') := by
  obtain ⟨hcond, hcls, hplace, hwrote⟩ := h
  subst i
  obtain ⟨state, layer, phase, role, mechanisms, localLimits, remoteLimits⟩ := s
  obtain ⟨pcond, pcls, ptext, pplace, pwrote⟩ := r
  obtain ⟨qcond, qcls, qtext, qplace, qreply⟩ := r'
  simp only [refPeerOf] at hplace
  cases hpp : pplace with
  | some p =>
    cases hqq : qplace with
    | none => rw [hpp, hqq] at hplace; simp at hplace
    | some q =>
      rw [hpp, hqq] at hplace
      simp only [Spec.Connection.Refusal.withPlace, Ref.Connection.placeRefusal]
      exact ⟨hcond, hcls, hplace, hwrote⟩
  | none =>
    cases hqq : qplace with
    | some q => rw [hpp, hqq] at hplace; simp at hplace
    | none =>
      rw [hpp, hqq] at hplace
      simp only [Spec.Connection.Refusal.withPlace, Ref.Connection.placeRefusal]
      cases outbound with
      | true => exact ⟨hcond, hcls, hplace, hwrote⟩
      | false =>
        have hstateEq : (refState state == Ref.Connection.State.done) =
            (state == Spec.Connection.State.end) := by cases state <;> rfl
        have hlayerEq : (refLayer layer == Ref.Connection.saslId) =
            (layer == Spec.Connection.Layer.sasl) := by cases layer <;> rfl
        cases hstate : (state == Spec.Connection.State.end) with
        | true =>
          simp only [refPeerOf, hstateEq, hstate, if_true]
          exact ⟨hcond, hcls, rfl, hwrote⟩
        | false =>
          cases hlayer : (layer == Spec.Connection.Layer.sasl) with
          | true =>
            simp only [refPeerOf, hstateEq, hlayerEq, hstate, hlayer, Bool.false_eq_true,
              if_true, if_false]
            exact ⟨hcond, hcls, rfl, hwrote⟩
          | false =>
            simp only [refPeerOf, hstateEq, hlayerEq, hstate, hlayer, Bool.false_eq_true,
              if_true, if_false]
            exact ⟨hcond, hcls, rfl, hwrote⟩

theorem refState_getD (o : Option Spec.Connection.State) (d : Spec.Connection.State)
    (q : Option Ref.Connection.State) (h : o.map refState = q) :
    refState (o.getD d) = q.getD (refState d) := by
  cases o <;> cases q <;> simp_all

theorem refPeerOf_setState (e : Spec.Connection.Endpoint) (x : Spec.Connection.State) :
    refPeerOf { e with state := x } = { refPeerOf e with state := refState x } := rfl

/-! ## The refusal placed by a step's wrapper, and what it does to the shape -/

def placedSpec (s : Spec.Connection.Endpoint) (outbound : Bool)
    (so : Except Spec.Connection.Refusal Spec.Connection.Outcome) :
    Except Spec.Connection.Refusal Spec.Connection.Outcome :=
  match so with
  | .ok outcome => .ok outcome
  | .error reason => .error (Spec.Connection.Refusal.withPlace s outbound reason)

def placedRef (i : Ref.Connection.Peer) (outbound : Bool)
    (ro : Except Ref.Connection.Refusal Ref.Connection.Peer) :
    Except Ref.Connection.Refusal Ref.Connection.Peer :=
  match ro with
  | .ok peer => .ok peer
  | .error reason => .error (Ref.Connection.placeRefusal i outbound reason)

theorem placedSpec_isOk (s : Spec.Connection.Endpoint) (outbound : Bool)
    (so : Except Spec.Connection.Refusal Spec.Connection.Outcome) :
    (placedSpec s outbound so).isOk = so.isOk := by
  cases so <;> rfl

theorem placedRef_isOk (i : Ref.Connection.Peer) (outbound : Bool)
    (ro : Except Ref.Connection.Refusal Ref.Connection.Peer) :
    (placedRef i outbound ro).isOk = ro.isOk := by
  cases ro <;> rfl

/-! ## The composition's own rules -/

/-- **A step slice's answer, with the shape it agrees on.**

`AnswersMatch`'s two conjuncts are implications keyed in opposite directions — the first on the
*specification* accepting, the second on the *reference* refusing — so they are vacuous
*asymmetrically*, and the direction that is vacuous is the dangerous one. Where the specification
refuses and the reference accepts, both antecedents are false and the relation holds however the two
answers differ, so a reference strictly more permissive than the specification would escape it. The
other mismatch is already caught: where the specification accepts, the first conjunct demands that the
reference accept too. The shape equality closes the escape, and it is what makes the answer the *same
answer* — which is what `PairMatches` compares. Both halves of that sentence are theorems in the
vocabulary section above: `answersMatch_of_spec_refuses` and `not_answersMatch_of_ref_refuses`. -/

def AnswersAgree (so : Except Spec.Connection.Refusal Spec.Connection.Outcome)
    (ro : Except Ref.Connection.Refusal Ref.Connection.Peer) (wrote : List Octets) : Prop :=
  AnswersMatch so ro wrote ∧ so.isOk = ro.isOk

theorem answersMatch_placed (s : Spec.Connection.Endpoint) (i : Ref.Connection.Peer)
    (hR : refPeerOf s = i) (outbound : Bool)
    (so : Except Spec.Connection.Refusal Spec.Connection.Outcome)
    (ro : Except Ref.Connection.Refusal Ref.Connection.Peer) (wrote : List Octets)
    (h : AnswersMatch so ro wrote) :
    AnswersMatch (placedSpec s outbound so) (placedRef i outbound ro) wrote := by
  cases so with
  | ok out =>
    obtain ⟨i', hro, hstate, hwrote⟩ := h.1 out rfl
    rw [hro]
    dsimp only [placedSpec, placedRef]
    refine ⟨fun out' hout' => ?_, fun r' hr' => absurd hr' (by simp)⟩
    obtain rfl := Except.ok.inj hout'
    exact ⟨i', rfl, hstate, hwrote⟩
  | error r =>
    cases ro with
    | ok p =>
      dsimp only [placedSpec, placedRef]
      exact ⟨fun out hout => absurd hout (by simp), fun r' hr' => absurd hr' (by simp)⟩
    | error r' =>
      obtain ⟨r0, hso, hcond, hcls, hplace, hwrote⟩ := h.2 r' rfl
      obtain rfl := Except.error.inj hso
      dsimp only [placedSpec, placedRef]
      obtain ⟨hcond', hcls', hplace', hwrote'⟩ :=
        placement_agrees s i hR outbound r r' ⟨hcond, hcls, hplace, hwrote⟩
      refine ⟨fun out hout => absurd hout (by simp), fun r0' hr0' => ?_⟩
      rw [← Except.error.inj hr0']
      exact ⟨_, rfl, hcond', hcls', hplace', hwrote'⟩

/-- The same, for the shape-bearing relation: the wrapper places a refusal and does not change whether
the step was taken. -/

theorem answersAgree_placed (s : Spec.Connection.Endpoint) (i : Ref.Connection.Peer)
    (hR : refPeerOf s = i) (outbound : Bool)
    (so : Except Spec.Connection.Refusal Spec.Connection.Outcome)
    (ro : Except Ref.Connection.Refusal Ref.Connection.Peer) (wrote : List Octets)
    (h : AnswersAgree so ro wrote) :
    AnswersAgree (placedSpec s outbound so) (placedRef i outbound ro) wrote :=
  ⟨answersMatch_placed s i hR outbound so ro wrote h.1,
   by rw [placedSpec_isOk, placedRef_isOk]; exact h.2⟩

/-- The two layers' refusals for a frame whose octets the frame layer could not read: the class is the
frame layer's own field on both sides, and the condition is the one a wire-level failure carries. -/

theorem fromFrame_refusal_agrees (refusal : Spec.Frame.Refusal) (failure : Ref.Frame.Refusal)
    (hcls : refusal.reasonClass = failure.reasonClass) :
    RefusalsAgree
      ⟨Spec.Connection.framingError, refusal.reasonClass, refusal.message, none, []⟩
      { Ref.Connection.fromFrame failure.message with reasonClass := failure.reasonClass } :=
  ⟨framingError_eq, hcls, rfl, rfl⟩

/-- The error case of the shape-bearing relation, from two refusals that agree. -/

theorem error_answers_agree (s : Spec.Connection.Endpoint) (i : Ref.Connection.Peer)
    (hR : refPeerOf s = i) (outbound : Bool) (r : Spec.Connection.Refusal)
    (r' : Ref.Connection.Refusal) (h : RefusalsAgree r r') :
    AnswersAgree (.error (Spec.Connection.Refusal.withPlace s outbound r))
      (.error (Ref.Connection.placeRefusal i outbound r')) [] := by
  obtain ⟨hcond, hcls, hplace, hwrote⟩ := placement_agrees s i hR outbound r r' h
  refine ⟨⟨fun out hout => absurd hout (by simp), fun r0 hr0 => ?_⟩, rfl⟩
  rw [← Except.error.inj hr0]
  exact ⟨_, rfl, hcond, hcls, hplace, hwrote⟩

/-! ## From a step's answer to the pair the composition compares -/

theorem refusal_answer_matches (s : Spec.Connection.Endpoint) (i : Ref.Connection.Peer)
    (hR : refPeerOf s = i) (outbound : Bool) (offer : Ref.Connection.Offer)
    (r : Spec.Connection.Refusal) (r' : Ref.Connection.Refusal) (h : RefusalsAgree r r') :
    PairMatches (specAnswerOf s (.error r)) (refAnswerOf i outbound offer (.error r')) := by
  obtain ⟨hcond, hcls, hplace, hwrote⟩ := h
  subst i
  refine ⟨?_, ?_⟩
  · simp only [specAnswerOf, refAnswerOf, refPeerOf]
    rw [refState_getD _ _ _ hplace]
  · simp only [specAnswerOf, refAnswerOf, hcond, hcls, hwrote]

theorem ok_answer_matches (s : Spec.Connection.Endpoint) (i : Ref.Connection.Peer)
    (hR : refPeerOf s = i) (outbound : Bool) (offer : Ref.Connection.Offer)
    (out : Spec.Connection.Outcome) (i' : Ref.Connection.Peer)
    (hstate : refPeerOf out.endpoint = i')
    (hwrote : out.wrote = refOfferWrote outbound offer) :
    PairMatches (specAnswerOf s (.ok out)) (refAnswerOf i outbound offer (.ok i')) := by
  subst i
  simp only [specAnswerOf, refAnswerOf]
  refine ⟨hstate, ?_⟩
  rw [hwrote, ← hstate, refState_name out.endpoint.state]
  rfl

/-- **The bridge the composition uses.** A step's answer, in the shape-bearing form, is what the
composition compares: the states are related and the two output sequences are the same one. -/

theorem answersAgree_pairMatches (s : Spec.Connection.Endpoint) (i : Ref.Connection.Peer)
    (hR : refPeerOf s = i) (outbound : Bool) (offer : Ref.Connection.Offer)
    (so : Except Spec.Connection.Refusal Spec.Connection.Outcome)
    (ro : Except Ref.Connection.Refusal Ref.Connection.Peer) (wrote : List Octets)
    (h : AnswersAgree so ro wrote) (hwrote : wrote = refOfferWrote outbound offer) :
    PairMatches (specAnswerOf s so) (refAnswerOf i outbound offer ro) := by
  cases so with
  | ok out =>
    obtain ⟨i', hro, hstate, houtwrote⟩ := h.1.1 out rfl
    rw [hro]
    exact ok_answer_matches s i hR outbound offer out i' hstate (by rw [houtwrote, hwrote])
  | error r =>
    cases ro with
    | ok p => exact absurd h.2 (by simp [Except.isOk, Except.toBool])
    | error r' =>
      obtain ⟨r0, hso, hcond, hcls, hplace, hrwrote⟩ := h.1.2 r' rfl
      cases hso
      exact refusal_answer_matches s i hR outbound offer r r' ⟨hcond, hcls, hplace, hrwrote⟩

/-! ## The frame half of the receive direction -/

/-- The reference's protocol id for a layer is the layer map, read as the reference reads it. -/

theorem refLayer_sasl_iff (l : Spec.Connection.Layer) :
    (refLayer l == Ref.Connection.saslId) = (l == Spec.Connection.Layer.sasl) := by
  cases l <;> rfl

/-- The endpoint a permitted frame leaves is the reference's placement of the reference's peer, on
both sides of the map — the state the diagram draws, the limits the frame declared, and nothing else. -/

theorem afterFrame_comm (s : Spec.Connection.Endpoint) (i : Ref.Connection.Peer)
    (hR : refPeerOf s = i) (outbound : Bool) (sbody : Spec.Codec.Value) (rbody : Ref.Value)
    (hrole : refRoleKind (Spec.Connection.roleOfBody sbody) = Ref.Connection.kindOfBody rbody)
    (d : Spec.Connection.Limits) :
    refPeerOf (Spec.Connection.Endpoint.afterFrame s outbound
        (Spec.Connection.roleOfBody sbody) d) =
      Ref.Connection.placed i outbound (Ref.Connection.kindOfBody rbody) (refBounds d) := by
  subst i
  obtain ⟨state, layer, phase, role, mechanisms, localLimits, remoteLimits⟩ := s
  cases outbound <;> cases hr : Spec.Connection.roleOfBody sbody <;>
    (rw [hr] at hrole) <;> rw [← hrole] <;> cases state <;> rfl

/-- What the specification answers for a frame the receive path has decoded. -/

def frameAnswerSpec (s : Spec.Connection.Endpoint) (bytes : Octets) :
    Except Spec.Connection.Refusal Spec.Connection.Outcome :=
  placedSpec s false
    (match Spec.Frame.readFrame bytes with
     | .error refusal =>
       .error ⟨Spec.Connection.framingError, refusal.reasonClass, refusal.message, none, []⟩
     | .ok (frame, consumed) =>
       match frame.body with
       | none => .ok ⟨s, []⟩
       | some body =>
         if s.layer == Spec.Connection.Layer.sasl then
           Spec.Connection.stepSaslFrame s false consumed body #[]
         else Spec.Connection.stepAmqpFrame s false frame.channel consumed body #[])

/-- What the reference answers for the same frame. -/

def frameAnswerRef (i : Ref.Connection.Peer) (bytes : Octets) :
    Except Ref.Connection.Refusal Ref.Connection.Peer :=
  placedRef i false
    (match Ref.Frame.readFrame bytes with
     | .error failure =>
       .error { Ref.Connection.fromFrame failure.message with
                  reasonClass := failure.reasonClass }
     | .ok (frame, used) =>
       match frame.body with
       | none => .ok i
       | some body =>
         if i.protocolId == Ref.Connection.saslId then
           Ref.Connection.takeSasl i false used body
         else Ref.Connection.takeFrame i false frame.channel used body)

/-- **The frame half of the receive direction.** Which frame arrived is the reader agreement's
business; once it has, the layer's own step answers, and each of the two layer steps is the slice's
lemma, placed by the wrapper the dispatcher applies. -/

theorem arriving_frame_answers (h : ReadersAgree) (s : Spec.Connection.Endpoint)
    (i : Ref.Connection.Peer) (hR : refPeerOf s = i) (bytes : Octets) :
    AnswersAgree (frameAnswerSpec s bytes) (frameAnswerRef i bytes) [] := by
  subst i
  unfold frameAnswerSpec frameAnswerRef placedSpec placedRef
  cases hread : Ref.Frame.readFrame bytes with
  | error failure =>
    obtain ⟨refusal, hspec, hcls⟩ := (h bytes).2 failure hread
    rw [hspec]
    try dsimp only []
    exact error_answers_agree s (refPeerOf s) rfl false _ _
      (fromFrame_refusal_agrees refusal failure hcls)
  | ok answer =>
    obtain ⟨rframe, used⟩ := answer
    obtain ⟨sframe, consumed, hspec, hcons, hagree⟩ := (h bytes).1 rframe used hread
    rw [hspec]
    try dsimp only []
    cases hsb : sframe.body with
    | none =>
      have hrb : rframe.body = none := hagree.bodyNone.mp hsb
      rw [hrb]
      try dsimp only []
      refine ⟨⟨fun out hout => ?_, fun r' hr' => absurd hr' (by simp)⟩, rfl⟩
      obtain rfl := Except.ok.inj hout
      exact ⟨refPeerOf s, rfl, rfl, rfl⟩
    | some sbody =>
      cases hrb : rframe.body with
      | none => exact absurd (hagree.bodyNone.mpr hrb) (by rw [hsb]; simp)
      | some rbody =>
        have hval : ValuesAgree sbody rbody := hagree.body sbody rbody hsb hrb
        try dsimp only []
        have hlayEq : ((refPeerOf s).protocolId == Ref.Connection.saslId) =
            (s.layer == Spec.Connection.Layer.sasl) := by
          rw [refPeerOf]
          exact refLayer_sasl_iff s.layer
        cases hlayer : s.layer with
        | amqp =>
          rw [hlayEq, hlayer, if_neg (by decide), hagree.channel, ← hcons]
          refine ⟨answersMatch_placed s (refPeerOf s) rfl false _ _ _
              (stepAmqpFrame_matched s (refPeerOf s) rfl false rframe.channel consumed sbody rbody
                #[] (frameCorresponds_of_valuesAgree s (refPeerOf s) rfl false sbody rbody hval)
                (afterFrame_comm s (refPeerOf s) rfl false sbody rbody
                  (frameCorresponds_of_valuesAgree s (refPeerOf s) rfl false sbody rbody hval).role)),
            ?_⟩
          show (placedSpec s false (Spec.Connection.stepAmqpFrame s false rframe.channel consumed
              sbody #[])).isOk =
            (placedRef (refPeerOf s) false (Ref.Connection.takeFrame (refPeerOf s) false
              rframe.channel consumed rbody)).isOk
          rw [placedSpec_isOk, placedRef_isOk]
          exact stepAmqpFrame_shapes s (refPeerOf s) rfl false rframe.channel consumed sbody rbody
            #[] (frameCorresponds_of_valuesAgree s (refPeerOf s) rfl false sbody rbody hval)
            (afterFrame_comm s (refPeerOf s) rfl false sbody rbody
              (frameCorresponds_of_valuesAgree s (refPeerOf s) rfl false sbody rbody hval).role)
        | sasl =>
          rw [hlayEq, hlayer, if_pos (by decide), ← hcons]
          refine ⟨answersMatch_placed s (refPeerOf s) rfl false _ _ _
              (stepSaslFrame_matched s (refPeerOf s) rfl false consumed sbody rbody #[]
                (saslCorresponds_of_valuesAgree s (refPeerOf s) rfl sbody rbody hval)), ?_⟩
          show (placedSpec s false (Spec.Connection.stepSaslFrame s false consumed sbody
              #[])).isOk =
            (placedRef (refPeerOf s) false (Ref.Connection.takeSasl (refPeerOf s) false consumed
              rbody)).isOk
          rw [placedSpec_isOk, placedRef_isOk]
          exact stepSaslFrame_shapes s (refPeerOf s) rfl false consumed sbody rbody #[]
            (saslCorresponds_of_valuesAgree s (refPeerOf s) rfl sbody rbody hval)

/-- **The receive direction.** Every question the receive path asks, answered the same way: the receive
column decides header-versus-frame on both sides, the two readers agree on the octets, and the step that
follows is the layer's own. -/

theorem arriving_answers (h : ReadersAgree) (s : Spec.Connection.Endpoint)
    (i : Ref.Connection.Peer) (hR : refPeerOf s = i) (bytes : Octets) :
    AnswersAgree (Spec.Connection.step s false (.arriving bytes))
      (Ref.Connection.apply i false (.arrives bytes)) [] := by
  subst i
  have hcol : (Ref.Connection.row (refState s.state)).receivesHeader =
      (s.state.receiveClass == Spec.Connection.ReceiveClass.header) :=
    ((receiveColumn s.state).1).symm
  unfold Spec.Connection.step Ref.Connection.apply
  try dsimp only []
  cases hrc : s.state.receiveClass with
  | header =>
    have hh : (Ref.Connection.row (refPeerOf s).state).receivesHeader = true := by
      show (Ref.Connection.row (refState s.state)).receivesHeader = true
      rw [hcol, hrc]
      rfl
    have hfalse : ¬ (false = true) := by decide
    have htrue : (true = true) := rfl
    simp only [hh, if_neg hfalse, if_pos htrue]
    try dsimp only []
    cases hread : Ref.Connection.readHeader bytes with
    | ok rh =>
      obtain ⟨sh, hsh, hpid, hmaj, hmin, hrev, _⟩ := (refHeader_matched bytes).1 rh hread
      rw [hsh]
      try dsimp only []
      refine ⟨answersMatch_placed s (refPeerOf s) rfl false _ _ _
          (stepHeader_matched s (refPeerOf s) rfl false sh rh hpid hmaj hmin hrev), ?_⟩
      show (placedSpec s false (Spec.Connection.stepHeader s false sh)).isOk =
        (placedRef (refPeerOf s) false (Ref.Connection.takeHeader (refPeerOf s) false rh)).isOk
      rw [placedSpec_isOk, placedRef_isOk]
      exact stepHeader_shapes s (refPeerOf s) rfl false sh rh hpid hmaj hmin hrev
    | error r =>
      obtain ⟨r', hr', hcond, hcls⟩ := refHeader_refusal_class bytes r hread
      rw [hr']
      try dsimp only []
      obtain ⟨hfok, hferr⟩ := headerFailure_matched s (refPeerOf s) rfl r' r hcond hcls
      have hshape := headerFailure_shapes s (refPeerOf s) rfl r' r
      cases hf : Spec.Connection.headerFailure s.layer r' with
      | ok reply =>
        obtain ⟨fixed, hfixed, hc2, hcl2, hp2, hw2⟩ := hfok reply hf
        rw [hfixed]
        try dsimp only []
        exact error_answers_agree s (refPeerOf s) rfl false reply fixed ⟨hc2, hcl2, hp2, hw2⟩
      | error missing =>
        cases hg : Ref.Connection.headerRefusal (refPeerOf s).protocolId r with
        | ok fixed' =>
          rw [hf, hg] at hshape
          exact absurd hshape (by simp [Except.isOk, Except.toBool])
        | error missing' =>
          obtain ⟨missing0, hso, hc2, hcl2, hp2, hw2⟩ := hferr missing' hg
          rw [hf] at hso
          cases hso
          exact error_answers_agree s (refPeerOf s) rfl false missing missing'
            ⟨hc2, hcl2, hp2, hw2⟩
  | «open» =>
    have hh : (Ref.Connection.row (refPeerOf s).state).receivesHeader = false := by
      show (Ref.Connection.row (refState s.state)).receivesHeader = false
      rw [hcol, hrc]
      rfl
    have hfalse : ¬ (false = true) := by decide
    simp only [hh, if_neg hfalse]
    try dsimp only []
    by_cases hshape : Spec.Connection.headerShaped bytes = true
    · have hshapeR : Ref.Connection.looksLikeHeader bytes = true := hshape
      rw [if_pos hshape, if_pos hshapeR]
      exact error_answers_agree s (refPeerOf s) rfl false _ _
        ⟨framingError_eq, rfl, rfl, rfl⟩
    · have hshapeF : Spec.Connection.headerShaped bytes = false := by simpa using hshape
      have hshapeRF : Ref.Connection.looksLikeHeader bytes = false := hshapeF
      rw [if_neg hshape, if_neg (by simp [hshapeRF])]
      exact arriving_frame_answers h s (refPeerOf s) rfl bytes
  | anyFrame =>
    have hh : (Ref.Connection.row (refPeerOf s).state).receivesHeader = false := by
      show (Ref.Connection.row (refState s.state)).receivesHeader = false
      rw [hcol, hrc]
      rfl
    have hfalse : ¬ (false = true) := by decide
    simp only [hh, if_neg hfalse]
    try dsimp only []
    by_cases hshape : Spec.Connection.headerShaped bytes = true
    · have hshapeR : Ref.Connection.looksLikeHeader bytes = true := hshape
      rw [if_pos hshape, if_pos hshapeR]
      exact error_answers_agree s (refPeerOf s) rfl false _ _
        ⟨framingError_eq, rfl, rfl, rfl⟩
    · have hshapeF : Spec.Connection.headerShaped bytes = false := by simpa using hshape
      have hshapeRF : Ref.Connection.looksLikeHeader bytes = false := hshapeF
      rw [if_neg hshape, if_neg (by simp [hshapeRF])]
      exact arriving_frame_answers h s (refPeerOf s) rfl bytes
  | nothing =>
    have hh : (Ref.Connection.row (refPeerOf s).state).receivesHeader = false := by
      show (Ref.Connection.row (refState s.state)).receivesHeader = false
      rw [hcol, hrc]
      rfl
    have hfalse : ¬ (false = true) := by decide
    simp only [hh, if_neg hfalse]
    try dsimp only []
    by_cases hshape : Spec.Connection.headerShaped bytes = true
    · have hshapeR : Ref.Connection.looksLikeHeader bytes = true := hshape
      rw [if_pos hshape, if_pos hshapeR]
      exact error_answers_agree s (refPeerOf s) rfl false _ _
        ⟨framingError_eq, rfl, rfl, rfl⟩
    · have hshapeF : Spec.Connection.headerShaped bytes = false := by simpa using hshape
      have hshapeRF : Ref.Connection.looksLikeHeader bytes = false := hshapeF
      rw [if_neg hshape, if_neg (by simp [hshapeRF])]
      trace_state
      exact arriving_frame_answers h s (refPeerOf s) rfl bytes

/-- **The receive direction's obligation.** The specification's answer to an arriving buffer is the
reference's: the same endpoint left, and the same octets written. -/

theorem arriving_matched (h : ReadersAgree) (s : Spec.Connection.Endpoint)
    (i : Ref.Connection.Peer) (hR : refPeerOf s = i) (bytes : Octets) :
    PairMatches (specArriving s bytes) (refArriving i bytes) :=
  answersAgree_pairMatches s i hR false (.arrives bytes) _ _ _
    (arriving_answers h s i hR bytes) rfl

/-! ## The step question -/

/-- The bodyless frame of `idle-time-out.7`: it is traffic, it carries no performative, and both layers
leave the endpoint alone and write nothing. -/

theorem frame_none_answers (s : Spec.Connection.Endpoint) (i : Ref.Connection.Peer)
    (hR : refPeerOf s = i) (outbound : Bool) (channel : Nat) (octets : Octets) :
    AnswersAgree (Spec.Connection.step s outbound (.frame channel octets none))
      (Ref.Connection.apply i outbound (.frame channel octets none)) [] := by
  subst i
  have hs : Spec.Connection.step s outbound (.frame channel octets none) = .ok ⟨s, []⟩ := rfl
  have hr : Ref.Connection.apply (refPeerOf s) outbound (.frame channel octets none) =
      .ok (refPeerOf s) := rfl
  rw [hs, hr]
  refine ⟨⟨fun out hout => ?_, fun r' hr' => absurd hr' (by simp)⟩, rfl⟩
  obtain rfl := Except.ok.inj hout
  exact ⟨refPeerOf s, rfl, rfl, rfl⟩

/-- **The step question.** The three slices, composed: the header exchange from the columns the table
states, the AMQP frame from the mandatory rule and the limits, the SASL dialogue from its stages, and the
bodyless frame from both layers leaving the endpoint alone. -/

theorem stepAgrees : StepAgrees := by
  intro h s i hR outbound sub offer hcorr
  cases sub with
  | header sh =>
    cases offer with
    | header rh =>
      obtain ⟨hcode, hmaj, hmin, hrev⟩ := hcorr
      have hoct : sh.octets = rh.octets := by
        rw [headerOctets_eq sh]
        cases rh with
        | mk pid maj min rev => simp only [hcode, hmaj, hmin, hrev]
      refine answersAgree_pairMatches s i hR outbound (.header rh) _ _ _
        (answersAgree_placed s i hR outbound _ _ _
          ⟨stepHeader_matched s i hR outbound sh rh hcode hmaj hmin hrev,
           stepHeader_shapes s i hR outbound sh rh hcode hmaj hmin hrev⟩) ?_
      cases outbound <;> simp only [refOfferWrote, hoct]
    | frame _ _ _ => exact absurd hcorr (by simp [SubmissionsCorrespond])
    | arrives _ => exact absurd hcorr (by simp [SubmissionsCorrespond])
  | frame channel octets body =>
    cases offer with
    | header _ => exact absurd hcorr (by simp [SubmissionsCorrespond])
    | frame channel' octets' body' =>
      cases body with
      | none =>
        cases body' with
        | none =>
          obtain ⟨hch, hoct⟩ := hcorr
          rw [← hch, ← hoct]
          exact answersAgree_pairMatches s i hR outbound (.frame channel octets none) _ _ _
            (frame_none_answers s i hR outbound channel octets) rfl
        | some _ => exact absurd hcorr (by simp [SubmissionsCorrespond])
      | some sbody =>
        cases body' with
        | none => exact absurd hcorr (by simp [SubmissionsCorrespond])
        | some rbody =>
          obtain ⟨hch, hoct, hval⟩ := hcorr
          rw [← hch, ← hoct]
          unfold Spec.Connection.step Ref.Connection.apply
          try dsimp only []
          have hlayEq : (i.protocolId == Ref.Connection.saslId) =
              (s.layer == Spec.Connection.Layer.sasl) := by
            rw [← hR, refPeerOf]
            exact refLayer_sasl_iff s.layer
          cases hlayer : s.layer with
          | amqp =>
            rw [hlayEq, hlayer, if_neg (by decide)]
            exact answersAgree_pairMatches s i hR outbound (.frame channel octets (some rbody))
              _ _ _ (answersAgree_placed s i hR outbound _ _ _
                ⟨stepAmqpFrame_matched s i hR outbound channel octets.size sbody rbody octets
                    (frameCorresponds_of_valuesAgree s i hR outbound sbody rbody hval)
                    (afterFrame_comm s i hR outbound sbody rbody
                      (frameCorresponds_of_valuesAgree s i hR outbound sbody rbody hval).role),
                 stepAmqpFrame_shapes s i hR outbound channel octets.size sbody rbody octets
                    (frameCorresponds_of_valuesAgree s i hR outbound sbody rbody hval)
                    (afterFrame_comm s i hR outbound sbody rbody
                      (frameCorresponds_of_valuesAgree s i hR outbound sbody rbody hval).role)⟩)
              (by cases outbound <;> rfl)
          | sasl =>
            rw [hlayEq, hlayer, if_pos (by decide)]
            exact answersAgree_pairMatches s i hR outbound (.frame channel octets (some rbody))
              _ _ _ (answersAgree_placed s i hR outbound _ _ _
                ⟨stepSaslFrame_matched s i hR outbound octets.size sbody rbody octets
                    (saslCorresponds_of_valuesAgree s i hR sbody rbody hval),
                 stepSaslFrame_shapes s i hR outbound octets.size sbody rbody octets
                    (saslCorresponds_of_valuesAgree s i hR sbody rbody hval)⟩)
              (by cases outbound <;> rfl)
    | arrives _ => exact absurd hcorr (by simp [SubmissionsCorrespond])
  | arriving a =>
    cases offer with
    | header _ => exact absurd hcorr (by simp [SubmissionsCorrespond])
    | frame _ _ _ => exact absurd hcorr (by simp [SubmissionsCorrespond])
    | arrives _ =>
      subst hcorr
      cases outbound with
      | false => exact arriving_matched h s i hR a
      | true =>
        exact answersAgree_pairMatches s i hR true (.arrives a) _ _ _
          (error_answers_agree s i hR true _ _ ⟨framingError_eq, rfl, rfl, rfl⟩) rfl

/-- **The connection layer conforms.** Every step the reference takes on an input of the interface's
alphabet is a step the specification permits, leaving the states related and emitting the same outputs —
given the two frame readers' agreement, which is what the layer's body handling rests on and which is
named here rather than assumed silently. -/

theorem ref_connection_conforms (h : ReadersAgree) :
    ConformsVia RConn specConn refConn := by
  refine ⟨refPeerOf_initial, ?_⟩
  intro s i inp hR out hstepImpl
  cases inp with
  | frame bytes =>
    have hout : out = refArriving i (toOctets bytes) := by
      unfold refConn refConnStep at hstepImpl
      simpa only [Option.some.injEq] using hstepImpl.symm
    obtain ⟨hst, houts⟩ := arriving_matched h s i hR (toOctets bytes)
    refine ⟨(specArriving s (toOctets bytes)).1, (specArriving s (toOctets bytes)).2, ?_, ?_, ?_⟩
    · rw [specConnection_choose_member]
      show specConn.step s (Input.frame bytes) =
        some ((specArriving s (toOctets bytes)).1, (specArriving s (toOctets bytes)).2)
      simp only [specConn, specConnStep, specArriving]
    · rw [hout]
      exact hst
    · rw [hout]
      exact houts.symm
  | api call =>
    unfold refConn refConnStep at hstepImpl
    cases hoffer : refOfferOf call with
    | none => exact absurd hstepImpl (by simp [hoffer])
    | some offer =>
      simp only [hoffer, Option.map_some, Option.some.injEq] at hstepImpl
      obtain ⟨sub, hsub, hcorr⟩ := submissionsCorrespond_of_call h call offer hoffer
      obtain ⟨hst, houts⟩ := stepAgrees h s i hR true sub offer hcorr
      refine ⟨(specSending s sub).1, (specSending s sub).2, ?_, ?_, ?_⟩
      · rw [specConnection_choose_member]
        show specConn.step s (Input.api call) =
          some ((specSending s sub).1, (specSending s sub).2)
        simp only [specConn, specConnStep, hsub, Option.map_some, specSending]
      · rw [← hstepImpl]
        exact hst
      · rw [← hstepImpl]
        exact houts.symm
  | tick t =>
    unfold refConn refConnStep at hstepImpl
    exact absurd hstepImpl (by simp)

/-- The same claim in the existential form `Conforms` states, built through the interface's own
`conforms_of_conforms_via` so that the instance is the one the interface defines rather than a
lookalike. -/

theorem ref_connection_conforms_existential (h : ReadersAgree) :
    Conforms specConn refConn :=
  conforms_of_conforms_via specConn refConn RConn (ref_connection_conforms h)

end SpecAMQP.Proofs
