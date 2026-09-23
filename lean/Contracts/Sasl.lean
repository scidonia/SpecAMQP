import Spec.Connection

/-!
# The security layer's laws (S7 acceptance statements)

The SASL layer's claims divide into three kinds, and this file says which is which rather than
dressing one as another. It is the same division `ConnectionLifecycle.lean` makes for the
connection lifecycle, for the same reason: where the artifact gives prose and pictures, the honest
artifact is a transcription plus an executable check, not a theorem about a picture.

**Proved, in `Proofs/SaslDialogue.lean`.** Four laws about the dialogue, each a statement over
*every* phase, direction and body rather than about the frames somebody thought to write down. Their
names are the contract's, and a reviewer can check them against the module:

* `sasl_layer_admits_only_sasl_performatives` and `amqp_layer_admits_no_sasl_performative`
* `sasl_phase_never_goes_back`
* `only_an_ok_outcome_establishes_the_layer`
* `dialogue_state_initial` and `dialogue_state_step` (the invariant `DialogueState`)

What each says:

* **The layer rule, both ways.** A SASL performative never crosses in the AMQP layer, and a body
  that is not one of the five performatives never crosses in the SASL layer — whatever the moment,
  the direction, or how well formed the frame is. This is the law the corpus's negative vectors
  exercise at five moments; the theorem is the same claim at every moment.
* **The dialogue's order.** Within the SASL layer the phase never moves backwards: the announcement,
  the init, and then the outcome, with the challenge/response step leaving it where it is.
* **Establishment is the `ok` outcome's alone.** A step admitted from an endpoint in the SASL layer
  leaves the layer at `AMQP` only by the `sasl-outcome` whose code is the value the `sasl-code`
  choice declares for `ok`, and it lands in the protocol headers' first state with the dialogue's
  knowledge cleared.
* **The invariant every reachable dialogue holds.** Once a peer has announced its mechanisms, its
  list is not empty and its role is fixed, and a dialogue that has begun is the SASL layer's — a
  state invariant preserved by every admitted step from the initial one.

**Executable evidence, not theorems: the refusal placement.** Every negative vector pins the state
a refusal leaves the peer in, and a refused send and a refused receive differ in where that is —
DISCARDING in the AMQP layer, where a close is written, and END in the SASL one, where no AMQP
close can be written because the layer is not established. Stating it again as a theorem about the
step functions would add a second description of behaviour the vectors already pin, written from the
code rather than from the artifact.

**Recorded readings, not theorems, and each with the clause or the gap that forces it.**

* **A declared `sasl-code` failure is a refusal whose reason is the code's own declared name, and
  whose condition is empty.** The artifact declares four failures as four distinct values for four
  distinct causes — `auth`, `sys`, `sys-perm`, `sys-temp` — and a layer that reported them all as
  "not ok" would have read the field and kept only a boolean. The condition is empty because the
  artifact obliges the peer to close "with the authentication-failure close-code" and **no value of
  the generated `connection-error` choice carries one**: the table has a shape for errors, not for
  every observable, and choosing a declared condition because the table has one of that shape would
  give this layer a condition the artifact never named. The four corpus vectors pin the empty
  condition by *omitting* the key, so a comparison of nothing with nothing is the assertion, and the
  mutation tier's "invent a condition for the failed authentication" control is what shows it is.
* **The reason vocabulary grew for this layer, by exactly the values the artifact declares for
  `sasl-code` and nothing else.** The driver's reason classes were the head tokens of its refusals
  and closed because the vector schema mirrored them; the four code names are appended, each read
  from the generated choice table rather than typed. A reader may still call the list closed, and
  the widening is a fact about what a class means here rather than an accident: a step's reason is
  now either a protocol fault class or a declared authentication outcome. A refusal in this model
  means the step returned no continuing layer, and the reason says why — which is why the outcome
  that reports a failure is refused under the code's own name by the peer that reads it *and* by the
  peer that wrote it, and is no longer an admitted step.
* **`mechanism.2`'s "highest-level security profile" is an unmodelled peer obligation.** The clause
  reads: "Each peer MUST authenticate using the highest-level security profile it can handle from
  the list provided by the partner", and the mechanisms field's own documentation says "The server
  mechanisms are ordered in decreasing level of preference." No security profile is defined anywhere
  in the pinned artifacts, and the only mechanisms named in them are ANONYMOUS (in the mechanisms
  field's SHOULD) and PLAIN and SCRAM-SHA1 (in the overview's conformance clause, citing RFC4616
  and RFC5802 — documents this repository does not vendor). A table of profiles would therefore make
  *our* table the source of a normative claim the artifact does not permit us to invent. What the
  layer enforces is the artifact's membership rule, that the init names one of the announced
  mechanisms; the preference rule is recorded here and pinned as a *freedom* by
  `sasl-mechanism-chosen-from-a-list`, which chooses the last of three announced mechanisms.
* **`sasl.8`'s SASL-to-TCP role correspondence cannot be stated about this layer.** The clause
  reads: "The peer playing the role of the SASL client and the peer playing the role of the SASL
  server MUST correspond to the TCP client and server respectively." `Endpoint` has no field for
  which end opened the socket: the SASL role is *decided* by the announcement, and a peer that has
  not announced is the client — so a peer cannot be refused for announcing when it was the TCP
  client, which is what the correspondence forbids. This is the fourth finding of the connection
  layer's audit, still open, and its vector cannot be written until the model can express the role.
  The goal, stated exactly: an `Endpoint` that carries the transport role it was given, an
  environment assumption that fixes it when the socket is opened, and a guard on the announcement
  that refuses a `sasl-mechanisms` sent by the TCP client. None of that is representable today, and
  a proof module restated against a `refPeerOf` that does not know the field would be the wrong
  place to put it.
* **The idle-timeout interaction is not statable about this layer at all.** The connection's
  `idle-time-out` is negotiated in `open`, and the transport clauses oblige a peer to close a
  connection on which nothing arrives for the negotiated interval. This layer's alphabet is a
  `Submission` — a header, a frame, or octets — and its state is the table's state, the layer, the
  dialogue's phase and the two limits; nothing carries a tick and nothing carries a deadline, so
  "a SASL frame counts as traffic against the negotiated timeout" has no place to live. Growing the
  alphabet for it would make every other claim in the layer depend on a quantity no vector
  exercises, which is the trade the plan refuses: a timeout claim belongs to a layer with time in
  it. The plan's S7 scope named this interaction and the alphabet cannot state it, which is a
  finding about scope rather than a missing piece of the slice.
* **TLS is an opaque boundary, and the model's side of it is that this peer does not speak it.**
  Protocol id two is assigned by the security artifact and refused as a protocol this peer does not
  speak, with the same condition and class as an unassigned protocol id; nothing about TLS
  negotiation, its records or its certificates is modelled, and the assumption is named here so that
  no claim in this slice is read as resting on it.

**Belonging to the corpus, not here.** The exchange corpus's own vectors are where each refusal's
condition, class and placement are pinned — the five performatives' mandatory fields, the empty and
null mechanism lists, the undeclared outcome code, `additional-data` on an unsuccessful outcome, and
the layer transitions in both directions. A theorem restating any of them would be a second
description of behaviour the vectors already pin, written from the code rather than from the
artifact, which is how a check decays into a restatement.
-/

namespace SpecAMQP.Contracts

open SpecAMQP.Spec.Connection
open SpecAMQP.Spec.Codec (Value)
open SpecAMQP.Harness (Octets)

/-- **The layer rule.** A body that is not one of the five SASL performatives never crosses inside
the SASL layer, and a SASL performative never crosses inside the AMQP layer — in either direction,
in any moment the layer permits at all, and however well formed the frame is.

Stated over `step` rather than over the arms because the claim is about the layer: which frames may
cross is decided by which layer the exchange is in, and the moment is a second question asked after
it. The corpus pins five instances of this law; the law itself is the claim at every moment, which
is what a vector cannot say. -/
def LayerAdmitsItsOwnPerformatives : Prop :=
  ∀ (endpoint : Endpoint) (outbound : Bool) (channel size : Nat) (body : Value)
    (wrote : Octets),
    (endpoint.layer = Layer.sasl → SaslFrame.ofBody body = SaslFrame.other →
      (stepSaslFrame endpoint outbound size body wrote).isOk = false) ∧
    (endpoint.layer = Layer.amqp → roleOfBody body = FrameRole.sasl →
      (stepAmqpFrame endpoint outbound channel size body wrote).isOk = false)

/-- **The dialogue's order.** Inside the SASL layer the phase never moves backwards: the
announcement, then the init, then the outcome, with the challenge and response step leaving the
phase where it is. -/
def DialoguePhaseNeverGoesBack : Prop :=
  ∀ (endpoint : Endpoint) (outbound : Bool) (size : Nat) (body : Value)
    (wrote : Octets) (out : Outcome),
    endpoint.layer = Layer.sasl → stepSaslFrame endpoint outbound size body wrote = .ok out →
      out.endpoint.layer = Layer.sasl → endpoint.phase.rank ≤ out.endpoint.phase.rank

/-- **Establishment is the `ok` outcome's alone.** A step admitted from an endpoint in the SASL
layer reaches the AMQP layer only by a `sasl-outcome` carrying the code the `sasl-code` choice
declares for `ok`, and it lands in the protocol headers' first state with the dialogue's knowledge
cleared — which is the clause that says the peers "MUST exchange protocol headers" again, this time
for the AMQP connection. -/
def OnlyAnOkOutcomeEstablishesTheLayer : Prop :=
  ∀ (endpoint : Endpoint) (outbound : Bool) (size : Nat) (body : Value)
    (wrote : Octets) (out : Outcome),
    endpoint.layer = Layer.sasl → stepSaslFrame endpoint outbound size body wrote = .ok out →
      out.endpoint.layer = Layer.amqp →
        out.endpoint.state = State.start ∧ out.endpoint.phase = SaslPhase.absent ∧
        out.endpoint.mechanisms = [] ∧ out.endpoint.role = none ∧
        SaslFrame.ofBody body = SaslFrame.outcome

/-- **The invariant every reachable dialogue holds.** A peer that has announced its mechanisms
holds a list that is not empty — the mechanisms arm refuses an empty one and nothing else writes the
field — its role is fixed by that announcement, and a dialogue that has begun is the SASL layer's.
Stated as an invariant rather than as three claims about three arms, because what a later arm may
assume of the state is exactly this: the init's membership test is a test against a list that
cannot be empty, and the direction checks are tests against a role that cannot be `none`. -/
def DialogueState (endpoint : Endpoint) : Prop :=
  (endpoint.phase = SaslPhase.mechanismsKnown ∨ endpoint.phase = SaslPhase.awaitingOutcome →
    endpoint.mechanisms ≠ []) ∧
  (endpoint.phase = SaslPhase.mechanismsKnown ∨ endpoint.phase = SaslPhase.awaitingOutcome →
    endpoint.role.isSome = true) ∧
  (endpoint.phase ≠ SaslPhase.absent → endpoint.layer = Layer.sasl)

end SpecAMQP.Contracts
