/-
# The pure protocol core (R2, `PLAN.md` §23.1)

The endpoint's protocol core: octets and events in, octets and events out, and no `IO`. It knows
nothing of sockets, of `Impl.Transport`, or of the filesystem — the shell that owns the socket
(`scripts/loopback/`, and the runner R4 adds) drives it through the functions below, and this module
is where every protocol-facing decision it makes is written down.

## What it is

A **driver** over the specification's own step. `Spec.Connection.step` is the connection layer's
transition relation — the connection state table of picture 24, version negotiation, the SASL
dialogue, the limits, the refusal conditions and reason classes — and the core calls it for every
buffer that arrives and every frame the application asks it to send. The core does not re-state one
rule of that layer. What it owns is the *plumbing*: the reading of the interface's alphabet, which
direction a step moves in, the order in which outputs are emitted, how an answer is rendered, and —
in `Impl.Stream` — how a byte stream becomes the buffers the layer is handed.

That division is deliberate and it is the whole of what this rung buys, so it is worth saying what
it does *not* buy:

* **Not an independent reading of Part 2.** A defect inside `Spec.Connection.step` — a mistranscribed
  row of the state table, a wrong condition, a missing guard — is *inherited* by this core and is not
  caught by any proof about it. What the core's proofs establish is that the loop, the framing and the
  reporting add no protocol decision of their own; whether the decisions are the right reading of the
  standard is what the second reading (`lean/Ref/`, the differential over the corpus) and the vector
  tiers are for, and that is why they are not redundant with this module. Any implementation shares
  its protocol decisions with the specification it is proved against when it *calls* that
  specification; the endpoint's own contribution is a process that speaks the protocol over a socket.
* **Not a proved relation for the session layer.** The connection layer relays a frame of role
  `other` with no state change and no write, and that is all this core does with session, link and
  transfer frames: their handling is reached *through* the connection layer and is **inherited, not
  separately proved**. There is no session-layer conformance instance in this repository, and
  `PLAN.md` §23.1 names the frame and connection instances as what R3 reuses, so inventing a session
  composition here would duplicate the corpus codec's dispatch (`Spec.SessionCodec.stepOf`) in the
  shipped tree and buy a proof about that duplication rather than about the layer. The consequence is
  stated rather than left to be discovered: R4's session vectors exercise the *plumbing* end to end,
  not a proved relation, and reading "the endpoint speaks AMQP" as "everything it does is proved" is
  reading this module wrongly.
* **Not a model of the transport's orderly close.** §10's `Input` has `frame`, `api` and `tick`, and
  no constructor for the byte stream ending; the artifact names TCP Close as a *connection action the
  state table mandates* — CLOSE_PIPE and CLOSE_SENT "TCP Close for Write", END "TCP Close" — never as
  an event an endpoint receives. `Impl.Stream.closed` drops the pending inbox and leaves the protocol
  state alone; the shell owns the consequence (close the descriptor, report the transport end). It is
  outside the interface alphabet and therefore outside every conformance claim. The reason it is not
  made an input is not merely that it is an environment event — `tick` is an environment event and is
  an input — but that `tick`'s *semantics are the specification's* while a stream end's would be
  **ours**: the artifact nowhere says what an endpoint does when the byte stream ends, so a
  constructor would force us to author the answer.
* **Not a claim about the api-response vocabulary's home.** `Output.api` carries a name and a flag, and
  what the name *means* — the state table's own name for a step taken, and on a refusal the protocol
  condition followed by the reason class — is defined today only inside
  `lean/Proofs/ConnectionConformance.lean` (`tookAnswer`, `refusedAnswer`, `wireOutput`). `Conforms`
  compares outputs exactly, so this core must render the same lists, and it may not import the proof
  library. The three renderings below are therefore a deliberate **duplication**, safe only because
  R3 proves the two agree; that agreement lemma is not optional, and the planner has taken the
  follow-up of moving the vocabulary into the module that declares the interface.

## The interface reading, which is the one thing that has to be fixed

`Conforms` (`Contracts.Conformance`, `PLAN.md` §10) quantifies over **every** `Input`, so the meaning
of `Input.frame` is not a matter of taste:

* **`.frame bytes` is one buffer offered to the connection layer** — a protocol header, or one
  frame — exactly as `specConn` reads it (`Proofs/ConnectionConformance.lean`'s `specConnStep`). It is
  *not* "some octets arrived": a core that buffered a fragment would answer nothing where the
  specification's own instance refuses, and no simulation relation can match an empty output sequence
  to a refusal. A byte stream with arbitrary fragmentation is therefore the *front end's* business
  (`Impl.Stream`), which is pure and total and hands the layer the octets that arrived; the layer
  never sees a fragment it has to guess about.
* **`.api call` is the application asking for a send**, read with the corpus's own convention: the
  call is named `send` and carries the octets hex-encoded, because the interface's `ApiCall` carries
  strings and the wire is octets. Octets that begin the way a protocol header does are that header;
  anything else is a frame the frame layer reads. What the layer then writes is the octets it was
  handed — the octets the caller's encoder produced — which is what the layer's own vocabulary says
  (`Submission.frame` carries them).
* **`.tick` is not a step this layer takes**, and the answer is `none`: the connection layer has no
  timer and no threshold behind one.
* A call the core cannot read is a call it has no answer for, which is the interface's own arm for an
  input an implementation rejects (`step` returning `none`), not a silently ignored input.

## What is answered, and the `Option`

`step` returns `some` for every frame input — the layer is total on a buffer — and for every call that
reads as a send. It returns `none` for a tick and for a call that does not read as one. R3's instance
would be vacuous if the core answered `none` everywhere, so the laws at the end of this module state
the positive direction as well: `step_frame` and `step_api` say exactly which answer comes back, which
is also what makes a later refactor of the plumbing visible as a failing theorem rather than as a
quiet change of behaviour.
-/

import Contracts.Conformance
import Spec.Connection
import Spec.Frame
import Spec.WidenedState
import Harness.Runner

namespace SpecAMQP.Impl.Core

open SpecAMQP.Contracts (ApiCall Output Input Endpoint)
open SpecAMQP.Harness (Octets toHex ofHex)

/-- The connection layer's own state, named here so that a use site cannot confuse it with the
interface's `Endpoint` — the two are different things and only one of them is a state. -/
abbrev Conn := SpecAMQP.Spec.Connection.Endpoint

/--
The endpoint's state: where the connection layer is, and the octets that have arrived but do not yet
make a complete wire unit.

The two fields are read by different callers on purpose. `step` — the frozen interface's view — is
about the layer: a `.frame` input *is* the buffer offered to it, so a step neither reads nor writes
`inbox`. `Impl.Stream.feed` — the transport's view — is what accumulates octets and decides how far
each unit extends, and it is the only thing that writes `inbox`.
-/
structure State where
  /-- The connection layer's state: the table's state, the layer, the SASL dialogue's position, the
  announced mechanisms and the two sides' limits. -/
  conn : Conn
  /-- Octets read from the transport that do not yet make a complete wire unit. -/
  inbox : Octets
  /-- The channel-indexed widened session table, `PLAN.md` §24 part 4. It defaults to the empty table so
  that a literal written before the field existed still elaborates; the *default* is a convenience, not a
  licence to drop the table, so every site that already holds a state updates through `{ state with … }`
  rather than rebuilding a literal (`Impl/Stream.lean`'s read path is the one that matters).

  The core's own `step` never writes it: this rung's protocol decisions are the connection layer's, and
  the session table is the state the *conformance* claim ranges over. It is here rather than in a second
  state type because `Contracts/WidenedEndpointConformance` fixes `WidenedImplementationState` to this
  structure and `WideningProjectsEndpointRelation` to the connection projection of it. -/
  sessions : Nat → Option SpecAMQP.Spec.WidenedSession := fun _ => none

/-- The core's state as the widened protocol state the conformance contract reads: the real `conn` field
as the connection endpoint and the real `sessions` table as the session table. This is a *view* rather
than a field, so it cannot drift from the two fields it is computed from. -/
def State.protocol (state : State) : SpecAMQP.Spec.WidenedProtocolState :=
  { connection := state.conn, sessions := state.sessions }

/-- The view's connection half is the `conn` field. -/
theorem protocol_connection (state : State) : state.protocol.connection = state.conn := rfl

/-- The view's session half is the `sessions` field. -/
theorem protocol_sessions (state : State) : state.protocol.sessions = state.sessions := rfl

/-- Two states with the same `conn` and the same `sessions` are the same state: `inbox` is the stream
front end's pending octets and is outside every protocol claim. -/
theorem state_eq_of_conn_sessions {left right : State} (hconn : left.conn = right.conn)
    (hsessions : left.sessions = right.sessions) (hbox : left.inbox = right.inbox) :
    left = right := by
  cases left
  cases right
  cases hconn
  cases hsessions
  cases hbox
  rfl

/-- The computed view is the pair of fields it is built from, which is the form every proof about it
uses: `State.protocol` reads `conn` and `sessions` and nothing else. -/
theorem protocol_eq_iff (state : State) (spec : SpecAMQP.Spec.WidenedProtocolState) :
    state.protocol = spec ↔ state.conn = spec.connection ∧ state.sessions = spec.sessions := by
  constructor
  · intro h
    exact ⟨by simpa only [State.protocol] using
             congrArg SpecAMQP.Spec.WidenedProtocolState.connection h,
           by simpa only [State.protocol] using
             congrArg SpecAMQP.Spec.WidenedProtocolState.sessions h⟩
  · rintro ⟨hconn, hsessions⟩
    cases spec
    simp only [State.protocol, hconn, hsessions]

/-- A peer that has exchanged nothing and has read nothing. -/
def initial : State :=
  { conn := SpecAMQP.Spec.Connection.Endpoint.initial, inbox := #[] }

/-! ## The interface's octets, and the layer's

`Contracts.Conformance` carries the wire as `ByteArray` — `Input.frame` and `Output.frame` both take
one — while the connection layer's octets are `Harness.Octets`, which is `Array UInt8`. `ByteArray.mk`
and `ByteArray.data` are `rfl`-inverses, so nothing is copied and nothing is decided here: every octet
that arrives reaches the layer unchanged, and every octet the layer writes reaches the interface
unchanged. (The same pair, with the same bodies, is used by the connection layer's instance; R3 proves
the two agree, which is a `rfl` because neither body does anything.) -/

/-- The interface's bytes, from the layer's octets. -/
def toBytes (octets : Octets) : ByteArray := ByteArray.mk octets

/-- The layer's octets, from the interface's bytes. -/
def toOctets (bytes : ByteArray) : Octets := bytes.data

/-- The conversions are inverses, which is the whole of what the core needs of them. -/
theorem toOctets_toBytes (octets : Octets) : toOctets (toBytes octets) = octets := rfl

/-- And in the other direction, which is the direction an input takes. -/
theorem toBytes_toOctets (bytes : ByteArray) : toBytes (toOctets bytes) = bytes := rfl

/-! ## Rendering an answer

What the layer did, as the interface's outputs: the octets it wrote, on the wire, and the answer the
application sees. Both halves are interface rather than prose — §10 rule 5 puts the mandated error
code in the observable, and the reason class with it, because the corpus compares classes between the
artefacts — and both are read off the layer's own `Outcome` / `Refusal` fields, never parsed out of a
message. See the header for why these three definitions are a duplication of the instance's. -/

/-- The octets the layer wrote, on the wire, as the interface carries them. -/
def wireOutput (wrote : List Octets) : List Output :=
  wrote.map (fun octets => Output.frame (toBytes octets))

/-- The answer to a step the layer took: the state table's own name, which is the one thing both
layers name the same way and the one the corpus pins. -/
def tookAnswer (stateName : String) : Output :=
  Output.api ⟨stateName, true⟩

/-- The answer to a refusal: the protocol condition, then the reason class. Neither is recoverable
from the other, and the client acts on which one it is told. -/
def refusedAnswer (condition reasonClass : String) : List Output :=
  [Output.api ⟨condition, false⟩, Output.api ⟨reasonClass, false⟩]

/-- The layer's answer to one step, as the pair the interface returns: the state the step left, and
the outputs.

The refusal a step answers with is already *placed* — `Spec.Connection.step` applies
`Refusal.withPlace` before answering, so `reason.state` is where the refusal leaves this peer — and
that is the whole of what this function has to read: a step that failed writes nothing and moves
nothing, a refused receive leaves the peer in the table's DISCARDING (or in END, in the SASL layer
and where the table already ended), and a failed negotiation carries its own row. -/
def answerOf (conn : Conn)
    (answer : Except SpecAMQP.Spec.Connection.Refusal SpecAMQP.Spec.Connection.Outcome) :
    Conn × List Output :=
  match answer with
  | .ok outcome =>
    (outcome.endpoint,
     wireOutput outcome.wrote ++ [tookAnswer outcome.endpoint.state.name])
  | .error reason =>
    ({ conn with state := reason.state.getD conn.state },
     wireOutput reason.wrote ++ refusedAnswer reason.condition reason.reasonClass)

/-- The specification's answer to one buffer offered to the connection layer: the receive direction,
which is the direction in which a buffer is an input rather than an answer. -/
def arriving (conn : Conn) (octets : Octets) : Conn × List Output :=
  answerOf conn (SpecAMQP.Spec.Connection.step conn false (.arriving octets))

/-- The specification's answer to one submission this peer is asked to send. -/
def sending (conn : Conn) (submission : SpecAMQP.Spec.Connection.Submission) : Conn × List Output :=
  answerOf conn (SpecAMQP.Spec.Connection.step conn true submission)

/-! ## The application's send, as this core reads a call

The vocabulary the corpus uses, and the one the connection layer's instance reads: a call named `send`
whose first argument is the octets hex-encoded. Reading the frame out of those octets needs the
channel and the body, so the frame layer does it here — the same two questions `Submission.frame`
carries — and a call whose octets are neither a header this peer speaks nor a frame it can read is a
call this core has no answer for. -/

/-- The name an api call must carry to be a send. -/
def sendName : String := "send"

/-- The api call that asks the endpoint to send octets. -/
def sendCall (octets : Octets) : ApiCall :=
  { name := sendName, arguments := [toHex octets] }

/-- The octets a call asks the endpoint to send, or `none` for a call that is not a send. -/
def callOctets (call : ApiCall) : Option Octets :=
  if call.name = sendName then
    match call.arguments with
    | arg :: _ => (ofHex arg).toOption
    | [] => none
  else none

/-- The octets a send decodes to.

Octets that begin the way a protocol header does *are* that header — a protocol header is not a frame,
so octets shaped like one can only mean it — and everything else is a frame the frame layer reads.
What a submission then carries is the octets the caller wrote, because the layer's own vocabulary says
so and the layer writes exactly them. -/
def readSubmission (octets : Octets) : Option SpecAMQP.Spec.Connection.Submission :=
  if SpecAMQP.Spec.Connection.headerShaped octets then
    match SpecAMQP.Spec.Connection.decodeHeader octets with
    | .ok header => some (.header header)
    | .error _ => none
  else
    match SpecAMQP.Spec.Frame.decodeFrame octets with
    | .ok (frame, _) => some (.frame frame.channel octets frame.body)
    | .error _ => none

/-- The submission an api call asks for, or `none` for a call this core cannot read. -/
def submissionOf (call : ApiCall) : Option SpecAMQP.Spec.Connection.Submission :=
  (callOctets call).bind readSubmission

/-! ## The step -/

/-- Apply one submission this core itself is asked to send. -/
def send (core : State) (submission : SpecAMQP.Spec.Connection.Submission) : State × List Output :=
  let answer := sending core.conn submission
  ({ core with conn := answer.1 }, answer.2)

/--
**The core's step**, over the frozen interface's alphabet.

* `.frame bytes` offers `bytes` to the connection layer, which is the layer's own reading of an
  arriving buffer and the reason the core needs no framing decision here. The inbox is untouched: a
  `.frame` input *is* the buffer the layer is handed, whether it came from a socket read or from the
  stream front end's decision that a unit had completed.
* `.api call` reads the call as a send and applies it in the send direction, or answers `none` for a
  call that is not a readable send.
* `.tick` is `none`: this layer has no timer.
-/
def step (core : State) (inp : Input) : Option (State × List Output) :=
  match inp with
  | .frame bytes =>
    let answer := arriving core.conn (toOctets bytes)
    some ({ core with conn := answer.1 }, answer.2)
  | .api call => (submissionOf call).map (fun submission => send core submission)
  | .tick _ => none

/--
Ask the endpoint to send octets, on the shell's side of the interface.

This is `step` on a `send` call with the octets already in hand, so the shell never has to build the
call or spell its hex form, and it fails **loudly** rather than answering `none`: octets that are
neither a header this peer speaks nor a frame the frame layer reads are a defect in the ask, and a
caller that got `none` back would have to guess which. `submit_step` below is the bridge back to the
interface: where `submit` succeeds, the interface's answer is the same pair.
-/
def submit (core : State) (octets : Octets) : Except String (State × List Output) :=
  match readSubmission octets with
  | some submission => .ok (send core submission)
  | none =>
    .error s!"the octets are not something this peer can send: they are neither a protocol \
      header it speaks nor a frame it can read"

/--
**The endpoint's fixed header**: the protocol header this peer announces, as the layout draws it.

The layer and its version are read from the specification — the layer's own protocol id, and the
version the artifact states in the generated constant table — so the header a peer announces is not a
typed-in constant that could drift from the artifact. `announceHeader_accepted` below is the law that
makes it usable: the header this core offers is one it would accept.
-/
def announceHeaderFor (layer : SpecAMQP.Spec.Connection.Layer) : Option Octets :=
  (SpecAMQP.Spec.Connection.Layer.version layer).map
    (fun version => (⟨layer.protocolId, version⟩ : SpecAMQP.Spec.Connection.ProtocolHeader).octets)

/-- The header this endpoint announces: the AMQP layer, at the version the artifact states. A `none`
here means the artifact states no version for the AMQP layer at all, which is the same defect
`Spec.Connection.negotiationReply` refuses to answer with. -/
def announceHeader : Option Octets := announceHeaderFor .amqp

/-! ## The endpoint, as the interface sees it -/

/--
**The implementation's side of §10's interface.** The core's own step as an `Endpoint`, which is what a
conformance instance pairs with the specification's: `Proofs.ConnectionConformance.specConn` is the
specification's own `Endpoint` for the same alphabet, and the relation between them is the plumbing —
`fun s i => i.conn = s`, over `State.conn` below, which is why that field is public and why this wrapper
carries no state of its own beyond the endpoint's.

`choose` is empty for the same reason the reference's instance leaves it empty: `ConformsVia` never
consults an implementation's `choose`, and a second set that could drift from the specification's is a
liability rather than a claim.

The instance says nothing about the byte stream — `Input` has no fragment to quantify over — and
`PLAN.md` §10's `Conforms` is therefore discharged against the *unit* reading of `.frame` documented
above. That the stream front end is a permitted sequence of these steps is `Impl.Stream`'s laws
composed with this instance, and it is R3's corollary to state.
-/
def implCore : Endpoint State where
  init := initial
  step := step
  choose := fun _ _ => ∅

/-! ## What the step answers

The four laws a later refactor has to keep, and the reason the instance is not vacuous: `step` answers
every frame input and every readable send, with exactly the pair the layer produced. -/

/-- A frame input is answered with the connection layer's own answer to those octets, and the inbox is
left as it was. -/
theorem step_frame (core : State) (bytes : ByteArray) :
    step core (.frame bytes) =
      some ({ core with conn := (arriving core.conn (toOctets bytes)).1 },
            (arriving core.conn (toOctets bytes)).2) := rfl

/-- A readable send call is answered in the send direction, with the submission the call names. -/
theorem step_api (core : State) (call : ApiCall)
    (submission : SpecAMQP.Spec.Connection.Submission)
    (h : submissionOf call = some submission) :
    step core (.api call) = some (send core submission) := by
  simp [step, h]

/-- A tick is not a step this layer takes. -/
theorem step_tick (core : State) (tick : SpecAMQP.Contracts.Tick) :
    step core (.tick tick) = none := rfl

/-- **The core's step never touches the session table.** A frame is the connection layer's and a
readable call is its send direction, so the widened view's session half is carried through every
step this endpoint takes; that is what lets the widened conformance claim relate the two sides
without this rung having to decide anything about sessions. -/
theorem step_preserves_sessions (core : State) (inp : Input) (out : State × List Output)
    (h : step core inp = some out) : out.1.sessions = core.sessions := by
  cases inp with
  | frame bytes =>
    have h' := h
    rw [step_frame] at h'
    exact (Option.some.inj h') ▸ rfl
  | api call =>
    cases hsub : submissionOf call with
    | none => exact absurd h (by simp [step, hsub])
    | some submission =>
      have h' := h
      rw [step_api core call submission hsub] at h'
      have h'' := Option.some.inj h'
      subst h''
      rfl
  | tick t => exact absurd h (by simp [step])

/-- `submit` fails exactly where the octets are not a send: the failure is the reading's own `none`,
not a second judgement made by the shell's path. -/
theorem submit_error (core : State) (octets : Octets) (message : String)
    (h : submit core octets = .error message) : readSubmission octets = none := by
  unfold submit at h
  split at h
  · simp at h
  · assumption

/-- The call this core builds from octets reads back as those octets: `sendCall`'s argument is the
hex form of the octets and `callOctets` decodes it with the harness's own decoder.

The hex round trip is a **hypothesis** here, which is the same hypothesis, stated the same way, as
`Proofs.ConnectionConformance.callOctets_sendCall` states it and for the same reason: both endpoints
run the *same* decoder, so what an instance needs of it is that the two agree, not that it is total.
What the hypothesis buys is the bridge below — the shell's typed send and the interface's `api` send
are one protocol. -/
theorem callOctets_sendCall {octets : Octets} (h : ofHex (toHex octets) = .ok octets) :
    callOctets (sendCall octets) = some octets := by
  have h' : (ofHex (toHex octets)).toOption = some octets := by
    rw [h]
    rfl
  show (if (sendCall octets).name = sendName then
      match (sendCall octets).arguments with
      | arg :: _ => (ofHex arg).toOption
      | [] => none
    else none) = some octets
  simp only [sendCall, sendName, h', if_true]

/-- Where `submit` succeeds, the interface's own answer to the same send is the same pair: the two
paths differ in spelling and in nothing else. -/
theorem submit_step (core : State) (octets : Octets) (out : State × List Output)
    (h : ofHex (toHex octets) = .ok octets) (hout : submit core octets = .ok out) :
    step core (.api (sendCall octets)) = some out := by
  unfold submit at hout
  split at hout
  · rename_i submission hsub
    simp only [Except.ok.injEq] at hout
    rw [← hout]
    exact step_api core (sendCall octets) submission (by
      unfold submissionOf
      rw [callOctets_sendCall h]
      exact hsub)
  · simp at hout

end SpecAMQP.Impl.Core
