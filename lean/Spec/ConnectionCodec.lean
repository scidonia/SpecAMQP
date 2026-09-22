import Harness.Runner
import Spec.Connection
import Spec.FrameCodec

/-!
# The specification's connection layer as a corpus codec

`Spec.Connection` carries the connection state machine; this file is the translation
between it and the exchange vocabulary of `tests/contracts/exchange-vector.schema.json`,
which is the vocabulary the shared runner compares in — never between the two
artefacts' own state types, which would need a third thing to trust.

Nothing here decides anything about the connection. A step's direction says which way
the peer is asked to move, a frame written as a structure is encoded by the frame
layer, octets that arrive are handed to the connection layer to decode — because which
of them is a protocol header and which a frame is the state's own question — and the
answer is reported in the corpus vocabulary: whether the peer took the step, the octets
it wrote, the state it is in, and on a refusal the condition with its class-led detail.
-/

namespace SpecAMQP.Spec.ConnectionCodec

open Lean
open SpecAMQP.Harness
open SpecAMQP.Spec.Connection
open SpecAMQP.Spec.FrameCodec (frameOfJson)

/-- The submission one step makes of the peer.

A send is the frame the corpus asks for: written as a structure it is encoded by the
frame layer, and written as octets those octets are decoded and re-encoded, so that
what the peer writes is its own encoding of the frame rather than the octets it was
handed. Octets that begin the way a protocol header does are a header rather than a
frame — a protocol header is not a frame, so the corpus writes it as octets and there is
nothing else it could be — and one the peer does not speak is a defect in the step
rather than a step, so it fails here by name. A receive is octets, and the connection
layer decides what they are. -/
def submissionOf (step : ExchangeStep) : Except String Submission := do
  if !step.send then
    match step.bytes with
    | some octets => return .arriving octets
    | none => .error "a receive step carries the octets it delivers"
  else
    match step.value with
    | some json =>
      let frame ← frameOfJson json
      let octets ← encoded frame
      return .frame frame.channel octets frame.body
    | none =>
      match step.bytes with
      | none => .error "a send step carries the frame, as a structure or as its octets"
      | some octets =>
        if headerShaped octets then
          match SpecAMQP.Spec.Connection.decodeHeader octets with
          | .ok header => return .header header
          | .error reason =>
            .error s!"the step asks the peer to send a header it does not speak: \
              {reason.detail}"
        else
          match SpecAMQP.Spec.Frame.decodeFrame octets with
          | .error message => .error s!"a send step's octets are not a frame: {message}"
          | .ok (frame, _) =>
            let produced ← encoded frame
            return .frame frame.channel produced frame.body
where
  /-- The octets a frame is written as, or the reason the frame layer refuses to write
  it: a step that asks for a frame the peer cannot encode is a defect in the step. -/
  encoded (frame : SpecAMQP.Spec.Frame.Frame) : Except String Octets :=
    match SpecAMQP.Spec.Frame.encodeFrame frame with
    | .ok octets => pure octets
    | .error message => .error s!"the frame the step asks for cannot be written: {message}"

/-- The connection action the table names for a state, as prose.

The table's third column is part of the relation it states, and a verdict that reported
only the state would leave the action unobservable — so it is reported with the state it
follows, which is what makes "TCP Close for Write" on CLOSE_PIPE a claim the corpus can
be read against rather than a remark in a doc comment. -/
def actionNote (state : State) : String :=
  match state.action with
  | some action => s!", and the connection action is {action.name}"
  | none => ""

/-- The corpus outcome of one step.

A refusal's state is the one it leaves the peer in and not the one it was in: a refused
send writes nothing and moves nothing, while a refused receive is an error on the wire
the peer answers by closing, which is why the corpus can pin the state either way. -/
def stepOf (endpoint : Endpoint) (step : ExchangeStep) :
    Except String (StepOutcome × Endpoint) := do
  let submission ← submissionOf step
  match SpecAMQP.Spec.Connection.step endpoint step.send submission with
  | .ok outcome =>
    return (⟨true, outcome.wrote.head?, outcome.endpoint.state.name, none,
             s!"admitted; the peer is in {outcome.endpoint.state.name}\
               {actionNote outcome.endpoint.state}"⟩, outcome.endpoint)
  | .error reason =>
    let endpoint := { endpoint with state := reason.state.getD endpoint.state }
    let reply :=
      match reason.wrote with
      | [] => ""
      | octets :: _ => s!", writing {toHexBrief octets}"
    return (⟨false, reason.wrote.head?, endpoint.state.name, some reason.condition,
             s!"{reason.detail}; the peer is in {endpoint.state.name}\
               {actionNote endpoint.state}{reply}"⟩, endpoint)

/-- The specification's connection layer behind the corpus interface. A state name the
table does not have fails here rather than being read as some default. -/
def specExchangeCodec : ExchangeCodec where
  name := "specification"
  St := Endpoint
  start := fun name =>
    match State.ofName name with
    | some state => .ok { Endpoint.initial with state }
    | none => .error s!"'{name}' is not a connection state the table declares"
  step := stepOf

end SpecAMQP.Spec.ConnectionCodec
