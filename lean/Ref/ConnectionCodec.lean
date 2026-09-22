import Harness.Runner
import Ref.Connection
import Ref.Vectors

/-!
# The reference implementation's connection layer as a corpus codec

The translation between `Ref.Connection` and the exchange vocabulary of
`tests/contracts/exchange-vector.schema.json`. As on the specification's side, nothing
here decides anything about the connection: a step's direction says which way the peer
is asked to move, a frame written as a structure is encoded by the frame layer, octets
that arrive are handed to the connection layer to read — the state's receive column is
what says whether they are a protocol header or a frame — and the answer is reported in
the corpus vocabulary, which is where the two artefacts are compared.
-/

namespace SpecAMQP.Ref.ConnectionCodec

open Lean
open SpecAMQP.Harness
open SpecAMQP.Ref.Connection
open SpecAMQP.Ref.Vectors (frameOfJson)

/-- The offer one step makes of the peer.

A send is the frame the corpus asks for: written as a structure it is encoded by the
frame layer, and written as octets those octets are read and re-encoded, so what the
peer writes is its own encoding of the frame rather than the octets it was handed.
Octets that begin the way a protocol header does are a header, because a header is not
a frame and the corpus has no other way to write one; a header the peer does not speak
is a defect in the step and fails here by name. -/
def offerOf (step : ExchangeStep) : Except String Offer := do
  if !step.send then
    match step.bytes with
    | some octets => return .arrives octets
    | none => .error "a receive step carries the octets it delivers"
  else
    match step.value with
    | some json =>
      let frame ← frameOfJson json
      let encoded ← asOctets frame
      return .frame frame.channel encoded frame.body
    | none =>
      match step.bytes with
      | none => .error "a send step carries the frame, as a structure or as its octets"
      | some octets =>
        if looksLikeHeader octets then
          match readHeader octets with
          | .ok header => return .header header
          | .error reason =>
            .error s!"the step asks the peer to send a header it does not speak: \
              {reason.detail}"
        else
          match SpecAMQP.Ref.Frame.decodeFrame octets with
          | .error message => .error s!"a send step's octets are not a frame: {message}"
          | .ok (frame, _) =>
            let encoded ← asOctets frame
            return .frame frame.channel encoded frame.body
where
  /-- The octets a frame is written as, or the reason the frame layer refuses to write
  it: a step that asks for a frame the peer cannot encode is a defect in the step. -/
  asOctets (frame : SpecAMQP.Ref.Frame.Frame) : Except String Octets :=
    match SpecAMQP.Ref.Frame.encodeFrame frame with
    | .ok octets => pure octets
    | .error message => .error s!"the frame the step asks for cannot be written: {message}"

/-- The connection action the table names for a state, as prose: the table's third
column is part of what it states, so the verdict reports it beside the state. -/
def actionNote (state : State) : String :=
  match (row state).action with
  | some action => s!", and the connection action is {action.label}"
  | none => ""

/-- The corpus outcome of one step: what the peer did, and where it now is. A refusal's
state is the one it leaves, not the one it was in — a refused send moves nothing, while
a refused receive is answered by closing. -/
def stepOf (peer : Peer) (step : ExchangeStep) : Except String (StepOutcome × Peer) := do
  let offer ← offerOf step
  match SpecAMQP.Ref.Connection.apply peer step.send offer with
  | .ok next =>
    let sent :=
      match offer with
      | .header header => some header.octets
      | .frame _ octets _ => some octets
      | .arrives _ => none
    return (⟨true, sent, next.state.label, none,
             s!"admitted; the peer is in {next.state.label}               {actionNote next.state}"⟩, next)
  | .error reason =>
    let peer := { peer with state := reason.place.getD peer.state }
    let reply :=
      match reason.reply with
      | [] => ""
      | octets :: _ => s!", writing {toHexBrief octets}"
    return (⟨false, reason.reply.head?, peer.state.label, some reason.condition,
             s!"{reason.detail}; the peer is in {peer.state.label}               {actionNote peer.state}{reply}"⟩, peer)

/-- The reference implementation's connection layer behind the corpus interface. A
state name the table does not have fails here rather than being read as some default. -/
def refExchangeCodec : ExchangeCodec where
  name := "reference"
  St := Peer
  start := fun name =>
    match State.lookup name with
    | some state => .ok { Peer.new with state }
    | none => .error s!"'{name}' is not a connection state the table declares"
  step := stepOf

end SpecAMQP.Ref.ConnectionCodec
