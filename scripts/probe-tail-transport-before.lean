import Spec.Connection
import Spec.Frame

/-! A probe for `sasl.8`'s and `version-negotiation.5`'s before-state: what the model does
when the transport role (which peer opened the socket) is nowhere in its state.

The two rows the sentence needs cannot be stated at all today — there is no field to name
the TCP client with — so this file states the *behaviour* the model has: the SASL
dialogue's announcement is admitted from either direction and from a peer whose socket
role nothing has fixed, and a protocol header is admitted in either direction at START.

Companion: `probe-tail-transport.lean`, which states the same two questions with the role
named and does not compile until the field exists. -/

open SpecAMQP.Spec.Connection
open SpecAMQP.Harness (Octets ofHex)

/-- The `sasl-mechanisms` frame the security corpus's server sends, from
`vectors/sasl.ndjson`'s `sasl-mechanisms-from-the-server`. -/
def mechanismsOctets : Octets :=
  match ofHex "0000002202010000005340c01501e01202a305504c41494e09414e4f4e594d4f5553" with
  | .ok bytes => bytes
  | .error _ => #[]

def showSasl (label : String) (outbound : Bool) : IO Unit :=
  let endpoint : Endpoint := { Endpoint.initial with layer := .sasl, phase := .awaitingMechanisms }
  let size : Nat := mechanismsOctets.size
  match SpecAMQP.Spec.Frame.decodeFrame mechanismsOctets with
  | .error reason => IO.println s!"  {label}: the probe's frame does not decode: {reason}"
  | .ok (frame, _) =>
    match frame.body with
    | none => IO.println s!"  {label}: the probe's frame carries no body"
    | some body =>
      match stepSaslFrame endpoint outbound size body #[] with
      | .ok _ => IO.println s!"  {label}: admitted"
      | .error refusal =>
        IO.println s!"  {label}: refused with {refusal.condition} / {refusal.reasonClass}: {refusal.detail}"

def showHeader (label : String) (outbound : Bool) : IO Unit :=
  let endpoint : Endpoint := Endpoint.initial
  let header : ProtocolHeader := ⟨Layer.amqp.protocolId, ⟨1, 0, 0⟩⟩
  match stepHeader endpoint outbound header with
  | .ok _ => IO.println s!"  {label}: admitted"
  | .error refusal =>
    IO.println s!"  {label}: refused with {refusal.condition} / {refusal.reasonClass}: {refusal.detail}"

def main : IO UInt32 := do
  IO.println "the SASL dialogue's announcement, with no transport role in the state"
  showSasl "a peer sends sasl-mechanisms    " true
  showSasl "a peer receives sasl-mechanisms" false
  IO.println "a protocol header at START, with no transport role in the state"
  showHeader "a peer sends a header    " true
  showHeader "a peer receives a header" false
  return 0
