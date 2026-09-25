import Spec.Connection
import Spec.Frame

/-! A probe for `sasl.8` and `version-negotiation.5` with the transport role named: the
same two questions `probe-tail-transport-before.lean` asks, now keyed on which peer opened
the socket.

Six rows: the SASL announcement sent and received by each TCP role, the announcement with
no socket role fixed, and the protocol header received at START by a TCP client and by a
TCP server. A header *sent* at START is admitted for both roles (the table's send column
and the .5/.6 pair agree about it), and is not re-probed here. -/

open SpecAMQP.Spec.Connection
open SpecAMQP.Harness (Octets ofHex)

/-- The `sasl-mechanisms` frame the security corpus's server sends, from
`vectors/sasl.ndjson`'s `sasl-mechanisms-from-the-server`. -/
def mechanismsOctets : Octets :=
  match ofHex "0000002202010000005340c01501e01202a305504c41494e09414e4f4e594d4f5553" with
  | .ok bytes => bytes
  | .error _ => #[]

def showSasl (label : String) (role : Option TransportRole) (outbound : Bool) : IO Unit :=
  let endpoint : Endpoint :=
    { Endpoint.initial with layer := .sasl, phase := .awaitingMechanisms, transportRole := role }
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

def showHeader (label : String) (role : Option TransportRole) (outbound : Bool) : IO Unit :=
  let endpoint : Endpoint := { Endpoint.initial with transportRole := role }
  let header : ProtocolHeader := ⟨Layer.amqp.protocolId, ⟨1, 0, 0⟩⟩
  match stepHeader endpoint outbound header with
  | .ok _ => IO.println s!"  {label}: admitted"
  | .error refusal =>
    IO.println s!"  {label}: refused with {refusal.condition} / {refusal.reasonClass}: {refusal.detail}"

def main : IO UInt32 := do
  IO.println "the SASL dialogue's announcement, keyed on which peer opened the socket"
  showSasl "TCP client sends sasl-mechanisms    " (some .tcpClient) true
  showSasl "TCP server sends sasl-mechanisms    " (some .tcpServer) true
  showSasl "TCP client receives sasl-mechanisms " (some .tcpClient) false
  showSasl "TCP server receives sasl-mechanisms " (some .tcpServer) false
  showSasl "no socket role fixed, sasl-mechanisms sent" none true
  IO.println "a protocol header at START, keyed on which peer opened the socket"
  showHeader "TCP client receives a header" (some .tcpClient) false
  showHeader "TCP server receives a header" (some .tcpServer) false
  IO.println (s!"version-negotiation.5 states it: " ++
    "the peer which acted in the role of the TCP client must send its outgoing protocol header on establishment")
  return 0
