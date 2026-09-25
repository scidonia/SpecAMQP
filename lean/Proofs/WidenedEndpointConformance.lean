import Contracts.WidenedEndpointConformance
import Proofs.EndpointConformance
import Impl.Core

/-!
# The endpoint's widened conformance

`Contracts/WidenedEndpointConformance` freezes the second endpoint claim: the widened relation, and
its acceptance parameterized by two `Endpoint`s. This module names the two and proves the instance.

## The specification's widened endpoint

`specProtocol` is `Proofs.specConn` — the connection layer's own endpoint, the one R3 pairs the core
with — lifted to the widened state: the frame stays entirely the connection layer's, and the session
table is carried through the step unchanged. It is the specification endpoint the widened claim is
about because *that is what the shipped core is*: a driver over `Spec.Connection.step`. The widened
relation's extra strength over R3's is the session half, and on this pairing the session half is the
identity — both sides begin with the empty table and neither step writes it (`Impl.Core.step`'s own
`step_preserves_sessions`), so the widened instance is R3's simulation with one more conjunct
maintained at each step.

## What this does *not* say, and why that is the honest reading

It does not say the shipped core implements the widened *session* protocol: `Impl.Core` relays a
session frame through the connection layer and inherits its handling, which `Impl/Core.lean`'s own
header states at length. The session-layer widening lives in `Spec.Protocol` and is exercised by the
corpus in both artefacts; what this instance establishes is the part that *is* this rung's — that the
core's state is the widened state, that its measured connection behaviour is the specification's, and
that nothing it does disturbs the session table the widened relation ranges over.
-/

namespace SpecAMQP.Proofs

open SpecAMQP.Contracts
open SpecAMQP.Impl.Core

/-- **The specification's connection endpoint, over the widened state.** The frame is the connection
layer's, and the session table is threaded through unchanged: this is the specification side of the
widened claim, and it is the lift of `specConn` rather than a second protocol decision. -/
def specProtocol : Endpoint SpecAMQP.Spec.WidenedProtocolState where
  init := { connection := specConn.init, sessions := fun _ => none }
  step := fun state inp =>
    match specConn.step state.connection inp with
    | none => none
    | some (conn', outs) =>
      some ({ connection := conn', sessions := state.sessions }, outs)
  choose := fun state inp =>
    { out | ∃ (conn' : SpecAMQP.Spec.Connection.Endpoint) (outs : List Output),
              (conn', outs) ∈ specConn.choose state.connection inp ∧
              out = ({ connection := conn', sessions := state.sessions }, outs) }

/-- **The widened endpoint conforms.** `WidenedEndpointConforms specProtocol implCore`, at exactly
the type the contract freezes: the relation's connection half is R3's own equality, and its session
half is the identity both sides carry through every step. -/
theorem widened_endpoint_conforms :
    WidenedEndpointConforms specProtocol Impl.Core.implCore := by
  refine ⟨?_, ?_⟩
  · -- the initial states: the same connection endpoint, and the empty session table on both sides
    refine ⟨?_, ?_⟩
    · rfl
    · intro channel session hSome
      have hnone : specProtocol.init.sessions channel = none := rfl
      rw [hnone] at hSome
      cases hSome
  · intro s i inp hR out hstep
    obtain ⟨hproto, hvalid⟩ := hR
    -- the relation's two halves, read off the computed view
    have hconn : i.conn = s.connection := by
      simpa only [State.protocol] using
        congrArg SpecAMQP.Spec.WidenedProtocolState.connection hproto
    have hsess : i.sessions = s.sessions := by
      simpa only [State.protocol] using
        congrArg SpecAMQP.Spec.WidenedProtocolState.sessions hproto
    -- the connection layer's own simulation, which is R3's theorem pointwise
    obtain ⟨s', outs, hmem, hrel, houts⟩ :=
      endpoint_conforms.2 s.connection i inp hconn out hstep
    -- and the session table is carried: neither side's step writes it
    have hcarried : out.1.sessions = s.sessions :=
      (step_preserves_sessions i inp out hstep).trans hsess
    refine ⟨{ connection := s', sessions := s.sessions }, outs, ?_, ?_, houts⟩
    · exact ⟨s', outs, hmem, rfl⟩
    · refine ⟨?_, ?_⟩
      · rw [protocol_eq_iff]
        exact ⟨hrel, hcarried⟩
      · exact hvalid

end SpecAMQP.Proofs
