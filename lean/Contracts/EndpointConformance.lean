import Contracts.Conformance
import Proofs.ConnectionConformance
import Impl.Core

/-!
# Acceptance: the endpoint's protocol core conforms

`Contracts.Conformance` states what conformance *is*, and `FrameConformance.lean` instantiates it at the frame
layer. This module states the claim for the **endpoint's protocol core** — the rung that turns "the shipped
endpoint is a driver over `Spec.Connection.step`" into a relation between two `Endpoint`s.

It is a *declaration* and not yet an acceptance: the theorem establishing `EndpointConforms` does not exist,
so this file freezes the statement before the proof is written, which is this repository's order — statement,
then proof, then acceptance. A `Prop` with no proof compiles cleanly, which is what makes the statement
frozen rather than promised.

## What it claims, and where the two sides come from

The claim is the **unit instance**: for the same input, every step the implementation's core takes is matched
by a step the specification's connection endpoint permits, with the two states related and the wire preserved.
Both sides are named rather than constructed here, because both already exist:

* `SpecAMQP.Impl.Core.implCore` — the shipped core as an `Endpoint State`, its `choose` empty for the reason
  every implementation's is: `ConformsVia` never consults one.
* `SpecAMQP.Proofs.specConn` — the specification's connection endpoint, wrapped in
  `Proofs/ConnectionConformance.lean`, which is where the connection layer's own instance lives.

The relation is `fun s i => i.conn = s`: the implementation's `conn` field *is* the specification's endpoint
state. It constrains `conn` alone, and deliberately does not mention `State.inbox` — the stream front end's
pending octets. That is not an omission: `step` neither reads nor writes `inbox`, which is what makes
`i.conn = s` sufficient rather than needing an inbox clause, and it is the reason the stream corollary below
is a *corollary* rather than part of this statement.

## What it does not claim, and what it waits on

* It does not claim anything about the socket boundary (`PLAN.md` §23.1), which stays the one named unproved
  dependency.
* It does not claim the stream corollary — that feeding a stream in one read equals feeding it in two. That is
  the front end's half and it rests on `ValuePrefixDetermined`, recorded as a residual in
  `Proofs/CoreLaws.lean`, which is also the property R2's review left open.
* It waits on the value layer's agreement: every frame instance takes it as a hypothesis, and the connection
  layer's instance does too, so this rung's proof needs that layer's relation before it can close.
-/

namespace SpecAMQP.Contracts

/-- **The endpoint's protocol core conforms to the specification's connection endpoint.**

The unit instance of `ConformsVia` for the shipped endpoint, stated over the relation that says the
implementation's connection field *is* the specification's endpoint state. The proof is R3.
-/
def EndpointConforms : Prop :=
  ConformsVia (fun s i => i.conn = s) SpecAMQP.Proofs.specConn SpecAMQP.Impl.Core.implCore

end SpecAMQP.Contracts
