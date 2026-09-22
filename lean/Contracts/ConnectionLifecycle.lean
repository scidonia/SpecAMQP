import Spec.Connection
import Spec.Session

/-!
# The connection lifecycle's laws (S3 acceptance statements)

The lifecycle's claims divide into three kinds, and this file is explicit about which is which
rather than presenting the executable ones as theorems or the theorems as evidence.

**Executable evidence, not theorems: the state table's totality.** For every state and every frame
the table permits, the specification should take the transition the table names — and that claim
*cannot* be a theorem here, because the table is a picture. There is no machine-readable
transcription to compare against, so a theorem would compare the implementation with a second
hand-written transcription, which is the one thing this project's design refuses: a second source
of truth that can drift from the first while looking like a check. The claim is therefore checked
by execution — probes over every state in both directions against every frame class the columns
distinguish, in `tests/contracts/` — and its report is where the deviations live. This is the same
reasoning that put the frame header's layout in a transcription with its source cited rather than
in a generated table: where the artifact gives prose and pictures, the honest artifact is a
transcription plus a check, not a theorem about a picture nobody can read.

**Executable evidence, not theorems: the refusal placement.** Every refusal in the exchange
corpus pins the state the peer is left in, and a refused send and a refused receive differ in
where that is. That is not stated as a law here because the corpus already states it per case:
each vector's `state` expectation *is* the claim, and stating it again as a theorem about the step
functions would add a second description of behaviour the vectors already pin — and one written
from the code rather than from the artifact, which is how a check becomes a restatement.

**Belonging to S4, not here: the window invariants.** Credit conservation and handle uniqueness
are properties of the session's arithmetic, which is in flight; stating them here would put a
claim in the contract before its subject exists.

What remains, and what this file states, is the one law about negotiation that is neither a
picture nor a per-case pin.
-/

namespace SpecAMQP.Contracts

open SpecAMQP.Spec.Connection (Endpoint ProtocolHeader Submission step)

/-- **Negotiation is decided by the header's own octets.** Two protocol headers that agree on the
magic, the protocol id and the version triple are accepted or refused identically — whatever
differs around them.

Stated about the header rather than about the decoder because that is where the law can fail. A
decoder that consulted the peer's limits, its layer or its role while judging the header would
still pass every vector the corpus has, because the corpus reaches each header from one state
each; the artifact's rule is about the header's contents, so the law is too. It is also the law
that makes the protocol header a *negotiation* rather than a handshake with state: if the outcome
depended on anything else, two peers with the same bytes could disagree about whether they had
agreed. -/
def NegotiationDependsOnTheHeaderAlone : Prop :=
  ∀ (a b : ProtocolHeader) (endpoint : Endpoint) (outbound : Bool),
    a.octets = b.octets →
    (step endpoint outbound (.header a)).isOk = (step endpoint outbound (.header b)).isOk

end SpecAMQP.Contracts
