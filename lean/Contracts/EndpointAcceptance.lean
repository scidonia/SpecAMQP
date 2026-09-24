import Contracts.EndpointConformance
import Proofs.EndpointConformance

/-!
# Acceptance: the endpoint's protocol core conforms

`Contracts.EndpointConformance` freezes what the endpoint's core claims — `ConformsVia` over the relation
`fun s i => i.conn = s`, between `Proofs.specConn` and `Impl.Core.implCore` — and recorded itself as a statement
awaiting a proof. This module is the acceptance: the proof is `Proofs/EndpointConformance.lean`, and the binding
below applies it at the frozen type.

**Why this is a module rather than a paragraph.** `Contracts.EndpointConformance` imports the two sides the
claim names, so the proof must import it back for the statement to be the one it proves, and a declaration
inside that file would close a cycle. Splitting the acceptance out keeps the dependency one-way — the
statement imports the specification and the two sides, the proof imports the statement, and this module
imports both — and it has a second effect the split exists for: **a statement module that cannot import any
proof is a statement nobody can quietly weaken to meet one.**

**What the proof rests on, since the difference between plumbing and protocol is the whole content of this
rung.** The four equalities relating the two plumbings — `arriving_agrees`, `sending_agrees`,
`answerOf_agrees`, `submissionOf_agrees` — with `toOctets_agrees` and `callOctets_agrees` as the two halves
the api reading stands on. Three of the four are `rfl`-level, which is the strongest available statement
that two separately written constructions are the same construction; `submissionOf_agrees` closes by case
split because `Except.toOption` is opaque to the elaborator's default transparency, and not because any
input disagrees. **The protocol decisions are not restated and not re-proved**: the core is a driver over
`Spec.Connection.step`, so it shares the specification's decision function by construction, a defect inside
that function is inherited by both sides rather than caught here, and the corpus and the differentials are
the instruments that look for one.

**What it does not reach** is unchanged from the statement's own list: the socket boundary stays the one
named unproved dependency (`PLAN.md` §23.1), the stream corollary waits on `ValuePrefixDetermined`, and
nothing here is a claim about the compiled binary.
-/

namespace SpecAMQP.Contracts

/-- **The endpoint's protocol core conforms to the specification's connection endpoint.**

The proof applied at exactly the type `Contracts.EndpointConformance` froze. The acceptance is therefore the
proof itself rather than a restatement of it: had the statement drifted, this would fail to elaborate instead
of passing through a second reading of a claim nobody proved. -/
theorem endpoint_conformance_public : EndpointConforms :=
  SpecAMQP.Proofs.endpoint_conforms

end SpecAMQP.Contracts
