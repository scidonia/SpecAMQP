import Contracts.WidenedEndpointConformance
import Impl.Core

/-!
# The widening projects onto the old endpoint relation

`Contracts.WidenedEndpointConformance` freezes the proposition
`WideningProjectsEndpointRelation`: on the fragment the old endpoint rung reaches — connection state
and buffering, no widened session table on either side — the widened relation agrees with the old
one after projection. This module proves it, and it is what licenses calling the widened relation an
*extension* rather than a second, unrelated claim.

## What the proof reads

`WidenedEndpointRelation` is `implementation.protocol = specification ∧ Valid specification`, where
`implementation.protocol` is the computed view of the core's two fields. So the whole proposition is
the structure-level fact that the view is exactly its two fields (`Impl.Core.protocol_eq_iff`) plus
the fragment's two session equalities. Under the fragment both sides' session tables are the empty
one, so the session half of the equality is an identity and the validity conjunct is vacuous — a
state whose table maps every channel to `none` has no session for the invariant to be about.

The interesting half is the *forward* direction, and the reason it is worth a theorem rather than a
remark: the widened relation is strictly stronger than the old one, and this says that on the
fragment the extra strength is empty. Without it, a widened relation that had quietly dropped the
connection equality would still be satisfiable there.
-/

namespace SpecAMQP.Proofs

open SpecAMQP.Contracts
open SpecAMQP.Impl.Core

/-- **The widening projects onto the old endpoint relation**, at exactly the frozen type. -/
theorem widening_projects_endpoint_relation : WideningProjectsEndpointRelation := by
  intro specification implementation fragment
  obtain ⟨specEmpty, implEmpty⟩ := fragment
  -- the fragment's two session equalities, as equalities between the two *functions* rather than
  -- as statements that each is empty somewhere: the two sides have to meet at one function
  have specNone : specification.sessions = fun _ => none := funext specEmpty
  have implNone : implementation.sessions = fun _ => none := by
    funext channel
    simpa only [State.protocol] using implEmpty channel
  constructor
  · -- the widened relation's connection half *is* the old relation
    intro widened
    have hconn := congrArg SpecAMQP.Spec.WidenedProtocolState.connection widened.1
    simpa only [State.protocol, projectImplementation, projectSpecification] using hconn
  · intro hconn
    have hconn' : implementation.conn = specification.connection := by
      simpa only [projectImplementation, projectSpecification] using hconn
    refine ⟨?_, ?_⟩
    · rw [protocol_eq_iff]
      exact ⟨hconn', by rw [implNone, specNone]⟩
    · -- the fragment's empty table satisfies the invariant vacuously
      intro channel session hSome
      rw [specNone] at hSome
      exact absurd hSome (by simp)

end SpecAMQP.Proofs
