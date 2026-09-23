import Contracts.Sasl
import Proofs.SaslDialogue

/-!
# Acceptance declarations for the security layer

`Contracts.Sasl` states what the SASL dialogue claims; this module names the proofs that establish
it, for the reason its frame-layer sibling records: the proofs state their results in the contract's
vocabulary, so they import `Contracts.Sasl`, and a declaration *inside* that module would then have
to import them back, which is a cycle. Splitting the acceptance from the statement keeps the
dependency one-way — the statement imports the specification, the proof imports the specification
and the statement, and this module imports all three.

**Every law below is proved, and these bindings are what make that a fact rather than a sentence in
a docstring.** A `Prop` defined in a contract compiles whether or not anything ever discharges it:
without a declaration like these, `Contracts.Sasl` would be green with its three laws unproved, and
the only record that they are theorems would be prose. That is the same failure this repository
refuses everywhere else — a claim that looks checked and is not — and it is why the acceptance is a
module rather than a paragraph.

A reader checking whether the security layer's claims are established reads these three declarations
and the proof module they name, and nothing further.

`DialogueState` has no binding here, deliberately rather than by omission: an invariant is not a
proposition to discharge but a preservation pair, and `Proofs.SaslDialogue.dialogue_state_initial`
with `dialogue_state_step` is that pair. It is the shape `Contracts.SessionCredit`'s invariant has,
and restating the pair as a `Prop` would add a second description of the same fact.
-/

namespace SpecAMQP.Contracts

/-- **The layer rule, both ways, at every moment.** Each proof is *stronger* than the claim it
discharges: both hold the body's shape as a hypothesis and dispense with the layer hypothesis the
claim carries, so a SASL performative never crosses in the AMQP layer whatever layer the endpoint
believes it is in, and a body naming none of the five never crosses inside the SASL layer whatever
the moment. The lambda discards that hypothesis rather than passing it, which is why the first
argument of each branch is `_`. -/
theorem layer_admits_its_own_performatives_public :
    LayerAdmitsItsOwnPerformatives :=
  fun endpoint outbound channel size body wrote =>
    ⟨fun _ hbody =>
      SpecAMQP.Proofs.sasl_layer_admits_only_sasl_performatives
        endpoint outbound size body wrote hbody,
     fun _ hbody =>
      SpecAMQP.Proofs.amqp_layer_admits_no_sasl_performative
        endpoint outbound channel size body wrote hbody⟩

/-- **The dialogue's order**, at every moment and in either direction. The proof likewise discards
the claim's layer hypothesis: the phase's rank does not decrease inside the SASL layer whether or
not the endpoint was already there. -/
theorem dialogue_phase_never_goes_back_public :
    DialoguePhaseNeverGoesBack :=
  fun endpoint outbound size body wrote out _ hstep hlayer =>
    SpecAMQP.Proofs.sasl_phase_never_goes_back endpoint outbound size body wrote out hstep hlayer

/-- **Establishment is the `ok` outcome's alone**, and this is the one law whose hypothesis is
load-bearing rather than decorative: **without `endpoint.layer = Layer.sasl` it is false.** A
`sasl-mechanisms` announcement is admitted whatever layer the endpoint is in — that arm keeps the
endpoint's own layer and sets only the phase, the announced list and the role — so an endpoint
already in the AMQP layer can be handed an announcement, be admitted, and reach the AMQP layer with
its state untouched and its body not an outcome. The hypothesis rules exactly that out, so it is
passed through rather than discarded. The two bindings above discard theirs, because those theorems
are *stronger* than the claims they discharge; this one is exactly as strong, and the difference is
a property of the layer rather than of the proofs.

The five equalities a step reaching the AMQP layer must carry are the protocol headers' first state,
the phase cleared, the mechanisms cleared, the role cleared, and the body an outcome. -/
theorem only_an_ok_outcome_establishes_the_layer_public :
    OnlyAnOkOutcomeEstablishesTheLayer :=
  fun endpoint outbound size body wrote out hfrom hstep hlayer =>
    SpecAMQP.Proofs.only_an_ok_outcome_establishes_the_layer
      endpoint outbound size body wrote out hfrom hstep hlayer

end SpecAMQP.Contracts
