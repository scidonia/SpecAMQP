import Contracts.Sasl
import Spec.Connection

/-!
# The SASL dialogue's laws: preservation, per step

`lean/Contracts/Sasl.lean` states the four claims and `lean/Contracts/SaslAcceptance.lean` binds them
to what is proved here. This module is that proof, in the shape `Proofs/SessionCredit.lean` and
`Proofs/FrameConformance.lean` established: statements about the specification's own `stepSaslFrame`
and `stepAmqpFrame` rather than about the frames somebody thought to write down, with the invariant
of the dialogue preserved step by step.

## Why the laws are stated over `stepSaslFrame` and not over `step`

`step` is the dispatcher: it decides which of the two step functions a submission reaches by asking
the endpoint's layer, and the layer is what these laws are about. Stating them over the dispatcher
would make each law carry the dispatcher's own case split as a hypothesis, and the laws are about the
dialogue rather than about how one reaches it. The corpus is where the two agree — every vector's
step goes through `step`.

## The decomposition: the size guard first

`stepSaslFrame`'s first question is the size guard, and it decides the whole step *before* any arm is
reached: a frame over MIN-MAX-FRAME-SIZE is refused whatever phase the dialogue is in and whatever
the frame says. That is a fact about the code's structure, so each law is discharged by two lemmas —
one where the guard passes (`hsize : size ≤ minMaxFrameSize`, the arms then reduce) and one where it
refuses (`stepSaslFrame_oversize`), and the law itself only chooses between them. It is also what
makes the reduction tractable: with the guard's branch given, the arms are `match`es on the phase and
`if`s on the frame, and each concrete case either refuses (an `Except.error` the simplifier refutes)
or leaves a record whose claim is a conjunction of equations.

## What the reduction needs, and why

Three things had to be named rather than left to the simplifier, each for a reason visible in the
code:

* **`beq_eq_true_iff`** — the arms ask whether the frame is the one they expect with `==`, and
  `SaslFrame`'s `BEq` is *derived* rather than a `DecidableEq` instance, so the comparison is a
  computation the simplifier does not reduce on its own.
* **`reduceCtorEq`**, which turns the resulting `SaslFrame.other = SaslFrame.mechanisms` into
  `False`, so the arm's `if` reduces to its refusing branch.
* the `Except` monad's own lemmas (`Except.bind`, `Except.map`, `Except.isOk`, `Except.toBool`),
  because a `do` block is a bind chain and `.isOk` unfolds through `toBool`.

No `sorry`, no new axiom, and no `native_decide`: every case is decided by the equation lemmas of the
functions it came from.
-/

namespace SpecAMQP.Proofs

open SpecAMQP.Spec.Connection
open SpecAMQP.Contracts (DialogueState)
open SpecAMQP.Spec.Codec (Value)
open SpecAMQP.Harness (Octets)

/-- The arms compare the frame against the five constructors with `==`, and `SaslFrame`'s `BEq` is
derived rather than a `DecidableEq` instance, so the comparison is a computation the simplifier does
not reduce on its own. This is that comparison, stated once. -/
private theorem beq_eq_true_iff (a b : SaslFrame) : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> decide

/-- The frame step's first question is a `!=` against the SASL role, and `FrameRole`'s `BEq` is
derived for the same reason `SaslFrame`'s is: the comparison is a computation the simplifier does not
reduce, so the one the guard makes is stated. -/
private theorem frameRole_sasl_bne_sasl : (FrameRole.sasl != FrameRole.sasl) = false := by decide

/-- A list whose `isEmpty` is false is not the empty list: the dialogue's invariant is stated with
the empty list, which is what it means, and the announcement's guard is stated with the boolean,
which is what it checks. -/
private theorem isEmpty_false_iff_ne_nil {l : List String} : l.isEmpty = false ↔ l ≠ [] := by
  cases l <;> simp_all

private theorem ne_nil_of_isEmpty_false {l : List String} (h : l.isEmpty = false) : l ≠ [] :=
  isEmpty_false_iff_ne_nil.mp h

/-- **An oversized SASL frame is refused before any arm is reached.** The size guard is the step's
first question, so the phase, the direction and the frame's own content play no part: a peer that
sends more than MIN-MAX-FRAME-SIZE octets is answered with the same refusal in every moment of the
dialogue. -/
theorem stepSaslFrame_oversize (endpoint : Endpoint) (outbound : Bool) (size : Nat) (body : Value)
    (wrote : Octets) (hsize : ¬ (size ≤ minMaxFrameSize)) :
    (stepSaslFrame endpoint outbound size body wrote).isOk = false := by
  have hdec : decide (size ≤ minMaxFrameSize) = false := by
    simpa [decide_eq_false_iff_not] using hsize
  cases endpoint with
  | mk st ly ph rl ms ll pl =>
    cases ph <;>
      simp only [stepSaslFrame, hdec, decide_true, decide_false, if_true, if_false,
        Bool.false_eq_true, refuseUnless, cond_false, cond_true, Except.bind, Except.map,
        Except.isOk, Except.toBool, bind, pure, Except.pure]

/-! ## The layer rule -/

/-- **A body that is none of the five performatives never crosses in the SASL layer.** Every arm of
the dialogue begins by asking whether the frame is the one it is waiting for, so a body that names
none of the five is refused by whichever arm the phase selects — in every phase, in either direction,
and however well formed the frame is. -/
theorem sasl_layer_admits_only_sasl_performatives (endpoint : Endpoint) (outbound : Bool)
    (size : Nat) (body : Value) (wrote : Octets) (hbody : SaslFrame.ofBody body = .other) :
    (stepSaslFrame endpoint outbound size body wrote).isOk = false := by
  by_cases hsize : size ≤ minMaxFrameSize
  · cases endpoint with
    | mk st ly ph rl ms ll pl =>
      cases ph <;>
        simp only [stepSaslFrame, hsize, decide_true, decide_false, if_true, if_false, refuseUnless,
          cond_false, cond_true, beq_eq_true_iff, reduceCtorEq, hbody, Except.bind, Except.map,
          Except.isOk, Except.toBool, bind, pure, Except.pure]
  · exact stepSaslFrame_oversize endpoint outbound size body wrote hsize

/-- **A SASL performative never crosses in the AMQP layer.** The frame step's first question is
whether the body belongs to this layer at all, and a SASL performative does not. -/
theorem amqp_layer_admits_no_sasl_performative (endpoint : Endpoint) (outbound : Bool)
    (channel size : Nat) (body : Value) (wrote : Octets) (hbody : roleOfBody body = .sasl) :
    (stepAmqpFrame endpoint outbound channel size body wrote).isOk = false := by
  cases hrole : roleOfBody body
  case sasl =>
    simp only [stepAmqpFrame, hrole, frameRole_sasl_bne_sasl, reduceCtorEq, decide_true,
      decide_false, if_true, if_false, refuseUnless, cond_false, cond_true, Except.bind, Except.map,
      Except.isOk, Except.toBool, bind, pure, Except.pure]
  all_goals simp_all

/-! ## The dialogue's order -/

/-- **The phase never moves backwards inside the SASL layer.** A `sasl-outcome` that establishes the
layer is not a counterexample: establishment leaves the record at `absent`, and it leaves the layer
at AMQP, which is the other conjunct of this law's hypothesis. -/
theorem sasl_phase_never_goes_back (endpoint : Endpoint) (outbound : Bool) (size : Nat)
    (body : Value) (wrote : Octets) (out : Outcome)
    (hstep : stepSaslFrame endpoint outbound size body wrote = .ok out)
    (hlayer : out.endpoint.layer = Layer.sasl) :
    endpoint.phase.rank ≤ out.endpoint.phase.rank := by
  by_cases hsize : size ≤ minMaxFrameSize
  · cases endpoint with
    | mk st ly ph rl ms ll pl =>
      cases ph <;> cases hf : SaslFrame.ofBody body <;>
        simp only [stepSaslFrame, hsize, decide_true, decide_false, if_true, if_false, refuseUnless,
          cond_false, cond_true, beq_eq_true_iff, reduceCtorEq, hf, Except.bind, Except.map,
          Except.isOk, Except.toBool, bind, pure, Except.pure] at hstep
      all_goals
        repeat' split at hstep
        all_goals (try (cases hstep)) <;> simp_all [SaslPhase.rank]
  · have hbad := stepSaslFrame_oversize endpoint outbound size body wrote hsize
    rw [hstep] at hbad
    simp [Except.isOk, Except.toBool] at hbad

/-! ## Establishment is the `ok` outcome's alone -/

/-- **Only the `ok` outcome reaches the AMQP layer.** The code the establishment test reads is the
value the `sasl-code` choice declares for `ok`, so a table that moved it would move this law rather
than leave it true by accident. -/
theorem only_an_ok_outcome_establishes_the_layer (endpoint : Endpoint) (outbound : Bool)
    (size : Nat) (body : Value) (wrote : Octets) (out : Outcome)
    (hfrom : endpoint.layer = Layer.sasl)
    (hstep : stepSaslFrame endpoint outbound size body wrote = .ok out)
    (hlayer : out.endpoint.layer = Layer.amqp) :
    out.endpoint.state = State.start ∧ out.endpoint.phase = SaslPhase.absent ∧
      out.endpoint.mechanisms = [] ∧ out.endpoint.role = none ∧
      SaslFrame.ofBody body = SaslFrame.outcome := by
  by_cases hsize : size ≤ minMaxFrameSize
  · cases endpoint with
    | mk st ly ph rl ms ll pl =>
      cases ph <;> cases hf : SaslFrame.ofBody body <;>
        simp only [stepSaslFrame, hsize, decide_true, decide_false, if_true, if_false, refuseUnless,
          cond_false, cond_true, beq_eq_true_iff, reduceCtorEq, hf, Except.bind, Except.map,
          Except.isOk, Except.toBool, bind, pure, Except.pure] at hstep
      all_goals
        repeat' split at hstep
        all_goals (try (cases hstep))
        all_goals
          first
            | exact ⟨rfl, rfl, rfl, rfl, rfl⟩
            | simp_all [hf, hlayer, hfrom]
  · have hbad := stepSaslFrame_oversize endpoint outbound size body wrote hsize
    rw [hstep] at hbad
    simp [Except.isOk, Except.toBool] at hbad

/-! ## The invariant every reachable dialogue holds -/

/-- The starting endpoint: no dialogue has begun, so all three clauses are vacuous. -/
theorem dialogue_state_initial : DialogueState Endpoint.initial := by
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> simp [Endpoint.initial] at h

/-- **The invariant is preserved by every step the dialogue admits.** The announcement's arm is the
one that makes the first two clauses true — it refuses an empty list and sets the role — and every
other admitted step leaves both where they were, which is why the law is stated once rather than per
arm. The third clause is the layer's, and the only arm that changes the layer is the establishment
branch, which leaves the phase `absent` and so makes the clause vacuous. -/
theorem dialogue_state_step {endpoint : Endpoint} (h : DialogueState endpoint) (outbound : Bool)
    (size : Nat) (body : Value) (wrote : Octets) (out : Outcome)
    (hstep : stepSaslFrame endpoint outbound size body wrote = .ok out) :
    DialogueState out.endpoint := by
  by_cases hsize : size ≤ minMaxFrameSize
  · cases endpoint with
    | mk st ly ph rl ms ll pl =>
      cases ph <;> cases hf : SaslFrame.ofBody body <;>
        simp only [stepSaslFrame, hsize, decide_true, decide_false, if_true, if_false, refuseUnless,
          cond_false, cond_true, beq_eq_true_iff, reduceCtorEq, hf, Except.bind, Except.map,
          Except.isOk, Except.toBool, bind, pure, Except.pure] at hstep
      all_goals
        repeat' split at hstep
        all_goals (try (cases hstep)) <;>
          simp_all [DialogueState, isEmpty_false_iff_ne_nil, ne_nil_of_isEmpty_false]
  · have hbad := stepSaslFrame_oversize endpoint outbound size body wrote hsize
    rw [hstep] at hbad
    simp [Except.isOk, Except.toBool] at hbad

end SpecAMQP.Proofs
