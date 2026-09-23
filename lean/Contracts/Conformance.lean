import Mathlib.Data.Set.Basic

/-!
# The conformance interface

What it means for an endpoint to conform, stated once so that it is frozen before any implementation
is proved against it. `PLAN.md` §10 is the design; this file is that design as Lean, and the rules it
carries are quoted where a reader needs them rather than paraphrased.

## Why this exists

A specification that does not define conformance gives downstream work no target. The claim this
repository wants a programme to be able to make is not "it computes this value" but **"it refines this
specification"**, and the difference is a relation rather than a function: the specification's step is a
set of permitted outcomes (`MAY` clauses and policy-dependent updates produce sets), the
implementation's step is a partial function, and conformance is a simulation between them that
preserves the *wire* exactly.

## The reading, in three sentences

An endpoint's observable output is the wire, so an implementation must emit exactly a sequence the
specification admits — output agreement, not trace inclusion. The specification's nondeterminism is a
set, and its adequacy obligation runs the *other* way from its safety obligation: the relation must
admit every behaviour a conforming third-party implementation exhibits, so a third-party vector the
specification rejects is a bug in the specification. And nothing here promotes a `SHOULD` to a `MUST`:
a `SHOULD` becomes either a fairness-qualified progress obligation or a recorded freedom, each with a
ledger disposition.

## What is deliberately opaque

The peer, the ordered byte stream with arbitrary fragmentation, timers as explicit ticks, and
TLS/crypto are named assumptions rather than modelled subsystems (`PLAN.md` §10 rule 6). They appear
below as carriers with no structure, so a `Conforms` claim that rests on one says so at its type
rather than in prose a reader has to find.
-/

namespace SpecAMQP.Contracts

/-- The application's side of the interface, opaque here: what a call *is* belongs to the endpoint's
own API, and nothing in the conformance relation inspects it beyond which call was made. -/
structure ApiCall where
  name : String
  arguments : List String
deriving BEq, Repr

/-- The application's answer, equally opaque. -/
structure ApiResponse where
  name : String
  ok : Bool
deriving BEq, Repr

/-- A tick, opaque: time crosses, and whether anything was due is the endpoint's business. -/
structure Tick where
  id : Nat
deriving BEq, Repr

/-- The alphabet an endpoint reads. A frame is the wire; an `ApiCall` is its own application asking it
to do something, which AMQP 1.0 specifies as thoroughly as it specifies the frames; a `Tick` is time
crossing, modelled as an input rather than as a clock so that replay is deterministic and no test needs
a wall clock. -/
inductive Input where
  | frame : ByteArray → Input
  | api : ApiCall → Input
  | tick : Tick → Input

/-- What an endpoint emits. Frames go on the wire; the rest is what it tells its own application. -/
inductive Output where
  | frame : ByteArray → Output
  | api : ApiResponse → Output

/-- An endpoint as the interface sees it. The specification supplies `choose` — a *set* of permitted
outcomes, because `MAY` clauses and policy-dependent updates permit several — and an implementation
supplies `step`, a partial function, because a real programme may have no answer for an input it
rejects. The two are different kinds of thing on purpose: collapsing the set to a function is how a
specification quietly becomes one implementation's behaviour. -/
structure Endpoint (σ : Type) where
  init : σ
  step : σ → Input → Option (σ × List Output)
  choose : σ → Input → Set (σ × List Output)

/-- **Conformance**, as a forward simulation preserving identical output sequences.

`R` relates specification states to implementation states; the initial states are related; and every
step the implementation takes must be matched by a step the *specification* permits, leaving the
states related and emitting **the same outputs in the same order**. Outputs are compared as sequences
rather than as sets because the wire is ordered, and the implementation's outputs are compared to a
permitted step's outputs rather than to the whole `choose` result because a permitted step is what the
implementation is claiming to have taken.

This is the shape `PLAN.md` §10 fixes. Its obligations beyond this relation — progress under a stated
fairness assumption, bounded resources answering with the mandated errors, and the environment
assumptions above — are stated per layer where a layer has something to say about them, rather than
folded into a definition that would then be claiming more than a simulation can check. -/
def Conforms {σs σi : Type} (spec : Endpoint σs) (impl : Endpoint σi) : Prop :=
  ∃ R : σs → σi → Prop,
    R spec.init impl.init ∧
    ∀ (s : σs) (i : σi) (inp : Input),
      R s i →
      ∀ out : σi × List Output,
        impl.step i inp = some out →
        ∃ s' : σs, ∃ outs : List Output,
          (s', outs) ∈ spec.choose s inp ∧ R s' out.1 ∧ out.2 = outs

/-- The relation at the heart of `Conforms`, exposed so a layer's proof can state the invariant it
maintains instead of re-deriving the existential every time. -/
def ConformsVia {σs σi : Type} (R : σs → σi → Prop) (spec : Endpoint σs)
    (impl : Endpoint σi) : Prop :=
  R spec.init impl.init ∧
  ∀ (s : σs) (i : σi) (inp : Input),
    R s i →
    ∀ out : σi × List Output,
      impl.step i inp = some out →
      ∃ s' : σs, ∃ outs : List Output,
        (s', outs) ∈ spec.choose s inp ∧ R s' out.1 ∧ out.2 = outs

/-- Taking the existential witness out of `Conforms`, which is what an instance proves. -/
theorem conforms_via_of_conforms {σs σi : Type} (spec : Endpoint σs) (impl : Endpoint σi)
    (h : Conforms spec impl) : ∃ R, ConformsVia R spec impl := h

/-- And putting one in, so a layer can build the instance from the relation it maintains. -/
theorem conforms_of_conforms_via {σs σi : Type} (spec : Endpoint σs) (impl : Endpoint σi)
    (R : σs → σi → Prop) (h : ConformsVia R spec impl) : Conforms spec impl := ⟨R, h⟩

end SpecAMQP.Contracts
