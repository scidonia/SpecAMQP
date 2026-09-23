import Contracts.Conformance
import Proofs.FrameConformance
import Spec.Codec
import Ref.Value

/-!
# The wire readers' agreement

`Proofs.FrameConformance.ValueLayersAgree` is the value layer's claim in the *wire* vocabulary: what
the reference's reader reads off a buffer, the specification's reader reads too - the same octets
consumed and bodies the frame layer views the same way - or a refusal of the same class. This module
is that claim's development, and it is **in progress**: the formulation and the base case are below,
and the per-branch lemmas and the fuel induction are the work it exists for.

## Why a fuel-indexed formulation, and what it carries

The two readers are the same shape: each is `readValue fuel cursor`, the entry points feed it the
*buffer's size* as the fuel ("every descent spends at least one octet of it"), and both start at
`⟨bytes, 0⟩`. So the contract's claim is this one at `fuel = bytes.size`, at the initial cursors - no
arbitrary fuwel to reconcile, unlike the corpus-vocabulary side.

What the formulation carries that the corpus side did not is the **cursor**: the two `Cursor`
structures are separate declarations with the same fields, so the relation is `CursorAgrees` (same
buffer, same position) and the induction hypothesis must preserve it through the descent, not merely
carry the value. That is where "the same octets consumed" comes from.

## The described branch, and the statement it needs first

`wireDescribed` (`0x00`) is the first branch that consumes the induction hypothesis, and reading it
shows the statement must be *strengthened* before it can be proved: a `.described` body's view is
`some (typeOfDescriptor descriptor)`, so agreeing on views is not enough — the two *descriptors* must
correspond, which is exactly `BodiesAgree` (`FrameSendConformance.lean`), the relation the corpus
side already uses between the two value types. The success conjunct should therefore carry
`BodiesAgree body other`, and the contract's view equality is then *derived* from it:

* `typeOfDescriptor` inspects only `.ulong` and `.symbol` descriptors, and both readers run `find?`
  over the **same generated table** — `Spec/Frame.lean:76` and `Ref/Frame.lean:39` both
  `open SpecAMQP.Generated.Oasis (TypeDecl types)`. There is no second table to compare, only the
  representation difference inside the predicate (`code` against `code.toNat`), which is the same
  `BodiesAgree` obligation at the descriptor.
* So `BodiesAgree body other → specBodyView body = refBodyView other` is a case analysis on the
  body, with the `.described` case asking the descriptor lemma above.

A later reader may wonder why the statement below says the view rather than `BodiesAgree`: it is the
contract's spelling, kept so the claim is the contract's own, and the strengthening is the route to
proving it.

## What the view weakens to

`specBodyView`/`refBodyView` look at a body only to ask *which described type it announces*
(`some (typeOfDescriptor descriptor)` for a `.described`, `none` otherwise). So the success conjunct
is far weaker than body equality: the same consumed octets, and the same descriptor type where the
body is described. Proving agreement *through* those views rather than through the values is what
makes the claim tractable, and it is what the contract asks for.

## The branches, and the bridge that turns out to be them

The specification dispatches on `classify code.toNat` and then on generated tables (`dataDecl`,
`elementDecl?`, the declared category), while the reference matches the constructor octet as a
*literal* — inline in its own `readValue`, with no table object to compare against. So there is no
separate bridge to build ahead of the branches: the two dispatches meet at the branch, and the
per-octet correspondence *is* the branch lemma. What the tables do offer is cheap resolution of
their own side, which is what a branch needs first:

```lean
example : (SpecAMQP.Spec.Codec.dataDecl 0x40).map (fun d => (d.width, d.owner)) =
    .ok (0, "null") := by decide
example : (SpecAMQP.Spec.Codec.dataDecl 0x01).isOk = false := by decide
example : (SpecAMQP.Spec.Value.classify 0x40 : SpecAMQP.Spec.Value.Constructor) = .fixed 0 := by
  decide
```

Ordinary `decide`, not `native_decide`: the lookups are computable and finite, so the trust base is
unchanged. Each branch then owes three things — the constructor octet, the declared form, and the
recursion at the fuel beneath — with `CursorAgrees` carried through the descent, and the branches
group by form: described (`0x00`), the four scalar categories (fixed widths 0/1/2/4/8/16, variable
1/4), compound (`list`, `map`), and array. `wireDescribed` and the compound ones are the only
branches that consume the induction hypothesis; the scalars and the refusals close against the
literal alone.
-/

open Lean (Json)

namespace SpecAMQP.Proofs

/-- The two wire cursors agree when they are the same buffer at the same position. -/
def CursorAgrees (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor) : Prop :=
  c.data = c'.data ∧ c.pos = c'.pos

/-- **The wire readers' agreement at a given fuel**, in the contract's direction. -/
def WireAgrees (fuel : Nat) : Prop :=
  ∀ (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor), CursorAgrees c c' →
    (∀ (other : SpecAMQP.Ref.Value) (c₂' : SpecAMQP.Ref.Cursor),
        SpecAMQP.Ref.readValue fuel c' = .ok (other, c₂') →
        ∃ (body : SpecAMQP.Spec.Codec.Value) (c₂ : SpecAMQP.Spec.Codec.Cursor),
          SpecAMQP.Spec.Codec.readValue fuel c = .ok (body, c₂) ∧
          CursorAgrees c₂ c₂' ∧ specBodyView body = refBodyView other) ∧
    (∀ (failure : SpecAMQP.Ref.DecodeError),
        SpecAMQP.Ref.readValue fuel c' = .error failure →
        ∃ refusal : SpecAMQP.Spec.Codec.Refusal,
          SpecAMQP.Spec.Codec.readValue fuel c = .error refusal ∧
          (SpecAMQP.Ref.Frame.valueFailure failure).reasonClass = refusal.reasonClass)

/-- **The base case.** At fuel 0 both readers refuse, with the same class: there is nothing to read
before the input ends. -/
theorem wireAgrees_zero : WireAgrees 0 := by
  intro c c' _
  refine ⟨?_, ?_⟩
  · intro other c₂' h
    simp only [SpecAMQP.Ref.readValue] at h
    exact absurd h (by simp)
  · intro failure h
    simp only [SpecAMQP.Ref.readValue] at h
    refine ⟨SpecAMQP.Spec.Codec.refusal "truncated" "the input ends before the value does", ?_, ?_⟩
    · simp only [SpecAMQP.Spec.Codec.readValue]
    · injection h with hf
      subst hf
      rfl

end SpecAMQP.Proofs
