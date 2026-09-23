import Contracts.Conformance
import Proofs.FrameConformance
import Proofs.FrameSendConformance
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

`bodyView_of_BodiesAgree`'s state, so a successor starts where this stopped rather than re-deriving
it: `typeOfDescriptor_agrees` **closes 623 of its 625 goals** with a case-driven closer —

```lean
cases d <;> cases d' <;>
  simp only [BodiesAgree, SpecAMQP.Spec.Frame.typeOfDescriptor,
    SpecAMQP.Ref.Frame.typeOfDescriptor] at h ⊢ <;>
  try rfl <;> simp_all
```

— and the two that remain are `.ulong/.ulong` and `.symbol/.symbol`, where `h` is the payload
equality and the goal is
`types.find? (fun entry => … == n) = types.find? (fun entry => … == n.toNat)`: equal once the
equality is rewritten *under the predicate's binder*, which is why a top-level `rw [h]` does not
reach it — enter the binder first (`congr 1`, then `funext entry`, then `rw [h]`).

Two shapes to avoid, both measured. A `match d, d' with` prologue before the `cases` abstracts the
two values, so the wildcard's `cases` acts on names the goal no longer mentions and fails with the
values still symbolic — the case-driven form above is the one that works even though the prologue
reads better. And one `simp` call over the 25×25 product exceeds the heartbeat budget while 625 goals
with the targeted `simp only` chain above close in about ten seconds: the budget is per-invocation,
so a fixed term per goal is cheap at any count and a search is expensive at one.

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

/-- **The two conjuncts of the claim at one fuel**, as a proposition in its own right, so that a
branch lemma can state what it owes without repeating them and the fuel induction can pass a whole
branch's obligation around as one term.

The success conjunct carries `BodiesAgree`, which is *stronger* than the contract's view equality and
is what the route needs: a described body's view is `some (typeOfDescriptor descriptor)`, so the two
descriptors must correspond, and `BodiesAgree` is exactly the relation that says so - the same one
the corpus side uses between the two value types. `bodyView_of_BodiesAgree` below recovers the
contract's spelling, so the claim is still the contract's own. -/
def StepAgrees (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor) : Prop :=
  (∀ (other : SpecAMQP.Ref.Value) (c₂' : SpecAMQP.Ref.Cursor),
      SpecAMQP.Ref.readValue fuel c' = .ok (other, c₂') →
      ∃ (body : SpecAMQP.Spec.Codec.Value) (c₂ : SpecAMQP.Spec.Codec.Cursor),
        SpecAMQP.Spec.Codec.readValue fuel c = .ok (body, c₂) ∧
        CursorAgrees c₂ c₂' ∧ BodiesAgree body other) ∧
  (∀ (failure : SpecAMQP.Ref.DecodeError),
      SpecAMQP.Ref.readValue fuel c' = .error failure →
      ∃ refusal : SpecAMQP.Spec.Codec.Refusal,
        SpecAMQP.Spec.Codec.readValue fuel c = .error refusal ∧
        (SpecAMQP.Ref.Frame.valueFailure failure).reasonClass = refusal.reasonClass)

/-- **The wire readers' agreement at a given fuel**, in the contract's direction, for cursors that
still hold the octets the fuel has to cover.

The bound `c.data.size - c.pos ≤ fuel` is not a convenience: **without it the statement is false**,
and the array's element loop is what refutes it. The two readers spend fuel differently on their way
into an array's elements — the specification's `readArrayData f` consumes one fuel entering its
element loop (`readElements (f - 1)` and then `readElementsLoop (f - 2)`) while the reference's
`readElements f` reads its first element at `f` — so for a fuel smaller than the octets left at the
cursor the two disagree: on `#[0xE0, 0x02, 0x00, 0x40]` at `⟨bytes, 0⟩` the reference answers `ok`
at fuel 2 where the specification answers `truncated`. What makes them agree is exactly the relation
the bound states, and at the entry point it holds for free: both entry points read at
`readValue bytes.size ⟨bytes, 0⟩`, and `bytes.size - 0 ≤ bytes.size`.

A fuel is only ever a bound on a reader's *recursion*, so the bound is what a reader needs: every
descent spends at least one octet, and the two readers' descents spend the same fuel per value, per
compound item and per array element, which is what the branch lemmas show one branch at a time. A law
quantified over every fuel a cursor can be paired with is a *different* law from the one the contract
asks for, and not a stronger one. -/
def WireAgrees (fuel : Nat) : Prop :=
  ∀ (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor), CursorAgrees c c' →
    c.data.size - c.pos ≤ fuel → StepAgrees fuel c c'

/-- **The base case.** At fuel 0 both readers refuse, with the same class: there is nothing to read
before the input ends. -/
theorem wireAgrees_zero : WireAgrees 0 := by
  intro c c' _ _hb
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

/-- **One octet, taken by two cursors that agree.** The same octet comes off the same buffer and the
cursors advance together — a cursor with nothing left fails on both sides with the same class — so every
branch of the induction begins here.

The cursors are destructured before the equalities are used, because `c.data[c.pos]` is a dependent
lookup: rewriting `c.data` under it is not type-correct, while `cases` on the equalities of the
destructured fields substitutes and leaves the lookup well-typed. -/
theorem takeU8_agrees {c : SpecAMQP.Spec.Codec.Cursor} {c' : SpecAMQP.Ref.Cursor}
    (hc : CursorAgrees c c') (b : UInt8) (d' : SpecAMQP.Ref.Cursor)
    (h : SpecAMQP.Ref.takeU8 c' = .ok (b, d')) :
    ∃ d : SpecAMQP.Spec.Codec.Cursor,
      SpecAMQP.Spec.Codec.takeU8 c = .ok (b, d) ∧ CursorAgrees d d' := by
  cases c with | mk data pos =>
  cases c' with | mk data' pos' =>
  obtain ⟨hd, hp⟩ := hc
  cases hd
  cases hp
  by_cases hlt : pos < data.size
  · have hlt' : pos < data.size := hlt
    rw [SpecAMQP.Spec.Codec.takeU8, dif_pos hlt]
    rw [SpecAMQP.Ref.takeU8, dif_pos hlt'] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hb, hc'⟩ := h
    subst hb
    refine ⟨⟨data, pos + 1⟩, rfl, ?_⟩
    rw [← hc']
    exact ⟨rfl, rfl⟩
  · have hlt' : ¬ (pos < data.size) := hlt
    rw [SpecAMQP.Ref.takeU8, dif_neg hlt'] at h
    exact absurd h (by simp)

/-- The failure half of the same step: a cursor that has run out refuses on both sides, with the same
class. -/
theorem takeU8_fails {c : SpecAMQP.Spec.Codec.Cursor} {c' : SpecAMQP.Ref.Cursor}
    (hc : CursorAgrees c c') (failure : SpecAMQP.Ref.DecodeError)
    (h : SpecAMQP.Ref.takeU8 c' = .error failure) :
    ∃ refusal : SpecAMQP.Spec.Codec.Refusal,
      SpecAMQP.Spec.Codec.takeU8 c = .error refusal ∧
      (SpecAMQP.Ref.Frame.valueFailure failure).reasonClass = refusal.reasonClass := by
  cases c with | mk data pos =>
  cases c' with | mk data' pos' =>
  obtain ⟨hd, hp⟩ := hc
  cases hd
  cases hp
  by_cases hlt : pos < data.size
  · have hlt' : pos < data.size := hlt
    rw [SpecAMQP.Ref.takeU8, dif_pos hlt'] at h
    exact absurd h (by simp)
  · have hlt' : ¬ (pos < data.size) := hlt
    rw [SpecAMQP.Ref.takeU8, dif_neg hlt'] at h
    rw [SpecAMQP.Spec.Codec.takeU8, dif_neg hlt]
    simp only [Except.error.injEq] at h
    subst h
    exact ⟨SpecAMQP.Spec.Codec.refusal "truncated"
      s!"no octet at offset {pos} of {data.size}", rfl, rfl⟩

/-- The description a body announces agrees when the bodies agree: `typeOfDescriptor` inspects only
`ulong` and `symbol` descriptors, and both readers run `find?` over the *same* generated table, so the
only obligation is the representational one `BodiesAgree` already carries. Stated case-driven rather
than with a `match` prologue: the prologue abstracts the two values, and `cases` then acts on names the
goal no longer mentions.

The two payload cases are the whole content: the tables are the same object, so the goals differ only
in the predicate's payload — `n` against `n.toNat`, a string against the same string — and rewriting
the `BodiesAgree` payload equality *under* the `find?` predicate's binder identifies them. -/
theorem typeOfDescriptor_agrees {d : SpecAMQP.Spec.Codec.Value} {d' : SpecAMQP.Ref.Value}
    (h : BodiesAgree d d') :
    SpecAMQP.Spec.Frame.typeOfDescriptor d = SpecAMQP.Ref.Frame.typeOfDescriptor d' := by
  cases d <;> cases d' <;>
    simp only [BodiesAgree, SpecAMQP.Spec.Frame.typeOfDescriptor,
      SpecAMQP.Ref.Frame.typeOfDescriptor] at h ⊢
  all_goals
    first
      | rfl
      | (congr 1
         funext entry
         rw [h]
         rfl)

/-- **The contract's view equality, from the strengthened conjunct.** A described body's view is its
descriptor's type; everything else views as `none`. -/
theorem bodyView_of_BodiesAgree {body : SpecAMQP.Spec.Codec.Value} {other : SpecAMQP.Ref.Value}
    (h : BodiesAgree body other) : specBodyView body = refBodyView other := by
  cases body <;> cases other <;>
    simp only [BodiesAgree, specBodyView, refBodyView] at h ⊢
  all_goals
    first
      | rfl
      | (rw [typeOfDescriptor_agrees h.1])

end SpecAMQP.Proofs
