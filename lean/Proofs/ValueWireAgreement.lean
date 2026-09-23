import Contracts.Conformance
import Proofs.FrameConformance
import Proofs.ReadProgress
import Proofs.FrameSendConformance
import Spec.Codec
import Ref.Value

/-!
# The wire readers' agreement

`Proofs.FrameConformance.ValueLayersAgree` is the value layer's claim in the *wire* vocabulary: what
the reference's reader reads off a buffer, the specification's reader reads too - the same octets
consumed and bodies the frame layer views the same way - or a refusal of the same class. This module
is that claim's development, and it is **in progress**. Landed: the formulation (with the fuel bound
its truth needs), the base case, the octet step and its payload bridges, the branch *pattern* and its
first three arms — the described branch and the two exemplars a scalar branch is copied from. Still
owed: the remaining scalar, compound and array arms, the loop relations they share, the dispatch that
turns the arms into the induction step, and the fuel induction itself. What each owes and how it is
proved is stated where it belongs rather than in a list here: see the octet step's arithmetic, and
`arm_0x00`'s docstring for the pattern the branches follow.

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
contract's spelling, so the claim is still the contract's own.

It also carries `c₂.data = c.data`: a read hands its own buffer back, so the *octets the fuel has to
cover* do not change as the induction descends. That component is what lets one read's bound become
the next read's bound — a described value reads its descriptor and then its value at *one* fuel, and
the second read's cursor is a position further on in the same buffer, so `d.pos ≤ d₂.pos`
(`ReadProgress`'s `readValue_progress`) with the buffer fixed is exactly the inequality the bound
needs. Without it the induction cannot relate one read's budget to the next's. -/
def StepAgrees (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor) : Prop :=
  (∀ (other : SpecAMQP.Ref.Value) (c₂' : SpecAMQP.Ref.Cursor),
      SpecAMQP.Ref.readValue fuel c' = .ok (other, c₂') →
      ∃ (body : SpecAMQP.Spec.Codec.Value) (c₂ : SpecAMQP.Spec.Codec.Cursor),
        SpecAMQP.Spec.Codec.readValue fuel c = .ok (body, c₂) ∧
        CursorAgrees c₂ c₂' ∧ c₂.data = c.data ∧ BodiesAgree body other) ∧
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

/-! ## The octet step's arithmetic, shared by every branch

A branch's proof begins by taking the octet and then reading a payload, and the two artefacts' payload
readers are different functions that compute the same thing: the reference takes its octets one at a
time (`takeU8`, `takeBeU`, `takeBytes`) while the specification accumulates a big-endian foldl over
the octets a declared width gives. What a branch needs first is the bridge between those, and what a
branch's fuel bound needs from a step is where the step left the cursor, which is why the `_data`
lemmas below sit beside the advances the round-trip rungs already state.

Three environment facts are worth recording here, because each costs an iteration otherwise. `simp`
cannot reduce an `Except` bind at all unless it is given the two lemmas that reduce it, so those two
(`Proofs/ExceptMap`'s `except_bind_ok` and `except_bind_error`) are named at every step that has to
see inside a `do` block, and `exists_of_bind_ok` recovers a bind's left side where a proof starts
from the whole read having accepted. The specification's `takeU8` is a *dependent* `if` while its
`takeBytes`/`takeBe` are not, so the three reduce through `dif_pos` and `if_pos` respectively. And a
`BodiesAgree` obligation between width-carrying carriers is an identity exactly on the width's range,
which is what `Proofs/CodecRoundTripNarrowest`'s `takeBe_lt` supplies. -/

/-- **A one-octet payload folds to the octet it holds.** The width-one rows read one octet and
accumulate it, so the foldl is that octet as a number — the fact that puts the specification's
one-octet fixed read and the reference's `takeU8` on one value. -/
theorem foldl_extract_one (a : Array UInt8) (i : Nat) (h : i < a.size) :
    (a.extract i (i + 1)).foldl (fun acc b => acc * 256 + b.toNat) 0 = a[i].toNat := by
  rw [← Array.foldl_toList, Array.toList_extract, List.extract_eq_take_drop]
  have hsub : i + 1 - i = 1 := by omega
  rw [hsub, List.drop_eq_getElem_cons (l := a.toList) (by simpa using h),
    List.take_succ_cons, List.take_zero, List.foldl_cons, List.foldl_nil]
  simp

/-- A step hands back the buffer it was given: the two cursors share the input rather than copying
it, so a read moves the position and leaves the data alone. Together with the advances the round-trip
rungs state (`takeBytes_advances`, `takeBe_advances`, and `takeU8`'s own record) this is what a
branch's fuel bound descends through. -/
theorem spec_takeU8_data {c d : SpecAMQP.Spec.Codec.Cursor} {b : UInt8}
    (h : SpecAMQP.Spec.Codec.takeU8 c = .ok (b, d)) : d.data = c.data := by
  have hpos : c.pos < c.data.size := by
    by_contra hlt
    unfold SpecAMQP.Spec.Codec.takeU8 at h
    rw [dif_neg hlt] at h
    exact absurd h (by simp)
  unfold SpecAMQP.Spec.Codec.takeU8 at h
  rw [dif_pos hpos] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, hd⟩ := h
  subst hd
  rfl

/-- The same for a payload read. -/
theorem spec_takeBytes_data {n : Nat} {c d : SpecAMQP.Spec.Codec.Cursor} {bytes : Array UInt8}
    (h : SpecAMQP.Spec.Codec.takeBytes n c = .ok (bytes, d)) : d.data = c.data := by
  unfold SpecAMQP.Spec.Codec.takeBytes at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hd⟩ := h
    subst hd
    rfl
  · exact absurd h (by simp)

/-- The same for a big-endian field: the foldl adds a value, not a buffer. -/
theorem spec_takeBe_data {w : Nat} {c d : SpecAMQP.Spec.Codec.Cursor} {m : Nat}
    (h : SpecAMQP.Spec.Codec.takeBe w c = .ok (m, d)) : d.data = c.data := by
  unfold SpecAMQP.Spec.Codec.takeBe at h
  obtain ⟨⟨bytes, d'⟩, hb, h⟩ := exists_of_bind_ok h
  dsimp only at h
  have hpair : (bytes.foldl (fun acc b => acc * 256 + b.toNat) 0, d') = (m, d) := Except.ok.inj h
  simp only [Prod.mk.injEq] at hpair
  obtain ⟨-, hd⟩ := hpair
  subst hd
  exact spec_takeBytes_data hb

/-! ## Taking the payload through two cursors that agree -/

/-- `n` octets, taken by two cursors that agree: the same payload comes off the same buffer and the
cursors advance together. This is `takeU8_agrees` one width up, and every payload read a branch
performs goes through it. -/
theorem takeBytes_agrees {c : SpecAMQP.Spec.Codec.Cursor} {c' : SpecAMQP.Ref.Cursor}
    (hc : CursorAgrees c c') (n : Nat) (bytes : Array UInt8) (d' : SpecAMQP.Ref.Cursor)
    (h : SpecAMQP.Ref.takeBytes n c' = .ok (bytes, d')) :
    ∃ d : SpecAMQP.Spec.Codec.Cursor,
      SpecAMQP.Spec.Codec.takeBytes n c = .ok (bytes, d) ∧ CursorAgrees d d' := by
  cases c with | mk data pos =>
  cases c' with | mk data' pos' =>
  obtain ⟨hd, hp⟩ := hc
  cases hd
  cases hp
  by_cases hle : pos + n ≤ data.size
  · have hle' : pos + n ≤ data.size := hle
    rw [SpecAMQP.Spec.Codec.takeBytes, if_pos hle]
    rw [SpecAMQP.Ref.takeBytes, if_pos hle'] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hb, hd'⟩ := h
    subst hb
    exact ⟨⟨data, pos + n⟩, rfl, by rw [← hd']; exact ⟨rfl, rfl⟩⟩
  · have hle' : ¬ (pos + n ≤ data.size) := hle
    rw [SpecAMQP.Ref.takeBytes, if_neg hle'] at h
    exact absurd h (by simp)

/-- The failure half of the same step: the same buffer runs out on both sides, with the same class. -/
theorem takeBytes_fails {c : SpecAMQP.Spec.Codec.Cursor} {c' : SpecAMQP.Ref.Cursor}
    (hc : CursorAgrees c c') (n : Nat) (failure : SpecAMQP.Ref.DecodeError)
    (h : SpecAMQP.Ref.takeBytes n c' = .error failure) :
    ∃ refusal : SpecAMQP.Spec.Codec.Refusal,
      SpecAMQP.Spec.Codec.takeBytes n c = .error refusal ∧
      (SpecAMQP.Ref.Frame.valueFailure failure).reasonClass = refusal.reasonClass := by
  cases c with | mk data pos =>
  cases c' with | mk data' pos' =>
  obtain ⟨hd, hp⟩ := hc
  cases hd
  cases hp
  by_cases hle : pos + n ≤ data.size
  · have hle' : pos + n ≤ data.size := hle
    rw [SpecAMQP.Ref.takeBytes, if_pos hle'] at h
    exact absurd h (by simp)
  · have hle' : ¬ (pos + n ≤ data.size) := hle
    rw [SpecAMQP.Ref.takeBytes, if_neg hle'] at h
    rw [SpecAMQP.Spec.Codec.takeBytes, if_neg hle]
    simp only [Except.error.injEq] at h
    subst h
    exact ⟨SpecAMQP.Spec.Codec.refusal "truncated"
      s!"{n} octet(s) needed at offset {pos} of {data.size}", rfl, rfl⟩

/-- A field the payload reader failed on is a field the foldl over that payload failed on, with the
same refusal: the foldl adds nothing to a read that did not happen. -/
theorem spec_takeBe_error (c : SpecAMQP.Spec.Codec.Cursor) (w : Nat)
    (refusal : SpecAMQP.Spec.Codec.Refusal) :
    SpecAMQP.Spec.Codec.takeBe w c = .error refusal ↔
      SpecAMQP.Spec.Codec.takeBytes w c = .error refusal := by
  constructor
  · intro h
    unfold SpecAMQP.Spec.Codec.takeBe at h
    cases hb : SpecAMQP.Spec.Codec.takeBytes w c with
    | error e =>
      rw [hb] at h
      rw [except_bind_error] at h
      simp only [Except.error.injEq] at h
      rw [h]
    | ok p => rw [hb] at h; rw [except_bind_ok] at h; exact absurd h (by simp)
  · intro h
    unfold SpecAMQP.Spec.Codec.takeBe
    rw [h, except_bind_error]

/-- A big-endian field of `w` octets, read by two cursors that agree. Both readers are the same foldl
over the same payload, so a branch that has taken the payload through `takeBytes_agrees` gets the
field's value on both sides at once. -/
theorem takeBe_agrees {c : SpecAMQP.Spec.Codec.Cursor} {c' : SpecAMQP.Ref.Cursor}
    (hc : CursorAgrees c c') (w : Nat) (m : Nat) (d' : SpecAMQP.Ref.Cursor)
    (h : SpecAMQP.Ref.takeBeU w c' = .ok (m, d')) :
    ∃ d : SpecAMQP.Spec.Codec.Cursor,
      SpecAMQP.Spec.Codec.takeBe w c = .ok (m, d) ∧ CursorAgrees d d' := by
  unfold SpecAMQP.Ref.takeBeU at h
  obtain ⟨⟨bytes, d₁'⟩, hb, h⟩ := exists_of_bind_ok h
  dsimp only at h
  have hpair : (bytes.foldl (fun acc byte => acc * 256 + byte.toNat) 0, d₁') = (m, d') :=
    Except.ok.inj h
  simp only [Prod.mk.injEq] at hpair
  obtain ⟨hm, hd₁⟩ := hpair
  subst hm
  subst hd₁
  obtain ⟨d₁, hsb, hd₁⟩ := takeBytes_agrees hc w bytes d₁' hb
  refine ⟨d₁, ?_, hd₁⟩
  unfold SpecAMQP.Spec.Codec.takeBe
  rw [hsb, except_bind_ok]
  dsimp only
  rfl

/-- The failure half of the big-endian field. -/
theorem takeBe_fails {c : SpecAMQP.Spec.Codec.Cursor} {c' : SpecAMQP.Ref.Cursor}
    (hc : CursorAgrees c c') (w : Nat) (failure : SpecAMQP.Ref.DecodeError)
    (h : SpecAMQP.Ref.takeBeU w c' = .error failure) :
    ∃ refusal : SpecAMQP.Spec.Codec.Refusal,
      SpecAMQP.Spec.Codec.takeBe w c = .error refusal ∧
      (SpecAMQP.Ref.Frame.valueFailure failure).reasonClass = refusal.reasonClass := by
  unfold SpecAMQP.Ref.takeBeU at h
  cases hb : SpecAMQP.Ref.takeBytes w c' with
  | error e =>
    rw [hb] at h
    rw [except_bind_error] at h
    simp only [Except.error.injEq] at h
    subst h
    obtain ⟨refusal, hspec, hcl⟩ := takeBytes_fails hc w e hb
    exact ⟨refusal, (spec_takeBe_error c w refusal).mpr hspec, hcl⟩
  | ok p =>
    rw [hb] at h
    rw [except_bind_ok] at h
    exact absurd h (by simp)

/-! ## The width-one bridge -/

/-- **The specification's one-octet payload read, in the octet step's own vocabulary.** A width-one
row reads one octet and accumulates it, so a branch that has the octet has the payload and the foldl
too. The payload is the `extract` that `takeBytes` returns rather than the octet itself, which is why
the bridge carries the foldl equation and not an array equality: what a value needs is the *number*,
and which array held it is the reader's own business. -/
theorem spec_takeBytes_one_of_takeU8 (d : SpecAMQP.Spec.Codec.Cursor) (b : UInt8)
    (d₂ : SpecAMQP.Spec.Codec.Cursor)
    (h : SpecAMQP.Spec.Codec.takeU8 d = .ok (b, d₂)) :
    SpecAMQP.Spec.Codec.takeBytes 1 d = .ok (d.data.extract d.pos (d.pos + 1), d₂) ∧
      (d.data.extract d.pos (d.pos + 1)).foldl (fun acc x => acc * 256 + x.toNat) 0 = b.toNat := by
  have hpos : d.pos < d.data.size := by
    by_contra hlt
    unfold SpecAMQP.Spec.Codec.takeU8 at h
    rw [dif_neg hlt] at h
    exact absurd h (by simp)
  have hb : b = d.data[d.pos]'hpos := by
    unfold SpecAMQP.Spec.Codec.takeU8 at h
    rw [dif_pos hpos] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact h.1.symm
  have hd₂ : d₂ = ⟨d.data, d.pos + 1⟩ := by
    unfold SpecAMQP.Spec.Codec.takeU8 at h
    rw [dif_pos hpos] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2.symm
  subst hb
  subst hd₂
  constructor
  · unfold SpecAMQP.Spec.Codec.takeBytes
    rw [if_pos (by omega : d.pos + 1 ≤ d.data.size)]
  · exact foldl_extract_one d.data d.pos hpos

/-- The width-one bridge in the form a branch wants: the field's value. -/
theorem spec_takeBe_one_of_takeU8 (d : SpecAMQP.Spec.Codec.Cursor) (b : UInt8)
    (d₂ : SpecAMQP.Spec.Codec.Cursor)
    (h : SpecAMQP.Spec.Codec.takeU8 d = .ok (b, d₂)) :
    SpecAMQP.Spec.Codec.takeBe 1 d = .ok (b.toNat, d₂) := by
  obtain ⟨hbytes, hfold⟩ := spec_takeBytes_one_of_takeU8 d b d₂ h
  unfold SpecAMQP.Spec.Codec.takeBe
  rw [hbytes, except_bind_ok]
  dsimp only
  rw [hfold]
  rfl

/-- A successful octet step's cursor is inside its buffer: the step took an octet from it. A
zero-width row reads *nothing* through `takeBytes 0`, and that read still needs the position to be
inside the buffer, so this is what a zero-width branch carries. -/
theorem spec_takeU8_lt {c : SpecAMQP.Spec.Codec.Cursor} {b : UInt8}
    {d : SpecAMQP.Spec.Codec.Cursor} (h : SpecAMQP.Spec.Codec.takeU8 c = .ok (b, d)) :
    c.pos < c.data.size := by
  by_contra hlt
  unfold SpecAMQP.Spec.Codec.takeU8 at h
  rw [dif_neg hlt] at h
  exact absurd h (by simp)

/-- An octet step leaves its cursor inside the buffer, which is what the zero-width rows' read of
nothing needs. -/
theorem spec_takeU8_next_le {c : SpecAMQP.Spec.Codec.Cursor} {b : UInt8}
    {d : SpecAMQP.Spec.Codec.Cursor} (h : SpecAMQP.Spec.Codec.takeU8 c = .ok (b, d)) :
    d.pos ≤ d.data.size := by
  have hlt : c.pos < c.data.size := spec_takeU8_lt h
  unfold SpecAMQP.Spec.Codec.takeU8 at h
  rw [dif_pos hlt] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, hd⟩ := h
  subst hd
  dsimp only
  omega
theorem spec_takeBytes_zero (c : SpecAMQP.Spec.Codec.Cursor) (h : c.pos ≤ c.data.size) :
    SpecAMQP.Spec.Codec.takeBytes 0 c = .ok (#[], ⟨c.data, c.pos + 0⟩) := by
  have hempty : c.data.extract c.pos (c.pos + 0) = #[] := by
    apply Array.eq_empty_of_size_eq_zero
    rw [Array.size_extract]
    omega
  unfold SpecAMQP.Spec.Codec.takeBytes
  rw [if_pos (by omega), hempty]

/-- A one-octet payload read fails exactly where the octet step fails, with the same class: the two
read the same octet, and each refuses it in its own words. -/
theorem spec_takeBytes_one_class {c : SpecAMQP.Spec.Codec.Cursor}
    (refusal : SpecAMQP.Spec.Codec.Refusal)
    (h : SpecAMQP.Spec.Codec.takeU8 c = .error refusal) :
    ∃ refusal' : SpecAMQP.Spec.Codec.Refusal,
      SpecAMQP.Spec.Codec.takeBytes 1 c = .error refusal' ∧
      refusal'.reasonClass = refusal.reasonClass := by
  by_cases hlt : c.pos < c.data.size
  · unfold SpecAMQP.Spec.Codec.takeU8 at h
    rw [dif_pos hlt] at h
    exact absurd h (by simp)
  · unfold SpecAMQP.Spec.Codec.takeU8 at h
    rw [dif_neg hlt] at h
    simp only [Except.error.injEq] at h
    subst h
    unfold SpecAMQP.Spec.Codec.takeBytes
    rw [if_neg (by omega)]
    exact ⟨_, rfl, rfl⟩

/-- The failure half of the width-one bridge: a payload read the reference fails, the specification
fails with the same class. -/
theorem spec_takeBytes_one_fails {c : SpecAMQP.Spec.Codec.Cursor} {c' : SpecAMQP.Ref.Cursor}
    (hc : CursorAgrees c c') (failure : SpecAMQP.Ref.DecodeError)
    (h : SpecAMQP.Ref.takeU8 c' = .error failure) :
    ∃ refusal : SpecAMQP.Spec.Codec.Refusal,
      SpecAMQP.Spec.Codec.takeBytes 1 c = .error refusal ∧
      (SpecAMQP.Ref.Frame.valueFailure failure).reasonClass = refusal.reasonClass := by
  obtain ⟨refusal, hspec, hcl⟩ := takeU8_fails hc failure h
  obtain ⟨refusal', hbytes, hcl'⟩ := spec_takeBytes_one_class refusal hspec
  exact ⟨refusal', hbytes, by rw [hcl, hcl']⟩

/-- **One value read's budget is the next read's.** A read leaves its cursor further on in the same
buffer, so the octets left at the cursor it hands back are no more than the octets left at the one it
was given — which is what lets a branch that reads twice at one fuel pass the bound along. The buffer
equality is the success conjunct's own, so this is stated against that component rather than against a
reader of its own. -/
theorem bound_of_read {fuel : Nat} {c d₂ : SpecAMQP.Spec.Codec.Cursor}
    {v : SpecAMQP.Spec.Codec.Value} (h : SpecAMQP.Spec.Codec.readValue fuel c = .ok (v, d₂))
    (hdata : d₂.data = c.data) (hb : c.data.size - c.pos ≤ fuel) :
    d₂.data.size - d₂.pos ≤ fuel := by
  have hpos := (readValue_progress fuel).1 c v d₂ h
  have hsize : d₂.data.size = c.data.size := by rw [hdata]
  omega

/-! ## The described branch (`0x00`), and the pattern the rest follow

A branch lemma is stated against the octet *step* rather than against the reader: what a dispatch
gives its arms is a pair of cursors that agree and one octet that both readers took, and what a
branch owes is `StepAgrees` one fuel up. The arm a reader selects is then its own, reduced by the
literal octet the statement names — which is why a branch lemma carries the octet in its hypotheses
and never in its statement, and why the branches below are written one octet at a time.

Three moves recur, and each cost an iteration to find. The specification's dispatch is on
`classify code.toNat` and its table lookups run `List.find?` over the generated surface, so a branch
resolves its own side with two `decide`-checked facts — the classification and the row — rather than
by `simp`: `decide` is ordinary evaluation over finite data, and the whole arm behind a lookup is a
`match` whose scrutinee only reduces once the row is named. The reference's dispatch is on the octet
itself and reduces by `rfl`. And every payload step is an `Except` bind, which the two lemmas in
`Proofs/ExceptMap` reduce and nothing else does. -/

/-- **The described branch (`0x00`).** The specification dispatches on the octet's *classification*
and the reference on the octet itself, and `classify 0 = descriptor` is exactly the octet `0x00`, so
the two readers run the same arm: a descriptor, then a value, then `.described`. Both reads are the
induction hypothesis one fuel down — the descriptor first, then the value at the cursor the first read
left — and the consumed octets agree because the hypothesis carries `CursorAgrees` through each of
them.

This is the branch the induction is shaped around: it is the only one that reads *two* values at one
fuel, which is why the success conjunct carries the buffer the reads share, and it is the pattern the
scalar branches follow with their reads replaced by a table lookup and the compound ones with theirs
replaced by a loop. -/
theorem arm_0x00 (fuel : Nat) (ih : WireAgrees fuel) (c : SpecAMQP.Spec.Codec.Cursor)
    (c' : SpecAMQP.Ref.Cursor) (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor)
    (hd : CursorAgrees d d') (hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x00, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x00, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hdata : d.data = c.data := spec_takeU8_data hs
  have hclass : SpecAMQP.Spec.Value.classify (0x00 : UInt8).toNat = .descriptor := by decide
  -- the arm each reader's own dispatch selects
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      (SpecAMQP.Spec.Codec.readValue fuel d) >>= (fun p =>
        (SpecAMQP.Spec.Codec.readValue fuel p.2) >>= (fun q =>
          .ok (.described p.1 q.1, q.2))) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      (SpecAMQP.Ref.readValue fuel d') >>= (fun p =>
        (SpecAMQP.Ref.readValue fuel p.2) >>= (fun q =>
          .ok (.described p.1 q.1, q.2))) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  constructor
  · intro other c₂' h
    rw [hR] at h
    obtain ⟨⟨desc, d₂'⟩, h1, h⟩ := exists_of_bind_ok h
    dsimp only at h
    obtain ⟨⟨val, d₃'⟩, h2, h⟩ := exists_of_bind_ok h
    dsimp only at h
    obtain ⟨hother, hcur⟩ : .described desc val = other ∧ d₃' = c₂' := by
      have hp := Except.ok.inj h
      simpa only [Prod.mk.injEq] using hp
    subst hother
    subst hcur
    obtain ⟨sdesc, d₂, hs1, hc1, hdat1, hb1⟩ := (ih d d' hd hb).1 desc d₂' h1
    obtain ⟨sval, d₃, hs2, hc2, hdat2, hb2⟩ :=
      (ih d₂ d₂' hc1 (bound_of_read hs1 hdat1 hb)).1 val d₃' h2
    refine ⟨.described sdesc sval, d₃, ?_, hc2, ?_, ?_⟩
    · rw [hS, hs1, except_bind_ok, hs2, except_bind_ok]
    · rw [hdat2, hdat1, hdata]
    · unfold BodiesAgree
      exact ⟨hb1, hb2⟩
  · intro failure h
    rw [hR] at h
    cases h1 : SpecAMQP.Ref.readValue fuel d' with
    | error e =>
      rw [h1] at h
      rw [except_bind_error] at h
      simp only [Except.error.injEq] at h
      subst h
      obtain ⟨refusal, hspec, hcl⟩ := (ih d d' hd hb).2 e h1
      refine ⟨refusal, ?_, hcl⟩
      rw [hS, hspec, except_bind_error]
    | ok p =>
      obtain ⟨desc, d₂'⟩ := p
      rw [h1] at h
      rw [except_bind_ok] at h
      cases h2 : SpecAMQP.Ref.readValue fuel d₂' with
      | error e =>
        rw [h2] at h
        rw [except_bind_error] at h
        simp only [Except.error.injEq] at h
        subst h
        obtain ⟨sdesc, d₂, hs1, hc1, hdat1, -⟩ := (ih d d' hd hb).1 desc d₂' h1
        obtain ⟨refusal, hspec, hcl⟩ :=
          (ih d₂ d₂' hc1 (bound_of_read hs1 hdat1 hb)).2 e h2
        refine ⟨refusal, ?_, hcl⟩
        rw [hS, hs1, except_bind_ok, hspec, except_bind_error]
      | ok q =>
        rw [h2] at h
        rw [except_bind_ok] at h
        exact absurd h (by simp)

/-- **A zero-width row (`0x40`, `null`).** The table's row for this octet names `null` at no width,
so the specification reads no payload and answers the value the table names, while the reference
matches the octet and answers the same value. Nothing recurses, which is why the scalar branches
carry no bound: only the two tables have to be resolved. -/
theorem arm_0x40 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x40, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x40, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x40 : UInt8).toNat = .fixed 0 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x40 : UInt8) =
      .ok ⟨64, none, SpecAMQP.Generated.Oasis.Category.fixed, 0, "null",
        "the null value"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c = .ok (.null, d) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    try dsimp only
    rw [spec_takeBytes_zero d (spec_takeU8_next_le hs), except_bind_ok]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' = .ok (.null, d') := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  constructor
  · intro other c₂' h
    rw [hR] at h
    obtain ⟨hother, hcur⟩ : .null = other ∧ d' = c₂' := by
      have hp := Except.ok.inj h
      simpa only [Prod.mk.injEq] using hp
    subst hother
    subst hcur
    exact ⟨.null, d, hS, hd, spec_takeU8_data hs, by simp only [BodiesAgree]⟩
  · intro failure h
    rw [hR] at h
    exact absurd h (by simp)

/-- **A width-one row with a payload (`0x50`, `ubyte`).** The reference takes one octet and answers
it; the specification's row reads one octet through `takeBytes`, accumulates it, and answers the
number. The bridge is the whole content: the payload and the foldl are the octet the reference took,
so the two values agree on the nose, and the cursor the reference's payload read left is the one the
specification's row left. -/
theorem arm_0x50 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x50, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x50, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hdata : d.data = c.data := spec_takeU8_data hs
  have hclass : SpecAMQP.Spec.Value.classify (0x50 : UInt8).toNat = .fixed 1 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x50 : UInt8) =
      .ok ⟨80, none, SpecAMQP.Generated.Oasis.Category.fixed, 1, "ubyte",
        "8-bit unsigned integer"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      (SpecAMQP.Spec.Codec.takeBytes 1 d) >>= (fun p =>
        .ok (.ubyte (p.1.foldl (fun acc x => acc * 256 + x.toNat) 0), p.2)) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      (SpecAMQP.Ref.takeU8 d') >>= (fun p => .ok (.ubyte p.1, p.2)) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  constructor
  · intro other c₂' h
    rw [hR] at h
    obtain ⟨⟨b, d₂'⟩, h1, h⟩ := exists_of_bind_ok h
    dsimp only at h
    obtain ⟨hother, hcur⟩ : .ubyte b = other ∧ d₂' = c₂' := by
      have hp := Except.ok.inj h
      simpa only [Prod.mk.injEq] using hp
    subst hother
    subst hcur
    obtain ⟨d₂, hsu8, hd₂⟩ := takeU8_agrees hd b d₂' h1
    obtain ⟨hbytes, hfold⟩ := spec_takeBytes_one_of_takeU8 d b d₂ hsu8
    refine ⟨.ubyte b.toNat, d₂, ?_, hd₂, ?_, ?_⟩
    · rw [hS, hbytes, except_bind_ok, hfold]
    · rw [spec_takeBytes_data hbytes, hdata]
    · simp only [BodiesAgree]
  · intro failure h
    rw [hR] at h
    cases h1 : SpecAMQP.Ref.takeU8 d' with
    | error e =>
      rw [h1] at h
      rw [except_bind_error] at h
      simp only [Except.error.injEq] at h
      subst h
      obtain ⟨refusal, hbytes, hcl⟩ := spec_takeBytes_one_fails hd e h1
      exact ⟨refusal, by rw [hS, hbytes, except_bind_error], hcl⟩
    | ok p =>
      rw [h1] at h
      rw [except_bind_ok] at h
      exact absurd h (by simp)
end SpecAMQP.Proofs
