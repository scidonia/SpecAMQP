import Contracts.Conformance
import Proofs.ValueCarrierAgreement
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
its truth needs), the base case, the octet step and its payload bridges, the branch *pattern*, and
**34 of the 40 arms** — the described branch and every row that reads no recursive value: the five
other zero-width rows, the one-octet payloads, the wide unsigned and `char` widths, the seven *signed*
widths, the six opaque widths, and the six variable rows. Still owed: the six compound and array rows,
with the three loop relations they share; the dispatch that turns the arms into the induction step;
and the fuel induction itself, whose entry point is free. What each owes and how it is
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
/-! ## The arm machinery: a step, a relation, and one stem per shape

Every arm still owed has the same skeleton — take the octet, read a payload, answer a value — and
differs from its neighbours only in the payload's shape and in the value. Twenty-four proofs of the
same two conjuncts would bury each arm's own content in boilerplate, so the skeleton is stated once
as a **step**: a reader whose value is an *intermediate* (an octet, a payload, a number) rather than
a body, with the relation between the two readers' intermediates made explicit. The relation is the
useful part: the two artefacts often read the same octets into different values — the
specification folds a payload into a number that the reference never forms bare — and a step
agreement is exactly the statement that lets one reader's octets be the other's number.

The instances below carry every fixed-width row. The relation each carries is the one its arm's
values need:

* `stepAgreesAll_takeBytes` — the opaque widths, where both readers hand the octets back and the
  relation is equality of arrays;
* `stepAgreesAll_takeBeNat` — the unsigned and `char` widths, where the specification folds the
  octets it read while the reference folds them inside `takeBeU`, so the relation is
  `payloadNat a = b`;
* `stepAgreesAll_takeU8Nat` — the one-octet payloads, the same relation at width one;
* `stepAgreesAll_takeBeEq`, `stepAgreesAll_takeBeOne` — the *variable* rows' length field, where both
  readers produce the same number (or the reference's octet is that number), because those rows read
  their length through `takeBe` rather than through the payload read a fixed row uses;
* `readersAgree_utf8` — the third reader of the two text families, where both readers decode the same
  octets with the same standard-library call and differ only in the refusal's prose. It is stated at
  the *reader* level rather than as a step, and that is not a matter of taste: a step agreement hands
  its intermediate back as one component of a pair, and re-pairing that component into the value the
  reader answers produces a term equal to the reader's own only through `>>=`'s associativity — not a
  definitional equality, and so not something a *hypothesis* can be checked against. The lesson is
  the same one the fuel bound taught: state the law at the shape the consumer has.

`readersAgreeAt_bind` is the composition the variable rows need — a length field, then the reader
below it — and the three stems turn a step plus a value into the `StepAgrees` an arm owes: `reader_of_ok` for the zero-width rows, `reader_of_step` for the payload rows, and
`reader_of_two_steps` for the variable ones. -/

/-- **The number the specification accumulates a payload's octets into.** Named because three of the
bridges below are stated in its terms and because it is the relation the number-carrying arms carry:
the reference's number and the specification's octets meet here. -/
def payloadNat (bytes : SpecAMQP.Harness.Octets) : Nat :=
  bytes.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- **Two readers' *steps* agree up to a relation on their values.** A step is a reader whose value is
an intermediate rather than a body; two steps agree when the reference's is a value the specification
also reaches, related to it by `R`, at a cursor the two agree on, with the same octets in hand. The
second conjunct is the refusal half, as in `StepAgrees`, and the buffer component is what an arm's
fuel bound descends through. -/
def StepAgreesAt {α β : Type} (R : α → β → Prop)
    (f : SpecAMQP.Spec.Codec.Cursor → Except SpecAMQP.Spec.Codec.Refusal
      (α × SpecAMQP.Spec.Codec.Cursor))
    (g : SpecAMQP.Ref.Cursor → Except SpecAMQP.Ref.DecodeError
      (β × SpecAMQP.Ref.Cursor))
    (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor) : Prop :=
  (∀ (b : β) (d' : SpecAMQP.Ref.Cursor), g c' = .ok (b, d') →
      ∃ (a : α) (d : SpecAMQP.Spec.Codec.Cursor), f c = .ok (a, d) ∧ R a b ∧
        CursorAgrees d d' ∧ d.data = c.data) ∧
  (∀ failure : SpecAMQP.Ref.DecodeError, g c' = .error failure →
      ∃ refusal : SpecAMQP.Spec.Codec.Refusal, f c = .error refusal ∧
        (SpecAMQP.Ref.Frame.valueFailure failure).reasonClass = refusal.reasonClass)

/-- The same obligation at every pair of agreeing cursors, which is the form a *nested* step needs:
an inner step starts from the cursors its outer step handed back, and those are known to agree only
from the outer step's own success. -/
def StepAgreesAll {α β : Type} (R : α → β → Prop)
    (f : SpecAMQP.Spec.Codec.Cursor → Except SpecAMQP.Spec.Codec.Refusal
      (α × SpecAMQP.Spec.Codec.Cursor))
    (g : SpecAMQP.Ref.Cursor → Except SpecAMQP.Ref.DecodeError
      (β × SpecAMQP.Ref.Cursor)) : Prop :=
  ∀ (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor),
    CursorAgrees c c' → StepAgreesAt R f g c c'

/-- **A payload read took at most what it asked for.** `takeBytes` answers an `extract`, and an
extract is as long as the request or shorter; this is the first half of the bound a width-carrying
arm's value equation needs. -/
theorem spec_takeBytes_size_le {n : Nat} {c d : SpecAMQP.Spec.Codec.Cursor}
    {bytes : SpecAMQP.Harness.Octets}
    (h : SpecAMQP.Spec.Codec.takeBytes n c = .ok (bytes, d)) : bytes.size ≤ n := by
  unfold SpecAMQP.Spec.Codec.takeBytes at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hb, -⟩ := h
    subst hb
    rw [Array.size_extract]
    omega
  · exact absurd h (by simp)

/-- **A fold over a payload is bounded by the payload's own width.** The array form of
`CodecRoundTripNarrowest`'s `foldl_be_bound` at an empty accumulator: `w` octets accumulate to a
number below `256 ^ w`, which is the reader's own account of what a width-`w` field can carry. -/
theorem payloadNat_lt (bytes : SpecAMQP.Harness.Octets) :
    payloadNat bytes < 256 ^ bytes.size := by
  rw [payloadNat, ← Array.foldl_toList]
  simpa using foldl_be_bound bytes.toList 0

/-- The two facts a width-`w` payload's value equation needs, together: the payload is no longer than
the width asked for, and the fold over it is below `256` to its own length. -/
theorem payloadNat_lt_of_takeBytes {w : Nat} {c d : SpecAMQP.Spec.Codec.Cursor}
    {bytes : SpecAMQP.Harness.Octets}
    (h : SpecAMQP.Spec.Codec.takeBytes w c = .ok (bytes, d)) : payloadNat bytes < 256 ^ w :=
  calc payloadNat bytes < 256 ^ bytes.size := payloadNat_lt bytes
    _ ≤ 256 ^ w := Nat.pow_le_pow_right (by decide) (spec_takeBytes_size_le h)

/-- A successful payload read is a successful big-endian field read at the same cursor, answering the
number the fold gives. This is what puts a variable row's length step (which reads through `takeBe`)
and a fixed row's payload step (which reads through `takeBytes`) on one footing. -/
theorem spec_takeBe_of_takeBytes {w : Nat} {c d : SpecAMQP.Spec.Codec.Cursor}
    {bytes : SpecAMQP.Harness.Octets}
    (h : SpecAMQP.Spec.Codec.takeBytes w c = .ok (bytes, d)) :
    SpecAMQP.Spec.Codec.takeBe w c = .ok (payloadNat bytes, d) := by
  unfold SpecAMQP.Spec.Codec.takeBe
  rw [h, except_bind_ok]
  rfl

/-- **The payload step, octet for octet.** Both readers take the same `n` octets off the same buffer at
the same position; the relation is equality of the arrays, which is what the opaque rows' values wait
for. -/
theorem stepAgreesAll_takeBytes (n : Nat) :
    StepAgreesAll (fun a b : SpecAMQP.Harness.Octets => a = b)
      (SpecAMQP.Spec.Codec.takeBytes n) (SpecAMQP.Ref.takeBytes n) := by
  intro c c' hc
  constructor
  · intro b d' h
    obtain ⟨d, hspec, hcd⟩ := takeBytes_agrees hc n b d' h
    exact ⟨b, d, hspec, rfl, hcd, spec_takeBytes_data hspec⟩
  · intro failure h
    exact takeBytes_fails hc n failure h

/-- **The big-endian field step.** The reference folds the octets inside `takeBeU` and hands back a
number; the specification's fixed-width rows fold the same octets outside it, so the two steps are
related by `payloadNat a = b` rather than by an equality of arrays. -/
theorem stepAgreesAll_takeBeNat (w : Nat) :
    StepAgreesAll (fun (a : SpecAMQP.Harness.Octets) (b : Nat) => payloadNat a = b)
      (SpecAMQP.Spec.Codec.takeBytes w) (SpecAMQP.Ref.takeBeU w) := by
  intro c c' hc
  constructor
  · intro b d' h
    unfold SpecAMQP.Ref.takeBeU at h
    obtain ⟨⟨bytes, d₁'⟩, hb, h⟩ := exists_of_bind_ok h
    dsimp only at h
    rw [except_pure_ok] at h
    have hp : (payloadNat bytes, d₁') = (b, d') := Except.ok.inj h
    simp only [Prod.mk.injEq] at hp
    obtain ⟨hm, hd⟩ := hp
    subst hm
    subst hd
    obtain ⟨d, hspec, hcd⟩ := takeBytes_agrees hc w bytes d₁' hb
    exact ⟨bytes, d, hspec, rfl, hcd, spec_takeBytes_data hspec⟩
  · intro failure h
    unfold SpecAMQP.Ref.takeBeU at h
    cases hb : SpecAMQP.Ref.takeBytes w c' with
    | error e =>
      rw [hb] at h
      rw [except_bind_error] at h
      simp only [Except.error.injEq] at h
      subst h
      exact takeBytes_fails hc w e hb
    | ok p =>
      rw [hb] at h
      rw [except_bind_ok] at h
      exact absurd h (by simp)

/-- **The one-octet payload step.** The same relation at width one: the reference's `takeU8` hands back
the octet, and the landed width-one bridge says the octet it took is the fold the specification's
`takeBytes 1` performs. -/
theorem stepAgreesAll_takeU8Nat :
    StepAgreesAll (fun (a : SpecAMQP.Harness.Octets) (b : UInt8) => payloadNat a = b.toNat)
      (SpecAMQP.Spec.Codec.takeBytes 1) (SpecAMQP.Ref.takeU8) := by
  intro c c' hc
  constructor
  · intro b d' h
    obtain ⟨d₂, hsu8, hcd⟩ := takeU8_agrees hc b d' h
    obtain ⟨hbytes, hfold⟩ := spec_takeBytes_one_of_takeU8 c b d₂ hsu8
    exact ⟨c.data.extract c.pos (c.pos + 1), d₂, hbytes, by simpa only [payloadNat] using hfold,
      hcd, spec_takeBytes_data hbytes⟩
  · intro failure h
    exact spec_takeBytes_one_fails hc failure h

/-- **The variable rows' length step, four octets wide.** Both readers produce the same number, so the
relation is equality — the difference between the two `takeBe`s is only which of them folds. -/
theorem stepAgreesAll_takeBeEq (w : Nat) :
    StepAgreesAll (fun a b : Nat => a = b) (SpecAMQP.Spec.Codec.takeBe w)
      (SpecAMQP.Ref.takeBeU w) := by
  intro c c' hc
  constructor
  · intro b d' h
    unfold SpecAMQP.Ref.takeBeU at h
    obtain ⟨⟨bytes, d₁'⟩, hb, h⟩ := exists_of_bind_ok h
    dsimp only at h
    rw [except_pure_ok] at h
    have hp : (payloadNat bytes, d₁') = (b, d') := Except.ok.inj h
    simp only [Prod.mk.injEq] at hp
    obtain ⟨hm, hd⟩ := hp
    subst hm
    subst hd
    obtain ⟨d, hspec, hcd⟩ := takeBytes_agrees hc w bytes d₁' hb
    have hbe := spec_takeBe_of_takeBytes hspec
    exact ⟨payloadNat bytes, d, hbe, rfl, hcd, spec_takeBe_data hbe⟩
  · intro failure h
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

/-- **The variable rows' length step, one octet wide.** Here the reference's octet reader is `takeU8`
while the specification's length field is `takeBe 1`, and the landed width-one bridge relates them:
the number the field carries is the octet's own value. -/
theorem stepAgreesAll_takeBeOne :
    StepAgreesAll (fun (a : Nat) (b : UInt8) => a = b.toNat) (SpecAMQP.Spec.Codec.takeBe 1)
      (SpecAMQP.Ref.takeU8) := by
  intro c c' hc
  constructor
  · intro b d' h
    obtain ⟨d₂, hsu8, hcd⟩ := takeU8_agrees hc b d' h
    have hbe := spec_takeBe_one_of_takeU8 c b d₂ hsu8
    exact ⟨b.toNat, d₂, hbe, rfl, hcd, spec_takeBe_data hbe⟩
  · intro failure h
    obtain ⟨refusal, hspec, hcl⟩ := takeU8_fails hc failure h
    obtain ⟨refusal', hbytes, hcl'⟩ := spec_takeBytes_one_class refusal hspec
    exact ⟨refusal', (spec_takeBe_error c 1 refusal').mpr hbytes, by rw [hcl, hcl']⟩

/-- **A payload the reference decodes is one the specification decodes**, to the same text: both
readers ask the same standard-library question of the same octets, so the success half of the bridge
is an identity. This is the wire-side counterpart of the corpus side's `fixedHex_ok_hexPayloadOf`. -/
theorem utf8Of_ok_of_decodeString {bytes : SpecAMQP.Ref.Octets} {kind : String} {text : String}
    (h : SpecAMQP.Ref.decodeString bytes kind = .ok text) :
    SpecAMQP.Spec.Codec.utf8Of bytes kind = .ok text := by
  unfold SpecAMQP.Ref.decodeString at h
  unfold SpecAMQP.Spec.Codec.utf8Of
  cases hu : String.fromUTF8? (ByteArray.mk bytes) with
  | none => simp only [hu] at h; exact absurd h (by simp)
  | some s => simp only [hu] at h ⊢; injection h with hb; subst hb; rfl

/-- The failure half: the same question refused by both, with the same class — the two readers differ
only in the prose of the refusal, which is why this is a class agreement rather than an equality. -/
theorem utf8Of_error_of_decodeString {bytes : SpecAMQP.Ref.Octets} {kind : String}
    {failure : SpecAMQP.Ref.DecodeError}
    (h : SpecAMQP.Ref.decodeString bytes kind = .error failure) :
    ∃ refusal : SpecAMQP.Spec.Codec.Refusal,
      SpecAMQP.Spec.Codec.utf8Of bytes kind = .error refusal ∧
      (SpecAMQP.Ref.Frame.valueFailure failure).reasonClass = refusal.reasonClass := by
  unfold SpecAMQP.Ref.decodeString at h
  cases hu : String.fromUTF8? (ByteArray.mk bytes) with
  | none =>
    simp only [hu] at h
    injection h with hb
    subst hb
    refine ⟨SpecAMQP.Spec.Codec.refusal "malformed"
      s!"a {kind} payload of {bytes.size} octet(s) is not valid UTF-8", ?_, rfl⟩
    unfold SpecAMQP.Spec.Codec.utf8Of
    simp only [hu]
  | some s => simp only [hu] at h; exact absurd h (by simp)

/-- **Two readers agree at one cursor pair.** The two conjuncts of `StepAgrees`, for readers whose
fuel is already spent — which is what a step's *continuation* is, and what the composition below
produces. The value relation is `BodiesAgree`, as in `StepAgrees`, and the buffer component says a
reader hands back the buffer it was given. -/
def ReadersAgreeAt
    (Ks : SpecAMQP.Spec.Codec.Cursor → Except SpecAMQP.Spec.Codec.Refusal
      (SpecAMQP.Spec.Codec.Value × SpecAMQP.Spec.Codec.Cursor))
    (Kr : SpecAMQP.Ref.Cursor → Except SpecAMQP.Ref.DecodeError
      (SpecAMQP.Ref.Value × SpecAMQP.Ref.Cursor))
    (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor) : Prop :=
  (∀ (other : SpecAMQP.Ref.Value) (c₂' : SpecAMQP.Ref.Cursor), Kr c' = .ok (other, c₂') →
      ∃ (body : SpecAMQP.Spec.Codec.Value) (c₂ : SpecAMQP.Spec.Codec.Cursor),
        Ks c = .ok (body, c₂) ∧ CursorAgrees c₂ c₂' ∧ c₂.data = c.data ∧ BodiesAgree body other) ∧
  (∀ failure : SpecAMQP.Ref.DecodeError, Kr c' = .error failure →
      ∃ refusal : SpecAMQP.Spec.Codec.Refusal, Ks c = .error refusal ∧
        (SpecAMQP.Ref.Frame.valueFailure failure).reasonClass = refusal.reasonClass)

/-- The same obligation at every pair of agreeing cursors. -/
def ReadersAgree
    (Ks : SpecAMQP.Spec.Codec.Cursor → Except SpecAMQP.Spec.Codec.Refusal
      (SpecAMQP.Spec.Codec.Value × SpecAMQP.Spec.Codec.Cursor))
    (Kr : SpecAMQP.Ref.Cursor → Except SpecAMQP.Ref.DecodeError
      (SpecAMQP.Ref.Value × SpecAMQP.Ref.Cursor)) : Prop :=
  ∀ (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor),
    CursorAgrees c c' → ReadersAgreeAt Ks Kr c c'

/-- **The two text families' decode, at one payload.** The same octets, the same standard-library
test, the same string on success and the same class on refusal — stated as the *reader* each artefact
writes (`utf8Of` then a value, the reference's `decodeStringAt` two-step), because the value the two
readers answer is the text rather than the octets they took. `Sv`/`Rv` are the two artefacts'
spellings of the value that text makes, which is what lets `string` and `symbol` share this lemma.
The payload is an explicit argument because this reader is *indexed* by what the reader above it
took, and the same array on both sides is what that reader's own agreement already gave. -/
theorem readersAgree_utf8 (kind : String) (bytes : SpecAMQP.Harness.Octets)
    (Sv : String → SpecAMQP.Spec.Codec.Value) (Rv : String → SpecAMQP.Ref.Value)
    (hval : ∀ text : String, BodiesAgree (Sv text) (Rv text)) :
    ReadersAgree
      (fun f : SpecAMQP.Spec.Codec.Cursor =>
        SpecAMQP.Spec.Codec.utf8Of bytes kind >>= fun s => .ok (Sv s, f))
      (fun f' : SpecAMQP.Ref.Cursor =>
        SpecAMQP.Ref.decodeStringAt bytes kind f' >>= fun r => .ok (Rv r.1, r.2)) := by
  intro c c' hc
  constructor
  · intro other c₂' h
    dsimp only at h
    cases hd : SpecAMQP.Ref.decodeString bytes kind with
    | error e =>
      have hda : SpecAMQP.Ref.decodeStringAt bytes kind c' = .error e := by
        unfold SpecAMQP.Ref.decodeStringAt
        rw [hd]
      rw [hda] at h
      rw [except_bind_error] at h
      exact absurd h (by simp)
    | ok text =>
      have hda : SpecAMQP.Ref.decodeStringAt bytes kind c' = .ok (text, c') := by
        unfold SpecAMQP.Ref.decodeStringAt
        rw [hd]
      rw [hda] at h
      rw [except_bind_ok] at h
      dsimp only at h
      obtain ⟨hother, hcur⟩ : Rv text = other ∧ c' = c₂' := by
        have hp := Except.ok.inj h
        simpa only [Prod.mk.injEq] using hp
      subst hother
      subst hcur
      refine ⟨Sv text, c, ?_, hc, rfl, hval text⟩
      dsimp only
      rw [utf8Of_ok_of_decodeString hd, except_bind_ok]
  · intro failure h
    dsimp only at h
    cases hd : SpecAMQP.Ref.decodeString bytes kind with
    | ok text =>
      have hda : SpecAMQP.Ref.decodeStringAt bytes kind c' = .ok (text, c') := by
        unfold SpecAMQP.Ref.decodeStringAt
        rw [hd]
      rw [hda] at h
      rw [except_bind_ok] at h
      exact absurd h (by simp)
    | error e =>
      have hda : SpecAMQP.Ref.decodeStringAt bytes kind c' = .error e := by
        unfold SpecAMQP.Ref.decodeStringAt
        rw [hd]
      rw [hda] at h
      rw [except_bind_error] at h
      rw [Except.error.injEq] at h
      subst h
      obtain ⟨r, hspec, hcl⟩ := utf8Of_error_of_decodeString hd
      refine ⟨r, ?_, hcl⟩
      dsimp only
      rw [hspec, except_bind_error]
/-- **A row that reads nothing but its octet.** The two readers answer a value and hand their cursors
back; the value relation and the cursor agreement are the whole content, and the refusal half is
vacuous because neither reader refuses. -/
theorem reader_of_ok (fuel : Nat) {c : SpecAMQP.Spec.Codec.Cursor} {c' : SpecAMQP.Ref.Cursor}
    {d : SpecAMQP.Spec.Codec.Cursor} {d' : SpecAMQP.Ref.Cursor} (hd : CursorAgrees d d')
    (Sv : SpecAMQP.Spec.Codec.Value) (Rv : SpecAMQP.Ref.Value) (hval : BodiesAgree Sv Rv)
    (hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c = .ok (Sv, d))
    (hR : SpecAMQP.Ref.readValue (fuel + 1) c' = .ok (Rv, d'))
    (hdata : d.data = c.data) : StepAgrees (fuel + 1) c c' := by
  constructor
  · intro other c₂' h
    rw [hR] at h
    obtain ⟨hother, hcur⟩ : Rv = other ∧ d' = c₂' := by
      have hp := Except.ok.inj h
      simpa only [Prod.mk.injEq] using hp
    subst hother
    subst hcur
    exact ⟨Sv, d, hS, hd, hdata, hval⟩
  · intro failure h
    rw [hR] at h
    exact absurd h (by simp)

/-- **A row that reads one payload.** The step hands the reference a value the specification reaches
too — related to it by `R` — and the arm answers a value from each; `hval` is the arm's own content,
and it is stated against the specification's *step success* because that is where a width-carrying
arm's bound on the number it read comes from: `R` alone cannot bound `payloadNat` of the payload a
reader happened to accept, but the read that accepted it can. -/
theorem reader_of_step {α β : Type} {R : α → β → Prop}
    {StepS : SpecAMQP.Spec.Codec.Cursor → Except SpecAMQP.Spec.Codec.Refusal
      (α × SpecAMQP.Spec.Codec.Cursor)}
    {StepR : SpecAMQP.Ref.Cursor → Except SpecAMQP.Ref.DecodeError (β × SpecAMQP.Ref.Cursor)}
    {fuel : Nat} {c : SpecAMQP.Spec.Codec.Cursor} {c' : SpecAMQP.Ref.Cursor}
    {d : SpecAMQP.Spec.Codec.Cursor} {d' : SpecAMQP.Ref.Cursor}
    (hstep : StepAgreesAt R StepS StepR d d')
    (Sv : α → SpecAMQP.Spec.Codec.Value) (Rv : β → SpecAMQP.Ref.Value)
    (hval : ∀ (a : α) (b : β), R a b → ∀ f : SpecAMQP.Spec.Codec.Cursor,
      StepS d = .ok (a, f) → BodiesAgree (Sv a) (Rv b))
    (hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c = StepS d >>= fun p => .ok (Sv p.1, p.2))
    (hR : SpecAMQP.Ref.readValue (fuel + 1) c' = StepR d' >>= fun p => .ok (Rv p.1, p.2))
    (hdata : d.data = c.data) : StepAgrees (fuel + 1) c c' := by
  constructor
  · intro other c₂' h
    rw [hR] at h
    obtain ⟨⟨b, d₂'⟩, hb, h⟩ := exists_of_bind_ok h
    dsimp only at h
    obtain ⟨hother, hcur⟩ : Rv b = other ∧ d₂' = c₂' := by
      have hp := Except.ok.inj h
      simpa only [Prod.mk.injEq] using hp
    subst hother
    subst hcur
    obtain ⟨a, f₂, hf, hrel, hcd, hdat⟩ := hstep.1 b d₂' hb
    exact ⟨Sv a, f₂, by rw [hS, hf, except_bind_ok], hcd, by rw [hdat, hdata],
      hval a b hrel f₂ hf⟩
  · intro failure h
    rw [hR] at h
    cases hb : StepR d' with
    | error e =>
      rw [hb] at h
      rw [except_bind_error] at h
      simp only [Except.error.injEq] at h
      subst h
      obtain ⟨refusal, hspec, hcl⟩ := hstep.2 e hb
      exact ⟨refusal, by rw [hS, hspec, except_bind_error], hcl⟩
    | ok p =>
      rw [hb] at h
      rw [except_bind_ok] at h
      exact absurd h (by simp)

/-- **A step composed with a reader below it.** The step's success hands back a value and two agreeing
cursors, and the reader below is applied there; this is the same reduction as `stepAgreesAll_bind`,
one level down, and it is what a variable row's length-then-payload read is. -/
theorem readersAgreeAt_bind {α β : Type} {R : α → β → Prop}
    {StepS : SpecAMQP.Spec.Codec.Cursor → Except SpecAMQP.Spec.Codec.Refusal
      (α × SpecAMQP.Spec.Codec.Cursor)}
    {StepR : SpecAMQP.Ref.Cursor → Except SpecAMQP.Ref.DecodeError (β × SpecAMQP.Ref.Cursor)}
    {d : SpecAMQP.Spec.Codec.Cursor} {d' : SpecAMQP.Ref.Cursor}
    (hstep : StepAgreesAt R StepS StepR d d')
    {Ks : α → SpecAMQP.Spec.Codec.Cursor → Except SpecAMQP.Spec.Codec.Refusal
      (SpecAMQP.Spec.Codec.Value × SpecAMQP.Spec.Codec.Cursor)}
    {Kr : β → SpecAMQP.Ref.Cursor → Except SpecAMQP.Ref.DecodeError
      (SpecAMQP.Ref.Value × SpecAMQP.Ref.Cursor)}
    (hinner : ∀ (a : α) (b : β), R a b → ReadersAgree (Ks a) (Kr b)) :
    ReadersAgreeAt (fun c => StepS c >>= fun p => Ks p.1 p.2)
      (fun c' => StepR c' >>= fun p => Kr p.1 p.2) d d' := by
  constructor
  · intro other c₂' h
    dsimp only at h ⊢
    obtain ⟨⟨b, d₁'⟩, hb, h⟩ := exists_of_bind_ok h
    dsimp only at h
    obtain ⟨a, d₁, hspec, hrel, hcd, hdat⟩ := hstep.1 b d₁' hb
    obtain ⟨body, d₂, hk, hcd2, hdat2, hba⟩ := (hinner a b hrel d₁ d₁' hcd).1 other c₂' h
    exact ⟨body, d₂, by rw [hspec, except_bind_ok, hk], hcd2, by rw [hdat2, hdat], hba⟩
  · intro failure h
    dsimp only at h ⊢
    cases hb : StepR d' with
    | error e =>
      rw [hb] at h
      rw [except_bind_error] at h
      simp only [Except.error.injEq] at h
      subst h
      obtain ⟨refusal, hspec, hcl⟩ := hstep.2 e hb
      exact ⟨refusal, by rw [hspec, except_bind_error], hcl⟩
    | ok p =>
      obtain ⟨b, d₁'⟩ := p
      rw [hb] at h
      rw [except_bind_ok] at h
      obtain ⟨a, d₁, hspec, hrel, hcd, -⟩ := hstep.1 b d₁' hb
      cases hb2 : Kr b d₁' with
      | error e =>
        rw [hb2] at h
        rw [Except.error.injEq] at h
        subst h
        obtain ⟨refusal, hspec2, hcl⟩ := (hinner a b hrel d₁ d₁' hcd).2 e hb2
        exact ⟨refusal, by rw [hspec, except_bind_ok, hspec2], hcl⟩
      | ok q =>
        rw [hb2] at h
        exact absurd h (by simp)

/-- The same, at every pair of agreeing cursors: the form an inner reader is *used* in. -/
theorem readersAgree_bind {α β : Type} {R : α → β → Prop}
    {StepS : SpecAMQP.Spec.Codec.Cursor → Except SpecAMQP.Spec.Codec.Refusal
      (α × SpecAMQP.Spec.Codec.Cursor)}
    {StepR : SpecAMQP.Ref.Cursor → Except SpecAMQP.Ref.DecodeError (β × SpecAMQP.Ref.Cursor)}
    (hstep : StepAgreesAll R StepS StepR)
    {Ks : α → SpecAMQP.Spec.Codec.Cursor → Except SpecAMQP.Spec.Codec.Refusal
      (SpecAMQP.Spec.Codec.Value × SpecAMQP.Spec.Codec.Cursor)}
    {Kr : β → SpecAMQP.Ref.Cursor → Except SpecAMQP.Ref.DecodeError
      (SpecAMQP.Ref.Value × SpecAMQP.Ref.Cursor)}
    (hinner : ∀ (a : α) (b : β), R a b → ReadersAgree (Ks a) (Kr b)) :
    ReadersAgree (fun c => StepS c >>= fun p => Ks p.1 p.2)
      (fun c' => StepR c' >>= fun p => Kr p.1 p.2) :=
  fun c c' hc => readersAgreeAt_bind (hstep c c' hc) hinner

/-- **A reader that answers a value and hands its cursor back.** The last step of every arm's chain:
the two readers have their payload and their value, nothing is consumed, and the agreement is the
value relation alone. -/
theorem readersAgree_ok (Sv : SpecAMQP.Spec.Codec.Value) (Rv : SpecAMQP.Ref.Value)
    (hval : BodiesAgree Sv Rv) :
    ReadersAgree (fun c => .ok (Sv, c)) (fun c' => .ok (Rv, c')) := by
  intro c c' hc
  constructor
  · intro other c₂' h
    obtain ⟨hother, hcur⟩ : Rv = other ∧ c' = c₂' := by
      have hp := Except.ok.inj h
      simpa only [Prod.mk.injEq] using hp
    subst hother
    subst hcur
    exact ⟨Sv, c, rfl, hc, rfl, hval⟩
  · intro failure h
    exact absurd h (by simp)

/-- **A variable row: a length field, then the payload that field announced.** The outer step's value
decides the inner reader's, and the inner reader's agreement holds at whatever cursors the outer step
left — which is why it is `ReadersAgree` rather than an obligation at `d`/`d'`. The rows that use this
stem are the six whose read is two steps deep: the payload step is the *whole* rest of the reader,
including the value it answers, so the composite is a reader rather than a step. -/
theorem reader_of_two_steps {α β : Type} {R : α → β → Prop}
    {Step1S : SpecAMQP.Spec.Codec.Cursor → Except SpecAMQP.Spec.Codec.Refusal
      (α × SpecAMQP.Spec.Codec.Cursor)}
    {Step1R : SpecAMQP.Ref.Cursor → Except SpecAMQP.Ref.DecodeError (β × SpecAMQP.Ref.Cursor)}
    {fuel : Nat} {c : SpecAMQP.Spec.Codec.Cursor} {c' : SpecAMQP.Ref.Cursor}
    {d : SpecAMQP.Spec.Codec.Cursor} {d' : SpecAMQP.Ref.Cursor}
    (Step2S : α → SpecAMQP.Spec.Codec.Cursor → Except SpecAMQP.Spec.Codec.Refusal
      (SpecAMQP.Spec.Codec.Value × SpecAMQP.Spec.Codec.Cursor))
    (Step2R : β → SpecAMQP.Ref.Cursor → Except SpecAMQP.Ref.DecodeError
      (SpecAMQP.Ref.Value × SpecAMQP.Ref.Cursor))
    (h1 : StepAgreesAt R Step1S Step1R d d')
    (hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c = Step1S d >>= fun p => Step2S p.1 p.2)
    (hR : SpecAMQP.Ref.readValue (fuel + 1) c' = Step1R d' >>= fun p => Step2R p.1 p.2)
    (h2 : ∀ (a : α) (b : β), R a b → ReadersAgree (Step2S a) (Step2R b))
    (hdata : d.data = c.data) : StepAgrees (fuel + 1) c c' := by
  obtain ⟨hok, herr⟩ := readersAgreeAt_bind h1 h2
  constructor
  · intro other c₂' h
    rw [hR] at h
    obtain ⟨body, c₂, hr, hcd, hdat, hba⟩ := hok other c₂' h
    refine ⟨body, c₂, ?_, hcd, ?_, hba⟩
    · rw [hS]
      exact hr
    · rw [hdat, hdata]
  · intro failure h
    rw [hR] at h
    obtain ⟨refusal, hr, hcl⟩ := herr failure h
    exact ⟨refusal, by rw [hS]; exact hr, hcl⟩

/-! ## The fixed-width arms

Everything below is one row of the declared surface per theorem, and every one of them is the octet
step's hypothesis plus three `decide`-checked facts and an instance of a stem. What each row owes
that its neighbours do not is stated in its own docstring; the groups, and why each is the size it is:

* the zero-width rows (`0x41`–`0x45`) read no payload at all — the table names the value, and the
  reference matches the octet — so they go through `reader_of_ok` and owe only their row;
* the one-octet payloads (`0x52`, `0x53`, `0x56`) read their octet through the specification's
  `takeBytes 1` and the reference's `takeU8`, which is `stepAgreesAll_takeU8Nat`: the relation is
  `payloadNat` against the octet's own value, and the value equations are the width-carrying round
  trips `Proofs/ValueCarrierAgreement` states for the corpus side (`u8_toNat` and its siblings);
* the wide unsigned and `char` rows (`0x60`, `0x70`, `0x73`, `0x80`) read a big-endian field, so
  their relation is `payloadNat a = b` and their value equations need the number's *bound*, which is
  why `reader_of_step`'s value hypothesis is stated against the specification's own step success:
  `payloadNat_lt_of_takeBytes` reads the bound off the read;
* the opaque rows (`0x72`, `0x74`, `0x82`, `0x84`, `0x94`, `0x98`) carry their payload octets and
  compare nothing, so their relation is equality of arrays and their value equations are `rfl`.

What is deliberately *not* here: the seven signed rows, whose value equations need a
`SpecAMQP.Spec.Codec.signedOfOctets` round trip, and the compound and array rows, which need the loop relations. Both are
named in the module's header and in the plan rather than left to look finished. -/

/-- **The octet an 8-bit boolean carries is zero exactly when the octet is `0x00`.** The reference
compares the octet, the specification compares the number it folded the octet into, so this is the
`0x56` row's whole value equation. Stated through `UInt8.toNat_inj` rather than by case analysis on
the carrier, because the two `!=`s are `Bool`s and the bridge between them is the proposition. -/
theorem uint8_ne_zero_bool (b : UInt8) : (b.toNat != 0) = (b != 0x00) := by
  have key : b.toNat = 0 ↔ b = 0 := by
    rw [← show (0 : UInt8).toNat = 0 from rfl]
    exact UInt8.toNat_inj
  rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne, ne_eq, ne_eq]
  exact not_congr key

/-- **The `true` row (`0x41`).** The table names the boolean and declares no payload, so the
specification reads its zero octets and answers `true`; the reference matches the octet. -/
theorem arm_0x41 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x41, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x41, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x41 : UInt8).toNat = .fixed 0 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x41 : UInt8) =
      .ok ⟨65, some "true", SpecAMQP.Generated.Oasis.Category.fixed, 0, "boolean",
        "the boolean value true"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c = .ok (.boolean true, d) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rw [spec_takeBytes_zero d (spec_takeU8_next_le hs), except_bind_ok]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' = .ok (.boolean true, d') := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_ok fuel hd _ _ (by simp only [BodiesAgree]) hS hR (spec_takeU8_data hs)

/-- **The `false` row (`0x42`).** The same row at the other boolean. -/
theorem arm_0x42 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x42, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x42, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x42 : UInt8).toNat = .fixed 0 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x42 : UInt8) =
      .ok ⟨66, some "false", SpecAMQP.Generated.Oasis.Category.fixed, 0, "boolean",
        "the boolean value false"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c = .ok (.boolean false, d) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rw [spec_takeBytes_zero d (spec_takeU8_next_le hs), except_bind_ok]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' = .ok (.boolean false, d') := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_ok fuel hd _ _ (by simp only [BodiesAgree]) hS hR (spec_takeU8_data hs)

/-- **The `uint0` row (`0x43`).** The specification's fixed-width reader folds the zero octets it
took into the number zero and answers `uint 0`; the reference matches the octet and answers the same.
The fold over an empty payload is the accumulator, definitionally. -/
theorem arm_0x43 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x43, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x43, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x43 : UInt8).toNat = .fixed 0 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x43 : UInt8) =
      .ok ⟨67, some "uint0", SpecAMQP.Generated.Oasis.Category.fixed, 0, "uint",
        "the uint value 0"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c = .ok (.uint 0, d) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rw [spec_takeBytes_zero d (spec_takeU8_next_le hs), except_bind_ok]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' = .ok (.uint 0, d') := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_ok fuel hd _ _ (by simp only [BodiesAgree]; decide) hS hR
    (spec_takeU8_data hs)

/-- **The `ulong0` row (`0x44`).** The same zero form at the wider type. -/
theorem arm_0x44 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x44, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x44, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x44 : UInt8).toNat = .fixed 0 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x44 : UInt8) =
      .ok ⟨68, some "ulong0", SpecAMQP.Generated.Oasis.Category.fixed, 0, "ulong",
        "the ulong value 0"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c = .ok (.ulong 0, d) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rw [spec_takeBytes_zero d (spec_takeU8_next_le hs), except_bind_ok]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' = .ok (.ulong 0, d') := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_ok fuel hd _ _ (by simp only [BodiesAgree]; decide) hS hR
    (spec_takeU8_data hs)

/-- **The `list0` row (`0x45`).** The declared surface's zero-width `list`, which the specification's
fixed-width reader answers as the empty list without recursing — one of the six zero-width rows that
make an array of zero-width elements bounded by its count rather than by the buffer. -/
theorem arm_0x45 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x45, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x45, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x45 : UInt8).toNat = .fixed 0 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x45 : UInt8) =
      .ok ⟨69, some "list0", SpecAMQP.Generated.Oasis.Category.fixed, 0, "list",
        "the empty list (i.e. the list with no elements)"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c = .ok (.list [], d) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rw [spec_takeBytes_zero d (spec_takeU8_next_le hs), except_bind_ok]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' = .ok (.list [], d') := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_ok fuel hd _ _ (by simp only [BodiesAgree, BodiesAgreeList]) hS hR
    (spec_takeU8_data hs)

/-- **The `smalluint` row (`0x52`).** One octet, read as an unsigned integer: the specification folds
the octet it took and the reference keeps it as a `UInt8`, so the value equation is the width-carrying
round trip (`UInt8.toNat_toUInt32`). -/
theorem arm_0x52 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x52, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x52, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x52 : UInt8).toNat = .fixed 1 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x52 : UInt8) =
      .ok ⟨82, some "smalluint", SpecAMQP.Generated.Oasis.Category.fixed, 1, "uint",
        "unsigned integer value in the range 0 to 255 inclusive"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 1 d >>= fun p => .ok (.uint (payloadNat p.1), p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeU8 d' >>= fun p => .ok (.uint p.1.toUInt32, p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeU8Nat d d' hd) (fun bytes => .uint (payloadNat bytes))
    (fun b => .uint b.toUInt32)
    (fun a b hrel _ _ => by
      simp only [BodiesAgree]
      rw [hrel]
      exact (UInt8.toNat_toUInt32 b).symm)
    hS hR (spec_takeU8_data hs)

/-- **The `smallulong` row (`0x53`).** The same one-octet payload at the wider type. -/
theorem arm_0x53 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x53, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x53, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x53 : UInt8).toNat = .fixed 1 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x53 : UInt8) =
      .ok ⟨83, some "smallulong", SpecAMQP.Generated.Oasis.Category.fixed, 1, "ulong",
        "unsigned long value in the range 0 to 255 inclusive"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 1 d >>= fun p => .ok (.ulong (payloadNat p.1), p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeU8 d' >>= fun p => .ok (.ulong p.1.toUInt64, p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeU8Nat d d' hd) (fun bytes => .ulong (payloadNat bytes))
    (fun b => .ulong b.toUInt64)
    (fun a b hrel _ _ => by
      simp only [BodiesAgree]
      rw [hrel]
      exact (UInt8.toNat_toUInt64 b).symm)
    hS hR (spec_takeU8_data hs)

/-- **The `boolean` row at one octet (`0x56`).** The one row whose two readers compare the payload in
different spellings: the specification folds the octet and asks whether the *number* is zero, the
reference asks whether the *octet* is `0x00`. `uint8_ne_zero_bool` is the whole value equation. -/
theorem arm_0x56 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x56, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x56, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x56 : UInt8).toNat = .fixed 1 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x56 : UInt8) =
      .ok ⟨86, none, SpecAMQP.Generated.Oasis.Category.fixed, 1, "boolean",
        "boolean with the octet 0x00 being false and octet 0x01 being true"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 1 d >>= fun p => .ok (.boolean (payloadNat p.1 != 0), p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeU8 d' >>= fun p => .ok (.boolean (p.1 != 0x00), p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeU8Nat d d' hd)
    (fun bytes => .boolean (payloadNat bytes != 0)) (fun b => .boolean (b != 0x00))
    (fun a b hrel _ _ => by
      simp only [BodiesAgree]
      rw [hrel]
      exact uint8_ne_zero_bool b)
    hS hR (spec_takeU8_data hs)

/-- **The `ushort` row (`0x60`).** Two octets folded into a number: the bound that makes the
specification's `Nat` the reference's `UInt16` is the read's own (`payloadNat_lt_of_takeBytes`), and
the value equation is the width-carrying round trip the corpus side states as `u16_toNat`. -/
theorem arm_0x60 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x60, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x60, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x60 : UInt8).toNat = .fixed 2 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x60 : UInt8) =
      .ok ⟨96, none, SpecAMQP.Generated.Oasis.Category.fixed, 2, "ushort",
        "16-bit unsigned integer in network byte order"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 2 d >>= fun p => .ok (.ushort (payloadNat p.1), p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeBeU 2 d' >>= fun p => .ok (.ushort p.1.toUInt16, p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeBeNat 2 d d' hd) (fun bytes => .ushort (payloadNat bytes))
    (fun n => .ushort n.toUInt16)
    (fun a b hrel f hf => by
      have hlt : b < 2 ^ 16 := by
        have h1 := payloadNat_lt_of_takeBytes hf
        rw [hrel] at h1
        have h2 : (256 : Nat) ^ 2 = 2 ^ 16 := by decide
        rw [h2] at h1
        exact h1
      simp only [BodiesAgree]
      rw [hrel]
      exact (UInt16.toNat_ofNat_of_lt (n := b) hlt).symm)
    hS hR (spec_takeU8_data hs)

/-- **The `uint` row (`0x70`).** The same fold at four octets. -/
theorem arm_0x70 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x70, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x70, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x70 : UInt8).toNat = .fixed 4 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x70 : UInt8) =
      .ok ⟨112, none, SpecAMQP.Generated.Oasis.Category.fixed, 4, "uint",
        "32-bit unsigned integer in network byte order"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 4 d >>= fun p => .ok (.uint (payloadNat p.1), p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeBeU 4 d' >>= fun p => .ok (.uint p.1.toUInt32, p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeBeNat 4 d d' hd) (fun bytes => .uint (payloadNat bytes))
    (fun n => .uint n.toUInt32)
    (fun a b hrel f hf => by
      have hlt : b < 2 ^ 32 := by
        have h1 := payloadNat_lt_of_takeBytes hf
        rw [hrel] at h1
        have h2 : (256 : Nat) ^ 4 = 2 ^ 32 := by decide
        rw [h2] at h1
        exact h1
      simp only [BodiesAgree]
      rw [hrel]
      exact (UInt32.toNat_ofNat_of_lt (n := b) hlt).symm)
    hS hR (spec_takeU8_data hs)

/-- **The `char` row (`0x73`).** The row the artifact frames as UTF-32BE, which this layer reads as
the number it is: the same fold and the same width-carrying round trip as `uint`, and no judgement
about whether the code point is assigned — that is the corpus vocabulary's business, not the wire's. -/
theorem arm_0x73 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x73, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x73, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x73 : UInt8).toNat = .fixed 4 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x73 : UInt8) =
      .ok ⟨115, some "utf32", SpecAMQP.Generated.Oasis.Category.fixed, 4, "char",
        "a UTF-32BE encoded Unicode character"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 4 d >>= fun p => .ok (.char (payloadNat p.1), p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeBeU 4 d' >>= fun p => .ok (.char p.1.toUInt32, p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeBeNat 4 d d' hd) (fun bytes => .char (payloadNat bytes))
    (fun n => .char n.toUInt32)
    (fun a b hrel f hf => by
      have hlt : b < 2 ^ 32 := by
        have h1 := payloadNat_lt_of_takeBytes hf
        rw [hrel] at h1
        have h2 : (256 : Nat) ^ 4 = 2 ^ 32 := by decide
        rw [h2] at h1
        exact h1
      simp only [BodiesAgree]
      rw [hrel]
      exact (UInt32.toNat_ofNat_of_lt (n := b) hlt).symm)
    hS hR (spec_takeU8_data hs)

/-- **The `ulong` row (`0x80`).** The same fold at eight octets, where the bound is `2 ^ 64`. -/
theorem arm_0x80 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x80, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x80, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x80 : UInt8).toNat = .fixed 8 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x80 : UInt8) =
      .ok ⟨128, none, SpecAMQP.Generated.Oasis.Category.fixed, 8, "ulong",
        "64-bit unsigned integer in network byte order"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 8 d >>= fun p => .ok (.ulong (payloadNat p.1), p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeBeU 8 d' >>= fun p => .ok (.ulong p.1.toUInt64, p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeBeNat 8 d d' hd) (fun bytes => .ulong (payloadNat bytes))
    (fun n => .ulong n.toUInt64)
    (fun a b hrel f hf => by
      have hlt : b < 2 ^ 64 := by
        have h1 := payloadNat_lt_of_takeBytes hf
        rw [hrel] at h1
        have h2 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
        rw [h2] at h1
        exact h1
      simp only [BodiesAgree]
      rw [hrel]
      exact (UInt64.toNat_ofNat_of_lt (n := b) hlt).symm)
    hS hR (spec_takeU8_data hs)


/-! ## The opaque widths

Six rows carry their payload without interpreting it: the artifact fixes these encodings' framing and
nothing in this layer does arithmetic on their contents, so the two readers answer the *octets* they
took. That makes them the cheapest group of all — the step relation is equality of arrays and the
value equation is `rfl` — and it is worth saying why the group is not smaller: `float`, `double`, the
three decimals and `uuid` are the six rows of the declared surface whose payload the value domain
keeps rather than reduces, and each one is still a separate arm because each is a separate arm of the
reference's own literal dispatch. -/

/-- **The `float` row (`0x72`).** Four payload octets, carried as they were read. -/
theorem arm_0x72 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x72, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x72, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x72 : UInt8).toNat = .fixed 4 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x72 : UInt8) =
      .ok ⟨114, some "ieee-754", SpecAMQP.Generated.Oasis.Category.fixed, 4, "float",
        "IEEE 754-2008 binary32"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 4 d >>= fun p => .ok (.float p.1, p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeBytes 4 d' >>= fun p => .ok (.float p.1, p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeBytes 4 d d' hd) (fun bytes => .float bytes)
    (fun bytes => .float bytes)
    (fun a b hrel _ _ => by simpa only [BodiesAgree] using hrel)
    hS hR (spec_takeU8_data hs)

/-- **The `decimal32` row (`0x74`).** The same four octets under the artifact's Binary Integer Decimal
framing, which this layer does not decode — the framing is what the row fixes. -/
theorem arm_0x74 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x74, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x74, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x74 : UInt8).toNat = .fixed 4 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x74 : UInt8) =
      .ok ⟨116, some "ieee-754", SpecAMQP.Generated.Oasis.Category.fixed, 4, "decimal32",
        "IEEE 754-2008 decimal32 using the Binary Integer Decimal encoding"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 4 d >>= fun p => .ok (.decimal32 p.1, p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeBytes 4 d' >>= fun p => .ok (.decimal32 p.1, p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeBytes 4 d d' hd) (fun bytes => .decimal32 bytes)
    (fun bytes => .decimal32 bytes)
    (fun a b hrel _ _ => by simpa only [BodiesAgree] using hrel)
    hS hR (spec_takeU8_data hs)

/-- **The `double` row (`0x82`).** The same carrier at eight octets. -/
theorem arm_0x82 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x82, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x82, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x82 : UInt8).toNat = .fixed 8 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x82 : UInt8) =
      .ok ⟨130, some "ieee-754", SpecAMQP.Generated.Oasis.Category.fixed, 8, "double",
        "IEEE 754-2008 binary64"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 8 d >>= fun p => .ok (.double p.1, p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeBytes 8 d' >>= fun p => .ok (.double p.1, p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeBytes 8 d d' hd) (fun bytes => .double bytes)
    (fun bytes => .double bytes)
    (fun a b hrel _ _ => by simpa only [BodiesAgree] using hrel)
    hS hR (spec_takeU8_data hs)

/-- **The `decimal64` row (`0x84`).** The same eight octets under the decimal framing. -/
theorem arm_0x84 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x84, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x84, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x84 : UInt8).toNat = .fixed 8 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x84 : UInt8) =
      .ok ⟨132, some "ieee-754", SpecAMQP.Generated.Oasis.Category.fixed, 8, "decimal64",
        "IEEE 754-2008 decimal64 using the Binary Integer Decimal encoding"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 8 d >>= fun p => .ok (.decimal64 p.1, p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeBytes 8 d' >>= fun p => .ok (.decimal64 p.1, p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeBytes 8 d d' hd) (fun bytes => .decimal64 bytes)
    (fun bytes => .decimal64 bytes)
    (fun a b hrel _ _ => by simpa only [BodiesAgree] using hrel)
    hS hR (spec_takeU8_data hs)

/-- **The `decimal128` row (`0x94`).** Sixteen octets, the widest opaque payload the surface
declares. -/
theorem arm_0x94 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x94, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x94, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x94 : UInt8).toNat = .fixed 16 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x94 : UInt8) =
      .ok ⟨148, some "ieee-754", SpecAMQP.Generated.Oasis.Category.fixed, 16, "decimal128",
        "IEEE 754-2008 decimal128 using the Binary Integer Decimal encoding"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 16 d >>= fun p => .ok (.decimal128 p.1, p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeBytes 16 d' >>= fun p => .ok (.decimal128 p.1, p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeBytes 16 d d' hd) (fun bytes => .decimal128 bytes)
    (fun bytes => .decimal128 bytes)
    (fun a b hrel _ _ => by simpa only [BodiesAgree] using hrel)
    hS hR (spec_takeU8_data hs)

/-- **The `uuid` row (`0x98`).** The same sixteen octets, whose fields this layer does not interpret:
the artifact fixes the width and the octet order, not what the fields mean. -/
theorem arm_0x98 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x98, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x98, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x98 : UInt8).toNat = .fixed 16 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x98 : UInt8) =
      .ok ⟨152, none, SpecAMQP.Generated.Oasis.Category.fixed, 16, "uuid",
        "UUID as defined in section 4.1.2 of RFC-4122"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 16 d >>= fun p => .ok (.uuid p.1, p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeBytes 16 d' >>= fun p => .ok (.uuid p.1, p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeBytes 16 d d' hd) (fun bytes => .uuid bytes)
    (fun bytes => .uuid bytes)
    (fun a b hrel _ _ => by simpa only [BodiesAgree] using hrel)
    hS hR (spec_takeU8_data hs)


/-! ## The variable rows

Six rows announce their own payload's length: `binary`, `string` and `symbol` in the eight- and
thirty-two-bit forms. They are the only arms whose read is *two* steps deep — a length field, then the
payload that field announced — and the reference reads the eight-bit length with its octet reader
(`takeU8`) while the specification reads it as a field (`takeBe 1`), which is
`stepAgreesAll_takeBeOne`: the relation is that the field's number is the octet's own value. The
thirty-two-bit rows agree on the number itself (`stepAgreesAll_takeBeEq`), because both readers fold
the same four octets.

The inner reader is `readersAgree_bind`'s composition: it takes the payload the outer step's number
announced and reads it at the cursors the outer step handed back. For `binary` the inner reader is the
payload read followed by the value (`readersAgree_ok`); for `string` and `symbol` it is the payload
read composed with `readersAgree_utf8`, the same-octets-same-text bridge above. -/

/-- **The `vbin8` row (`0xA0`).** A one-octet length, then that many octets carried as binary. -/
theorem arm_0xA0 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0xA0, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0xA0, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0xA0 : UInt8).toNat = .variable 1 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0xA0 : UInt8) =
      .ok ⟨160, some "vbin8", SpecAMQP.Generated.Oasis.Category.variable, 1, "binary",
        "up to 2^8 - 1 octets of binary data"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBe 1 d >>= fun p =>
        SpecAMQP.Spec.Codec.takeBytes p.1 p.2 >>= fun q => .ok (.binary q.1, q.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readVariable]
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeU8 d' >>= fun p =>
        SpecAMQP.Ref.takeBytes p.1.toNat p.2 >>= fun q => .ok (.binary q.1.toList, q.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_two_steps
    (fun n f => SpecAMQP.Spec.Codec.takeBytes n f >>= fun q => .ok (.binary q.1, q.2))
    (fun b f' => SpecAMQP.Ref.takeBytes b.toNat f' >>= fun q => .ok (.binary q.1.toList, q.2))
    (stepAgreesAll_takeBeOne d d' hd)
    hS hR
    (fun a b hab => by
      rw [← hab]
      exact readersAgree_bind (stepAgreesAll_takeBytes a)
        (fun bytes bytes' hb => by
          subst hb
          exact readersAgree_ok (.binary bytes) (.binary bytes.toList)
            (by simp only [BodiesAgree])))
    (spec_takeU8_data hs)

/-- **The `vbin32` row (`0xB0`).** The same payload behind a four-octet length, which both readers
fold the same way. -/
theorem arm_0xB0 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0xB0, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0xB0, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0xB0 : UInt8).toNat = .variable 4 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0xB0 : UInt8) =
      .ok ⟨176, some "vbin32", SpecAMQP.Generated.Oasis.Category.variable, 4, "binary",
        "up to 2^32 - 1 octets of binary data"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBe 4 d >>= fun p =>
        SpecAMQP.Spec.Codec.takeBytes p.1 p.2 >>= fun q => .ok (.binary q.1, q.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readVariable]
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeBeU 4 d' >>= fun p =>
        SpecAMQP.Ref.takeBytes p.1 p.2 >>= fun q => .ok (.binary q.1.toList, q.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_two_steps
    (fun n f => SpecAMQP.Spec.Codec.takeBytes n f >>= fun q => .ok (.binary q.1, q.2))
    (fun b f' => SpecAMQP.Ref.takeBytes b f' >>= fun q => .ok (.binary q.1.toList, q.2))
    (stepAgreesAll_takeBeEq 4 d d' hd)
    hS hR
    (fun a b hab => by
      rw [← hab]
      exact readersAgree_bind (stepAgreesAll_takeBytes a)
        (fun bytes bytes' hb => by
          subst hb
          exact readersAgree_ok (.binary bytes) (.binary bytes.toList)
            (by simp only [BodiesAgree])))
    (spec_takeU8_data hs)

/-- **The `str8-utf8` row (`0xA1`).** A one-octet length, the payload, then the payload decoded as
UTF-8 — the step `stepAgreesAll_utf8` carries, since both readers ask the same standard-library
question and the only difference is the refusal's prose. -/
theorem arm_0xA1 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0xA1, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0xA1, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0xA1 : UInt8).toNat = .variable 1 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0xA1 : UInt8) =
      .ok ⟨161, some "str8-utf8", SpecAMQP.Generated.Oasis.Category.variable, 1, "string",
        "up to 2^8 - 1 octets worth of UTF-8 Unicode (with no byte order mark)"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBe 1 d >>= fun p =>
        SpecAMQP.Spec.Codec.takeBytes p.1 p.2 >>= fun q =>
          SpecAMQP.Spec.Codec.utf8Of q.1 "string" >>= fun s => .ok (.string s, q.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readVariable]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeU8 d' >>= fun p =>
        SpecAMQP.Ref.takeBytes p.1.toNat p.2 >>= fun q =>
          SpecAMQP.Ref.decodeStringAt q.1 "string" q.2 >>= fun r => .ok (.string r.1, r.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_two_steps
    (fun n f => SpecAMQP.Spec.Codec.takeBytes n f >>= fun q =>
      SpecAMQP.Spec.Codec.utf8Of q.1 "string" >>= fun s => .ok (.string s, q.2))
    (fun b f' => SpecAMQP.Ref.takeBytes b.toNat f' >>= fun q =>
      SpecAMQP.Ref.decodeStringAt q.1 "string" q.2 >>= fun r => .ok (.string r.1, r.2))
    (stepAgreesAll_takeBeOne d d' hd)
    hS hR
    (fun a b hab => by
      rw [← hab]
      exact readersAgree_bind (stepAgreesAll_takeBytes a)
        (fun bytes bytes' hb => by
          subst hb
          exact readersAgree_utf8 "string" bytes (fun s => .string s) (fun s => .string s)
            (fun s => by simp only [BodiesAgree])))
    (spec_takeU8_data hs)

/-- **The `str32-utf8` row (`0xB1`).** The same text payload behind a four-octet length. -/
theorem arm_0xB1 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0xB1, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0xB1, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0xB1 : UInt8).toNat = .variable 4 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0xB1 : UInt8) =
      .ok ⟨177, some "str32-utf8", SpecAMQP.Generated.Oasis.Category.variable, 4, "string",
        "up to 2^32 - 1 octets worth of UTF-8 Unicode (with no byte order mark)"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBe 4 d >>= fun p =>
        SpecAMQP.Spec.Codec.takeBytes p.1 p.2 >>= fun q =>
          SpecAMQP.Spec.Codec.utf8Of q.1 "string" >>= fun s => .ok (.string s, q.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readVariable]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeBeU 4 d' >>= fun p =>
        SpecAMQP.Ref.takeBytes p.1 p.2 >>= fun q =>
          SpecAMQP.Ref.decodeStringAt q.1 "string" q.2 >>= fun r => .ok (.string r.1, r.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_two_steps
    (fun n f => SpecAMQP.Spec.Codec.takeBytes n f >>= fun q =>
      SpecAMQP.Spec.Codec.utf8Of q.1 "string" >>= fun s => .ok (.string s, q.2))
    (fun b f' => SpecAMQP.Ref.takeBytes b f' >>= fun q =>
      SpecAMQP.Ref.decodeStringAt q.1 "string" q.2 >>= fun r => .ok (.string r.1, r.2))
    (stepAgreesAll_takeBeEq 4 d d' hd)
    hS hR
    (fun a b hab => by
      rw [← hab]
      exact readersAgree_bind (stepAgreesAll_takeBytes a)
        (fun bytes bytes' hb => by
          subst hb
          exact readersAgree_utf8 "string" bytes (fun s => .string s) (fun s => .string s)
            (fun s => by simp only [BodiesAgree])))
    (spec_takeU8_data hs)

/-- **The `sym8` row (`0xA3`).** The symbol payload, which this layer decodes through the same UTF-8
test as `string`: the artifact restricts symbols to ASCII on the wire, and requiring the stricter of
the two rules is what makes the two artefacts agree on the payload. -/
theorem arm_0xA3 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0xA3, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0xA3, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0xA3 : UInt8).toNat = .variable 1 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0xA3 : UInt8) =
      .ok ⟨163, some "sym8", SpecAMQP.Generated.Oasis.Category.variable, 1, "symbol",
        "up to 2^8 - 1 seven bit ASCII characters representing a symbolic value"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBe 1 d >>= fun p =>
        SpecAMQP.Spec.Codec.takeBytes p.1 p.2 >>= fun q =>
          SpecAMQP.Spec.Codec.utf8Of q.1 "symbol" >>= fun s => .ok (.symbol s, q.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readVariable]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeU8 d' >>= fun p =>
        SpecAMQP.Ref.takeBytes p.1.toNat p.2 >>= fun q =>
          SpecAMQP.Ref.decodeStringAt q.1 "symbol" q.2 >>= fun r => .ok (.symbol r.1, r.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_two_steps
    (fun n f => SpecAMQP.Spec.Codec.takeBytes n f >>= fun q =>
      SpecAMQP.Spec.Codec.utf8Of q.1 "symbol" >>= fun s => .ok (.symbol s, q.2))
    (fun b f' => SpecAMQP.Ref.takeBytes b.toNat f' >>= fun q =>
      SpecAMQP.Ref.decodeStringAt q.1 "symbol" q.2 >>= fun r => .ok (.symbol r.1, r.2))
    (stepAgreesAll_takeBeOne d d' hd)
    hS hR
    (fun a b hab => by
      rw [← hab]
      exact readersAgree_bind (stepAgreesAll_takeBytes a)
        (fun bytes bytes' hb => by
          subst hb
          exact readersAgree_utf8 "symbol" bytes (fun s => .symbol s) (fun s => .symbol s)
            (fun s => by simp only [BodiesAgree])))
    (spec_takeU8_data hs)

/-- **The `sym32` row (`0xB3`).** The same symbol payload behind a four-octet length. -/
theorem arm_0xB3 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0xB3, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0xB3, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0xB3 : UInt8).toNat = .variable 4 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0xB3 : UInt8) =
      .ok ⟨179, some "sym32", SpecAMQP.Generated.Oasis.Category.variable, 4, "symbol",
        "up to 2^32 - 1 seven bit ASCII characters representing a symbolic value"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBe 4 d >>= fun p =>
        SpecAMQP.Spec.Codec.takeBytes p.1 p.2 >>= fun q =>
          SpecAMQP.Spec.Codec.utf8Of q.1 "symbol" >>= fun s => .ok (.symbol s, q.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readVariable]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeBeU 4 d' >>= fun p =>
        SpecAMQP.Ref.takeBytes p.1 p.2 >>= fun q =>
          SpecAMQP.Ref.decodeStringAt q.1 "symbol" q.2 >>= fun r => .ok (.symbol r.1, r.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_two_steps
    (fun n f => SpecAMQP.Spec.Codec.takeBytes n f >>= fun q =>
      SpecAMQP.Spec.Codec.utf8Of q.1 "symbol" >>= fun s => .ok (.symbol s, q.2))
    (fun b f' => SpecAMQP.Ref.takeBytes b f' >>= fun q =>
      SpecAMQP.Ref.decodeStringAt q.1 "symbol" q.2 >>= fun r => .ok (.symbol r.1, r.2))
    (stepAgreesAll_takeBeEq 4 d d' hd)
    hS hR
    (fun a b hab => by
      rw [← hab]
      exact readersAgree_bind (stepAgreesAll_takeBytes a)
        (fun bytes bytes' hb => by
          subst hb
          exact readersAgree_utf8 "symbol" bytes (fun s => .symbol s) (fun s => .symbol s)
            (fun s => by simp only [BodiesAgree])))
    (spec_takeU8_data hs)


/-! ## The signed rows

Seven rows carry two's-complement integers, and each owes a *value equation* rather than a new read:
the specification computes the field's value with `SpecAMQP.Spec.Codec.signedOfOctets` (a conditional subtraction of the
modulus) while the reference keeps it in a width-carrying carrier (`Int8`…`Int64`) built from the
same octets. The bridges below are therefore pure arithmetic on two spellings of one number, and the
three narrow rows (`0x51`, `0x54`, `0x55` — one octet carrying a wider-typed value) additionally need
the reference's *sign extension*: `Int32.ofBitVec (BitVec.ofNat 32 (signedOctet b % 2 ^ 32).toNat)`.
`Proofs/ValueCarrierAgreement`'s `i8_toInt`…`i64_toInt` are exactly that sign extension — the corpus
side reached them from the other direction — which is why this module imports that one. -/

/-- **A two's-complement field, as the carrier the same octets make.** `SpecAMQP.Spec.Codec.signedOfOctets` subtracts the
modulus above the half-way point and `BitVec.toInt` does the same, so the two are one function in two
spellings; the condition each tests is `2 * m < 2 ^ (8 * w)`, which is `m < 2 ^ (8 * w - 1)`. -/
theorem signedOfOctets_8 (m : Nat) (h : m < 2 ^ 8) :
    SpecAMQP.Spec.Codec.signedOfOctets 1 m = (Int8.ofBitVec (BitVec.ofNat 8 m)).toInt := by
  rw [Int8.toInt_ofBitVec, BitVec.toInt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  unfold SpecAMQP.Spec.Codec.signedOfOctets
  split <;> split <;> omega

/-- The same at two octets. -/
theorem signedOfOctets_16 (m : Nat) (h : m < 2 ^ 16) :
    SpecAMQP.Spec.Codec.signedOfOctets 2 m = (Int16.ofBitVec (BitVec.ofNat 16 m)).toInt := by
  rw [Int16.toInt_ofBitVec, BitVec.toInt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  unfold SpecAMQP.Spec.Codec.signedOfOctets
  split <;> split <;> omega

/-- The same at four octets. -/
theorem signedOfOctets_32 (m : Nat) (h : m < 2 ^ 32) :
    SpecAMQP.Spec.Codec.signedOfOctets 4 m = (Int32.ofBitVec (BitVec.ofNat 32 m)).toInt := by
  rw [Int32.toInt_ofBitVec, BitVec.toInt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  unfold SpecAMQP.Spec.Codec.signedOfOctets
  split <;> split <;> omega

/-- The same at eight octets. -/
theorem signedOfOctets_64 (m : Nat) (h : m < 2 ^ 64) :
    SpecAMQP.Spec.Codec.signedOfOctets 8 m = (Int64.ofBitVec (BitVec.ofNat 64 m)).toInt := by
  rw [Int64.toInt_ofBitVec, BitVec.toInt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  unfold SpecAMQP.Spec.Codec.signedOfOctets
  split <;> split <;> omega

/-- **The reference's octet reader, as the specification's one-octet field.** The reference spells a
signed octet `signedOctet`, the specification `SpecAMQP.Spec.Codec.signedOfOctets 1`; this is the first bridge as an
equation between the two, which is what the narrow rows' value equations rewrite through. -/
theorem signedOctet_eq (b : UInt8) :
    SpecAMQP.Ref.signedOctet b = SpecAMQP.Spec.Codec.signedOfOctets 1 b.toNat := by
  unfold SpecAMQP.Ref.signedOctet
  exact (signedOfOctets_8 b.toNat b.toNat_lt).symm

/-- The range a signed octet's value actually occupies, which is what the sign-extension lemmas below
need: one octet of two's complement is `-2 ^ 7` to `2 ^ 7 - 1`, never the wider type's extremes. -/
theorem signedOctet_bounds (b : UInt8) :
    -(2 ^ 7) ≤ SpecAMQP.Ref.signedOctet b ∧ SpecAMQP.Ref.signedOctet b ≤ 2 ^ 7 - 1 := by
  rw [signedOctet_eq b]
  unfold SpecAMQP.Spec.Codec.signedOfOctets
  have hlt := b.toNat_lt
  split <;> omega

/-- **The reference's sign extension into `Int32`.** A signed octet read into a four-octet carrier
keeps its sign: the octet's value is taken modulo the wider modulus and interpreted again, which is
the identity exactly on the octet's own range. `Proofs/ValueCarrierAgreement`'s `i32_toInt` is this
statement, reached from the corpus side; here it is applied to what the *reader* produced. -/
theorem signedOctet_int32 (b : UInt8) :
    (Int32.ofBitVec (BitVec.ofNat 32
      (SpecAMQP.Ref.signedOctet b % 4294967296).toNat)).toInt = SpecAMQP.Spec.Codec.signedOfOctets 1 b.toNat := by
  rw [← signedOctet_eq b]
  exact i32_toInt (SpecAMQP.Ref.signedOctet b) (by have := signedOctet_bounds b; omega)
    (by have := signedOctet_bounds b; omega)

/-- The same sign extension into `Int64`. -/
theorem signedOctet_int64 (b : UInt8) :
    (Int64.ofBitVec (BitVec.ofNat 64
      (SpecAMQP.Ref.signedOctet b % 18446744073709551616).toNat)).toInt =
      SpecAMQP.Spec.Codec.signedOfOctets 1 b.toNat := by
  rw [← signedOctet_eq b]
  exact i64_toInt (SpecAMQP.Ref.signedOctet b) (by have := signedOctet_bounds b; omega)
    (by have := signedOctet_bounds b; omega)

/-- **The `byte` row (`0x51`).** One octet, read as a signed byte: the specification's field value and
the reference's `Int8` carrier are the same number in two spellings. -/
theorem arm_0x51 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x51, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x51, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x51 : UInt8).toNat = .fixed 1 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x51 : UInt8) =
      .ok ⟨81, none, SpecAMQP.Generated.Oasis.Category.fixed, 1, "byte",
        "8-bit two's-complement integer"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 1 d >>= fun p =>
        .ok (.byte (SpecAMQP.Spec.Codec.signedOfOctets 1 (payloadNat p.1)), p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeU8 d' >>= fun p =>
        .ok (.byte (Int8.ofBitVec (BitVec.ofNat 8 p.1.toNat)), p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeU8Nat d d' hd)
    (fun bytes => .byte (SpecAMQP.Spec.Codec.signedOfOctets 1 (payloadNat bytes)))
    (fun b => .byte (Int8.ofBitVec (BitVec.ofNat 8 b.toNat)))
    (fun a b hrel _ _ => by
      simp only [BodiesAgree]
      rw [hrel]
      exact signedOfOctets_8 b.toNat b.toNat_lt)
    hS hR (spec_takeU8_data hs)

/-- **The `smallint` row (`0x54`).** One octet read into a four-octet `int`: the reference sign-extends
the octet, which is `signedOctet_int32`, and the specification's one-octet field already carries that
value. -/
theorem arm_0x54 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x54, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x54, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x54 : UInt8).toNat = .fixed 1 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x54 : UInt8) =
      .ok ⟨84, some "smallint", SpecAMQP.Generated.Oasis.Category.fixed, 1, "int",
        "8-bit two's-complement integer"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 1 d >>= fun p =>
        .ok (.int (SpecAMQP.Spec.Codec.signedOfOctets 1 (payloadNat p.1)), p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeU8 d' >>= fun p =>
        .ok (.int (Int32.ofBitVec (BitVec.ofNat 32
          (SpecAMQP.Ref.signedOctet p.1 % 4294967296).toNat)), p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeU8Nat d d' hd)
    (fun bytes => .int (SpecAMQP.Spec.Codec.signedOfOctets 1 (payloadNat bytes)))
    (fun b => .int (Int32.ofBitVec (BitVec.ofNat 32
      (SpecAMQP.Ref.signedOctet b % 4294967296).toNat)))
    (fun a b hrel _ _ => by
      simp only [BodiesAgree]
      rw [hrel]
      exact (signedOctet_int32 b).symm)
    hS hR (spec_takeU8_data hs)

/-- **The `smalllong` row (`0x55`).** The same one-octet form at `long`, with the eight-octet sign
extension. -/
theorem arm_0x55 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x55, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x55, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x55 : UInt8).toNat = .fixed 1 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x55 : UInt8) =
      .ok ⟨85, some "smalllong", SpecAMQP.Generated.Oasis.Category.fixed, 1, "long",
        "8-bit two's-complement integer"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 1 d >>= fun p =>
        .ok (.long (SpecAMQP.Spec.Codec.signedOfOctets 1 (payloadNat p.1)), p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeU8 d' >>= fun p =>
        .ok (.long (Int64.ofBitVec (BitVec.ofNat 64
          (SpecAMQP.Ref.signedOctet p.1 % 18446744073709551616).toNat)), p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeU8Nat d d' hd)
    (fun bytes => .long (SpecAMQP.Spec.Codec.signedOfOctets 1 (payloadNat bytes)))
    (fun b => .long (Int64.ofBitVec (BitVec.ofNat 64
      (SpecAMQP.Ref.signedOctet b % 18446744073709551616).toNat)))
    (fun a b hrel _ _ => by
      simp only [BodiesAgree]
      rw [hrel]
      exact (signedOctet_int64 b).symm)
    hS hR (spec_takeU8_data hs)

/-- **The `short` row (`0x61`).** Two octets as a signed sixteen-bit integer: the same fold as the
unsigned row, and the same value in two spellings. -/
theorem arm_0x61 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x61, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x61, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x61 : UInt8).toNat = .fixed 2 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x61 : UInt8) =
      .ok ⟨97, none, SpecAMQP.Generated.Oasis.Category.fixed, 2, "short",
        "16-bit two's-complement integer in network byte order"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 2 d >>= fun p =>
        .ok (.short (SpecAMQP.Spec.Codec.signedOfOctets 2 (payloadNat p.1)), p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeBeU 2 d' >>= fun p =>
        .ok (.short (Int16.ofBitVec (BitVec.ofNat 16 p.1)), p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeBeNat 2 d d' hd)
    (fun bytes => .short (SpecAMQP.Spec.Codec.signedOfOctets 2 (payloadNat bytes)))
    (fun n => .short (Int16.ofBitVec (BitVec.ofNat 16 n)))
    (fun a b hrel f hf => by
      have hlt : b < 2 ^ 16 := by
        have h1 := payloadNat_lt_of_takeBytes hf
        rw [hrel] at h1
        have h2 : (256 : Nat) ^ 2 = 2 ^ 16 := by decide
        rw [h2] at h1
        exact h1
      simp only [BodiesAgree]
      rw [hrel]
      exact signedOfOctets_16 b hlt)
    hS hR (spec_takeU8_data hs)

/-- **The `int` row (`0x71`).** The same at four octets. -/
theorem arm_0x71 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x71, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x71, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x71 : UInt8).toNat = .fixed 4 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x71 : UInt8) =
      .ok ⟨113, none, SpecAMQP.Generated.Oasis.Category.fixed, 4, "int",
        "32-bit two's-complement integer in network byte order"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 4 d >>= fun p =>
        .ok (.int (SpecAMQP.Spec.Codec.signedOfOctets 4 (payloadNat p.1)), p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeBeU 4 d' >>= fun p =>
        .ok (.int (Int32.ofBitVec (BitVec.ofNat 32 p.1)), p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeBeNat 4 d d' hd)
    (fun bytes => .int (SpecAMQP.Spec.Codec.signedOfOctets 4 (payloadNat bytes)))
    (fun n => .int (Int32.ofBitVec (BitVec.ofNat 32 n)))
    (fun a b hrel f hf => by
      have hlt : b < 2 ^ 32 := by
        have h1 := payloadNat_lt_of_takeBytes hf
        rw [hrel] at h1
        have h2 : (256 : Nat) ^ 4 = 2 ^ 32 := by decide
        rw [h2] at h1
        exact h1
      simp only [BodiesAgree]
      rw [hrel]
      exact signedOfOctets_32 b hlt)
    hS hR (spec_takeU8_data hs)

/-- **The `long` row (`0x81`).** The same at eight octets. -/
theorem arm_0x81 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x81, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x81, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x81 : UInt8).toNat = .fixed 8 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x81 : UInt8) =
      .ok ⟨129, none, SpecAMQP.Generated.Oasis.Category.fixed, 8, "long",
        "64-bit two's-complement integer in network byte order"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 8 d >>= fun p =>
        .ok (.long (SpecAMQP.Spec.Codec.signedOfOctets 8 (payloadNat p.1)), p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeBeU 8 d' >>= fun p =>
        .ok (.long (Int64.ofBitVec (BitVec.ofNat 64 p.1)), p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeBeNat 8 d d' hd)
    (fun bytes => .long (SpecAMQP.Spec.Codec.signedOfOctets 8 (payloadNat bytes)))
    (fun n => .long (Int64.ofBitVec (BitVec.ofNat 64 n)))
    (fun a b hrel f hf => by
      have hlt : b < 2 ^ 64 := by
        have h1 := payloadNat_lt_of_takeBytes hf
        rw [hrel] at h1
        have h2 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
        rw [h2] at h1
        exact h1
      simp only [BodiesAgree]
      rw [hrel]
      exact signedOfOctets_64 b hlt)
    hS hR (spec_takeU8_data hs)

/-- **The `timestamp` row (`0x83`).** The same eight octets read as a signed count of milliseconds:
the row's only content beyond `long` is which type name the two artefacts give the value. -/
theorem arm_0x83 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x83, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x83, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x83 : UInt8).toNat = .fixed 8 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x83 : UInt8) =
      .ok ⟨131, some "ms64", SpecAMQP.Generated.Oasis.Category.fixed, 8, "timestamp",
        "64-bit two's-complement integer representing milliseconds since the unix epoch"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 8 d >>= fun p =>
        .ok (.timestamp (SpecAMQP.Spec.Codec.signedOfOctets 8 (payloadNat p.1)), p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeBeU 8 d' >>= fun p =>
        .ok (.timestamp (Int64.ofBitVec (BitVec.ofNat 64 p.1)), p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeBeNat 8 d d' hd)
    (fun bytes => .timestamp (SpecAMQP.Spec.Codec.signedOfOctets 8 (payloadNat bytes)))
    (fun n => .timestamp (Int64.ofBitVec (BitVec.ofNat 64 n)))
    (fun a b hrel f hf => by
      have hlt : b < 2 ^ 64 := by
        have h1 := payloadNat_lt_of_takeBytes hf
        rw [hrel] at h1
        have h2 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
        rw [h2] at h1
        exact h1
      simp only [BodiesAgree]
      rw [hrel]
      exact signedOfOctets_64 b hlt)
    hS hR (spec_takeU8_data hs)

end SpecAMQP.Proofs
