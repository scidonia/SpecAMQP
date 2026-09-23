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
widths, the six opaque widths, and the six variable rows. Also landed: the fuel-irrelevance family
(`fuelIrrelevant_all`, with its six reader clauses), which is the fact the loop relations need — the
specification's reader answers the same at every fuel above the octet bound, so its item loop can be
put on the reference's footing one fuel lower. Still owed: the six compound and array rows,
with the three loop relations they share; the dispatch that turns the arms into the induction step;
and the fuel induction itself, whose entry point is free. What each owes and how it is
proved is stated where it belongs rather than in a list here: see the octet step's arithmetic, and
`arm_0x00`'s docstring for the pattern the branches follow.

## What the compound and array rows owe, and the fuel asymmetry that shapes them

The tools the loop relations need are landed — `pairUp_agrees` (the two artefacts' map pairings),
`specElementData` with `specElementData_loop` and `specElementData_progress` (the specification's
element read, named as a reader so the element count can be inducted on), the reference's own cursor
advances, the element-constructor bridge (`elementDecl?_isSome`, `elementDecl?_of_assigned`,
`elementDecl?_refusal`), and the refusal families for an octet the declared surface does not assign
(`encodingOf_none_of_not_assigned`, `ref_readValue_unassigned`, `spec_readValue_unassigned`,
`dataDecl_of_unassigned`). The loop relations themselves are **not** landed, and the reason is a
finding that shapes them rather than a missing lemma — the plan owner's response to it is the
irrelevance family now landed at the end of this module:

**The two artefacts spend fuel differently on a compound's header.** The reference's `readCompound`
matches on `fuel + 1`, so it spends one unit on its own header and reads its items at `readItems
(F - 1)`; the specification's `readValue` is where that unit was spent, and its `readCompound` passes
its own fuel through, reading its items at `readItems F`. At one value-level fuel the two item loops
therefore sit **one apart**, and the offset *compounds*: an item that is itself a compound puts its
own items one further apart again, so the difference is `1` per nesting level and grows without bound
as the input nests. `split`-free measurement of the two: `readItems 3 1` and `readItems 2 1` are the
item loops of the two artefacts on the same value-level fuel, and at fuel zero they are not even the
same function — `Ref.readItems 0 0 c` refuses where `Spec.readItems 1 0 c` accepts — so no statement
of the form "ref `readItems j` ↔ spec `readItems j`" can be proved from the readers as they are.

Two designs close the gap, and a successor should pick one deliberately. **The plan owner chose the
first** (`4c3c4a0`), and the account below is what designing it showed:

* **The specification's fuel is irrelevant above the bound.** A fuel unit is spent only where a reader
  *descends*, and a descent consumes octets (a described value behind one constructor octet, a
  compound's items behind two size fields, an array's elements behind a size field, a count field and
  a constructor). So at a cursor whose remaining octets the fuel covers, one unit more of fuel changes
  no answer — and the item loops can then be put on one footing by converting the specification's fuel
  down. This is the cheaper design and it needs *no* per-octet work: the specification's dispatch is
  on `classify code.toNat` and on the generated table, so its cases are six, and the four width cases
  are uniform in the row (`specElementData` is exactly the reader's own decision, so a whole width
  case is one application of the element clause). **Implemented** at the end of this module
  (`fuelIrrelevant_all` and its six corollaries), with the guards that designing it established. What
  designing it established, and what a successor should not have to rediscover:
  - It must be stated as an *agreement* and not an equality (a refusal's prose names the cursor it was
    refused at), and each clause must carry the *buffer invariance* of its read as well as its answer
    — `c₂.data = c.data`. The arms supply that per row from the primitive lemmas; the loops need it for
    the bound arithmetic, because the tail of an item loop is read at a cursor the item read advanced,
    so the bound at the tail is only expressible through the buffer the read handed back.
  - It is a joint induction over the six readers, and the level's clauses must be proved in dependency
    order: the value reader descends into the compound, the array and the element decision at one fuel
    less, so those three come from the induction hypothesis; the compound's items are read at the
    *same* fuel the compound was, and the element decision's data likewise, so the item clause and the
    element clause are read at the same level as the clauses that call them; the element loop is its
    decision and then itself, the latter by a count induction.
  - Two clauses are false as stated at the boundary and need a guard. The item loop's is false from
    fuel zero to one at a *zero count* (`Ref.readItems 0 0` refuses where `Spec.readItems 1 0`
    accepts), which no octet bound excludes; it is stated from fuel one, and the middle layer never
    needs it lower because a compound's items are only reached behind a readable header. The compound
    reader's is false at fuel zero for a declaration of width **zero** (the header consumes nothing, so
    the two fuels' item loops are reached and they differ at a zero count); the declared surface's
    compound rows are one and four octets wide, so no reader reaches one, but the *statement* has to
    carry that width — or the family has to be stated per category — and any successor that omits it
    will find the clause unprovable rather than false-by-assumption.
  - Two `split` behaviours decide how the value clause's width case is written, measured rather than
    guessed. `split at h` on a match whose scrutinee is a variable *substitutes* that variable
    everywhere, the goal included (and leaves the catch-all's negations), so the compound reader's
    owner match — a `String`-literal match — costs one `split at h` and nothing else. But `split`
    *cannot* reach a match under a bind's continuation: the width case's `match decl.category` sits
    inside `dataDecl code >>= fun decl => …`, and the fix is to destruct the read's own equation first
    (`dataDecl code = .ok decl`, then `split at h` for the category), then rewrite the goal's copy of
    the bind with the same two facts. Following that order, the width case needs no width hypothesis of
    its own; the compound clause's boundary guard is supplied at the branch rather than threaded
    through the value clause.
  - At the entry fuel the claim is not in doubt: an entry-point differential over **101,585** buffers
    (70,644 up to length 3 over a 41-octet alphabet spanning every category, 30,941 up to length 4
    over a 13-octet alphabet chosen for compounds, arrays and described values) reports **zero**
    divergences in shape, consumed count, body view and reason class — so the offset is an accounting
    difference between the readers, not a behavioural one.
* **The value relation is stated at a fuel pair.** State the middle layer with the reference's fuel
  and the specification's as parameters and carry the offset symbolically. This needs no new fact, but
  it needs the *scalar* rows re-proved at shifted fuel pairs, since the landed arms relate the two
  readers at one fuel: forty branches of the same size as the arms, or the arms restated with a second
  fuel parameter. The plan owner rejected it for that reason: it invalidates landed work by
  construction and buys nothing the first design does not.

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
descent spends at least one octet, and a reader spends fuel only by descending, which is what the
branch lemmas show one branch at a time.

What is **not** true, and what this docstring said until the compound rows were attempted, is that the
two readers spend the same fuel for the same descent. The reference's `readCompound` matches on
`fuel + 1` and so spends one unit on its own header, while the specification's `readValue` already
spent that unit and its `readCompound` passes its own fuel through: the reference's `readCompound F`
reads `readItems (F - 1)` where the specification's reads `readItems F`. The two *item loops* therefore
sit one fuel apart at one value-level fuel, and the difference is visible in the loops themselves —
`Ref.readItems 0 0 c` refuses where `Spec.readItems 1 0 c` accepts, so no statement of the form
"ref `readItems j` ↔ spec `readItems j`" is provable from the readers as they are. The offset is an
accounting difference and not a behavioural one — both readers answer identically at the fuel the
contract uses, which is what the entry-point differential measures — and what closes it is the fact
that the specification's fuel is irrelevant above the bound; the module header's section on the
compound and array rows states that fact and the design it wants.

A law
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

/-! ## What the induction carries, and why it is not the law itself

The compound and array rows read *below* the fuel their own value was read at: a `list8` opened by
`readValue (fuel + 1)` reads its items at `readValue (fuel - 1)`, two levels down, while a described
value reads its descriptor and its value at `readValue fuel`, one level down. So a step lemma cannot
rest on `WireAgrees fuel` alone — it needs the agreement at every fuel beneath it — and this is that
obligation, named once rather than spelled out at every branch:

`WireAgreesUpTo n` is `WireAgrees` at every fuel up to `n`. It is *not* a strengthening of the law a
contract needs; it is the induction's own invariant, and `wireLayer_all` below ends by reading the
top of it off at `n = n`. -/
def WireAgreesUpTo (n : Nat) : Prop := ∀ k, k ≤ n → WireAgrees k

/-- The invariant at a lower fuel, which is what every descent inside a branch needs. -/
theorem wireAgreesUpTo_mono {m n : Nat} (h : WireAgreesUpTo n) (hmn : m ≤ n) : WireAgreesUpTo m :=
  fun k hk => h k (by omega)

/-- The invariant at its own fuel. -/
theorem wireAgreesUpTo_self {n : Nat} (h : WireAgreesUpTo n) : WireAgrees n := h n (le_refl n)

/-! ## An octet the declared surface does not assign

The reference dispatches on the constructor octet as a literal, so its own arms cover forty of the
256 and its catch-all covers the rest; the specification dispatches on `classify` and the generated
table, so an octet outside those forty reaches `declInRange`, which refuses it by name. What the
catch-all needs is that "outside the reference's forty" and "the declared surface assigns no row" are
the same set, and the two artefacts' own tests are the cheapest way to say so: `assignedConstructor`
is the reference's own forty-literal test, and the sweep below checks the generated table against it
for every octet there is, by ordinary evaluation over the 256 of them. -/

set_option maxRecDepth 10000 in
/-- **The declared surface and the reference's constructor test assign the same octets.** One finite
evaluation over all 256 octets, with the table's own `find?` asked about each; the reference's test is
asked of `UInt8.ofNat n`, which *is* `n` as an octet for every `n < 256`, so the sweep covers every
octet there is. -/
theorem no_encoding_of_unassigned_constructor :
    (List.range 256).all (fun n =>
      (SpecAMQP.Generated.Oasis.encodingOf n).isNone
        || SpecAMQP.Ref.assignedConstructor (UInt8.ofNat n)) = true := by
  decide

/-- The sweep, read off at one octet: an octet the reference does not accept has no row in the
declared surface. -/
theorem encodingOf_none_of_not_assigned {code : UInt8}
    (h : SpecAMQP.Ref.assignedConstructor code = false) :
    SpecAMQP.Generated.Oasis.encodingOf code.toNat = none := by
  have hmem := List.all_eq_true.mp no_encoding_of_unassigned_constructor code.toNat
    (List.mem_range.mpr code.toNat_lt)
  rw [Bool.or_eq_true] at hmem
  rcases hmem with hnone | hassigned
  · exact Option.isNone_iff_eq_none.mp hnone
  · rw [show UInt8.ofNat code.toNat = code from by simp [UInt8.ofNat_toNat]] at hassigned
    rw [h] at hassigned
    exact absurd hassigned (by simp)

/-- **The reference refuses an octet it does not accept, naming it `unassigned`.** The reference's own
dispatch has one arm per assigned octet and one catch-all, so the catch-all is exactly the
`assignedConstructor` test failing — which is what makes this provable from the test alone. -/
theorem ref_readValue_unassigned (fuel : Nat) (c' : SpecAMQP.Ref.Cursor) (code : UInt8)
    (d' : SpecAMQP.Ref.Cursor) (hr : SpecAMQP.Ref.takeU8 c' = .ok (code, d'))
    (hass : SpecAMQP.Ref.assignedConstructor code = false) :
    SpecAMQP.Ref.readValue (fuel + 1) c' = .error (.unassigned code) := by
  simp only [SpecAMQP.Ref.readValue]
  rw [hr, except_bind_ok]
  dsimp only
  split
  all_goals first
    | rfl
    | (simp only [SpecAMQP.Ref.assignedConstructor] at hass; exact absurd hass (by simp))

set_option maxRecDepth 10000 in
/-- The grammar's classification, checked against the octet it classifies: `%x00` is the only
descriptor prefix, so every *other* octet is refused by the specification's own dispatch rather than
read as one. -/
theorem classify_sweep :
    (List.range 255).all (fun k =>
      decide (SpecAMQP.Spec.Value.classify (k + 1) ≠ .descriptor)) = true := by
  decide

/-- A non-zero octet is never the descriptor prefix. -/
theorem classify_ne_descriptor_of_ne_zero (n : Nat) (hn : n < 256) (h : n ≠ 0) :
    SpecAMQP.Spec.Value.classify n ≠ SpecAMQP.Spec.Value.Constructor.descriptor := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact of_decide_eq_true
    (List.all_eq_true.mp classify_sweep k (List.mem_range.mpr (by omega)))

/-- **The declared surface's range check, in the shape a refusal needs.** A row the table does not
hold is refused with the class `unassigned`, whatever the range the octet's classification gave it. -/
theorem declInRange_of_none {code : UInt8} {cat : SpecAMQP.Generated.Oasis.Category} {w : Nat}
    (h : SpecAMQP.Generated.Oasis.encodingOf code.toNat = none) :
    ∃ r : SpecAMQP.Spec.Codec.Refusal,
      SpecAMQP.Spec.Codec.declInRange code cat w = .error r ∧ r.reasonClass = "unassigned" := by
  unfold SpecAMQP.Spec.Codec.declInRange
  rw [h]
  exact ⟨_, rfl, rfl⟩

/-- The declared surface's lookup refuses an octet it has no row for, in the same words. The
descriptor prefix and the reserved octets are refusals here too, so this needs no hypothesis beyond
the missing row. -/
theorem dataDecl_of_unassigned (code : UInt8)
    (hnone : SpecAMQP.Generated.Oasis.encodingOf code.toNat = none) :
    ∃ r : SpecAMQP.Spec.Codec.Refusal,
      SpecAMQP.Spec.Codec.dataDecl code = .error r ∧ r.reasonClass = "unassigned" := by
  unfold SpecAMQP.Spec.Codec.dataDecl
  split
  all_goals first
    | exact ⟨_, rfl, rfl⟩
    | exact declInRange_of_none hnone

/-- **The specification refuses an octet the declared surface does not assign, naming it
`unassigned`.** The one place this needs more than the missing row is the descriptor prefix: `%x00`
is unassigned in the table and would send the reader down the described-value arm, so the octet has to
be excluded by name — which is what the reference's own test already does, since it counts `%x00`
among the constructors it accepts. -/
theorem spec_readValue_unassigned (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (code : UInt8)
    (d : SpecAMQP.Spec.Codec.Cursor)
    (hu : SpecAMQP.Spec.Codec.takeU8 c = .ok (code, d))
    (hnone : SpecAMQP.Generated.Oasis.encodingOf code.toNat = none)
    (hne : code ≠ 0x00) :
    ∃ refusal : SpecAMQP.Spec.Codec.Refusal,
      SpecAMQP.Spec.Codec.readValue (fuel + 1) c = .error refusal ∧
      refusal.reasonClass = "unassigned" := by
  obtain ⟨r, hd, hc⟩ := dataDecl_of_unassigned code hnone
  have hne0 : code.toNat ≠ 0 := fun h => hne (UInt8.toNat_inj.mp (by simpa using h))
  have hcl : SpecAMQP.Spec.Value.classify code.toNat ≠ .descriptor :=
    classify_ne_descriptor_of_ne_zero code.toNat code.toNat_lt hne0
  simp only [SpecAMQP.Spec.Codec.readValue]
  rw [hu, except_bind_ok]
  split
  all_goals first
    | exact absurd ‹SpecAMQP.Spec.Value.classify code.toNat = .descriptor› hcl
    | exact ⟨_, rfl, rfl⟩
    | exact ⟨r, by dsimp only; rw [hd]; simp only [except_bind_error], hc⟩

/-! ## The element constructor: two tests, one set of octets

An array's element constructor is checked by both readers *after* the count and the limit and *before*
any element is read: the reference asks its own `assignedConstructor`, and the specification asks
`elementDecl?`, whose answer is the declaration the element's data is read under (or `none` for the
descriptor prefix). The two tests accept the same octets, which is one finite evaluation over the 256
of them — `elementDecl?` is asked of `UInt8.ofNat n`, which is `n` as an octet for every `n < 256`. -/

set_option maxRecDepth 10000 in
/-- **The two element-constructor tests accept the same octets.** -/
theorem elementDecl?_sweep :
    (List.range 256).all (fun n =>
      (SpecAMQP.Spec.Codec.elementDecl? (UInt8.ofNat n)).toOption.isSome
        == SpecAMQP.Ref.assignedConstructor (UInt8.ofNat n)) = true := by
  decide

/-- The sweep as an equation at one octet. -/
theorem elementDecl?_isSome (ctor : UInt8) :
    (SpecAMQP.Spec.Codec.elementDecl? ctor).toOption.isSome =
      SpecAMQP.Ref.assignedConstructor ctor := by
  have hall := List.all_eq_true.mp elementDecl?_sweep ctor.toNat
    (List.mem_range.mpr ctor.toNat_lt)
  rwa [show UInt8.ofNat ctor.toNat = ctor from by simp [UInt8.ofNat_toNat], beq_iff_eq] at hall

/-- An octet the reference accepts as an element constructor is one the specification looks up
successfully. -/
theorem elementDecl?_of_assigned {ctor : UInt8}
    (h : SpecAMQP.Ref.assignedConstructor ctor = true) :
    ∃ ed : Option SpecAMQP.Generated.Oasis.EncodingDecl,
      SpecAMQP.Spec.Codec.elementDecl? ctor = .ok ed := by
  cases hed : SpecAMQP.Spec.Codec.elementDecl? ctor with
  | ok ed => exact ⟨ed, rfl⟩
  | error e =>
    have his := elementDecl?_isSome ctor
    rw [hed] at his
    simp only [Except.toOption, Option.isSome] at his
    rw [h] at his
    exact absurd his (by simp)

/-- **An octet the reference refuses as an element constructor is refused by name.** The specification
has two more refusal sites than the reference here — the reserved range and the range check — but both
name `unassigned`, and the octet below `%x40` that the reference's test also rejects cannot reach the
descriptor-prefix arm, since `elementDecl?` handles `%x00` before it classifies anything. -/
theorem elementDecl?_refusal {ctor : UInt8}
    (h : SpecAMQP.Ref.assignedConstructor ctor = false) :
    ∃ r : SpecAMQP.Spec.Codec.Refusal,
      SpecAMQP.Spec.Codec.elementDecl? ctor = .error r ∧ r.reasonClass = "unassigned" := by
  have hnone := encodingOf_none_of_not_assigned h
  have hne : ctor.toNat ≠ 0 := by
    intro hz
    have hz' : ctor = 0x00 := by
      have : ctor.toNat = (0x00 : UInt8).toNat := by simpa using hz
      exact UInt8.toNat_inj.mp this
    rw [hz'] at h
    exact absurd h (by decide)
  have hcl : SpecAMQP.Spec.Value.classify ctor.toNat ≠ .descriptor :=
    classify_ne_descriptor_of_ne_zero ctor.toNat ctor.toNat_lt hne
  unfold SpecAMQP.Spec.Codec.elementDecl?
  rw [if_neg hne]
  split
  all_goals first
    | exact absurd ‹SpecAMQP.Spec.Value.classify ctor.toNat = .descriptor› hcl
    | exact ⟨_, rfl, rfl⟩
    | (obtain ⟨r, hr, hc⟩ := declInRange_of_none (cat := .fixed) hnone
       exact ⟨r, by rw [hr]; simp only [except_map_error], hc⟩)
    | (obtain ⟨r, hr, hc⟩ := declInRange_of_none (cat := .variable) hnone
       exact ⟨r, by rw [hr]; simp only [except_map_error], hc⟩)
    | (obtain ⟨r, hr, hc⟩ := declInRange_of_none (cat := .compound) hnone
       exact ⟨r, by rw [hr]; simp only [except_map_error], hc⟩)
    | (obtain ⟨r, hr, hc⟩ := declInRange_of_none (cat := .array) hnone
       exact ⟨r, by rw [hr]; simp only [except_map_error], hc⟩)

/-! ## The reference's own reads, as the arithmetic a loop's bound needs

Every bound in this development is a statement about the octets left at a cursor, and the cursor
arithmetic that carries one bound to the next read is the readers' own advances. The specification's
are in `Proofs.ReadProgress`; these are the reference's, stated the same way — where the read left the
cursor, on which buffer, and what the read therefore required of the buffer. The requirement is what a
*small* fuel is excluded by: a header that was read says the buffer held its octets. -/

/-- **The reference's payload read.** -/
theorem ref_takeBytes_of_ok {n : Nat} {c c' : SpecAMQP.Ref.Cursor}
    {bytes : SpecAMQP.Harness.Octets} (h : SpecAMQP.Ref.takeBytes n c = .ok (bytes, c')) :
    c'.data = c.data ∧ c'.pos = c.pos + n ∧ c.pos + n ≤ c.data.size := by
  by_cases hn : c.pos + n ≤ c.data.size
  · simp only [SpecAMQP.Ref.takeBytes, if_pos hn, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hcur⟩ := h
    subst hcur
    exact ⟨rfl, rfl, hn⟩
  · simp only [SpecAMQP.Ref.takeBytes, if_neg hn] at h
    exact absurd h (by simp)

/-- **The reference's octet read.** -/
theorem ref_takeU8_of_ok {c c' : SpecAMQP.Ref.Cursor} {b : UInt8}
    (h : SpecAMQP.Ref.takeU8 c = .ok (b, c')) :
    c'.data = c.data ∧ c'.pos = c.pos + 1 ∧ c.pos + 1 ≤ c.data.size := by
  by_cases hn : c.pos < c.data.size
  · simp only [SpecAMQP.Ref.takeU8, dif_pos hn, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hcur⟩ := h
    subst hcur
    exact ⟨rfl, rfl, hn⟩
  · simp only [SpecAMQP.Ref.takeU8, dif_neg hn] at h
    exact absurd h (by simp)

/-- **The reference's big-endian field read.** -/
theorem ref_takeBeU_of_ok {w : Nat} {c c' : SpecAMQP.Ref.Cursor} {m : Nat}
    (h : SpecAMQP.Ref.takeBeU w c = .ok (m, c')) :
    c'.data = c.data ∧ c'.pos = c.pos + w ∧ c.pos + w ≤ c.data.size := by
  unfold SpecAMQP.Ref.takeBeU at h
  obtain ⟨⟨bytes, d⟩, hb, h⟩ := exists_of_bind_ok h
  dsimp only at h
  rw [except_pure_ok, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, hcur⟩ := h
  subst hcur
  exact ref_takeBytes_of_ok hb

/-- The specification's octet read leaves its cursor one further on, which is the arithmetic its own
branches need. Stated here because `Proofs.ReadProgress` gives the *inequality* the fuel law needs and
the loops need the advance itself. -/
theorem spec_takeU8_pos {c d : SpecAMQP.Spec.Codec.Cursor} {b : UInt8}
    (h : SpecAMQP.Spec.Codec.takeU8 c = .ok (b, d)) : d.pos = c.pos + 1 := by
  by_cases hn : c.pos < c.data.size
  · simp only [SpecAMQP.Spec.Codec.takeU8, dif_pos hn, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
  · simp only [SpecAMQP.Spec.Codec.takeU8, dif_neg hn] at h
    exact absurd h (by simp)

/-! ## A map's pairs, from the items it read

The two artefacts pair a map's items the same way — consecutive items, key then value, in wire order —
but they say it differently: the reference's `pairUp` is the partial function that *refuses* an odd
tail (`none`), the specification's drops a dangling item rather than refusing it. The parity check
ahead of the items read is what makes the two agree, so the bridge below is stated with the reference's
`pairUp` succeeding as a hypothesis; the specification's list is then the same pairing, and the
hypothesis is exactly what the reference's own reader had established. -/

/-- Two lists that agree are both empty or both consed; the mismatched shapes are the relation's own
`False`, so they are the two sides of the induction's base. -/
theorem bodiesAgreeList_cons {x : SpecAMQP.Spec.Codec.Value}
    {xs : List SpecAMQP.Spec.Codec.Value} {y : SpecAMQP.Ref.Value} {ys : List SpecAMQP.Ref.Value}
    (h : BodiesAgreeList (x :: xs) (y :: ys)) : BodiesAgree x y ∧ BodiesAgreeList xs ys := by
  simpa only [BodiesAgreeList] using h

/-- An agreeing list is empty on the right when it is empty on the left. -/
theorem bodiesAgreeList_nil_left {ys : List SpecAMQP.Ref.Value}
    (h : BodiesAgreeList [] ys) : ys = [] := by
  cases ys with
  | nil => rfl
  | cons y ys => simp only [BodiesAgreeList] at h

/-- ... and empty on the left when it is empty on the right. -/
theorem bodiesAgreeList_nil_right {xs : List SpecAMQP.Spec.Codec.Value}
    (h : BodiesAgreeList xs []) : xs = [] := by
  cases xs with
  | nil => rfl
  | cons x xs => simp only [BodiesAgreeList] at h

/-- **The two artefacts' pairings agree.** Inducting on the *pairing* rather than on the items: the
reference's `pairUp` is the partial function, so its success is what says how many items there were
and how they were grouped, and each pair of the reference's is a pair of the specification's, key
against key and value against value. Inducting on the grouping rather than on the items is what keeps
the induction hypothesis available at the list the recursion actually reaches — the items come two at
a time, so the tail the recursion reaches is two shorter than the tail the item induction would
reach. The shapes where the two disagree about a dangling item are the ones the reference's success
excludes, and each is closed as the contradiction it is. -/
theorem pairUp_agrees (zs : List (SpecAMQP.Ref.Value × SpecAMQP.Ref.Value)) :
    ∀ (xs : List SpecAMQP.Spec.Codec.Value) (ys : List SpecAMQP.Ref.Value),
      BodiesAgreeList xs ys → SpecAMQP.Ref.pairUp ys = some zs →
      BodiesAgreePairs (SpecAMQP.Spec.Codec.pairUp xs) zs := by
  induction zs with
  | nil =>
    intro xs ys h hz
    cases ys with
    | nil =>
      rw [bodiesAgreeList_nil_right h]
      simp only [SpecAMQP.Spec.Codec.pairUp, BodiesAgreePairs]
    | cons y ys =>
      cases ys with
      | nil =>
        simp only [SpecAMQP.Ref.pairUp] at hz
        exact absurd hz (by intro hh; cases hh)
      | cons y' ys' =>
        cases hp : SpecAMQP.Ref.pairUp ys' with
        | none =>
          simp only [SpecAMQP.Ref.pairUp, hp, Option.map_none] at hz
          exact absurd hz (by intro hh; cases hh)
        | some zs'' =>
          simp only [SpecAMQP.Ref.pairUp, hp, Option.map_some] at hz
          exact absurd hz (by intro hh; cases hh)
  | cons z zs' ih =>
    cases z with
    | mk z₁ z₂ =>
      intro xs ys h hz
      cases ys with
      | nil =>
        simp only [SpecAMQP.Ref.pairUp, Option.some.injEq] at hz
        exact absurd hz (by intro hh; cases hh)
      | cons y ys =>
        cases ys with
        | nil =>
          simp only [SpecAMQP.Ref.pairUp] at hz
          exact absurd hz (by intro hh; cases hh)
        | cons y' ys' =>
          cases hp : SpecAMQP.Ref.pairUp ys' with
          | none =>
            simp only [SpecAMQP.Ref.pairUp, hp, Option.map_none] at hz
            exact absurd hz (by intro hh; cases hh)
          | some zs'' =>
            simp only [SpecAMQP.Ref.pairUp, hp, Option.map_some, Option.some.injEq] at hz
            injection hz with hhead htailz
            injection hhead with h1 h2
            subst h1
            subst h2
            subst htailz
            cases xs with
            | nil => simp only [BodiesAgreeList] at h
            | cons x xs₁ =>
              obtain ⟨hxy, htail⟩ := bodiesAgreeList_cons h
              cases xs₁ with
              | nil => simp only [BodiesAgreeList] at htail
              | cons x' xs' =>
                obtain ⟨hx', hrest⟩ := bodiesAgreeList_cons htail
                simp only [SpecAMQP.Spec.Codec.pairUp]
                unfold BodiesAgreePairs
                exact ⟨hxy, hx', ih xs' ys' hrest hp⟩

/-! ## The specification's array element, as a reader of its own

An array's elements are read by `readElementsLoop`, whose one element is a *decision* on the element
constructor's declaration rather than a reader: the descriptor prefix reads the element's own
descriptor and value, and an assigned row reads the data its category names. The loop's agreement has
to be an induction on the element count, and an induction on a count needs its step to be a *step* —
so the decision is named here as a reader, and `specElementData_loop` below is the equation that says
this is the reader's own read rather than a second reading of the same octets. -/
def specElementData (fuel : Nat) (elementDecl : Option SpecAMQP.Generated.Oasis.EncodingDecl)
    (c : SpecAMQP.Spec.Codec.Cursor) :
    Except SpecAMQP.Spec.Codec.Refusal
      (SpecAMQP.Spec.Codec.Value × SpecAMQP.Spec.Codec.Cursor) :=
  match elementDecl with
  | none => (do
      let (descriptor, c) ← SpecAMQP.Spec.Codec.readValue fuel c
      let (value, c) ← SpecAMQP.Spec.Codec.readValue fuel c
      return (.described descriptor value, c))
  | some decl =>
    match decl.category with
    | .fixed | .variable => SpecAMQP.Spec.Codec.readScalarData decl c
    | .compound => SpecAMQP.Spec.Codec.readCompound fuel decl c
    | .array => SpecAMQP.Spec.Codec.readArrayData fuel decl c

/-- **The element loop is its element read and then the loop.** An identity of the reader's own
definition, so a step of the count induction is the element read and the induction hypothesis. Proved
through the equation lemmas rather than by `rfl`: the specification's readers are one `mutual` block,
so their unfoldings are the compiler's equations and not `iota`. -/
theorem specElementData_loop (fuel : Nat) (elementDecl : Option SpecAMQP.Generated.Oasis.EncodingDecl)
    (count : Nat) (c : SpecAMQP.Spec.Codec.Cursor) :
    SpecAMQP.Spec.Codec.readElementsLoop fuel elementDecl (count + 1) c =
      specElementData fuel elementDecl c >>= fun p =>
        SpecAMQP.Spec.Codec.readElementsLoop fuel elementDecl count p.2 >>= fun q =>
          .ok (p.1 :: q.1, q.2) := by
  cases elementDecl <;> cases count <;>
    (unfold SpecAMQP.Spec.Codec.readElementsLoop specElementData
     dsimp only
     first
       | rfl
       | ((simp only [SpecAMQP.Spec.Codec.readElementsLoop, except_bind_ok, except_pure_ok]) <;> rfl))

/-- **An element read does not move its cursor backwards.** The loop's bound is a statement about the
octets left at the loop's *entry* cursor, and the induction hands it to the read of the next element:
what makes it still hold there is that the cursor only moves forward. The four readers the element
decision selects are the ones `Proofs.ReadProgress` already states this for, at the fuels this
decision uses them at. -/
theorem specElementData_progress (fuel : Nat)
    (elementDecl : Option SpecAMQP.Generated.Oasis.EncodingDecl) :
    ∀ (c : SpecAMQP.Spec.Codec.Cursor) (v : SpecAMQP.Spec.Codec.Value)
      (c₂ : SpecAMQP.Spec.Codec.Cursor),
      specElementData fuel elementDecl c = .ok (v, c₂) → c.pos ≤ c₂.pos := by
  intro c v c₂ h
  cases elementDecl with
  | none =>
    unfold specElementData at h
    obtain ⟨⟨d, c₁⟩, h1, h⟩ := exists_of_bind_ok h
    dsimp only at h
    obtain ⟨⟨val, c₃⟩, h2, h⟩ := exists_of_bind_ok h
    dsimp only at h
    rw [except_pure_ok, Except.ok.injEq, Prod.mk.injEq] at h
    have p1 := (readValue_progress fuel).1 c d c₁ h1
    have p2 := (readValue_progress fuel).1 c₁ val c₃ h2
    rw [← h.2]
    omega
  | some decl =>
    simp only [specElementData] at h
    split at h
    all_goals first
      | exact readScalarData_progress decl c v c₂ h
      | exact (readValue_progress fuel).2.2.1 decl c v c₂ h
      | exact (readValue_progress fuel).2.2.2.1 decl c v c₂ h

/-! ## An exhausted cursor, and what the container readers answer there

A compound's zero-fuel case is the one place the two readers' *shape* differs rather than their fuel:
the reference's `readCompound` matches on `fuel + 1` and refuses at zero, while the specification's has
no match of its own and refuses at zero by failing to read its first size field. The two refusals are
the same class, and these are the facts that say so without either reader having to name the prose it
refused with. -/

/-- **An exhausted cursor makes the specification's big-endian field read refuse as `truncated`.** The
refusal is the one a compound's or an array's header meets first, and its *class* is what the fuel
comparison reads. -/
theorem spec_takeBe_exhausted {w : Nat} (hw : 1 ≤ w) {c : SpecAMQP.Spec.Codec.Cursor}
    (h : c.data.size ≤ c.pos) :
    SpecAMQP.Spec.Codec.takeBe w c = .error (SpecAMQP.Spec.Codec.refusal "truncated"
      s!"{w} octet(s) needed at offset {c.pos} of {c.data.size}") := by
  unfold SpecAMQP.Spec.Codec.takeBe SpecAMQP.Spec.Codec.takeBytes
  rw [if_neg (by omega), except_bind_error]

/-- The same for a compound's own header. The fuel does not appear: a compound's items are only
reached behind two size fields, so a cursor with nothing left refuses before any of the reader's own
decisions. -/
theorem spec_readCompound_header {fuel : Nat} {decl : SpecAMQP.Generated.Oasis.EncodingDecl}
    (hwidth : 1 ≤ decl.width) (c : SpecAMQP.Spec.Codec.Cursor) (h : c.data.size ≤ c.pos) :
    SpecAMQP.Spec.Codec.readCompound fuel decl c = .error (SpecAMQP.Spec.Codec.refusal "truncated"
      s!"{decl.width} octet(s) needed at offset {c.pos} of {c.data.size}") := by
  unfold SpecAMQP.Spec.Codec.readCompound
  rw [spec_takeBe_exhausted hwidth h, except_bind_error]


/-! ## The specification's fuel is irrelevant above the octet bound

The tooling above is what the middle layer's compound and array rows need; this is the fact that lets
them be stated. The two artefacts spend fuel differently on a compound's header — the reference's
`readCompound` matches on `fuel + 1` and so spends a unit on its own header, while the specification's
`readValue` is where that unit was spent and its `readCompound` passes its own fuel through — so the
item loops sit one apart at one value-level fuel. What closes the gap is that a fuel unit is spent
only where a reader *descends*, and a descent consumes octets: at a cursor the fuel covers, one unit
more of fuel changes no answer. That is the family below, and it is what the loops are then put on one
footing with.

The statements carry three things beyond the answer. The agreement is an *agreement* and not an
equality, because a refusal's prose names the cursor it was refused at. Each reader's read is shown to
hand back the buffer it was given (`readRows_data`), because a loop's tail is read at a cursor the item
read advanced and the octet bound at the tail is expressible only through that buffer. And two clauses
carry guards that are conditions on the *statement*: the item loop refuses at fuel zero and accepts at
fuel one with a zero count, so its clause is stated from fuel one, and the compound and array readers
need a header wide enough to spend the octet that puts their item loops a level down, which is
`WideOption` and the two table sweeps. -/

open SpecAMQP.Spec.Codec
open SpecAMQP.Generated.Oasis (EncodingDecl)


/-- **A fixed-width row's read hands back its own buffer.** The value the row answers is built from
the payload, but the cursor it answers with is the one the payload read left, and that read took an
`extract` of the buffer rather than a copy of it. -/
theorem readFixed_data (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor)
    (h : readFixed decl c = .ok (v, c')) : c'.data = c.data := by
  obtain ⟨payload, c₁, hb, hc⟩ := readFixed_ok decl c v c' h
  rw [← hc]
  exact spec_takeBytes_data hb

/-- **A variable-width row's read hands back its own buffer.** -/
theorem readVariable_data (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor)
    (h : readVariable decl c = .ok (v, c')) : c'.data = c.data := by
  obtain ⟨length, c₁, payload, c₂, hbe, hbp, hc, -⟩ := readVariable_ok decl c v c' h
  rw [← hc, spec_takeBytes_data hbp, spec_takeBe_data hbe]

/-- **A scalar row's read hands back its own buffer**, whichever of the two categories it declares. -/
theorem readScalarData_data (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor)
    (h : readScalarData decl c = .ok (v, c')) : c'.data = c.data := by
  unfold readScalarData at h
  split at h
  all_goals first
    | exact readFixed_data decl c v c' h
    | exact readVariable_data decl c v c' h
    | exact absurd h (by simp)

/-- **Every reader in the value cluster hands back the buffer it was given.**

The companion of `readValue_progress`, and the fact the fuel-irrelevance clauses need: a loop's tail
is read at the cursor the item or element read handed back, so the octet bound at the tail is
expressible only through the buffer the read left. The six clauses are one induction on the fuel, in
dependency order, because the `mutual` block cannot be separated: the compound reader reads its items
at its *own* fuel, and the element loop's element decision reads the value reader at its own fuel
too, so those two clauses are reached at the same level they are proved at. -/
theorem readRows_data : ∀ (fuel : Nat),
    (∀ (c : Cursor) (v : Value) (c' : Cursor), readValue fuel c = .ok (v, c') → c'.data = c.data) ∧
    (∀ (count : Nat) (c : Cursor) (items : List Value) (c' : Cursor),
      readItems fuel count c = .ok (items, c') → c'.data = c.data) ∧
    (∀ (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor),
      readCompound fuel decl c = .ok (v, c') → c'.data = c.data) ∧
    (∀ (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor),
      readArrayData fuel decl c = .ok (v, c') → c'.data = c.data) ∧
    (∀ (elementDecl : Option EncodingDecl) (count : Nat) (c : Cursor) (items : List Value)
      (c' : Cursor), readElements fuel elementDecl count c = .ok (items, c') → c'.data = c.data) ∧
    (∀ (elementDecl : Option EncodingDecl) (count : Nat) (c : Cursor) (items : List Value)
      (c' : Cursor), readElementsLoop fuel elementDecl count c = .ok (items, c') →
        c'.data = c.data) := by
  intro fuel
  induction fuel with
  | zero =>
    have hValue : ∀ (c : Cursor) (v : Value) (c' : Cursor),
        readValue 0 c = .ok (v, c') → c'.data = c.data := by
      intro c v c' h
      simp only [readValue] at h
      exact absurd h (by simp)
    have hItems : ∀ (count : Nat) (c : Cursor) (items : List Value) (c' : Cursor),
        readItems 0 count c = .ok (items, c') → c'.data = c.data := by
      intro count c items c' h
      simp only [readItems] at h
      exact absurd h (by simp)
    have hCompound : ∀ (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor),
        readCompound 0 decl c = .ok (v, c') → c'.data = c.data := by
      intro decl c v c' h
      unfold readCompound at h
      obtain ⟨⟨size, c₁⟩, h1, h⟩ := exists_of_bind_ok h
      try dsimp only at h
      obtain ⟨⟨count, c₂⟩, h2, h⟩ := exists_of_bind_ok h
      try dsimp only at h
      have d1 := spec_takeBe_data h1
      have d2 := spec_takeBe_data h2
      split at h
      · obtain ⟨⟨items, c₃⟩, h3, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        have d3 := hItems count c₂ items c₃ h3
        split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          rw [← h.2, d3, d2, d1]
        · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · obtain ⟨⟨items, c₃⟩, h3, h⟩ := exists_of_bind_ok h
          try dsimp only at h
          have d3 := hItems count c₂ items c₃ h3
          split at h
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            rw [← h.2, d3, d2, d1]
          · exact absurd h (by simp)
      · exact absurd h (by simp)
    have hArrayData : ∀ (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor),
        readArrayData 0 decl c = .ok (v, c') → c'.data = c.data := by
      intro decl c v c' h
      simp only [readArrayData] at h
      exact absurd h (by simp)
    have hElements : ∀ (elementDecl : Option EncodingDecl) (count : Nat) (c : Cursor)
        (items : List Value) (c' : Cursor),
        readElements 0 elementDecl count c = .ok (items, c') → c'.data = c.data := by
      intro elementDecl count c items c' h
      simp only [readElements] at h
      exact absurd h (by simp)
    have hElementData : ∀ (elementDecl : Option EncodingDecl) (c : Cursor) (v : Value)
        (c' : Cursor), specElementData 0 elementDecl c = .ok (v, c') → c'.data = c.data := by
      intro elementDecl c v c' h
      unfold specElementData at h
      split at h <;> try (split at h)
      all_goals first
        | (obtain ⟨⟨dsc, c₁⟩, h1, h⟩ := exists_of_bind_ok h
           try dsimp only at h
           simp only [readValue] at h1
           exact absurd h1 (by simp))
        | exact readScalarData_data _ c v c' h
        | exact hCompound _ c v c' h
        | exact hArrayData _ c v c' h
    have hElementsLoop : ∀ (elementDecl : Option EncodingDecl) (count : Nat) (c : Cursor)
        (items : List Value) (c' : Cursor),
        readElementsLoop 0 elementDecl count c = .ok (items, c') → c'.data = c.data := by
      intro elementDecl count
      induction count with
      | zero =>
        intro c items c' h
        simp only [readElementsLoop] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2]
      | succ k ihk =>
        intro c items c' h
        rw [specElementData_loop] at h
        obtain ⟨⟨item, c₁⟩, h1, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        obtain ⟨⟨rest, c₂⟩, h2, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        have d1 := hElementData elementDecl c item c₁ h1
        have d2 := ihk c₁ rest c₂ h2
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2, d2, d1]
    exact ⟨hValue, hItems, hCompound, hArrayData, hElements, hElementsLoop⟩
  | succ n ih =>
    obtain ⟨ihValue, ihItems, ihCompound, ihArrayData, ihElements, ihElementsLoop⟩ := ih
    have hValue : ∀ (c : Cursor) (v : Value) (c' : Cursor),
        readValue (n + 1) c = .ok (v, c') → c'.data = c.data := by
      intro c v c' h
      unfold readValue at h
      obtain ⟨⟨code, c₁⟩, hu, h⟩ := exists_of_bind_ok h
      try dsimp only at h
      have d0 := spec_takeU8_data hu
      split at h
      all_goals first
        | (obtain ⟨⟨descriptor, c₂⟩, h1, h⟩ := exists_of_bind_ok h
           try dsimp only at h
           obtain ⟨⟨inner, c₃⟩, h2, h⟩ := exists_of_bind_ok h
           try dsimp only at h
           have d1 := ihValue c₁ descriptor c₂ h1
           have d2 := ihValue c₂ inner c₃ h2
           simp only [except_pure_ok, Except.ok.injEq, Prod.mk.injEq] at h
           rw [← h.2, d2, d1, d0])
        | (obtain ⟨decl, hd, h⟩ := exists_of_bind_ok h
           try dsimp only at h
           split at h <;> try (split at h)
           all_goals first
             | (have hh := readScalarData_data decl c₁ v c' h; rw [hh, d0])
             | (have hh := ihCompound decl c₁ v c' h; rw [hh, d0])
             | (have hh := ihArrayData decl c₁ v c' h; rw [hh, d0]))
        | exact absurd h (by simp)
    have hItems : ∀ (count : Nat) (c : Cursor) (items : List Value) (c' : Cursor),
        readItems (n + 1) count c = .ok (items, c') → c'.data = c.data := by
      intro count
      cases count with
      | zero =>
        intro c items c' h
        simp only [readItems] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2]
      | succ k =>
        intro c items c' h
        unfold readItems at h
        obtain ⟨⟨item, c₁⟩, h1, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        obtain ⟨⟨rest, c₂⟩, h2, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        have d1 := ihValue c item c₁ h1
        have d2 := ihItems k c₁ rest c₂ h2
        simp only [except_pure_ok, Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2, d2, d1]
    have hCompound : ∀ (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor),
        readCompound (n + 1) decl c = .ok (v, c') → c'.data = c.data := by
      intro decl c v c' h
      unfold readCompound at h
      obtain ⟨⟨size, c₁⟩, h1, h⟩ := exists_of_bind_ok h
      try dsimp only at h
      obtain ⟨⟨count, c₂⟩, h2, h⟩ := exists_of_bind_ok h
      try dsimp only at h
      have d1 := spec_takeBe_data h1
      have d2 := spec_takeBe_data h2
      split at h
      · obtain ⟨⟨items, c₃⟩, h3, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        have d3 := hItems count c₂ items c₃ h3
        split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          rw [← h.2, d3, d2, d1]
        · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · obtain ⟨⟨items, c₃⟩, h3, h⟩ := exists_of_bind_ok h
          try dsimp only at h
          have d3 := hItems count c₂ items c₃ h3
          split at h
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            rw [← h.2, d3, d2, d1]
          · exact absurd h (by simp)
      · exact absurd h (by simp)
    have hArrayData : ∀ (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor),
        readArrayData (n + 1) decl c = .ok (v, c') → c'.data = c.data := by
      intro decl c v c' h
      unfold readArrayData at h
      obtain ⟨⟨size, c₁⟩, h1, h⟩ := exists_of_bind_ok h
      try dsimp only at h
      obtain ⟨⟨count, c₂⟩, h2, h⟩ := exists_of_bind_ok h
      try dsimp only at h
      have d1 := spec_takeBe_data h1
      have d2 := spec_takeBe_data h2
      split at h
      · exact absurd h (by simp)
      · obtain ⟨⟨constructor, c₃⟩, h3, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        have d3 := spec_takeU8_data h3
        obtain ⟨elementDecl, h4, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        obtain ⟨⟨items, c₄⟩, h5, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        have d4 := ihElements elementDecl count c₃ items c₄ h5
        split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          rw [← h.2, d4, d3, d2, d1]
        · exact absurd h (by simp)
    have hElements : ∀ (elementDecl : Option EncodingDecl) (count : Nat) (c : Cursor)
        (items : List Value) (c' : Cursor),
        readElements (n + 1) elementDecl count c = .ok (items, c') → c'.data = c.data := by
      intro elementDecl count c items c' h
      simp only [readElements] at h
      exact ihElementsLoop elementDecl count c items c' h
    have hElementData : ∀ (elementDecl : Option EncodingDecl) (c : Cursor) (v : Value)
        (c' : Cursor), specElementData (n + 1) elementDecl c = .ok (v, c') → c'.data = c.data := by
      intro elementDecl c v c' h
      unfold specElementData at h
      split at h <;> try (split at h)
      all_goals first
        | (obtain ⟨⟨dsc, c₁⟩, h1, h⟩ := exists_of_bind_ok h
           try dsimp only at h
           obtain ⟨⟨val, c₂⟩, h2, h⟩ := exists_of_bind_ok h
           try dsimp only at h
           have d1 := hValue c dsc c₁ h1
           have d2 := hValue c₁ val c₂ h2
           simp only [except_pure_ok, Except.ok.injEq, Prod.mk.injEq] at h
           rw [← h.2, d2, d1])
        | exact readScalarData_data _ c v c' h
        | exact hCompound _ c v c' h
        | exact hArrayData _ c v c' h
    have hElementsLoop : ∀ (elementDecl : Option EncodingDecl) (count : Nat) (c : Cursor)
        (items : List Value) (c' : Cursor),
        readElementsLoop (n + 1) elementDecl count c = .ok (items, c') → c'.data = c.data := by
      intro elementDecl count
      induction count with
      | zero =>
        intro c items c' h
        simp only [readElementsLoop] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2]
      | succ k ihk =>
        intro c items c' h
        rw [specElementData_loop] at h
        obtain ⟨⟨item, c₁⟩, h1, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        obtain ⟨⟨rest, c₂⟩, h2, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        have d1 := hElementData elementDecl c item c₁ h1
        have d2 := ihk c₁ rest c₂ h2
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2, d2, d1]
    exact ⟨hValue, hItems, hCompound, hArrayData, hElements, hElementsLoop⟩

/-- **A value read spends its constructor octet before anything else**, so at a fuel at least one it
leaves the cursor strictly further on. The weak progress `readValue_progress` gives is not enough for
the item loop's tail: its bound is one octet tighter than the loop's, and only the octet the value
reader took makes up the difference. -/
theorem readValue_lt {f : Nat} {c : Cursor} {v : Value} {d : Cursor}
    (hf : 1 ≤ f) (h : readValue f c = .ok (v, d)) : c.pos < d.pos := by
  obtain ⟨k, rfl⟩ : ∃ k, f = k + 1 := ⟨f - 1, by omega⟩
  unfold readValue at h
  obtain ⟨⟨code, c₁⟩, hu, h⟩ := exists_of_bind_ok h
  try dsimp only at h
  have h1 : c₁.pos = c.pos + 1 := spec_takeU8_pos hu
  split at h
  all_goals first
    | (obtain ⟨⟨descriptor, c₂⟩, h2, h⟩ := exists_of_bind_ok h
       try dsimp only at h
       obtain ⟨⟨inner, c₃⟩, h3, h⟩ := exists_of_bind_ok h
       try dsimp only at h
       have p1 := (readValue_progress k).1 c₁ descriptor c₂ h2
       have p2 := (readValue_progress k).1 c₂ inner c₃ h3
       simp only [except_pure_ok, Except.ok.injEq, Prod.mk.injEq] at h
       rw [← h.2]
       omega)
    | (obtain ⟨decl, hd, h⟩ := exists_of_bind_ok h
       try dsimp only at h
       split at h <;> try (split at h)
       all_goals first
         | (have p := readScalarData_progress decl c₁ v d h; omega)
         | (have p := (readValue_progress k).2.2.1 decl c₁ v d h; omega)
         | (have p := (readValue_progress k).2.2.2.1 decl c₁ v d h; omega))
    | exact absurd h (by simp)

/-- **The element decision hands back its own buffer.** Read off the cluster: the descriptor prefix's
two value reads and the compound and array rows are all cases of it, and the scalar rows are the
payload-free ones. -/
theorem specElementData_data (fuel : Nat) (ed : Option EncodingDecl) (c : Cursor) (v : Value)
    (c' : Cursor) (h : specElementData fuel ed c = .ok (v, c')) : c'.data = c.data := by
  unfold specElementData at h
  split at h <;> try (split at h)
  all_goals first
    | (obtain ⟨⟨dsc, c₁⟩, h1, h⟩ := exists_of_bind_ok h
       try dsimp only at h
       obtain ⟨⟨val, c₂⟩, h2, h⟩ := exists_of_bind_ok h
       try dsimp only at h
       have d1 := (readRows_data fuel).1 c dsc c₁ h1
       have d2 := (readRows_data fuel).1 c₁ val c₂ h2
       simp only [except_pure_ok, Except.ok.injEq, Prod.mk.injEq] at h
       rw [← h.2, d2, d1])
    | exact readScalarData_data _ c v c' h
    | exact (readRows_data fuel).2.2.1 _ c v c' h
    | exact (readRows_data fuel).2.2.2.1 _ c v c' h


/-! ## The specification's fuel is irrelevant above the octet bound -/

/-- **The specification's two answers agree**: the same value and cursor, or refusals of the same
class. An *agreement* rather than an equality, because a refusal's prose names the cursor it was
refused at: `readValue 0 c` says the input ends before the value does, while the same read at a
larger fuel fails to take its constructor octet and says so. -/
def AnswerAgrees {α : Type} (x y : Except SpecAMQP.Spec.Codec.Refusal α) : Prop :=
  (∀ a, x = .ok a → y = .ok a) ∧
  (∀ r : SpecAMQP.Spec.Codec.Refusal, x = .error r →
    ∃ r' : SpecAMQP.Spec.Codec.Refusal, y = .error r' ∧ r.reasonClass = r'.reasonClass)

theorem answerAgrees_refl {α : Type} (x : Except SpecAMQP.Spec.Codec.Refusal α) :
    AnswerAgrees x x :=
  ⟨fun _ h => h, fun r h => ⟨r, h, rfl⟩⟩

/-- A shared continuation preserves the relation: everything a reader's caller does with the answer —
a size comparison, a pairing, a value constructor — is fuel-free. -/
theorem answerAgrees_bind {α β : Type} {x y : Except SpecAMQP.Spec.Codec.Refusal α}
    (h : AnswerAgrees x y) (k : α → Except SpecAMQP.Spec.Codec.Refusal β) :
    AnswerAgrees (x >>= k) (y >>= k) := by
  constructor
  · intro b hb
    obtain ⟨a, hx, hk⟩ := exists_of_bind_ok hb
    rw [h.1 a hx, except_bind_ok, hk]
  · intro r hr
    cases hx : x with
    | error e =>
      rw [hx, except_bind_error] at hr
      obtain ⟨r', hr', hcl⟩ := h.2 e hx
      exact ⟨r', by rw [hr', except_bind_error], by rw [← Except.error.inj hr]; exact hcl⟩
    | ok a =>
      rw [hx, except_bind_ok] at hr
      exact ⟨r, by rw [h.1 a hx, except_bind_ok, hr], rfl⟩

/-- The same, for a continuation that consumes the *cursor* as well as the value — which every
reader below a read does, since the read beneath starts where the read above left off. The
continuation's agreement is asked only of the pair the left read actually answers, because that is
the cursor the second read's octet bound has to be about. -/
theorem answerAgrees_bind₂ {α β : Type} {x y : Except SpecAMQP.Spec.Codec.Refusal (α × Cursor)}
    {F G : α × Cursor → Except SpecAMQP.Spec.Codec.Refusal (β × Cursor)}
    (h : AnswerAgrees x y)
    (hk : ∀ (p : α × Cursor), x = .ok p → AnswerAgrees (F p) (G p)) :
    AnswerAgrees (x >>= F) (y >>= G) := by
  constructor
  · intro b hb
    obtain ⟨p, hx, hk'⟩ := exists_of_bind_ok hb
    have hy := h.1 p hx
    rw [hy, except_bind_ok, (hk p hx).1 b hk']
  · intro r hr
    cases hx : x with
    | error e =>
      rw [hx, except_bind_error] at hr
      obtain ⟨r', hr', hcl⟩ := h.2 e hx
      exact ⟨r', by rw [hr', except_bind_error], by rw [← Except.error.inj hr]; exact hcl⟩
    | ok p =>
      rw [hx, except_bind_ok] at hr
      obtain ⟨r', hr', hcl⟩ := (hk p hx).2 r hr
      exact ⟨r', by rw [h.1 p hx, except_bind_ok, hr'], hcl⟩

/-- **A continuation under a read that refuses.** When the left read never accepts, the two
continuations are never reached and nothing about them matters — which is how the item loop's
zero-fuel tail is closed. -/
theorem answerAgrees_bind_error {α β : Type} {x y : Except SpecAMQP.Spec.Codec.Refusal α}
    (h : AnswerAgrees x y) (hx : ∀ a, x ≠ .ok a)
    (K : α → Except SpecAMQP.Spec.Codec.Refusal β) (K' : α → Except SpecAMQP.Spec.Codec.Refusal β) :
    AnswerAgrees (x >>= K) (y >>= K') := by
  constructor
  · intro b hb
    obtain ⟨a, ha, -⟩ := exists_of_bind_ok hb
    exact absurd ha (hx a)
  · intro r hr
    cases hxe : x with
    | error e =>
      rw [hxe, except_bind_error] at hr
      obtain ⟨r', hr', hcl⟩ := h.2 e hxe
      exact ⟨r', by rw [hr', except_bind_error], by rw [← Except.error.inj hr]; exact hcl⟩
    | ok a => exact absurd hxe (hx a)

/-- The class a failed octet step names: `truncated`, whatever the prose. -/
theorem spec_takeU8_error_class {c : Cursor} {r : SpecAMQP.Spec.Codec.Refusal}
    (h : takeU8 c = .error r) : r.reasonClass = "truncated" := by
  unfold takeU8 at h
  split at h
  · exact absurd h (by simp)
  · simp only [Except.error.injEq] at h
    rw [← h]
    rfl

/-- The same for a failed payload read. -/
theorem spec_takeBytes_error_class {n : Nat} {c : Cursor} {r : SpecAMQP.Spec.Codec.Refusal}
    (h : takeBytes n c = .error r) : r.reasonClass = "truncated" := by
  unfold takeBytes at h
  split at h
  · exact absurd h (by simp)
  · simp only [Except.error.injEq] at h
    rw [← h]
    rfl

/-- ... and for a failed big-endian field, which refuses through the payload read. -/
theorem spec_takeBe_error_class {w : Nat} {c : Cursor} {r : SpecAMQP.Spec.Codec.Refusal}
    (h : takeBe w c = .error r) : r.reasonClass = "truncated" := by
  unfold takeBe at h
  cases hb : takeBytes w c with
  | error e =>
    rw [hb, except_bind_error] at h
    rw [← Except.error.inj h]
    exact spec_takeBytes_error_class hb
  | ok p => rw [hb, except_bind_ok] at h; exact absurd h (by simp)

/-- **The budget a read hands to the read beneath it**: the same buffer, a cursor no further back. -/
theorem bound_tail_value {f : Nat} {c d : Cursor} {v : Value}
    (h : readValue f c = .ok (v, d)) (hb : c.data.size - c.pos ≤ f) :
    d.data.size - d.pos ≤ f := by
  have hd := (readRows_data f).1 c v d h
  have hp := (readValue_progress f).1 c v d h
  rw [hd]; omega

/-- **One octet of the budget is spent by the value reader's own constructor**, which is what makes the
item loop's tail bound one tighter than the loop's. -/
theorem bound_tail_lt {f : Nat} {c d : Cursor} {v : Value}
    (h : readValue f c = .ok (v, d)) (hb : c.data.size - c.pos ≤ f) :
    d.data.size - d.pos ≤ f - 1 := by
  have hf : 1 ≤ f := by
    cases f with
    | zero => simp only [readValue] at h; exact absurd h (by simp)
    | succ k => omega
  have hd := (readRows_data f).1 c v d h
  have hp := readValue_lt hf h
  rw [hd]; omega

/-- The element read's budget, which the element loop's count induction passes on. -/
theorem bound_tail_element {f : Nat} {ed : Option EncodingDecl} {c d : Cursor} {v : Value}
    (h : specElementData f ed c = .ok (v, d)) (hb : c.data.size - c.pos ≤ f) :
    d.data.size - d.pos ≤ f := by
  have hd := specElementData_data f ed c v d h
  have hp := specElementData_progress f ed c v d h
  rw [hd]; omega

/-- **An element declaration set whose rows carry a width.** The declared surface's rows below the
fixed category are one and four octets wide, and a zero-width header would leave the two fuels' item
loops reached with nothing spent — which is why the element clauses carry this rather than a bare
`Option EncodingDecl`. -/
def WideOption (ed : Option EncodingDecl) : Prop :=
  ∀ decl : EncodingDecl, ed = some decl → decl.category ≠ Generated.Oasis.Category.fixed →
    1 ≤ decl.width

/-- **Every reader in the value cluster agrees with itself across fuels above the octet bound**, at
one fuel. Six clauses rather than one, because the readers are mutually recursive and their
guard-free forms are false at the boundary: the item loop refuses at fuel zero and accepts at fuel one
with a zero count, so its clause is stated from fuel one, and the compound and array readers need a
header wide enough to spend the octet that puts their item loops a level down. -/
structure FuelIrrelevant (f : Nat) : Prop where
  value : ∀ (f' : Nat), f ≤ f' → ∀ (c : Cursor), c.data.size - c.pos ≤ f →
    AnswerAgrees (readValue f c) (readValue f' c)
  items : ∀ (f' : Nat), f ≤ f' → 1 ≤ f → ∀ (count : Nat) (c : Cursor),
    c.data.size - c.pos ≤ f - 1 → AnswerAgrees (readItems f count c) (readItems f' count c)
  compound : ∀ (f' : Nat), f ≤ f' → ∀ (decl : EncodingDecl) (c : Cursor), 1 ≤ decl.width →
    c.data.size - c.pos ≤ f → AnswerAgrees (readCompound f decl c) (readCompound f' decl c)
  array : ∀ (f' : Nat), f ≤ f' → ∀ (decl : EncodingDecl) (c : Cursor), 1 ≤ decl.width →
    c.data.size - c.pos ≤ f → AnswerAgrees (readArrayData f decl c) (readArrayData f' decl c)
  element : ∀ (f' : Nat), f ≤ f' → ∀ (ed : Option EncodingDecl) (c : Cursor), WideOption ed →
    c.data.size - c.pos ≤ f → AnswerAgrees (specElementData f ed c) (specElementData f' ed c)
  elementLoop : ∀ (f' : Nat), f ≤ f' → ∀ (ed : Option EncodingDecl) (count : Nat) (c : Cursor),
    WideOption ed → c.data.size - c.pos ≤ f →
    AnswerAgrees (readElementsLoop f ed count c) (readElementsLoop f' ed count c)


/-- The invariant at every fuel up to `n`. A clause is read at the fuel below when a reader descends
into a container two levels down, so the step has to reach every lower level, not only its own. -/
def FuelIrrelevantUpTo (n : Nat) : Prop := ∀ k, k ≤ n → FuelIrrelevant k

set_option maxRecDepth 10000 in
/-- **The declared surface's rows below the fixed category carry a width.** One finite evaluation of
the table itself, asked of every octet there is. -/
theorem dataDecl_rows_wide :
    (List.range 256).all (fun n =>
      match (SpecAMQP.Spec.Codec.dataDecl (UInt8.ofNat n)).toOption with
      | some d => (match d.category with
        | Generated.Oasis.Category.fixed => true
        | _ => decide (1 ≤ d.width))
      | none => true) = true := by
  decide

set_option maxRecDepth 10000 in
/-- The same for the element-constructor lookup, which reads the same table. -/
theorem elementDecl_rows_wide :
    (List.range 256).all (fun n =>
      match (SpecAMQP.Spec.Codec.elementDecl? (UInt8.ofNat n)).toOption with
      | some (some d) => (match d.category with
        | Generated.Oasis.Category.fixed => true
        | _ => decide (1 ≤ d.width))
      | _ => true) = true := by
  decide

/-- **The declared surface's rows below the fixed category carry a width**, read off the sweep at one
octet: the compound, array and variable rows are one and four octets wide, and a zero-width header
would leave the item loop reached with nothing spent. -/
theorem width_of_dataDecl {code : UInt8} {decl : EncodingDecl}
    (hd : SpecAMQP.Spec.Codec.dataDecl code = .ok decl)
    (hc : decl.category ≠ Generated.Oasis.Category.fixed) : 1 ≤ decl.width := by
  have hmem := List.all_eq_true.mp dataDecl_rows_wide code.toNat
    (List.mem_range.mpr code.toNat_lt)
  rw [show UInt8.ofNat code.toNat = code from by simp [UInt8.ofNat_toNat]] at hmem
  rw [hd] at hmem
  simp only [Except.toOption] at hmem
  cases hcat : decl.category with
  | fixed => exact absurd hcat hc
  | «variable» => exact of_decide_eq_true hmem
  | compound => exact of_decide_eq_true hmem
  | array => exact of_decide_eq_true hmem

/-- The same read off `elementDecl?`: an array's element constructor names a row of the same table. -/
theorem wideOption_of_elementDecl {ctor : UInt8} {ed : Option EncodingDecl}
    (h : SpecAMQP.Spec.Codec.elementDecl? ctor = .ok ed) : WideOption ed := by
  intro decl heq hc
  have hmem := List.all_eq_true.mp elementDecl_rows_wide ctor.toNat
    (List.mem_range.mpr ctor.toNat_lt)
  rw [show UInt8.ofNat ctor.toNat = ctor from by simp [UInt8.ofNat_toNat]] at hmem
  rw [h] at hmem
  simp only [Except.toOption, heq] at hmem
  cases hcat : decl.category with
  | fixed => exact absurd hcat hc
  | «variable» => exact of_decide_eq_true hmem
  | compound => exact of_decide_eq_true hmem
  | array => exact of_decide_eq_true hmem

/-- **Every reader in the value cluster answers the same way at every fuel above the octet bound.**

The proof is one induction over the fuel, and each level's six clauses are proved in dependency order,
because the readers are one `mutual` block and two of the dependences stay *inside* a level: the
compound reader reads its items at its own fuel, and the element loop reads the element decision at
its own fuel too. Everything else descends a level, which is why the induction hypothesis has to be
the family at every fuel below rather than the last one. -/
theorem fuelIrrelevantUpTo_all : ∀ n : Nat, FuelIrrelevantUpTo n := by
  intro n
  induction n with
  | zero =>
    have hVal0 : ∀ (f' : Nat), 0 ≤ f' → ∀ (c : Cursor), c.data.size - c.pos ≤ 0 →
        AnswerAgrees (readValue 0 c) (readValue f' c) := by
      intro f' _ c hb
      have hle : c.data.size ≤ c.pos := by omega
      cases f' with
      | zero => exact answerAgrees_refl _
      | succ m =>
        have h0 : readValue 0 c = .error (SpecAMQP.Spec.Codec.refusal "truncated"
            "the input ends before the value does") := by simp only [readValue]
        cases hu : takeU8 c with
        | error r =>
          have h1 : readValue (m + 1) c = .error r := by
            simp only [readValue, hu, except_bind_error]
          have hcl := spec_takeU8_error_class hu
          rw [h0, h1]
          exact ⟨fun a ha => absurd ha (by simp),
            fun r₀ hr₀ => ⟨r, rfl, by rw [← Except.error.inj hr₀]; exact hcl.symm⟩⟩
        | ok p => obtain ⟨b, d⟩ := p; exact absurd (spec_takeU8_lt hu) (by omega)
    have hIt0 : ∀ (f' : Nat), 0 ≤ f' → 1 ≤ 0 → ∀ (count : Nat) (c : Cursor),
        c.data.size - c.pos ≤ 0 - 1 →
        AnswerAgrees (readItems 0 count c) (readItems f' count c) := by
      intro f' _ h1
      exact absurd h1 (by omega)
    have hComp0 : ∀ (f' : Nat), 0 ≤ f' → ∀ (decl : EncodingDecl) (c : Cursor), 1 ≤ decl.width →
        c.data.size - c.pos ≤ 0 →
        AnswerAgrees (readCompound 0 decl c) (readCompound f' decl c) := by
      intro f' _ decl c hw hb
      have hle : c.data.size ≤ c.pos := by omega
      have h0 := spec_readCompound_header (fuel := 0) hw c hle
      cases f' with
      | zero => exact answerAgrees_refl _
      | succ m =>
        rw [h0, spec_readCompound_header (fuel := m + 1) hw c hle]
        exact answerAgrees_refl _
    have hArr0 : ∀ (f' : Nat), 0 ≤ f' → ∀ (decl : EncodingDecl) (c : Cursor), 1 ≤ decl.width →
        c.data.size - c.pos ≤ 0 →
        AnswerAgrees (readArrayData 0 decl c) (readArrayData f' decl c) := by
      intro f' _ decl c hw hb
      have hle : c.data.size ≤ c.pos := by omega
      cases f' with
      | zero => exact answerAgrees_refl _
      | succ m =>
        have h0 : readArrayData 0 decl c = .error (SpecAMQP.Spec.Codec.refusal "truncated"
            "the input ends before the array does") := by simp only [readArrayData]
        cases h1 : takeBe decl.width c with
        | error r =>
          have h1' : readArrayData (m + 1) decl c = .error r := by
            simp only [readArrayData, h1, except_bind_error]
          have hcl := spec_takeBe_error_class h1
          rw [h0, h1']
          exact ⟨fun a ha => absurd ha (by simp),
            fun r₀ hr₀ => ⟨r, rfl, by rw [← Except.error.inj hr₀]; exact hcl.symm⟩⟩
        | ok p => obtain ⟨size, c₁⟩ := p; rw [spec_takeBe_exhausted hw hle] at h1; exact absurd h1 (by simp)
    have hEl0 : ∀ (f' : Nat), 0 ≤ f' → ∀ (ed : Option EncodingDecl) (c : Cursor), WideOption ed →
        c.data.size - c.pos ≤ 0 →
        AnswerAgrees (specElementData 0 ed c) (specElementData f' ed c) := by
      intro f' _ ed c hw hb
      have hle : c.data.size ≤ c.pos := by omega
      cases f' with
      | zero => exact answerAgrees_refl _
      | succ m =>
        cases hed : ed with
        | none =>
          simp only [specElementData]
          exact answerAgrees_bind_error (hVal0 (m + 1) (Nat.zero_le (m + 1)) c (by omega))
            (fun a ha => by simp only [readValue] at ha; exact absurd ha (by simp)) _ _
        | some decl =>
          simp only [specElementData]
          cases hcat : decl.category with
          | fixed => exact answerAgrees_refl _
          | «variable» => exact answerAgrees_refl _
          | compound =>
            exact hComp0 (m + 1) (Nat.zero_le (m + 1)) decl c
              (hw decl hed (by rw [hcat]; simp)) (by omega)
          | array =>
            exact hArr0 (m + 1) (Nat.zero_le (m + 1)) decl c
              (hw decl hed (by rw [hcat]; simp)) (by omega)
    have hElLoop0 : ∀ (f' : Nat), 0 ≤ f' → ∀ (ed : Option EncodingDecl) (count : Nat) (c : Cursor),
        WideOption ed → c.data.size - c.pos ≤ 0 →
        AnswerAgrees (readElementsLoop 0 ed count c) (readElementsLoop f' ed count c) := by
      intro f' _ ed count
      cases f' with
      | zero => intro c hw hb; exact answerAgrees_refl _
      | succ m =>
       induction count with
       | zero => intro c hw hb; simp only [readElementsLoop]; exact answerAgrees_refl _
       | succ k ihk =>
        intro c hw hb
        rw [specElementData_loop, specElementData_loop]
        refine answerAgrees_bind₂ (hEl0 (m + 1) (Nat.zero_le (m + 1)) ed c hw hb) ?_
        intro p hrd
        obtain ⟨a, d⟩ := p
        dsimp only at hrd ⊢
        exact answerAgrees_bind (ihk d hw (bound_tail_element hrd (by omega))) _
    have hLvl : FuelIrrelevant 0 := ⟨hVal0, hIt0, hComp0, hArr0, hEl0, hElLoop0⟩
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    exact hLvl
  | succ n ih =>
    have hVal : ∀ (f' : Nat), n + 1 ≤ f' → ∀ (c : Cursor), c.data.size - c.pos ≤ n + 1 →
        AnswerAgrees (readValue (n + 1) c) (readValue f' c) := by
      intro f' hf' c hb
      obtain ⟨m, rfl⟩ : ∃ m, f' = m + 1 := ⟨f' - 1, by omega⟩
      have hm : n ≤ m := by omega
      cases hu : takeU8 c with
      | error r => simp only [readValue, hu, except_bind_error]; exact answerAgrees_refl _
      | ok p =>
        obtain ⟨code, c₁⟩ := p
        have hc1d : c₁.data = c.data := spec_takeU8_data hu
        have hc1p : c₁.pos = c.pos + 1 := spec_takeU8_pos hu
        have hb1 : c₁.data.size - c₁.pos ≤ n := by rw [hc1d, hc1p]; omega
        simp only [readValue, hu, except_bind_ok]
        split
        all_goals first
          | (refine answerAgrees_bind₂ ((ih n le_rfl).value m hm c₁ hb1) ?_
             intro p hrd
             obtain ⟨a, d⟩ := p
             dsimp only at hrd ⊢
             exact answerAgrees_bind ((ih n le_rfl).value m hm d (bound_tail_value hrd hb1)) _)
          | exact answerAgrees_refl _
          | (cases hd : SpecAMQP.Spec.Codec.dataDecl code with
             | error r => exact answerAgrees_refl _
             | ok decl =>
               cases hcat : decl.category with
               | fixed => simp only [except_bind_ok, hcat]; exact answerAgrees_refl _
               | «variable» =>
                 simp only [except_bind_ok, hcat]; exact answerAgrees_refl _
               | compound =>
                 simp only [except_bind_ok, hcat]
                 exact (ih n le_rfl).compound m hm decl c₁
                   (width_of_dataDecl hd (by rw [hcat]; simp)) hb1
               | array =>
                 simp only [except_bind_ok, hcat]
                 exact (ih n le_rfl).array m hm decl c₁
                   (width_of_dataDecl hd (by rw [hcat]; simp)) hb1)
    have hIt : ∀ (f' : Nat), n + 1 ≤ f' → 1 ≤ n + 1 → ∀ (count : Nat) (c : Cursor),
        c.data.size - c.pos ≤ (n + 1) - 1 →
        AnswerAgrees (readItems (n + 1) count c) (readItems f' count c) := by
      intro f' hf' _ count c hb
      obtain ⟨m, rfl⟩ : ∃ m, f' = m + 1 := ⟨f' - 1, by omega⟩
      have hm : n ≤ m := by omega
      cases count with
      | zero => simp only [readItems]; exact answerAgrees_refl _
      | succ k =>
        cases n with
        | zero =>
          -- the item read at this level is the value reader at fuel zero, which refuses outright
          simp only [readItems]
          have hb0 : c.data.size - c.pos ≤ 0 := by simpa using hb
          refine answerAgrees_bind_error ((ih 0 (Nat.zero_le 0)).value m (Nat.zero_le m) c hb0) ?_ _ _
          intro a ha
          simp only [readValue] at ha
          exact absurd ha (by simp)
        | succ n' =>
          simp only [readItems]
          refine answerAgrees_bind₂ ((ih (n' + 1) (by omega)).value m (by omega) c (by omega)) ?_
          intro p hrd
          obtain ⟨a, d⟩ := p
          dsimp only at hrd ⊢
          exact answerAgrees_bind ((ih (n' + 1) (by omega)).items m (by omega) (by omega) k d
            (bound_tail_lt hrd (by omega))) _
    have hComp : ∀ (f' : Nat), n + 1 ≤ f' → ∀ (decl : EncodingDecl) (c : Cursor), 1 ≤ decl.width →
        c.data.size - c.pos ≤ n + 1 →
        AnswerAgrees (readCompound (n + 1) decl c) (readCompound f' decl c) := by
      intro f' hf' decl c hw hb
      obtain ⟨m, rfl⟩ : ∃ m, f' = m + 1 := ⟨f' - 1, by omega⟩
      have hm : n ≤ m := by omega
      cases h1 : takeBe decl.width c with
      | error r => simp only [readCompound, h1, except_bind_error]; exact answerAgrees_refl _
      | ok p =>
        obtain ⟨size, c₁⟩ := p
        cases h2 : takeBe decl.width c₁ with
        | error r =>
          simp only [readCompound, h1, h2, except_bind_ok, except_bind_error]
          exact answerAgrees_refl _
        | ok q =>
          obtain ⟨count, c₂⟩ := q
          have hb2 : c₂.data.size - c₂.pos ≤ (n + 1) - 1 := by
            rw [spec_takeBe_data h2, spec_takeBe_data h1]
            have p1 := takeBe_advances decl.width c size c₁ h1
            have p2 := takeBe_advances decl.width c₁ count c₂ h2
            omega
          simp only [readCompound, h1, h2, except_bind_ok]
          split
          all_goals first
            | (refine answerAgrees_bind (hIt (m + 1) (by omega) (by omega) count c₂ hb2) _)
            | (split
               all_goals first
                 | (refine answerAgrees_bind (hIt (m + 1) (by omega) (by omega) count c₂ hb2) _)
                 | exact answerAgrees_refl _)
            | exact answerAgrees_refl _
    have hArr : ∀ (f' : Nat), n + 1 ≤ f' → ∀ (decl : EncodingDecl) (c : Cursor), 1 ≤ decl.width →
        c.data.size - c.pos ≤ n + 1 →
        AnswerAgrees (readArrayData (n + 1) decl c) (readArrayData f' decl c) := by
      intro f' hf' decl c hw hb
      obtain ⟨m, rfl⟩ : ∃ m, f' = m + 1 := ⟨f' - 1, by omega⟩
      have hm : n ≤ m := by omega
      cases h1 : takeBe decl.width c with
      | error r => simp only [readArrayData, h1, except_bind_error]; exact answerAgrees_refl _
      | ok p =>
        obtain ⟨size, c₁⟩ := p
        cases h2 : takeBe decl.width c₁ with
        | error r =>
          simp only [readArrayData, h1, h2, except_bind_ok, except_bind_error]
          exact answerAgrees_refl _
        | ok q =>
          obtain ⟨count, c₂⟩ := q
          simp only [readArrayData, h1, h2, except_bind_ok]
          split
          · all_goals exact answerAgrees_refl _
          · cases h3 : takeU8 c₂ with
            | error r =>
              simp only [except_bind_error]
              exact answerAgrees_refl _
            | ok p3 =>
              obtain ⟨ctor, c₃⟩ := p3
              cases h4 : elementDecl? ctor with
              | error r =>
                simp only [h4, except_bind_ok, except_bind_error]
                exact answerAgrees_refl _
              | ok ed =>
                simp only [h4, except_bind_ok]
                have hp3 := spec_takeU8_pos h3
                have hle3 := spec_takeU8_next_le h3
                have hp1 := takeBe_advances decl.width c size c₁ h1
                have hp2 := takeBe_advances decl.width c₁ count c₂ h2
                have hdd : c₃.data.size = c.data.size := by
                  rw [spec_takeU8_data h3, spec_takeBe_data h2, spec_takeBe_data h1]
                have hge : 2 ≤ n := by omega
                obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
                obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
                simp only [readElements]
                refine answerAgrees_bind ((ih n' (by omega)).elementLoop m' (by omega) ed count c₃
                  (wideOption_of_elementDecl h4) (by omega)) _
    have hEl : ∀ (f' : Nat), n + 1 ≤ f' → ∀ (ed : Option EncodingDecl) (c : Cursor), WideOption ed →
        c.data.size - c.pos ≤ n + 1 →
        AnswerAgrees (specElementData (n + 1) ed c) (specElementData f' ed c) := by
      intro f' hf' ed c hw hb
      obtain ⟨m, rfl⟩ : ∃ m, f' = m + 1 := ⟨f' - 1, by omega⟩
      have hm : n ≤ m := by omega
      cases hed : ed with
      | none =>
        simp only [specElementData]
        refine answerAgrees_bind₂ (hVal (m + 1) (by omega) c hb) ?_
        intro p hrd
        obtain ⟨a, d⟩ := p
        dsimp only at hrd ⊢
        exact answerAgrees_bind (hVal (m + 1) (by omega) d (bound_tail_value hrd hb)) _
      | some decl =>
        simp only [specElementData]
        cases hcat : decl.category with
        | fixed => exact answerAgrees_refl _
        | «variable» => exact answerAgrees_refl _
        | compound =>
          exact hComp (m + 1) (by omega) decl c (hw decl hed (by rw [hcat]; simp)) hb
        | array =>
          exact hArr (m + 1) (by omega) decl c (hw decl hed (by rw [hcat]; simp)) hb
    have hElLoop : ∀ (f' : Nat), n + 1 ≤ f' → ∀ (ed : Option EncodingDecl) (count : Nat) (c : Cursor),
        WideOption ed → c.data.size - c.pos ≤ n + 1 →
        AnswerAgrees (readElementsLoop (n + 1) ed count c) (readElementsLoop f' ed count c) := by
      intro f' hf' ed count
      obtain ⟨m, rfl⟩ : ∃ m, f' = m + 1 := ⟨f' - 1, by omega⟩
      induction count with
      | zero => intro c hw hb; simp only [readElementsLoop]; exact answerAgrees_refl _
      | succ k ihk =>
        intro c hw hb
        rw [specElementData_loop, specElementData_loop]
        refine answerAgrees_bind₂ (hEl (m + 1) (by omega) ed c hw hb) ?_
        intro p hrd
        obtain ⟨a, d⟩ := p
        dsimp only at hrd ⊢
        exact answerAgrees_bind (ihk d hw (bound_tail_element hrd hb)) _
    have hLvl : FuelIrrelevant (n + 1) := ⟨hVal, hIt, hComp, hArr, hEl, hElLoop⟩
    intro k hk
    by_cases hkn : k ≤ n
    · exact ih k hkn
    · have hk1 : k = n + 1 := by omega
      subst hk1
      exact hLvl

/-- The level family holds at every fuel. -/
theorem fuelIrrelevant_all (f : Nat) : FuelIrrelevant f := fuelIrrelevantUpTo_all f f le_rfl

/-- **The specification's value reader answers the same at every fuel above the octet bound.** -/
theorem readValue_irrel {f f' : Nat} (hle : f ≤ f') {c : Cursor} (hb : c.data.size - c.pos ≤ f) :
    AnswerAgrees (readValue f c) (readValue f' c) :=
  (fuelIrrelevant_all f).value f' hle c hb

/-- **The item loop, from fuel one** at a cursor whose octets the fuel covers one below itself. -/
theorem readItems_irrel {f f' : Nat} (hle : f ≤ f') (hf : 1 ≤ f) {count : Nat} {c : Cursor}
    (hb : c.data.size - c.pos ≤ f - 1) :
    AnswerAgrees (readItems f count c) (readItems f' count c) :=
  (fuelIrrelevant_all f).items f' hle hf count c hb

/-- **The compound reader**, whose header the width guard makes spend octets. -/
theorem readCompound_irrel {f f' : Nat} (hle : f ≤ f') {decl : EncodingDecl} {c : Cursor}
    (hw : 1 ≤ decl.width) (hb : c.data.size - c.pos ≤ f) :
    AnswerAgrees (readCompound f decl c) (readCompound f' decl c) :=
  (fuelIrrelevant_all f).compound f' hle decl c hw hb

/-- The array reader, the same clause. -/
theorem readArrayData_irrel {f f' : Nat} (hle : f ≤ f') {decl : EncodingDecl} {c : Cursor}
    (hw : 1 ≤ decl.width) (hb : c.data.size - c.pos ≤ f) :
    AnswerAgrees (readArrayData f decl c) (readArrayData f' decl c) :=
  (fuelIrrelevant_all f).array f' hle decl c hw hb

/-- The element decision. -/
theorem specElementData_irrel {f f' : Nat} (hle : f ≤ f') {ed : Option EncodingDecl} {c : Cursor}
    (hw : WideOption ed) (hb : c.data.size - c.pos ≤ f) :
    AnswerAgrees (specElementData f ed c) (specElementData f' ed c) :=
  (fuelIrrelevant_all f).element f' hle ed c hw hb

/-- The element loop. -/
theorem readElementsLoop_irrel {f f' : Nat} (hle : f ≤ f') {ed : Option EncodingDecl}
    {count : Nat} {c : Cursor} (hw : WideOption ed) (hb : c.data.size - c.pos ≤ f) :
    AnswerAgrees (readElementsLoop f ed count c) (readElementsLoop f' ed count c) :=
  (fuelIrrelevant_all f).elementLoop f' hle ed count c hw hb

end SpecAMQP.Proofs
