import Spec.Codec
/-!
# Laws about the reader, stated beside the reader

`Spec/Codec.lean` defines the reader and the writer; this module states the facts about
the reader that the round-trip proofs need and that the codec itself has no reason to
name. They are theorems, and they change no definition: the codec's behaviour is fixed in
the module they are about.

The two facts belong together and are what a composition site wants. The first identifies
the octets a reader consumes with a slice of the buffer it read them from — the reader
takes a field by `Array.extract`, the writer's output is a list, and a proof about the
*value* of the field wants the list. The second is the value itself: the reader's fold of
those octets is the big-endian fold of the writer's octets, with the cursor advance
included, so the composition is arithmetic on octets rather than array bookkeeping.

Neither carries a precondition beyond what the cursor already guarantees. `List.extract`
is *defined* as `drop`/`take` — it is an abbreviation, and `List.extract_eq_take_drop` is
`rfl` — so the slice identity holds with no side condition at all: `Array.extract` clamps
its `stop` and `take` saturates, and both sides saturate at the same end of the same list,
which is why the checked offset the reader carries is not needed to state it. The value
law does use that check, because `takeBe` refuses rather than truncating when the field is
not there; `takeBytes`' success is what removes the refusal branch and fixes the cursor's
position at `pos + width`.
-/
namespace SpecAMQP.Spec.ReadLaws

open SpecAMQP.Harness (Octets)
open SpecAMQP.Spec.Codec

/-- The reader's big-endian fold of a list of octets: the accumulator every fixed-width
integer case reduces to, named so a statement about `takeBe` can be read as arithmetic on
octets. -/
def beValue (bytes : List UInt8) : Nat :=
  bytes.foldl (fun acc byte => acc * 256 + byte.toNat) 0

/-- **The octets a reader consumes are a slice of the buffer it consumes them from.**

`takeBytes` takes a field with `Array.extract`, and the writer's output is a list, so this
is the bridge between the two vocabularies: the octets the reader has in hand are
`(buffer.toList.drop pos).take width`, exactly the slice a proof about the writer's own
list of octets can talk about.

No precondition: `List.extract` is an abbreviation for `drop`/`take`
(`List.extract_eq_take_drop` is `rfl`), and saturation at the end of the buffer happens on
both sides at the same place. -/
theorem extract_toList_eq_drop_take (buffer : Octets) (pos width : Nat) :
    (buffer.extract pos (pos + width)).toList = (buffer.toList.drop pos).take width := by
  simp [Array.toList_extract]

/-- **Reading a big-endian field back.**

At an offset where `width` octets are present, `takeBe` returns the big-endian fold of
exactly those octets — written as the `drop`/`take` slice of the buffer's list that the
writer's output corresponds to — and the cursor it returns sits at the end of the field.
After this, a fixed-width case is arithmetic on octets: no branch, no refusal, no offset
arithmetic, and no `Array` slice left to reason about. -/
theorem takeBe_eq_fold (width : Nat) (c : Cursor) (h : c.pos + width ≤ c.data.size) :
    takeBe width c =
      .ok (beValue ((c.data.toList.drop c.pos).take width),
           (⟨c.data, c.pos + width⟩ : Cursor)) := by
  have hbytes : takeBytes width c
      = .ok (c.data.extract c.pos (c.pos + width), (⟨c.data, c.pos + width⟩ : Cursor)) := by
    simp [takeBytes, h]
  have hoctets : takeBe width c
      = .ok (beValue ((c.data.extract c.pos (c.pos + width)).toList),
             (⟨c.data, c.pos + width⟩ : Cursor)) := by
    unfold takeBe beValue
    rw [hbytes]
    show Except.ok ((Array.foldl (fun acc byte => acc * 256 + byte.toNat) 0
            (c.data.extract c.pos (c.pos + width)),
            (⟨c.data, c.pos + width⟩ : Cursor)))
          = Except.ok (((c.data.extract c.pos (c.pos + width)).toList).foldl
              (fun acc byte => acc * 256 + byte.toNat) 0,
            (⟨c.data, c.pos + width⟩ : Cursor))
    rw [← Array.foldl_toList]
  rw [hoctets, extract_toList_eq_drop_take]

end SpecAMQP.Spec.ReadLaws
