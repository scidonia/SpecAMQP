import Proofs.CodecRoundTripCompound

/-!
# The value codec's round trip: R4, described values

The three rungs below this one prove framings around *octets*: R1 a fixed-width field, R2 a
length prefix, R3 a size and a count. A described value is a framing around *two values* —
the writer emits the descriptor prefix, the descriptor's own encoding, then the value's
encoding, and the reader reads the first value back and then the second. So R4's proof is a
*composition* of two applications of a lower rung rather than a new kind of reasoning, and
the composition is where its work is.

## What is proved

* `descriptorPrefix_length` — the framing's own overhead is one octet.
* `described_overhead` — the framed octets are that one octet plus the two encodings,
  unchanged.
* `writeValue_described` — the writer's described case in closed form: given the
  descriptor's and the value's own encodings, the described value's octets are the prefix
  followed by those two, in that order. It is the framing half of the composition; the
  values inside it are what the lower rungs (or this rung) supply.

**The choice rule takes no new instance here.** R2 named the narrow/wide decision and R3
generalised it as `widthChoice` over the quantities a field carries. A described value's
framing carries no quantity at all — the prefix is one octet and the descriptor and value
bring their own encodings — so `widthChoice` is not consulted and this rung adds no
instance of it. That is worth stating rather than leaving implied, because a statement of
the form "the writer takes the narrowest form" would otherwise read as if it applied here.

## What is stated

`DescribedScalar` and `RoundTripDescribed`, the claim of this rung, over the
specification's own `encodeValue`/`decodeValue`.

**The descriptor read-back fact is shared, not duplicated.** The frame layer's contract
(`Contracts/FrameCodec.lean`) is stated over `∃ descriptor inner, frame.body = .described
descriptor inner`, and its descriptor statement is proved there: every frame the decoder
accepts carries a performative whose descriptor names a declared type with the frame type's
role. That is the same fact this rung's claim supplies for descriptors — what a described
value's descriptor reads back as — so the two are one fact with two consumers, and this
module states it rather than proving a second version of it.

**The fuel accounting is still the structural gap.** `readValue` enters with the octet
count as the budget; at a described value it spends one octet on the prefix and then reads
the descriptor and the value at the *same* remaining fuel. As in R3, a statement at entry
fuel therefore says nothing directly usable about either inner value, and this rung records
the accounting as an obligation instead of assuming the entry budget reaches them.

## What is stated but not yet proved

`RoundTripDescribed`. What remains is: that the prefix octet classifies as `.descriptor`
(the table's own fact, from `Spec.Value.classify` and the generated range); that
`takeBytes`-style consumption of that octet leaves the cursor where the descriptor's
encoding begins; and the composition itself, in which the descriptor's round trip and the
inner value's are used as hypotheses at the fuel the descent supplies — the same
accounting R3 recorded, one level further in.
-/
namespace SpecAMQP.Proofs

open SpecAMQP.Spec.Codec
open SpecAMQP.Spec.ReadLaws
open SpecAMQP.Harness (Octets)

/-! ## The framing, in closed form -/

/-- The framing's own overhead is one octet: the descriptor prefix, which is what tells the
reader that a descriptor follows rather than a constructor. -/
theorem descriptorPrefix_length : ([descriptorPrefix] : List UInt8).length = 1 := by
  simp [descriptorPrefix]

/-- The described framing carries two encodings and one prefix octet, with nothing
inserted between them: the octets of a described value are the prefix, the descriptor's
octets and the value's octets, in that order. This is why the framing needs no width
decision — there is no quantity in it for a field to carry. -/
theorem described_overhead (head tail : List UInt8) :
    ([descriptorPrefix] ++ head ++ tail).length = 1 + head.length + tail.length := by
  simp [List.length_append] <;> omega

/-- **The writer's described case, in closed form.** Given the descriptor's own encoding
and the value's, the described value's octets are the prefix followed by those two. The
hypotheses are the two successes — which the lower rungs' claims are what establish — and
nothing here re-derives any of their reasoning. -/
theorem writeValue_described (descriptor inner : Value) (head tail : List UInt8)
    (hh : writeValue descriptor = .ok head) (ht : writeValue inner = .ok tail) :
    writeValue (.described descriptor inner) = .ok ([descriptorPrefix] ++ head ++ tail) := by
  simp only [writeValue, hh, ht]
  rfl

/-! ## The rung's claim -/

/-- The values R4 covers: a described value, whatever its descriptor and body are.

A *shape* predicate, not a restriction on what is inside: the descriptor and the value are
covered by whichever rung their own shape belongs to, which is what makes this claim a
composition rather than a case. -/
def DescribedScalar : Value → Prop
  | .described _ _ => True
  | _ => False

/-- **R4: described values round-trip.**

For every described value the writer encodes, the reader recovers that value from exactly
those octets and consumes the whole buffer. Its proof is two applications of a lower rung —
one for the descriptor, one for the value — plus the framing this module has proved the
shape of. -/
def RoundTripDescribed : Prop :=
  ∀ (value : Value) (bytes : Octets),
    DescribedScalar value → encodeValue value = .ok bytes →
      decodeValue bytes = .ok (value, bytes.size)

end SpecAMQP.Proofs
