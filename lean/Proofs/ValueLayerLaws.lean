import Contracts.Conformance
import Proofs.FrameConformance
import Proofs.FrameSendConformance
import Proofs.ValueWireAgreement

/-!
# The value layer's hypotheses, at the evidence

`Proofs.FrameConformance.ValueLayersAgree`, `Proofs.FrameSendConformance.ValueCarrierAgree` and
`Proofs.FrameSendConformance.ValueWriterAgree` are the three value-layer hypotheses the frame
layer's two `Conforms` instances rest on. This module asks what is provable about them, and the
answer is not the one the instances' prose hoped for: **`ValueWriterAgree` was false as stated and is
undecided now** — classing the reference's writer made a reachable refutation of it expressible, and the
fix that closed the hole it named withdrew the refutation and left a statement with no witness and no
available proof; **`ValueLayersAgree` is undecided for the same shape of reason**, its divergence having
been fixed earlier and its proof needing a value-layer instance that does not exist; and
**`ValueCarrierAgree` is untested here**.

## What the evidence says, statement by statement

* **`ValueLayersAgree` was false when this module was written, and is undecided now.** Its
  divergence was a check-order difference inside the map path: the specification reads a compound's
  `size` and `count` fields and asks whether the count is even *before* it reads the items, while the
  reference read the items, compared the declared size with what they measured, and asked about
  parity afterwards. Part 1 forbids an odd count outright ("Map encodings MUST contain an even
  number of items", `amqp-core-types-v1.0-os.xml` `…/type:map.1`), so `mapWitness` — odd count *and*
  a declared size that disagrees with its items — was the smallest buffer the two answered
  differently. `Ref.Value.readMap`'s parity guard has since moved ahead of the items read, so both
  now refuse it `malformed`; a sweep of 114,225 buffers (every length 1-3 buffer over a 45-octet
  alphabet, every length-4 buffer over a 12-octet alphabet, and a structured set of arrays,
  compounds and described values) now finds **no class divergence at all**. So the receive direction
  has no witness: a refutation is not provable because the divergence is gone, and a proof is not
  available here because it would need the value layer's own `Conforms` instance, which does not
  exist. That state is *undecided*, and this module leaves it there rather than writing either
  direction.
* **`ValueWriterAgree` was false, and this module carried the refutation; the hole that refuted it is
  closed, so the law is *undecided* now** — no witness, and no available proof either. Two families are
  worth separating, because they are different in kind and because one of them has been fixed.
  * *The ill-width family is out of the carrier's reach.* The reference's writer emits a raw payload at
    whatever width the value carries (`#[0x72] ++ payload`) while the specification's writer looks the
    width up in the declared surface and refuses a payload the type has no encoding for, so `.float #[]`
    has the reference write `#[0x72]` where the specification refuses. `valueOfJson` fixes that payload
    at four octets on the way in, so this family refutes the *every-related-pair* statement of this law
    rather than the one landed here; `bodiesAgree_floatEmpty` and its two companions are that
    measurement, and they are what narrowed the domain to `CarrierReachable`.
  * *The empty-array family was in the carrier's reach, and it was the refutation.* An array whose
    declared element constructor the grammar assigns no encoding, carrying **no elements**, was written
    by the reference and refused by the specification: `not_valueWriterAgree`, landed in the commit that
    classed the writer — which is what made it expressible — and **withdrawn by the fix that closed the
    hole**. `Ref.encode` now consults the array's declared constructor before its elements
    (`Ref.requireAssignedConstructor`), which is the check the specification makes through
    `elementDecl?`; a refutation of a defect that has been fixed argues for a world a later commit
    changed, so it is not kept standing. What remains of it is kept: the witness, the measurement, the
    class agreement it now shows (`arrayUnassignedEmpty_class_agrees`) and the general closure
    (`ref_encode_unassignedConstructor`) are all below.

    The mechanism, since it is why patch 3 missed it: `Ref.arrayElement`'s catch-all runs **once per
    element**, so an array with no elements never reached it and the declared constructor was never
    consulted at all. `.array 0x57 [.null]` refused correctly and `.array 0x57 []` did not — the same
    constructor, one element apart — and what the second wrote was four octets this module's own reader
    then refused.
  * *What blocks a proof is one thing now, and it is not a witness.* The **wide-form family** used to
    be the other: the reference wrote a four-octet size, count or length field through `u32be`, which
    truncates, where the specification's `filled`, `compoundOctets` and `arrayOctets` refuse `limit`
    for a field that cannot carry the value — so the first conjunct failed for a compound, a variable
    value or an array whose body reaches 2^32 octets. That input is representable in the corpus
    vocabulary (`ofHex` of a long enough string) and no term can carry it, so the law was *unprovable*
    there and *unrefutable* too. **That third check of the same family was made rather than reported:**
    every four-octet size, count and length field is written through `Ref.fieldOctets`, which refuses
    `limit` where it cannot announce the value, and the section at the end of this module carries the
    closure in general and states what it does to the first conjunct. What that leaves is the
    **traversal**: the two encoders were written independently, and relating them means a mutual
    induction over `encode`, `encodeAll`, `encodePairs`, `arrayElementItems` and `arrayElement` against
    `writeValue`, `writeItems`, `writePairs`, `writeElements`, `writeDeclared`, `writeCompoundData` and
    `writeArrayData`, with a table reduction (`rowOf`, `tagOf`, `elementDecl?`, `filled`,
    `lengthPrefixed`, `twosComplement`) per shape and a constructor-by-constructor correspondence on the
    element forms. That is the shape of `Proofs.ValueWireAgreement` for the readers, and its size is the
    size to expect.
* **`ValueCarrierAgree` is untouched here**: it is a claim about the two corpus-vocabulary readers
  (`Spec.Codec.valueOfJson` against `Ref.Vectors.valueOfJson`), not about the wire, and this module
  has no evidence against it.
* **The send *endpoint*'s consequent was refutable before patch 3, and is undecided now — and the
  search that says so is stated here rather than assumed.** The record this bullet used to carry said
  the negation was *expressible and untried*: the reference's writer answered `Except String Octets`,
  its class could only be recovered by `Ref.Frame.classOf` (a `String.splitOn ":"`), and the classing
  turned that into a field, so `¬ Conforms specFrameSend refFrameSend` could be written through a frame
  whose body is a described performative carrying the empty-array pair. The first half is right and the
  second is now stale: the pair it was expressible through — an array whose declared element constructor
  the grammar assigns no encoding — is alignment, not refutation, since the fix that closed the hole,
  and the class-family divergence that *was* the consequent's falsity (`.array 0x00 [null]` and
  `.array 0xE0 [null]`: `malformed` against `limit`, patch 3's own split) went with it. So there is a
  witness **or** there is not, and the two possibilities were told apart rather than left standing:
  **80,204 frame-encode inputs** — every one of the 256 array element constructors against a 113-item
  pool of in-range, out-of-range and mismatched shapes; the `0x00` descriptor, `0x40`/`0x41`/`0x42`
  zero-width, `0xC0`/`0xC1`/`0xD0`/`0xD1` compound and `0xE0`/`0xF0` array rows against the same pool;
  the array materialisation limit at 65535/65536/65537 elements; nesting depth 30–100; string, symbol
  and binary lengths 0–300 across the 255/256-octet form boundary; `doff` 0–256, `channel` 0–65536,
  both frame types, extended and payload combinations; and 16,000 seeded random values over the
  corpus grammar — draw **identical verdicts from both artefacts**, with no input on which the
  reference takes a step the specification does not permit and no input on which the two write different
  octets. The one asymmetry the sweep *does* find is a reader's, not the writers': the specification's
  corpus reader accepts a `timestamp` outside `[-2^63, 2^63-1]` where the reference's refuses it, and
  its own writer then refuses that value `limit` — a defect in the specification's reader rather than a
  divergence a `Conforms` refutation can use, since an input the reference's carrier refuses gives the
  reference no step to match. The nearest true statement where the refutation lived is therefore not a
  refutation but a family agreement, and it is landed below: `unassignedConstructor_class_agrees` —
  and the search's extent is the whole of the evidence that no witness exists, which is why it is a
  number with its families named rather than a claim.

## Where the class comparison now stands

The vocabulary that blocked the class-comparing statements has been removed on **both** sides. The
specification's class is a **field** (`Spec.Codec.Refusal.reasonClass`); the reference's *reader*
carries its class as a variant (`Ref.DecodeError`); and the reference's *writer* now answers with a
classed refusal of its own (`Ref.EncodeRefusal`, whose `reasonClass` is a field). So every class on
either side is a term, and the comparisons this module could only state over prose are goals a kernel
proof can carry. `bodiesAgree_floatEmpty`'s companions are one place that became possible, and the other
is `not_valueWriterAgree` — landed with the classing and withdrawn by the fix below, so what the new
vocabulary carries today is the same family as a *theorem* rather than a witness:
`ref_encode_unassignedConstructor` on the reference's side, `spec_encode_unassignedConstructor` on the
specification's, and `unassignedConstructor_class_agrees` for the pair — plus
`arrayUnassignedEmpty_class_agrees`, the one value the refutation used, and the zero-width and
four-octet families below.

**What classing the writer did *not* change, and the reason it is stated here.** `Ref.encode`'s refusal
messages are byte for byte what they were: the class is a field and the message still leads with it, so
`refusalText`-style rendering at the corpus boundary (`Ref.Vectors.refCodec`, `Ref.Message`) produces the
same string, and the corpus's own comparisons see exactly what they saw before. A class is what the law
compares and the sentence is what a human reads; a classed failure that dropped the sentence would keep
every gate green and make the reference worse to debug. `Ref.Frame.classOf` — the `String.splitOn ":"`
recovery — therefore has no caller any more, and it is kept and reported rather than deleted, because
whether the layer should still offer that recovery is a question about its surface.

The `splitOn` observation is kept because it is *why* the earlier refutation had to be written against
the first conjunct, and the next reader deserves to know that the limit was a type and not a taste:

  `example : ("a:b".splitOn ":") == ["a", "b"]` is closed by neither `decide`, `simp`, nor
  `with_unfolding_all decide`; only `native_decide`, which this repository does not use.

What this module lands, then, is the artefacts' answers for a witness, in each artefact's own terms:
the two readers' answers to `mapWitness`, the two writers' answers for the ill-width and
array-constructor families, the refutation of `ValueWriterAgree` at a value the corpus vocabulary
produces, and the reference's size accounting. Where a class-comparing statement follows from them it is
named in the docstring beside the fact, and where no witness exists it is named as undecided rather than
written.
-/

-- The cursor types carry no `DecidableEq`, because no proof has needed to compare cursors yet.
-- The walks below do, and these are proof-side instances: neither artefact changes.
deriving instance DecidableEq for SpecAMQP.Spec.Codec.Cursor
deriving instance DecidableEq for SpecAMQP.Ref.Cursor
deriving instance DecidableEq for SpecAMQP.Ref.DecodeError

namespace SpecAMQP.Proofs

open SpecAMQP.Contracts
open SpecAMQP.Harness (Octets)
open Lean (Json)


/-! ## The witness for the readers

`map8` (`%xC1`), its size field `%x03`, its count field `%x01`, then one `null` (`%x40`).

Two defects in one buffer, which is what made the readers' check order observable: the count is odd,
which Part 1 forbids, *and* the size field says three octets follow it while the count field and the
one item measure two. When the two readers ranked those checks differently this buffer was the
smallest witness of a class divergence (`sizeMismatch` against `malformed`); `Ref.Value.readMap` now
decides parity first, as `Spec.Codec` always has, so the two answers below agree. -/
def mapWitness : Octets := #[0xC1, 0x03, 0x01, 0x40]

theorem mapWitness_size : mapWitness.size = 4 := by decide

/-! ## The reference's reader, stepped

Each lemma walks one decision of `Ref.readValue` (or of the map path beneath it) with the branch
fact its caller supplies, which is how the repository's frame proofs walk a reader: the recursive
definition is unfolded once, the branch that the concrete octets select is reduced, and the
remaining work is the caller's hypotheses. -/

theorem ref_readValue_map (fuel : Nat) (c c' : SpecAMQP.Ref.Cursor)
    (h : SpecAMQP.Ref.takeU8 c = .ok (0xC1, c')) :
    SpecAMQP.Ref.readValue (fuel + 1) c = SpecAMQP.Ref.readMap fuel 1 c' := by
  unfold SpecAMQP.Ref.readValue
  try dsimp only []
  rw [h]
  try simp only [Bind.bind, Except.bind]
  try dsimp only []
  try (first | rfl | (split <;> first | rfl | simp_all))

theorem ref_readItems_nil (fuel : Nat) (c : SpecAMQP.Ref.Cursor) :
    SpecAMQP.Ref.readItems (fuel + 1) 0 c = .ok ([], c) := by
  unfold SpecAMQP.Ref.readItems
  try dsimp only []
  try (first | rfl | (split <;> first | rfl | simp_all))

/-- **The reference's map read up to its parity guard.** The count field alone decides whether the
items are read at all: an odd count is refused before `readItems` is reached and before the declared
size is compared. This is the order the specification has always had, and the order this reader now
shares with its own array path. -/
theorem ref_readMap_odd (fuel width : Nat) (c c₁ c₂ : SpecAMQP.Ref.Cursor)
    (size count : Nat)
    (h₁ : SpecAMQP.Ref.takeBeU width c = .ok (size, c₁))
    (h₂ : SpecAMQP.Ref.takeBeU width c₁ = .ok (count, c₂))
    (hodd : (count % 2 != 0) = true) :
    SpecAMQP.Ref.readMap (fuel + 1) width c =
      .error (.malformed "a map must have an even number of items") := by
  unfold SpecAMQP.Ref.readMap
  try dsimp only []
  rw [h₁]
  try simp only [Bind.bind, Except.bind]
  try dsimp only []
  rw [h₂]
  try dsimp only []
  rw [hodd]
  try dsimp only []
  try (first | rfl | (split <;> first | rfl | simp_all))

/-- **The reference's answer to the witness, now the aligned one**: the parity refusal, the same
class the specification names for the same buffer in `spec_mapWitness_decodeValue`. Before
`Ref.Value.readMap`'s parity guard was moved ahead of the items read this theorem read
`.error (.sizeMismatch "map" 3 2)`, and the two artefacts disagreed about the class. -/
theorem ref_mapWitness_decode :
    SpecAMQP.Ref.decode mapWitness = .error (.malformed "a map must have an even number of items") := by
  have hstep : SpecAMQP.Ref.readValue 4 { data := mapWitness, pos := 0 } =
      SpecAMQP.Ref.readMap 3 1 { data := mapWitness, pos := 1 } :=
    ref_readValue_map 3 _ _ (by decide)
  have hmap : SpecAMQP.Ref.readMap 3 1 { data := mapWitness, pos := 1 } =
      .error (.malformed "a map must have an even number of items") :=
    ref_readMap_odd (fuel := 2) (width := 1)
      (c := { data := mapWitness, pos := 1 }) (c₁ := { data := mapWitness, pos := 2 })
      (c₂ := { data := mapWitness, pos := 3 }) (size := 3) (count := 1)
      (by decide) (by decide) (by decide)
  unfold SpecAMQP.Ref.decode
  rw [mapWitness_size, hstep, hmap]
  try dsimp only []
  try (first | rfl | (split <;> first | rfl | simp_all))

/-! ## The specification's reader, stepped -/

/-- The specification's reader at a compound constructor: the octet is looked up in the declared
surface and the compound is read, with no branch on the count before the items. -/
theorem spec_readValue_compound (fuel : Nat) (c c' : SpecAMQP.Spec.Codec.Cursor)
    (code : UInt8) (decl : SpecAMQP.Generated.Oasis.EncodingDecl)
    (h : SpecAMQP.Spec.Codec.takeU8 c = .ok (code, c'))
    (hclass : SpecAMQP.Spec.Value.classify code.toNat =
      SpecAMQP.Spec.Value.Constructor.compound 1)
    (hdecl : SpecAMQP.Spec.Codec.dataDecl code = .ok decl)
    (hcat : decl.category = SpecAMQP.Generated.Oasis.Category.compound) :
    SpecAMQP.Spec.Codec.readValue (fuel + 1) c = SpecAMQP.Spec.Codec.readCompound fuel decl c' := by
  unfold SpecAMQP.Spec.Codec.readValue
  try dsimp only []
  rw [h]
  try simp only [Bind.bind, Except.bind]
  try dsimp only []
  rw [hclass]
  try dsimp only []
  rw [hdecl]
  try simp only [Bind.bind, Except.bind]
  try dsimp only []
  rw [hcat]
  try dsimp only []
  try (first | rfl | (split <;> first | rfl | simp_all))

/-- **The specification's map read**: the parity of the count is decided *before* the items are
read and before the declared size is compared, which is the other half of the divergence. -/
theorem spec_readCompound_map_odd (fuel : Nat) (decl : SpecAMQP.Generated.Oasis.EncodingDecl)
    (c c₁ c₂ : SpecAMQP.Spec.Codec.Cursor) (size count : Nat)
    (howner : decl.owner = "map")
    (h₁ : SpecAMQP.Spec.Codec.takeBe decl.width c = .ok (size, c₁))
    (h₂ : SpecAMQP.Spec.Codec.takeBe decl.width c₁ = .ok (count, c₂))
    (hodd : (count % 2 != 0) = true) :
    SpecAMQP.Spec.Codec.readCompound (fuel + 1) decl c =
      .error (SpecAMQP.Spec.Codec.refusal "malformed"
        s!"a map declares {count} item(s): keys and values come in pairs, so an odd count is not a map") := by
  unfold SpecAMQP.Spec.Codec.readCompound
  try dsimp only []
  rw [h₁]
  try simp only [Bind.bind, Except.bind]
  try dsimp only []
  rw [h₂]
  try dsimp only []
  rw [howner]
  try dsimp only []
  rw [hodd]
  try dsimp only []
  try (first | rfl | (split <;> first | rfl | simp_all))

/-- **The specification's answer to the witness**: the parity refusal, its class a field of the
`Spec.Codec.Refusal` this reader answers with (and its message that class, a colon and the prose).
The reference's answer to the same buffer is `ref_mapWitness_decode`'s, whose class is `.malformed` —
the same class, since `Ref.Value.readMap`'s parity guard now runs first, so the two answers agree
where they once disagreed. -/
theorem spec_mapWitness_decodeValue :
    SpecAMQP.Spec.Codec.decodeValue mapWitness =
      .error (SpecAMQP.Spec.Codec.refusal "malformed"
        "a map declares 1 item(s): keys and values come in pairs, so an odd count is not a map") := by
  have hrow : (SpecAMQP.Spec.Codec.dataDecl 0xC1).map
      (fun d => (d.owner, d.category, d.width)) =
      .ok ("map", SpecAMQP.Generated.Oasis.Category.compound, 1) := by decide
  cases hdecl : SpecAMQP.Spec.Codec.dataDecl 0xC1 with
  | error err => rw [hdecl] at hrow; cases hrow
  | ok decl =>
    rw [hdecl] at hrow
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at hrow
    obtain ⟨howner, hcat, hwidth⟩ := hrow
    have hstep : SpecAMQP.Spec.Codec.readValue 4 { data := mapWitness, pos := 0 } =
        SpecAMQP.Spec.Codec.readCompound 3 decl { data := mapWitness, pos := 1 } :=
      spec_readValue_compound (fuel := 3) (c := { data := mapWitness, pos := 0 })
        (c' := { data := mapWitness, pos := 1 }) (code := 0xC1) (decl := decl)
        (by decide) (by decide) hdecl hcat
    have hmap : SpecAMQP.Spec.Codec.readCompound 3 decl { data := mapWitness, pos := 1 } =
        .error (SpecAMQP.Spec.Codec.refusal "malformed"
          "a map declares 1 item(s): keys and values come in pairs, so an odd count is not a map") :=
      spec_readCompound_map_odd (fuel := 2) (decl := decl)
        (c := { data := mapWitness, pos := 1 }) (c₁ := { data := mapWitness, pos := 2 })
        (c₂ := { data := mapWitness, pos := 3 }) (size := 3) (count := 1)
        howner (by rw [hwidth]; decide) (by rw [hwidth]; decide) (by decide)
    unfold SpecAMQP.Spec.Codec.decodeValue
    rw [mapWitness_size, hstep, hmap]
    try dsimp only []
    try simp only [Except.error.injEq, SpecAMQP.Spec.Codec.refusal,
      SpecAMQP.Spec.Codec.refusalMessage]
    try decide

/-! ## The writer's witness

The reference's writer writes a fixed-width payload unchanged (`#[0x72] ++ payload`); the
specification's writer looks the payload's width up in the declared surface
(`rowOf "float" bits.size`) and refuses a width the surface does not declare. Values reach a writer
from a reader, so this witness is outside the corpus vocabulary — `valueOfJson` and `hexPayloadOf`
fix a `float`'s payload at four octets — and that is why these three theorems refute the
*every-related-pair* statement of `ValueWriterAgree` and not the one landed now: the domain is
`CarrierReachable`, and `.float #[]` is not in it. They are kept as the measurement that narrowed the
domain. The specification's refusal for this value leads with `limit` — it spelled the bare prose
until the classless refusals in `Spec/Codec.lean` were given their class, and that change moved this
theorem's message and nothing else in this module. The divergence that *is* in the carrier's reach is
the empty-array family, and it is landed with its refutation below. -/

theorem bodiesAgree_floatEmpty : BodiesAgree (.float #[]) (.float #[]) := by
  unfold BodiesAgree
  rfl

theorem ref_encode_floatEmpty : SpecAMQP.Ref.encode (.float #[]) = .ok #[0x72] := by
  unfold SpecAMQP.Ref.encode
  try dsimp only []
  try (first | rfl | (split <;> first | rfl | simp_all))
  try decide

theorem spec_encodeValue_floatEmpty :
    SpecAMQP.Spec.Codec.encodeValue (.float #[]) =
      .error (SpecAMQP.Spec.Codec.refusal "limit"
        "the declared surface has no float encoding of width 0") := by
  unfold SpecAMQP.Spec.Codec.encodeValue SpecAMQP.Spec.Codec.writeValue
    SpecAMQP.Spec.Codec.emitScalar SpecAMQP.Spec.Codec.rowOf
  try dsimp only []
  try (first | rfl | (split <;> first | rfl | simp_all))
  try decide

/-! ## The reachable writer divergence, at the answers

Both writers are asked for an array whose declared element constructor is `%x57` — an octet inside
the fixed-width range that the declared surface assigns no encoding — carrying one `null`. The
corpus vocabulary can produce that pair (`"constructor": "57"`), so this is a *reachable* pair, and
it is the one that mattered: the specification refused it `unassigned` while the reference's catch-all
said `limit`. `Ref.arrayElement`'s catch-all has since been split — `unassigned` where the surface
assigns the constructor no encoding, `malformed` where the value does not fit the constructor it does
assign — so the two now agree, and these two theorems are the pair that goes red if either side's
class is weakened rather than aligned. The specification's two *classless* refusals in this family
(`.array %x00 [x]` and `.array %xE0 [x]`) were given `malformed` in the same pass.

This check is reached once per element, which is the whole of the next section's subject: an array
whose element list is empty never reaches it. -/

theorem ref_encode_arrayUnassigned :
    SpecAMQP.Ref.encode (.array 0x57 [.null]) =
      .error (SpecAMQP.Ref.encodeRefusal "unassigned"
        "octet 87 is not an encoding the constructor grammar assigns") := by
  unfold SpecAMQP.Ref.encode SpecAMQP.Ref.arrayElementItems SpecAMQP.Ref.arrayElement
  try dsimp only []
  try simp only [SpecAMQP.Ref.assignedConstructor]
  try rfl

theorem spec_encodeValue_arrayUnassigned :
    SpecAMQP.Spec.Codec.encodeValue (.array 0x57 [.null]) =
      .error (SpecAMQP.Spec.Codec.refusal "unassigned"
        "octet 0x57 lies in the fixed range of width 1 but the declared surface assigns it no encoding") := by
  unfold SpecAMQP.Spec.Codec.encodeValue SpecAMQP.Spec.Codec.writeValue
    SpecAMQP.Spec.Codec.elementDecl?
  try dsimp only []
  try (first | rfl | (split <;> first | rfl | simp_all))
  try decide

theorem bodiesAgree_arrayUnassigned :
    BodiesAgree (.array 0x57 [.null]) (.array 0x57 [.null]) := by
  simp [BodiesAgree, BodiesAgreeList]

/-! ## The empty-array hole, and what closed it

The pair above is the *non-empty* case of the family, and it is the case patch 3 fixed. The check it
names lives in `Ref.arrayElement`'s catch-all, which runs once per element — so an array with no
elements never reached it, and the declared constructor that was refused with one `null` in the array
was written when the array was empty. `.array 0x57 [.null]` and `.array 0x57 []` differ by one element
and answered differently; the second was the hole.

It was reachable through the corpus vocabulary, which is what made it a refutation rather than a
curiosity about values no reader produces, and `not_valueWriterAgree` carried it in the commit that
classed the writer — classing the writer being what made it expressible at all. **That refutation is
withdrawn here**, by the fix that closed the hole, because a refutation of a defect that has been fixed
argues for a world a later commit changed. The witness is kept, and everything measurable about it,
because it is the measurement that found the hole and the regression test the fix leaves behind:
`Ref.encode` consults the array's declared constructor before its elements now —
`Ref.requireAssignedConstructor`, in the place the specification consults `elementDecl?` — so the writer
refuses where it used to write.

What the facts below are: each artefact's own answer to the same value, the third showing what each
*writer* does with it and the fourth showing what the reference's **own** reader does with the octets its
writer had produced. A writer's domain is meant to sit inside its reader's — `Ref/Value.lean`'s head says
so, and the specification's array path does so by construction — and the fourth fact is the one that said
it did not.

**How the reachability is proved, since `valueOfJson` on a literal is the part that resists.** The
three accessor facts are `decide`-able for the `String` keys and one rewrite for the `items` key; the
`items` case is the one to know about, because `getObjValAs?` is `fromJson?` of a lookup and the
`FromJson` instance for `Array` is an `Array.mapM` whose empty case is **not** definitionally reducible
— `Array.mapM_empty` is the lemma that closes it, and without it `rfl` leaves
`Array.mapM.map✝ … 0 #[] = .ok #[]`. With the three facts in hand the whole reader reduces: `unfold`,
three `rw`s, `rfl`. Note also what is *not* available here — `DecidableEq` for `Ref.Value` (the type
deliberately does not derive it) and for `Lean.Json`, so `decide` cannot be asked the question
directly and the reduction has to be done in steps. -/

/-- The corpus value that produces the witness: an array whose declared element constructor is `%x57`
— inside the fixed range, assigned no encoding — carrying no elements. -/
def arrayUnassignedEmptyJson : Json :=
  Json.mkObj [("type", "array"), ("constructor", "57"), ("items", Json.arr #[])]

theorem arrayUnassignedEmptyJson_type :
    arrayUnassignedEmptyJson.getObjValAs? String "type" = .ok "array" := by decide

theorem arrayUnassignedEmptyJson_constructor :
    arrayUnassignedEmptyJson.getObjValAs? String "constructor" = .ok "57" := by decide

/-- The corpus reader's `items` read: an empty JSON array as an empty `Array Json`. `Array.mapM_empty`
is the step that has to be named; the `FromJson` instance's own body does not reduce on its own. -/
theorem arrayUnassignedEmptyJson_items :
    arrayUnassignedEmptyJson.getObjValAs? (Array Json) "items" = .ok #[] := by
  simp only [Json.getObjValAs?]
  rw [show arrayUnassignedEmptyJson.getObjValD "items" = Json.arr #[] from rfl]
  simp only [Lean.FromJson.fromJson?, Array.fromJson?, Array.mapM_empty]
  rfl

/-- **The witness is carrier-reachable**, which is the domain `ValueWriterAgree` is stated over and
the thing the previous sitting's refutations could not supply for a shape divergence. -/
theorem carrier_witness_arrayUnassignedEmpty :
    SpecAMQP.Ref.Vectors.valueOfJson 64 arrayUnassignedEmptyJson = .ok (.array 0x57 []) := by
  unfold SpecAMQP.Ref.Vectors.valueOfJson
  rw [arrayUnassignedEmptyJson_type, arrayUnassignedEmptyJson_constructor,
    arrayUnassignedEmptyJson_items]
  rfl

theorem carrierReachable_arrayUnassignedEmpty : CarrierReachable (.array 0x57 []) :=
  carrierReachable_of_valueOfJson carrier_witness_arrayUnassignedEmpty

/-- **The fix, at the witness.** The reference refuses it, `unassigned`, where before the fix it wrote
`#[0xE0,0x02,0x00,0x57]` — an `array8`, size field `2` (the count octet and the constructor), count `0`,
constructor `%x57`, no element data. The message is the one `arrayElement`'s catch-all already spelled
for the non-empty case, because it is the same check made once for the array instead of once per
element, and keeping the sentence means the non-empty case's observable did not move. -/
theorem ref_encode_arrayUnassignedEmpty :
    SpecAMQP.Ref.encode (.array 0x57 []) =
      .error (SpecAMQP.Ref.encodeRefusal "unassigned"
        "octet 87 is not an encoding the constructor grammar assigns") := by
  unfold SpecAMQP.Ref.encode SpecAMQP.Ref.requireAssignedConstructor
  rfl

/-- The specification refuses the same value, and names `unassigned`: its element-constructor lookup
runs *before* any element is written, so an empty array reaches it too. -/
theorem spec_encodeValue_arrayUnassignedEmpty :
    SpecAMQP.Spec.Codec.encodeValue (.array 0x57 ([] : List SpecAMQP.Spec.Codec.Value)) =
      .error (SpecAMQP.Spec.Codec.refusal "unassigned"
        "octet 0x57 lies in the fixed range of width 1 but the declared surface assigns it no encoding") := by
  unfold SpecAMQP.Spec.Codec.encodeValue SpecAMQP.Spec.Codec.writeValue
    SpecAMQP.Spec.Codec.elementDecl?
  rfl

theorem bodiesAgree_arrayUnassignedEmpty :
    BodiesAgree (.array 0x57 []) (.array 0x57 []) := by
  simp [BodiesAgree, BodiesAgreeList]

/-- **The reference's own reader refuses the octets its writer used to write.** This is the fact that
made the divergence a defect and not two readings of Part 1: `Ref.readArray` looks the element
constructor up before it reads an element, exactly as the specification's writer does, so the octets the
pre-fix writer produced for the witness were octets this implementation could not read back. The reader is
unchanged by the fix — the writer stopped producing those octets rather than the reader starting to accept
them, which is the direction that keeps the writer's domain inside the reader's. -/
theorem ref_decode_arrayUnassignedEmpty :
    SpecAMQP.Ref.decode #[0xE0, 0x02, 0x00, 0x57] = .error (.unassigned 0x57) := by
  unfold SpecAMQP.Ref.decode SpecAMQP.Ref.readValue SpecAMQP.Ref.readArray
  rfl

/-- **The class agreement at the witness**, which is the second conjunct of `ValueWriterAgree` at the
one input that used to refute it: whatever failure the reference answers with, the specification answers
with a refusal of the same class. Stated in the law's own form rather than as an equality of two
strings, so that it is the conjunct's shape and not a lookalike. -/
theorem arrayUnassignedEmpty_class_agrees :
    ∀ failure : SpecAMQP.Ref.EncodeRefusal,
      SpecAMQP.Ref.encode (.array 0x57 []) = .error failure →
      ∃ refusal : SpecAMQP.Spec.Codec.Refusal,
        SpecAMQP.Spec.Codec.encodeValue (.array 0x57 []) = .error refusal ∧
        refusal.reasonClass = failure.reasonClass := by
  intro failure h
  rw [ref_encode_arrayUnassignedEmpty] at h
  have hcl : failure.reasonClass = "unassigned" := by rw [← Except.error.inj h]; rfl
  exact ⟨_, spec_encodeValue_arrayUnassignedEmpty, by rw [hcl]; rfl⟩

/-- **The hole closed in general, not at the witness.** Every array whose declared element constructor
the grammar assigns no encoding is refused by the reference, whatever it carries: the check is on the
constructor, before any element is written, so the element list cannot affect it. The length hypothesis
is the over-limit check that precedes it, which is the order the specification uses as well
(`writeArrayData` asks about the count first and consults its element declaration second).

This is the statement the fix is *for*, and it is why the refutation above could be withdrawn rather than
weakened: the class it names is the one the specification names, for every constructor the two artefacts
disagree about rather than for `%x57` alone. -/
theorem ref_encode_unassignedConstructor
    {constructor : UInt8} {items : List SpecAMQP.Ref.Value}
    (hunassigned : SpecAMQP.Ref.assignedConstructor constructor = false)
    (hlen : items.length ≤ SpecAMQP.Ref.arrayElementLimit) :
    SpecAMQP.Ref.encode (.array constructor items) =
      .error (SpecAMQP.Ref.encodeRefusal "unassigned"
        s!"octet {constructor.toNat} is not an encoding the constructor grammar assigns") := by
  unfold SpecAMQP.Ref.encode SpecAMQP.Ref.requireAssignedConstructor
  try dsimp only []
  rw [if_neg (by omega)]
  simp only [hunassigned, Bool.false_eq_true, if_false]
  rfl

/-- And the check is where the array is written rather than at the top level, which the nested witness
shows: an inner array whose constructor is unassigned is refused inside an outer array that carries it,
which the per-element catch-all could only have refused if the inner array had had an element of its own.
`Ref.arrayElement`'s own array arms consult the constructor too, so an array is refused on its declared
constructor wherever an array is written. -/
theorem ref_encode_nestedUnassignedEmpty :
    SpecAMQP.Ref.encode (.array 0xE0 [.array 0x57 []]) =
      .error (SpecAMQP.Ref.encodeRefusal "unassigned"
        "octet 87 is not an encoding the constructor grammar assigns") := by
  unfold SpecAMQP.Ref.encode SpecAMQP.Ref.arrayElementItems SpecAMQP.Ref.arrayElement
    SpecAMQP.Ref.requireAssignedConstructor
  rfl

/-! ## The unassigned-constructor family, at the specification, and the law's conjunct over it

`ref_encode_unassignedConstructor` closes the *reference's* side of the family the withdrawn refutation
lived in, and `arrayUnassignedEmpty_class_agrees` states the law's error conjunct at the one value that
refuted it. Neither is the *pair* statement — the specification's own refusal for every member of the
family, and the two answers agreeing on it — and this section lands both, generally in the constructor
and in the item list.

The gate is the same one the readers' agreement uses (`elementDecl?_refusal`, in
`Proofs.ValueWireAgreement`), and the reason the statement can be general is the reason the hole existed.
An array declares its element constructor whether or not it carries elements, so the check belongs on the
constructor and before any element is written; `Ref.arrayElement`'s catch-all, which is where the class
lived, ran once per element and an empty list never reached it. A statement that does not read the items
is one an empty list cannot escape — which is the property the withdrawn hole lacked, stated as a theorem
instead of as a value. -/

/-- **The specification's writer refuses every array whose declared element constructor the grammar
assigns no encoding**, whatever it carries: the counterpart of `ref_encode_unassignedConstructor`, and
general for the same reason — `elementDecl?` is consulted before `writeElements`, so the refusal precedes
the items. The class is the one the reference names (`unassigned`), which is what makes the pair below
the law's error conjunct rather than two refusals that happen to both be refusals. -/
theorem spec_encode_unassignedConstructor {constructor : UInt8}
    {items : List SpecAMQP.Spec.Codec.Value}
    (hunassigned : SpecAMQP.Ref.assignedConstructor constructor = false)
    (hlen : items.length ≤ SpecAMQP.Spec.Codec.arrayElementLimit) :
    ∃ refusal : SpecAMQP.Spec.Codec.Refusal,
      SpecAMQP.Spec.Codec.encodeValue (.array constructor items) = .error refusal ∧
      refusal.reasonClass = "unassigned" := by
  obtain ⟨refusal, hdecl, hclass⟩ := elementDecl?_refusal hunassigned
  refine ⟨refusal, ?_, hclass⟩
  unfold SpecAMQP.Spec.Codec.encodeValue SpecAMQP.Spec.Codec.writeValue
  rw [if_neg (by omega)]
  simp only [hdecl, Bind.bind, Except.bind]

/-- **The writer law's error conjunct, over the whole unassigned-constructor family.** Every array whose
declared element constructor the grammar assigns no encoding is refused by both writers, and always with
the same class: `arrayUnassignedEmpty_class_agrees` at every member of the family rather than at `%x57`
with no elements, which is the nearest true statement to the refutation that lived here and the statement
a regression in either writer would break.

The two item lists are unrelated on purpose, and that is stronger than the law's instantiation rather
than a gap in it: the constructor decides the answer before any element is written, so no relation
between the lists is needed for the conclusion and none is assumed — a hypothesis the conclusion does not
use is a hypothesis a reader has to check for nothing. The first conjunct is the law's write side, and
here it is vacuous for the same reason the conclusion is general: the reference's answer at this family
is a refusal, so there is no `octets` for its premise to be given. -/
theorem unassignedConstructor_class_agrees {constructor : UInt8}
    {items : List SpecAMQP.Spec.Codec.Value} {otherItems : List SpecAMQP.Ref.Value}
    (hunassigned : SpecAMQP.Ref.assignedConstructor constructor = false)
    (hlen : items.length ≤ SpecAMQP.Spec.Codec.arrayElementLimit)
    (holen : otherItems.length ≤ SpecAMQP.Ref.arrayElementLimit) :
    (∀ octets : Octets, SpecAMQP.Ref.encode (.array constructor otherItems) = .ok octets →
      SpecAMQP.Spec.Codec.encodeValue (.array constructor items) = .ok octets) ∧
    (∀ failure : SpecAMQP.Ref.EncodeRefusal,
      SpecAMQP.Ref.encode (.array constructor otherItems) = .error failure →
      ∃ refusal : SpecAMQP.Spec.Codec.Refusal,
        SpecAMQP.Spec.Codec.encodeValue (.array constructor items) = .error refusal ∧
        refusal.reasonClass = failure.reasonClass) := by
  obtain ⟨refusal, hspec, hclass⟩ := spec_encode_unassignedConstructor hunassigned hlen
  have href := ref_encode_unassignedConstructor (constructor := constructor) hunassigned holen
  refine ⟨fun octets h => by rw [href] at h; simp at h, fun failure h => ?_⟩
  rw [href] at h
  have hf : failure.reasonClass = "unassigned" := by
    rw [← Except.error.inj h]
    rfl
  exact ⟨refusal, hspec, by rw [hf, hclass]⟩

/-! ## The zero-width element forms, and the value they were dropping

The array-constructor hole above had a twin inside the element writer, and it was worse: not a class
the two artefacts could disagree about, but octets that read back as a *different value*.

`Ref.arrayElement` writes the zero-width forms — the constructors whose encoding is the constructor
octet and nothing else — and three of them matched **any** item:

    0x40, _ => .ok #[]      0x41, _ => .ok #[]      0x42, _ => .ok #[]

`null0`, `true` and `false` therefore wrote no element data for whatever item they were handed, and an
array's element data carries no second constructor: `Ref.encode (.array 0x40 [.ubyte 7])` emitted
`#[0xE0,0x02,0x01,0x40]`, and that reader returns `.array 0x40 [.null]` — `ref_readElement_null` is why,
under `%x40` the reader yields `null` whatever follows. The reference wrote a different value than the
one it was given, where the specification refused the same item `malformed`. The zero-*value* arms
beside them never had this defect (`0x43` matches `.uint 0` and nothing else), so the wildcard was the
whole of it; the three arms now check the item's kind, inside the arm rather than in the pattern,
because refining these three patterns makes Lean's match compiler build the 40-by-25 product tree and
exhaust its heartbeat budget.

After the fix `zeroWidthMismatch_class_agrees` is the law's error conjunct at the witness, in the law's
own form, and `ref_arrayElement_null_refuses_mismatch` closes the whole `%x40` family rather than the
witness alone: every item that is not `null` is refused. The matching cases still write, and
`ref_encode_zeroWidthMatch` is their octets — which is the other half of the measurement, since the same
four octets used to come from a mismatched value.

**One interaction, which was a divergence this fix made *visible* and which the specification's own
slice then closed.** `0x41` carries `true` and `0x42` carries `false`, so `Ref.arrayElement 0x41
(.boolean false)` is refused — correctly, because writing nothing under `%x41` reads back as `true`. When
this fix landed the specification still *wrote* that pair: its `writeFixedData` boolean arm answered
`.ok []` for any zero-width boolean row regardless of `b`, so it dropped the value rather than refusing
it, and the two artefacts read as a shape divergence for as long as that stood — with the reference
giving the answer both should give. The specification's arm now compares the row's name against the
value (`0ad854f`, the slice that also landed `constructor-disagreement.ndjson`'s four vectors for these
two pairs), so **both refuse `malformed` and the pair is a class agreement like the rest**. It is
recorded because a reader meeting the reference's refusal should be able to see that the divergence was
real, transient and shared, rather than read it as a regression from this fix. -/

/-- **The reader's side of the data loss**: under `%x40` this reader produces `null` whatever data
follows, so an element written with no data at all under `%x40` reads back as a `null` — which is why a
writer that emitted nothing for a `ubyte` under that constructor had written a different value. -/
theorem ref_readElement_null (fuel : Nat) (c : SpecAMQP.Ref.Cursor) :
    SpecAMQP.Ref.readElement fuel 0x40 c = .ok (.null, c) := by
  unfold SpecAMQP.Ref.readElement
  rfl

/-- **A zero-width form carries exactly one value, and the reference refuses any other.** General over
*every* item rather than at one witness: whatever is handed to `%x40` that is not `null` is refused,
with the class the specification names for the same item. The residual goals of this proof are equalities
of rendered strings — the two `s!` spellings of the same message — which is what the trailing `decide`
closes and why the repo's `rfl`-only recipe does not. -/
theorem ref_arrayElement_null_refuses_mismatch {item : SpecAMQP.Ref.Value} (h : item ≠ .null) :
    SpecAMQP.Ref.arrayElement 0x40 item =
      .error (SpecAMQP.Ref.encodeRefusal "malformed"
        s!"an array whose element constructor is 64 cannot carry a {SpecAMQP.Ref.typeName item}") := by
  cases item <;>
    simp_all [SpecAMQP.Ref.arrayElement, SpecAMQP.Ref.elementShapeRefusal,
      SpecAMQP.Ref.assignedConstructor, SpecAMQP.Ref.typeName] <;>
    decide

/-- The two boolean forms are subject to the same rule: `%x41` names `true` and `%x42` names `false`, so
a `false` under `%x41` is a value that form cannot carry, and the reference refuses it. The
specification refuses it too — `writeFixedData` compares the row's name against the value since
`0ad854f`, the slice that landed the four `constructor-disagreement` vectors for these two pairs — so
this is a class agreement; it was not when this fix landed, and the paragraph above records why. -/
theorem ref_arrayElement_true_refuses_false :
    SpecAMQP.Ref.arrayElement 0x41 (.boolean false) =
      .error (SpecAMQP.Ref.encodeRefusal "malformed"
        "an array whose element constructor is 65 cannot carry a boolean") := by
  unfold SpecAMQP.Ref.arrayElement SpecAMQP.Ref.elementShapeRefusal
  simp only [SpecAMQP.Ref.assignedConstructor]
  decide

/-- No array elements write no data, which is the base case the array writer's own `do` block needs
before its element-list guard can be reduced — the module's reader-side proofs need the same shape
(`ref_readItems_nil`), for the same reason: the iterator is a member of a `mutual` block, so it has no
equation `unfold` can reach on its own. -/
theorem ref_arrayElementItems_nil (constructor : UInt8) :
    SpecAMQP.Ref.arrayElementItems constructor [] = .ok #[] := by
  unfold SpecAMQP.Ref.arrayElementItems
  rfl

/-- **The fix, at the witness**: the reference refuses the mismatch, `malformed`, where before the fix it
wrote `#[0xE0,0x02,0x01,0x40]` — octets that read back as `.array 0x40 [.null]`. -/
theorem ref_encode_zeroWidthMismatch :
    SpecAMQP.Ref.encode (.array 0x40 [.ubyte 7]) =
      .error (SpecAMQP.Ref.encodeRefusal "malformed"
        "an array whose element constructor is 64 cannot carry a ubyte") := by
  unfold SpecAMQP.Ref.encode SpecAMQP.Ref.arrayElementItems SpecAMQP.Ref.arrayElement
    SpecAMQP.Ref.requireAssignedConstructor SpecAMQP.Ref.elementShapeRefusal
  simp only [SpecAMQP.Ref.arrayElementLimit, SpecAMQP.Ref.assignedConstructor]
  try dsimp only []
  try (first | rfl | (split <;> first | rfl | simp_all))
  try decide

/-- And the matching case still writes those same four octets, which is the measurement's other half. -/
theorem ref_encode_zeroWidthMatch :
    SpecAMQP.Ref.encode (.array 0x40 [.null]) = .ok #[0xE0, 0x02, 0x01, 0x40] := by
  unfold SpecAMQP.Ref.encode SpecAMQP.Ref.arrayElementItems SpecAMQP.Ref.arrayElement
    SpecAMQP.Ref.requireAssignedConstructor
  rw [show SpecAMQP.Ref.arrayElementItems 0x40 [] = .ok #[] from ref_arrayElementItems_nil 0x40]
  simp only [SpecAMQP.Ref.arrayElementLimit, SpecAMQP.Ref.assignedConstructor]
  decide

/-- The specification's answer for the same item, and the class the reference now agrees with. -/
theorem spec_encodeValue_zeroWidthMismatch :
    SpecAMQP.Spec.Codec.encodeValue (.array 0x40 [.ubyte 7]) =
      .error (SpecAMQP.Spec.Codec.refusal "malformed"
        "the declared surface calls octet 0x40 a null encoding, which cannot carry ubyte") := by
  unfold SpecAMQP.Spec.Codec.encodeValue SpecAMQP.Spec.Codec.writeValue
    SpecAMQP.Spec.Codec.writeElements SpecAMQP.Spec.Codec.writeDeclared
    SpecAMQP.Spec.Codec.writeFixedData SpecAMQP.Spec.Codec.elementDecl?
  try dsimp only []
  try (first | rfl | (split <;> first | rfl | simp_all))
  try decide

/-- **The class agreement at the zero-width witness**, the law's error conjunct in the law's own form. -/
theorem zeroWidthMismatch_class_agrees :
    ∀ failure : SpecAMQP.Ref.EncodeRefusal,
      SpecAMQP.Ref.encode (.array 0x40 [.ubyte 7]) = .error failure →
      ∃ refusal : SpecAMQP.Spec.Codec.Refusal,
        SpecAMQP.Spec.Codec.encodeValue (.array 0x40 [.ubyte 7]) = .error refusal ∧
        refusal.reasonClass = failure.reasonClass := by
  intro failure h
  rw [ref_encode_zeroWidthMismatch] at h
  have hcl : failure.reasonClass = "malformed" := by rw [← Except.error.inj h]; rfl
  exact ⟨_, spec_encodeValue_zeroWidthMismatch, by rw [hcl]; rfl⟩

/-! ## The size accounting, settled by the artefacts

The divergence above is an *order* difference, not an *accounting* difference, and this section is
the measurement rather than the claim: `list8` with a size field of `1`, a count field of `0` and no
items is **accepted by both readers**, consuming its three octets. A size field of one octet covers
exactly the count field, in both artefacts — so a compound's size counts the octets that follow the
size field (the count field included), which is `ledger/ambiguities/compound-size-field.json`'s
adopted reading with its arithmetic evidence from Part 1's own worked examples.

The odd-count maps above are therefore not two readings of `size`; they are two readings of *when*
the parity rule is consulted. -/

def listWitness : Octets := #[0xC0, 0x01, 0x00]

theorem listWitness_size : listWitness.size = 3 := by decide

theorem ref_readValue_compound (fuel : Nat) (c c' : SpecAMQP.Ref.Cursor)
    (h : SpecAMQP.Ref.takeU8 c = .ok (0xC0, c')) :
    SpecAMQP.Ref.readValue (fuel + 1) c = SpecAMQP.Ref.readCompound fuel 1 c' := by
  unfold SpecAMQP.Ref.readValue
  try dsimp only []
  rw [h]
  try simp only [Bind.bind, Except.bind]
  try dsimp only []
  try (first | rfl | (split <;> first | rfl | simp_all))

theorem ref_readCompound_list_ok (fuel width : Nat) (c c₁ c₂ c₃ : SpecAMQP.Ref.Cursor)
    (size count : Nat) (items : List SpecAMQP.Ref.Value)
    (h₁ : SpecAMQP.Ref.takeBeU width c = .ok (size, c₁))
    (h₂ : SpecAMQP.Ref.takeBeU width c₁ = .ok (count, c₂))
    (h₃ : SpecAMQP.Ref.readItems fuel count c₂ = .ok (items, c₃))
    (heq : (c₃.pos - c₁.pos != size) = false) :
    SpecAMQP.Ref.readCompound (fuel + 1) width c = .ok (.list items, c₃) := by
  unfold SpecAMQP.Ref.readCompound
  try dsimp only []
  rw [h₁]
  try simp only [Bind.bind, Except.bind]
  try dsimp only []
  rw [h₂]
  try dsimp only []
  rw [h₃]
  try simp only [Bind.bind, Except.bind]
  try dsimp only []
  rw [heq]
  try dsimp only []
  try (first | rfl | (split <;> first | rfl | simp_all))

/-- **The reference accepts a `list8` whose size field covers only its count field**, consuming
its three octets: a size field of one octet is the count field and nothing else. -/
theorem ref_listWitness_decode :
    SpecAMQP.Ref.decode listWitness = .ok (.list [], 3) := by
  have hstep : SpecAMQP.Ref.readValue 3 { data := listWitness, pos := 0 } =
      SpecAMQP.Ref.readCompound 2 1 { data := listWitness, pos := 1 } :=
    ref_readValue_compound 2 _ _ (by decide)
  have hlist : SpecAMQP.Ref.readCompound 2 1 { data := listWitness, pos := 1 } =
      .ok (.list [], { data := listWitness, pos := 3 }) :=
    ref_readCompound_list_ok (fuel := 1) (width := 1)
      (c := { data := listWitness, pos := 1 }) (c₁ := { data := listWitness, pos := 2 })
      (c₂ := { data := listWitness, pos := 3 }) (c₃ := { data := listWitness, pos := 3 })
      (size := 1) (count := 0) (items := [])
      (by decide) (by decide) (ref_readItems_nil 0 _) (by decide)
  unfold SpecAMQP.Ref.decode
  rw [listWitness_size, hstep, hlist]
  try dsimp only []

/-! ## The four-octet field family, and what closes it

The reference's writer emitted a compound's size, a variable value's length and an array's size and
count through `u32be`, which reads a `Nat` four octets wide and keeps its low thirty-two bits. Where
the value did not fit — a body that reaches 2^32 octets — the specification's `filled`,
`compoundOctets` and `arrayOctets` refuse class `limit`, so those octets were ones the specification
refused while a reader accepted them and called the value something else: the same defect as a
zero-width element form writing the wrong item, one field to the left.

**This is the family the module header called reported rather than made, and it is closed now:** every
four-octet size, count and length field is written through `Ref.fieldOctets`, which refuses `limit`
where it cannot announce the value. The lemmas below are the closure *in general* — they hold for every
field value, not at a witness — and that is what this family needs, because it has no witness:
`ofHex` of a 2^33-character string is representable in the corpus vocabulary and no term can carry it,
which is why the law was *unprovable* and *unrefutable* here rather than one of the two. A refutation
needs a value and a proof needs the traversal; the check needed neither, only the field writer, and
that is what landed.

**What this does to `ValueWriterAgree`'s first conjunct at that boundary: it is true, and trivially.**
The conjunct is `Ref.encode other = .ok octets → Spec.encodeValue body = .ok octets`; at a body whose
encoding reaches 2^32 octets the reference now *refuses*, so there is no `octets` for the hypothesis to
be given and the implication holds through the refusal rather than through the octets. So the closest
true statement is about the refusal's *existence*, and it is the first lemma below: no value too wide
for its four-octet field reaches the writer's output at all. What remains between the law and a proof
is the traversal alone — the family that made it false at this point is gone, for every shape and not
only for the shapes with a nameable witness. -/

/-- **The field writer refuses what it cannot announce**, for every field: the statement that replaces
the law's first conjunct where it used to fail. Stated for an arbitrary `what` because the check is the
field's width and not the quantity it carries — the same shape the specification's `filled` has. -/
theorem ref_fieldOctets_refuses (what : String) (n : Nat) (h : 2 ^ 32 ≤ n) :
    SpecAMQP.Ref.fieldOctets what n =
      .error (SpecAMQP.Ref.encodeRefusal "limit"
        s!"a four-octet {what} field cannot announce {n}") := by
  unfold SpecAMQP.Ref.fieldOctets
  rw [if_neg (Nat.not_lt.mpr h)]

/-- Where the value fits, the guard writes exactly what the raw four-octet writer writes: the refusal
moved no octets the writer had produced before it existed. -/
theorem ref_fieldOctets_writes (what : String) (n : Nat) (h : n < 2 ^ 32) :
    SpecAMQP.Ref.fieldOctets what n = .ok (SpecAMQP.Ref.u32be n) := by
  unfold SpecAMQP.Ref.fieldOctets
  rw [if_pos h]

/-- **Where both artefacts can announce the value, they write the same four octets** — the reference's
`u32be` against the specification's `beOctets 4`, through the two shape lemmas the frame layer already
carries. So `fieldOctets` is a refusal attached to a shared encoding rather than a second convention
beside the specification's: the two agree on the octets where they write and on the class where they
do not. -/
theorem ref_u32be_eq_beOctets (n : Nat) :
    (SpecAMQP.Ref.u32be n).toList = SpecAMQP.Spec.Codec.beOctets 4 n := by
  rw [SpecAMQP.Proofs.u32be_form, SpecAMQP.Proofs.beOctets_four]

/-- The specification's side of the boundary: `filled 4` refuses class `limit` for the same value,
which is the class the reference's `fieldOctets` names. -/
theorem spec_filled_refuses (n : Nat) (h : 2 ^ 32 ≤ n) :
    SpecAMQP.Spec.Codec.filled 4 n =
      .error (SpecAMQP.Spec.Codec.refusal "limit"
        s!"{n} does not fit in {4} big-endian octet(s)") := by
  unfold SpecAMQP.Spec.Codec.filled
  rw [if_neg (Nat.not_lt.mpr h)]

/-- **The closure at a writer, general over the payload**: a binary value whose payload reaches 2^32
octets is refused, classed `limit`, where before the change its length field kept the payload's low
four octets. No term can carry such a payload, so this is a statement about the writer's *domain*
rather than a measurement at a value — which is exactly why the family needed a check and not a
witness, and why the check is where the fix belongs. -/
theorem ref_encode_binary_wide_refuses (payload : List UInt8) (h : 2 ^ 32 ≤ payload.length) :
    SpecAMQP.Ref.encode (.binary payload) =
      .error (SpecAMQP.Ref.encodeRefusal "limit"
        s!"a four-octet binary length field cannot announce {payload.length}") := by
  unfold SpecAMQP.Ref.encode SpecAMQP.Ref.variableData
  try dsimp only []
  have hlt : (255 : Nat) < payload.length :=
    Nat.lt_of_lt_of_le (by decide : (255 : Nat) < 2 ^ 32) h
  rw [if_neg (Nat.not_le_of_lt hlt)]
  try dsimp only []
  rw [ref_fieldOctets_refuses "binary length" payload.length h]
  try simp only [Bind.bind, Except.bind]
  rfl

/-- **The closure at the compound and array sites, stated by class.** A body too wide for the
four-octet size field is refused, classed `limit`: the shape the writer takes for a `list32`, a
`map32`, an `array32`, a wide compound array element and an inner `array32` element alike — every one
of them reaches `elementCompoundData` or the array arm's two `fieldOctets` calls, and each refuses
here rather than wrapping the size. Stated over the class rather than over the sentence because the
class is what `ValueWriterAgree` compares, and the sentence is the field writer's own, named in
`ref_fieldOctets_refuses` and reached through `fieldOctets` at every one of these sites. -/
theorem ref_elementCompoundData_wide_size_class (kind : String) (count : Nat) (body : Octets)
    (h : 2 ^ 32 ≤ 4 + body.size) :
    ∀ failure : SpecAMQP.Ref.EncodeRefusal,
      SpecAMQP.Ref.elementCompoundData 4 kind count body = .error failure →
      failure.reasonClass = "limit" := by
  intro failure hf
  have hfield := ref_fieldOctets_refuses s!"{kind} size" (4 + body.size) h
  unfold SpecAMQP.Ref.elementCompoundData at hf
  try dsimp only at hf
  rw [if_neg (by decide : ¬ (4 = 1))] at hf
  try dsimp only at hf
  rw [hfield] at hf
  try simp only [Bind.bind, Except.bind] at hf
  rw [← Except.error.inj hf]
  rfl

end SpecAMQP.Proofs
