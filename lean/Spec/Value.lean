import Generated.Oasis.Encodings

/-!
# The AMQP 1.0 constructor grammar

Part 1 states the encoding grammar in its own words:

```text
constructor = format-code
            / %x00 descriptor constructor

format-code = fixed / variable / compound / array
      fixed = empty / fixed-one / fixed-two / fixed-four
            / fixed-eight / fixed-sixteen
   variable = variable-one / variable-four
   compound = compound-one / compound-four
      array = array-one / array-four
```

That block lives inside a `<picture>` in the OASIS artifact, which is why
`ledger/pictures.json` tracks it and `ledger/dispositions/picture-review.json`
disposes it here: excluding a picture from clause extraction is a decision, and
this picture is normative — it is the specification's own statement of which
leading octets are format codes, and what each one promises about the bytes that
follow.

This module formalises the grammar as a function on the leading octet and checks
it against the generated encoding table. It carries no codec: the value domain and
the reader/writer arrive with the rest of the type system, and this classification
is what they dispatch on.
-/

namespace SpecAMQP.Spec.Value

/-- What a leading octet promises about the bytes that follow it.

`width` is the width in octets of the encoded size or length field, exactly as
the grammar's subcategories specify: fixed widths have no size field, variable and
compound encodings prefix one, and array encodings prefix a size and a count. -/
inductive Constructor where
  /-- `%x00`: a described-type constructor, where an encoded value names the type. -/
  | descriptor
  | fixed (width : Nat)
  | variable (width : Nat)
  | compound (width : Nat)
  | array (width : Nat)
  /-- Outside every range the grammar assigns: not a format code. -/
  | reserved
deriving Repr, DecidableEq, BEq

/-- Classify a leading octet by the range the grammar gives it.

The grammar's extension alternatives (`%x4F %x00-FF` and its siblings) belong to
a range while being unassigned: `classify` reports the range, and `escapeOctets`
below names the twelve octets the grammar reserves for future formats. -/
def classify (code : Nat) : Constructor :=
  if code = 0x00 then .descriptor
  else if 0x40 ≤ code ∧ code ≤ 0x4F then .fixed 0
  else if 0x50 ≤ code ∧ code ≤ 0x5F then .fixed 1
  else if 0x60 ≤ code ∧ code ≤ 0x6F then .fixed 2
  else if 0x70 ≤ code ∧ code ≤ 0x7F then .fixed 4
  else if 0x80 ≤ code ∧ code ≤ 0x8F then .fixed 8
  else if 0x90 ≤ code ∧ code ≤ 0x9F then .fixed 16
  else if 0xA0 ≤ code ∧ code ≤ 0xAF then .variable 1
  else if 0xB0 ≤ code ∧ code ≤ 0xBF then .variable 4
  else if 0xC0 ≤ code ∧ code ≤ 0xCF then .compound 1
  else if 0xD0 ≤ code ∧ code ≤ 0xDF then .compound 4
  else if 0xE0 ≤ code ∧ code ≤ 0xEF then .array 1
  else if 0xF0 ≤ code ∧ code ≤ 0xFF then .array 4
  else .reserved

/-- The octets the grammar does not assign to any category: `%x01-3F`. -/
def reservedCodes : List Nat :=
  (List.range 256).filter (fun code => classify code == Constructor.reserved)

/-- The reserved octets are exactly `%x01-3F`: every octet below `%x40` other than
`%x00`, which is the descriptor prefix rather than a format code. -/
theorem reservedCodes_eq : reservedCodes = (List.range 0x3F).map (fun offset => offset + 1) := by
  decide

/-- The grammar's extension hooks: one octet per range whose following octet
extends the format code (`%x4F %x00-FF`, `%x5F %x00-FF`, ...). None of them is an
assigned encoding, so a reader that meets one has met a reserved format code
rather than a type it failed to recognise. -/
def escapeOctets : List Nat :=
  [0x4F, 0x5F, 0x6F, 0x7F, 0x8F, 0x9F, 0xAF, 0xBF, 0xCF, 0xDF, 0xEF, 0xFF]

/-- Every escape octet is unassigned in the generated table. -/
theorem escapeOctets_unassigned :
    escapeOctets.all (fun code => (Generated.Oasis.encodingOf code).isNone) = true := by
  decide

/-- Each escape octet still lies in the range its category covers, so a reader
knows which kind of data a reserved extension would extend. -/
theorem escapeOctets_in_range :
    escapeOctets.all (fun code => classify code != Constructor.reserved) = true := by
  decide

/-- The grammar a table row claims to follow: the row's declared category and
size width must be the ones the range gives its octet.

It is a computation rather than a proposition so that the check below is a
finite evaluation over concrete data — the same reason the table itself is
generated rather than argued about. -/
def followsRange (encoding : Generated.Oasis.EncodingDecl) : Bool :=
  match classify encoding.code with
  | .fixed width => decide (encoding.category = .fixed) && decide (encoding.width = width)
  | .variable width => decide (encoding.category = .variable) && decide (encoding.width = width)
  | .compound width => decide (encoding.category = .compound) && decide (encoding.width = width)
  | .array width => decide (encoding.category = .array) && decide (encoding.width = width)
  | .descriptor => false
  | .reserved => false

/-- Every encoding in the generated table sits in the range its category claims,
with the width that range specifies.

This is the binding between the grammar (`classify`, handwritten from the
picture) and the declared surface (generated from the artifact's `encoding`
elements): a table row and a range disagreeing is a specification defect, not an
implementation choice. -/
theorem encodings_follow_range :
    Generated.Oasis.encodings.all followsRange = true := by
  decide

set_option maxRecDepth 10000 in
/-- The format-code ranges hold no gaps: `%x00` is the descriptor prefix, every
octet from `%x40` to `%xFF` falls in a category, and everything between is
reserved. A reader can therefore decide what a leading octet is from one
comparison chain, with no unassigned hole to treat as a special case. -/
theorem formatCodeRanges_exact :
    (List.range 256).filter (fun code => classify code != Constructor.reserved) =
      [0x00] ++ (List.range 0xC0).map (fun offset => offset + 0x40) := by
  decide

end SpecAMQP.Spec.Value
