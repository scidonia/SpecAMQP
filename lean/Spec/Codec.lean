import Harness.Runner
import Spec.Value
import Generated.Oasis.Encodings

/-!
# The specification's reader and writer for the AMQP 1.0 type system

`Spec.Value` classifies a leading octet into the constructor grammar's categories
(`descriptor`, `fixed`, `variable`, `compound`, `array`, `reserved`), and
`Generated.Oasis.Encodings` is the declared surface: which type each assigned octet
selects, at which size width. This module is the executable reader and writer built
from those two tables. No octet table is transcribed here: the writer selects a row
of the declared surface and writes what that row declares, and the reader looks the
row up and refuses one whose category is not the category the grammar's range gives
the octet — the run-time counterpart of `Spec.Value.encodings_follow_range`.

Where Part 1 leaves the writer a choice, this module adopts the narrowest form the
table offers: `uint 0` as `uint0`, `uint 255` as `smalluint`, `uint 256` in the
four-octet form, a payload of at most 255 octets in the eight-bit variable form, an
empty list as `list0`, and a compound in the eight-bit form whenever its count and
size fit. `int` and `long` are the deliberate exception: their small forms are read
but never written, because the corpus's canonical vectors fix the writer to the
type's own width.

Other readings this module makes, each recorded because a reader has to choose:

* **Every form the table assigns is read**, `smallint` and `smalllong` included, so
  a conforming sender's choice of form is never a decode error.
* **A compound's size must agree with the octets it announces**, counted from the
  octet after the size field: the count field, the array's element constructor,
  then the items. A declared size that disagrees is a decode error rather than
  something to resynchronise past.
* **A map's count counts items**, two per key-value pair, so an odd count is not a
  map. Pairs keep wire order, which Part 1 makes semantically significant.
* **An array's elements are read in the array's declared constructor form**, one
  constructor for the whole array. The descriptor prefix `%x00` standing as an
  element constructor means each element carries its own descriptor and value.
* **Strings and symbols must be valid UTF-8.** Part 1 calls a symbol seven-bit
  ASCII; making a reader enforce that would have it reject a payload its own value
  domain can carry, so the rule enforced here for both is the one this reader
  needs — a payload that is a Unicode string.
* **`boolean` at width one** is false for the octet `%x00` and true for any other,
  which admits what senders write rather than rejecting an octet no clause names.

Totality: nothing here is `partial`, and no definition is `noncomputable`. The
reader carries a `fuel` argument that decreases at every recursive call — including
the loops that read a compound's items and an array's elements — so no input makes
it diverge. Its entry point passes the number of octets it was given; every value
and every constructed item consumes at least one octet, so a well-formed input is
not refused for want of fuel. An element constructor that carries no octets at all
(`null`, `true`, `false`) is the one shape the octet count does not bound, and an
array with more of those than the fuel allows is refused rather than read to an
unbounded length. The writer needs no fuel: every recursive call is on a strictly
smaller subterm of the value being written, and the loops over items, pairs and
elements recurse on the list they are handed.
-/

namespace SpecAMQP.Spec.Codec

open Lean
open SpecAMQP.Harness
open SpecAMQP.Generated.Oasis (Category EncodingDecl encodings encodingOf)
open SpecAMQP.Spec.Value (Constructor classify)

/-- A cursor over the input: the whole buffer and where the reader has got to. The
buffer is shared rather than copied, so a nested read costs no copy. -/
structure Cursor where
  data : Octets
  pos : Nat
deriving Repr

/-- Reading either yields a value and the rest of the input, or says why it failed.
A notation rather than a parameterised `abbrev`, deliberately: instance search does
not unfold an abbreviation, so `do` blocks over one cannot find `Bind`. -/
notation "Result" α:max => Except String (α × Cursor)

/-! ## Refusals and the declared limit

A decode refusal's detail leads with its reason class: `truncated`, `unassigned`,
`unsupported`, `sizeMismatch`, `malformed` or `limit`. The differential contract reads
that token from the verdict and requires both artefacts to name the same one, so the
vocabulary is interface rather than prose, and it lives here so that a message cannot
quietly acquire a class nobody else uses.

`unsupported` is not a claim about the grammar: it is a legal constructor whose form
this reader does not handle. `unassigned` is the grammar's answer — the octet is below
every format-code range, one of the escapes held for future formats, or a format code
the declared surface leaves unassigned. -/

/-- A refusal's detail: the reason class, then the prose. -/
def refusal (reasonClass prose : String) : String := s!"{reasonClass}: {prose}"

/-- The most array elements this reader materialises.

Part 1 fixes an array as `size`, `count`, one element constructor, then `count`
elements in that constructor's form, and its table assigns width zero to six legal
element constructors (`null`, `true`, `false` and the three zero forms of the integers
and of `list`). Those two rules together admit an encoding that declares billions of
elements in ten octets, because the count is bounded by the width of the count field
and by nothing in the data. A specification that models an array as a list of values
must therefore bound the count or accept an unbounded memory obligation; this one
bounds it, loudly and by name (`limit`), rather than letting whatever recursion device
the reader happens to use bound it silently.

The same number is declared by the reference implementation, because a limit that
differed between the two would make the differential contract compare two different
specifications. The decision and its rejected alternatives are recorded in
`ledger/ambiguities/zero-width-array-count.json`. -/
def arrayElementLimit : Nat := 65536

/-- The specification's value domain: the types Part 1 defines, with the payloads
this corpus can carry exactly. `float`, `double` and the three decimals keep their
octets rather than a number, because what the clause fixes for them is the framing,
and a decimal's Binary Integer Decimal pattern is not a Lean number.

Integer types keep their width in the value rather than in an encoding form: the
form is the wire's business, and two forms may carry the same value. -/
inductive Value where
  | null
  | boolean (b : Bool)
  | ubyte (n : Nat)
  | ushort (n : Nat)
  | uint (n : Nat)
  | ulong (n : Nat)
  | byte (n : Int)
  | short (n : Int)
  | int (n : Int)
  | long (n : Int)
  | float (bits : Octets)
  | double (bits : Octets)
  | decimal32 (bits : Octets)
  | decimal64 (bits : Octets)
  | decimal128 (bits : Octets)
  | char (codepoint : Nat)
  | timestamp (milliseconds : Int)
  | uuid (bits : Octets)
  | binary (payload : Octets)
  | string (text : String)
  | symbol (text : String)
  | list (items : List Value)
  /-- A map with its pairs in wire order. -/
  | map (pairs : List (Value × Value))
  /-- An array as it appears on the wire: one constructor octet for every element,
  and the elements' values (their data having been read in that constructor's
  form). -/
  | array (constructor : UInt8) (items : List Value)
  | described (descriptor : Value) (value : Value)
deriving Repr

/-- A value's name in the corpus vocabulary, for diagnostics. -/
def typeName : Value → String
  | .null => "null"
  | .boolean _ => "boolean"
  | .ubyte _ => "ubyte"
  | .ushort _ => "ushort"
  | .uint _ => "uint"
  | .ulong _ => "ulong"
  | .byte _ => "byte"
  | .short _ => "short"
  | .int _ => "int"
  | .long _ => "long"
  | .float _ => "float"
  | .double _ => "double"
  | .decimal32 _ => "decimal32"
  | .decimal64 _ => "decimal64"
  | .decimal128 _ => "decimal128"
  | .char _ => "char"
  | .timestamp _ => "timestamp"
  | .uuid _ => "uuid"
  | .binary _ => "binary"
  | .string _ => "string"
  | .symbol _ => "symbol"
  | .list _ => "list"
  | .map _ => "map"
  | .array _ _ => "array"
  | .described _ _ => "described"

/-! ## Numbers

Every numeric encoding in Part 1's table is big-endian, and every integer field is
either unsigned or two's complement at the width the table declares. -/

/-- `n` in `width` big-endian octets, most significant first. -/
def beOctets (width : Nat) (n : Nat) : List UInt8 :=
  let rec go : Nat → Nat → List UInt8
    | 0, _ => []
    | k + 1, m => UInt8.ofNat (m % 256) :: go k (m / 256)
  (go width n).reverse

/-- `n` in `width` big-endian octets, refusing a value that does not fit rather
than truncating it: a payload that silently lost its high octets would encode a
different value than the one asked for. -/
def filled (width : Nat) (n : Nat) : Except String (List UInt8) :=
  if n < 2 ^ (8 * width) then .ok (beOctets width n)
  else .error s!"{n} does not fit in {width} big-endian octet(s)"

/-- `i` in `width` two's-complement octets, refusing a value outside the range. -/
def twosComplement (width : Nat) (i : Int) : Except String (List UInt8) :=
  let modulus : Int := (2 : Int) ^ (8 * width)
  if -(modulus / 2) ≤ i ∧ i < modulus / 2 then .ok (beOctets width (i % modulus).toNat)
  else .error s!"{i} does not fit in {width} octet(s) of two's complement"

/-- A `width`-octet big-endian field read as a two's-complement integer. -/
def signedOfOctets (width : Nat) (n : Nat) : Int :=
  if n < 2 ^ (8 * width - 1) then (n : Int) else (n : Int) - (2 : Int) ^ (8 * width)

/-- A payload as a Unicode string, or why it is not one. -/
def utf8Of (bytes : Octets) (kind : String) : Except String String :=
  match String.fromUTF8? (ByteArray.mk bytes) with
  | some text => .ok text
  | none => .error (refusal "malformed" s!"a {kind} payload of {bytes.size} octet(s) is not valid UTF-8")

/-! ## The declared surface, looked up rather than transcribed -/

def categoryName : Category → String
  | .fixed => "fixed"
  | .variable => "variable"
  | .compound => "compound"
  | .array => "array"

/-- The table row for an octet, checked against the range the grammar gives that
octet. A row whose category is not the range's would make the reader read the wrong
number of octets, so it is refused here; `Spec.Value.encodings_follow_range` is the
theorem that no committed row can do this, and this is the reader's own guard for
tables that change. -/
def declInRange (code : UInt8) (category : Category) (width : Nat) :
    Except String EncodingDecl :=
  match encodingOf code.toNat with
  | none =>
    .error (refusal "unassigned" s!"octet 0x{toHex #[code]} lies in the \
      {categoryName category} range of width {width} but the declared surface assigns \
      it no encoding")
  | some decl =>
    if decl.category = category then .ok decl
    else
      .error (refusal "malformed" s!"octet 0x{toHex #[code]} lies in the \
        {categoryName category} range while the declared surface places it in the \
        {categoryName decl.category} category, so the table and the constructor \
        grammar disagree")

/-- The declaration a leading octet selects, by the grammar's classification of it. -/
def dataDecl (code : UInt8) : Except String EncodingDecl :=
  match classify code.toNat with
  | .descriptor =>
    .error (refusal "unassigned" s!"octet 0x{toHex #[code]} is the descriptor prefix, not an encoding")
  | .reserved =>
    .error (refusal "unassigned" s!"octet 0x{toHex #[code]} is reserved: the constructor grammar gives it no category")
  | .fixed width => declInRange code .fixed width
  | .variable width => declInRange code .variable width
  | .compound width => declInRange code .compound width
  | .array width => declInRange code .array width

/-- The declaration an array's element constructor selects. `none` is the descriptor
prefix `%x00`: an array of described values states that prefix once and each
element's own descriptor and value after it, so there is no one row under which
their data could be written. -/
def elementDecl? (constructor : UInt8) : Except String (Option EncodingDecl) :=
  if constructor.toNat = 0 then .ok none
  else
    match classify constructor.toNat with
    | .descriptor => .ok none
    | .reserved =>
      .error (refusal "unassigned" s!"an array's element constructor \
        0x{toHex #[constructor]} is reserved: the constructor grammar gives it no \
        category")
    | .fixed width => some <$> declInRange constructor .fixed width
    | .variable width => some <$> declInRange constructor .variable width
    | .compound width => some <$> declInRange constructor .compound width
    | .array width => some <$> declInRange constructor .array width

/-- The declared surface's row of a type at a size width. The writer selects octets
this way rather than naming them, so a wrong encoding here has to be a wrong table. -/
def rowOf (owner : String) (width : Nat) : Except String EncodingDecl :=
  match encodings.find? (fun decl => decl.owner == owner && decl.width == width) with
  | some decl => .ok decl
  | none => .error s!"the declared surface has no {owner} encoding of width {width}"

/-- The `boolean` row that names `true` or `false`, which is how the table
distinguishes the two fixed-width zero-octet boolean encodings. -/
def booleanRow (b : Bool) : Except String EncodingDecl :=
  let wanted := if b then "true" else "false"
  match encodings.find? (fun decl => decl.owner == "boolean" && decl.name == some wanted) with
  | some decl => .ok decl
  | none => .error s!"the declared surface has no boolean encoding named {wanted}"

/-- A declaration's constructor octet, read from the table. -/
def tagOf (decl : EncodingDecl) : List UInt8 := [UInt8.ofNat decl.code]

/-- `%x00`, the prefix a described value starts with. It is the grammar's rather
than a row of the declared surface: a described value names its own type. -/
def descriptorPrefix : UInt8 := 0x00

/-! ## Reading

A declaration fixes how many octets a type's data occupies and how they are to be
read; the reader below is nothing but that, plus the checks Part 1's clauses make a
receiver responsible for. -/

/-- One octet. -/
def takeU8 (c : Cursor) : Result UInt8 :=
  if h : c.pos < c.data.size then .ok (c.data[c.pos]'h, ⟨c.data, c.pos + 1⟩)
  else .error (refusal "truncated" s!"no octet at offset {c.pos} of {c.data.size}")

/-- Exactly `n` octets. -/
def takeBytes (n : Nat) (c : Cursor) : Result Octets :=
  if c.pos + n ≤ c.data.size then
    .ok (c.data.extract c.pos (c.pos + n), ⟨c.data, c.pos + n⟩)
  else .error (refusal "truncated" s!"{n} octet(s) needed at offset {c.pos} of {c.data.size}")

/-- A `width`-octet big-endian unsigned field. -/
def takeBe (width : Nat) (c : Cursor) : Result Nat := do
  let (bytes, c) ← takeBytes width c
  return (bytes.foldl (fun acc byte => acc * 256 + byte.toNat) 0, c)

/-- A fixed-width encoding's data: the octets the table declares, read as the type
the table's row names. -/
def readFixed (decl : EncodingDecl) (c : Cursor) : Result Value := do
  let (payload, c) ← takeBytes decl.width c
  let n := payload.foldl (fun acc byte => acc * 256 + byte.toNat) 0
  match decl.owner with
  | "null" => .ok (.null, c)
  | "boolean" =>
    if decl.width = 0 then
      match decl.name with
      | some "true" => .ok (.boolean true, c)
      | some "false" => .ok (.boolean false, c)
      | other =>
        .error (refusal "unsupported" s!"the declared surface assigns no boolean encoding named {other} at width 0")
    else .ok (.boolean (n != 0), c)
  | "ubyte" => .ok (.ubyte n, c)
  | "ushort" => .ok (.ushort n, c)
  | "uint" => .ok (.uint n, c)
  | "ulong" => .ok (.ulong n, c)
  | "byte" => .ok (.byte (signedOfOctets decl.width n), c)
  | "short" => .ok (.short (signedOfOctets decl.width n), c)
  | "int" => .ok (.int (signedOfOctets decl.width n), c)
  | "long" => .ok (.long (signedOfOctets decl.width n), c)
  | "char" => .ok (.char n, c)
  | "timestamp" => .ok (.timestamp (signedOfOctets decl.width n), c)
  | "uuid" => .ok (.uuid payload, c)
  | "float" => .ok (.float payload, c)
  | "double" => .ok (.double payload, c)
  | "decimal32" => .ok (.decimal32 payload, c)
  | "decimal64" => .ok (.decimal64 payload, c)
  | "decimal128" => .ok (.decimal128 payload, c)
  | "list" => .ok (.list [], c)
  | owner =>
    .error (refusal "unsupported" s!"the declared surface assigns octet \
      0x{toHex #[UInt8.ofNat decl.code]} ({owner}) to a fixed-width form this reader \
      does not read")

/-- A variable-width encoding's data: the declared length, then that many octets,
read as the type the row names. -/
def readVariable (decl : EncodingDecl) (c : Cursor) : Result Value := do
  let (length, c) ← takeBe decl.width c
  let (payload, c) ← takeBytes length c
  match decl.owner with
  | "binary" => .ok (.binary payload, c)
  | "string" => return (.string (← utf8Of payload "string"), c)
  | "symbol" => return (.symbol (← utf8Of payload "symbol"), c)
  | owner =>
    .error (refusal "unsupported" s!"the declared surface assigns octet \
      0x{toHex #[UInt8.ofNat decl.code]} ({owner}) to a variable-width form this reader \
      does not read")

/-- Items taken two at a time, as a map's pairs. A map with an odd item count is
refused before this is reached, so an unpaired tail is unreachable. -/
def pairUp : List Value → List (Value × Value)
  | key :: value :: rest => (key, value) :: pairUp rest
  | _ => []

/-- The data of a scalar declaration — one whose encoding is fixed or variable — read
without recursion. That is also the form an array's elements take when the array's
constructor is one of them. -/
def readScalarData (decl : EncodingDecl) (c : Cursor) : Result Value :=
  match decl.category with
  | .fixed => readFixed decl c
  | .variable => readVariable decl c
  | _ =>
    .error (refusal "unsupported" s!"the declared surface calls octet \
      0x{toHex #[UInt8.ofNat decl.code]} a {categoryName decl.category} encoding, whose \
      data is not read as a scalar")

mutual

/-- Read one constructed value: its constructor octet, then the data that octet's
declaration describes.

`fuel` decreases at every recursive call, so no input makes this reader diverge — but
it bounds the reader's *nesting*, never a count. Every descent spends octets as it
spends fuel (a value spends its constructor octet, an array its header), while the
loops over a compound's items and an array's elements carry their own count, which is
what makes an array of zero-width elements as long as its declared limit readable out
of a short buffer. -/
def readValue (fuel : Nat) (c : Cursor) : Result Value :=
  match fuel with
  | 0 => .error (refusal "truncated" "the input ends before the value does")
  | fuel + 1 => do
    let (code, c) ← takeU8 c
    match classify code.toNat with
    | .descriptor => do
      let (descriptor, c) ← readValue fuel c
      let (value, c) ← readValue fuel c
      return (.described descriptor value, c)
    | .reserved =>
      .error (refusal "unassigned" s!"octet 0x{toHex #[code]} is reserved: the \
        constructor grammar gives it no category")
    | .fixed _ | .variable _ | .compound _ | .array _ => do
      let decl ← dataDecl code
      match decl.category with
      | .fixed | .variable => readScalarData decl c
      | .compound => readCompound fuel decl c
      | .array => readArrayData fuel decl c

/-- A compound value: `size`, `count`, then the items. The size counts the octets
that follow it — the count field, then the items — so a size that disagrees with what
the reading measured is a decode error. -/
def readCompound (fuel : Nat) (decl : EncodingDecl) (c : Cursor) : Result Value := do
  let (size, c) ← takeBe decl.width c
  let start := c.pos
  let (count, c) ← takeBe decl.width c
  match decl.owner with
  | "list" => do
    let (items, c) ← readItems fuel count c
    let measured := c.pos - start
    if measured = size then .ok (.list items, c)
    else .error (refusal "sizeMismatch" s!"a list declares {size} octet(s) after its \
      size field and measures {measured}")
  | "map" =>
    if count % 2 != 0 then
      .error (refusal "malformed" s!"a map declares {count} item(s): keys and values \
        come in pairs, so an odd count is not a map")
    else do
      let (items, c) ← readItems fuel count c
      let measured := c.pos - start
      if measured = size then .ok (.map (pairUp items), c)
      else .error (refusal "sizeMismatch" s!"a map declares {size} octet(s) after its \
        size field and measures {measured}")
  | owner =>
    .error (refusal "unsupported" s!"the declared surface assigns octet \
      0x{toHex #[UInt8.ofNat decl.code]} ({owner}) to a compound form this reader does \
      not read")

/-- An array: `size`, `count`, one element constructor, then the elements' data. The
size counts the count field, the constructor and the elements.

The count is checked against `arrayElementLimit` before an element is read: a
zero-width element constructor leaves the count bounded by nothing in the data, and a
reader that discovers that bound by running out of input reports a legal encoding as
truncated. -/
def readArrayData (fuel : Nat) (decl : EncodingDecl) (c : Cursor) : Result Value :=
  match fuel with
  | 0 => .error (refusal "truncated" "the input ends before the array does")
  | fuel + 1 => do
    let (size, c) ← takeBe decl.width c
    let start := c.pos
    let (count, c) ← takeBe decl.width c
    if count > arrayElementLimit then
      .error (refusal "limit" s!"an array declares {count} element(s): this reader \
        materialises at most {arrayElementLimit}")
    else do
      let (constructor, c) ← takeU8 c
      let elementDecl ← elementDecl? constructor
      let (items, c) ← readElements fuel elementDecl count c
      let measured := c.pos - start
      if measured = size then .ok (.array constructor items, c)
      else .error (refusal "sizeMismatch" s!"an array declares {size} octet(s) after \
        its size field and measures {measured}")

/-- `count` items, each carrying its own constructor. -/
def readItems (fuel : Nat) (count : Nat) (c : Cursor) : Result (List Value) :=
  match fuel, count with
  | 0, _ => .error (refusal "truncated" "the input ends before the list's items do")
  | _, 0 => .ok ([], c)
  | fuel + 1, count + 1 => do
    let (item, c) ← readValue fuel c
    let (rest, c) ← readItems fuel count c
    return (item :: rest, c)

/-- `count` array elements, each in the array's declared constructor form. One unit of
fuel is spent for the array's elements as a whole rather than for each of them, and the
elements themselves are read by a loop that decreases its own count. -/
def readElements (fuel : Nat) (elementDecl : Option EncodingDecl) (count : Nat) (c : Cursor) :
    Result (List Value) :=
  match fuel with
  | 0 => .error (refusal "truncated" "the input ends before the array's elements do")
  | fuel + 1 => readElementsLoop fuel elementDecl count c

/-- The elements themselves, `count` of them, in the array's one declared constructor
form. The count is what decreases here: an element whose data occupies no octets is
still an element, so the count is bounded by the array's declared limit rather than by
the buffer, and every element of the array is read under the same fuel.

What follows an array's constructor is either the row that constructor names — a
scalar, or a compound or array whose items recurse in the ordinary way — or, under the
descriptor prefix, the element's own descriptor and value. -/
def readElementsLoop (fuel : Nat) (elementDecl : Option EncodingDecl) (count : Nat)
    (c : Cursor) : Result (List Value) :=
  match count with
  | 0 => .ok ([], c)
  | count + 1 => do
    let (item, c) ←
      (match elementDecl with
       | none => (do
         let (descriptor, c) ← readValue fuel c
         let (value, c) ← readValue fuel c
         return (.described descriptor value, c) : Result Value)
       | some decl =>
         (match decl.category with
          | .fixed | .variable => readScalarData decl c
          | .compound => readCompound fuel decl c
          | .array => readArrayData fuel decl c : Result Value))
    let (rest, c) ← readElementsLoop fuel elementDecl count c
    return (item :: rest, c)

end

/-- Decode a buffer: the value, and how many octets it consumed. The depth budget is
the number of octets, which every descent spends at least one of. -/
def decodeValue (bytes : Octets) : Except String (Value × Nat) :=
  match readValue bytes.size ⟨bytes, 0⟩ with
  | .ok (value, c) => .ok (value, c.pos)
  | .error e => .error e

/-! ## The corpus's vocabulary

The harness compares values in the corpus's own vocabulary, never between this
module's representation and another artefact's, so these two translations are the
whole of this codec's interface: a decoded value rendered, and a corpus value read.
-/

mutual

/-- A value in the corpus vocabulary. -/
def toJson : Value → Json
  | .null => Json.mkObj [("type", "null")]
  | .boolean b => Json.mkObj [("type", "boolean"), ("value", b)]
  | .ubyte n => Json.mkObj [("type", "ubyte"), ("value", n)]
  | .ushort n => Json.mkObj [("type", "ushort"), ("value", n)]
  | .uint n => Json.mkObj [("type", "uint"), ("value", n)]
  | .ulong n => Json.mkObj [("type", "ulong"), ("value", n)]
  | .byte i => Json.mkObj [("type", "byte"), ("value", i)]
  | .short i => Json.mkObj [("type", "short"), ("value", i)]
  | .int i => Json.mkObj [("type", "int"), ("value", i)]
  | .long i => Json.mkObj [("type", "long"), ("value", i)]
  | .float bits => Json.mkObj [("type", "float"), ("hex", toHex bits)]
  | .double bits => Json.mkObj [("type", "double"), ("hex", toHex bits)]
  | .decimal32 bits => Json.mkObj [("type", "decimal32"), ("hex", toHex bits)]
  | .decimal64 bits => Json.mkObj [("type", "decimal64"), ("hex", toHex bits)]
  | .decimal128 bits => Json.mkObj [("type", "decimal128"), ("hex", toHex bits)]
  | .char codepoint => Json.mkObj [("type", "char"), ("codepoint", codepoint)]
  | .timestamp milliseconds =>
    Json.mkObj [("type", "timestamp"), ("milliseconds", milliseconds)]
  | .uuid bits => Json.mkObj [("type", "uuid"), ("hex", toHex bits)]
  | .binary payload => Json.mkObj [("type", "binary"), ("hex", toHex payload)]
  | .string text => Json.mkObj [("type", "string"), ("text", text)]
  | .symbol text => Json.mkObj [("type", "symbol"), ("text", text)]
  | .list items => Json.mkObj [("type", "list"), ("items", Json.arr (toJsonList items).toArray)]
  | .map pairs => Json.mkObj [("type", "map"), ("pairs", Json.arr (toJsonPairs pairs).toArray)]
  | .array constructor items =>
    Json.mkObj [("type", "array"), ("constructor", toHex #[constructor]),
                ("items", Json.arr (toJsonList items).toArray)]
  | .described descriptor value =>
    Json.mkObj [("type", "described"), ("descriptor", toJson descriptor),
                ("value", toJson value)]

/-- Items in order. -/
def toJsonList : List Value → List Json
  | [] => []
  | item :: rest => toJson item :: toJsonList rest

/-- A map's pairs, each a two-element array, in wire order. -/
def toJsonPairs : List (Value × Value) → List Json
  | [] => []
  | (key, value) :: rest => Json.arr #[toJson key, toJson value] :: toJsonPairs rest

end

/-- A payload the corpus carries as raw hex, at the length the wire format fixes for
the type. What such a vector pins down is the framing, so the payload is octets
rather than a number that could not hold them exactly. -/
def hexPayloadOf (json : Json) (width : Nat) (kind : String) : Except String Octets := do
  let bytes ← ofHex (← json.getObjValAs? String "hex")
  if bytes.size = width then .ok bytes
  else .error s!"a {kind} payload is {width} octet(s); the value gives {bytes.size}"

/-- A code point only where Unicode defines one. -/
def codePointOf (json : Json) : Except String Nat := do
  let codepoint ← json.getObjValAs? Nat "codepoint"
  if codepoint ≤ 1114111 then .ok codepoint
  else .error s!"{codepoint} is not a Unicode code point"

/-- The corpus's value vocabulary, read as this specification's values. `fuel` bounds
the nesting so the reading is total: a corpus value nested deeper than this is
malformed for the corpus's purposes, and a partial function would leave the
executable's behaviour undefined exactly where a corpus defect lives. -/
def valueOfJson (fuel : Nat) (json : Json) : Except String Value :=
  match fuel with
  | 0 => .error "the corpus value is nested too deeply"
  | fuel + 1 => do
    let kind ← json.getObjValAs? String "type"
    match kind with
    | "null" => .ok .null
    | "boolean" => .ok (.boolean (← json.getObjValAs? Bool "value"))
    | "ubyte" => .ok (.ubyte (← unsignedOf json 255))
    | "ushort" => .ok (.ushort (← unsignedOf json 65535))
    | "uint" => .ok (.uint (← unsignedOf json 4294967295))
    | "ulong" => .ok (.ulong (← unsignedOf json 18446744073709551615))
    | "byte" => .ok (.byte (← signedOf json 8))
    | "short" => .ok (.short (← signedOf json 16))
    | "int" => .ok (.int (← signedOf json 32))
    | "long" => .ok (.long (← signedOf json 64))
    | "float" => .ok (.float (← hexPayloadOf json 4 "float"))
    | "double" => .ok (.double (← hexPayloadOf json 8 "double"))
    | "decimal32" => .ok (.decimal32 (← hexPayloadOf json 4 "decimal32"))
    | "decimal64" => .ok (.decimal64 (← hexPayloadOf json 8 "decimal64"))
    | "decimal128" => .ok (.decimal128 (← hexPayloadOf json 16 "decimal128"))
    | "char" => .ok (.char (← codePointOf json))
    | "timestamp" => .ok (.timestamp (← json.getObjValAs? Int "milliseconds"))
    | "uuid" => .ok (.uuid (← hexPayloadOf json 16 "uuid"))
    | "binary" => .ok (.binary (← ofHex (← json.getObjValAs? String "hex")))
    | "string" => .ok (.string (← json.getObjValAs? String "text"))
    | "symbol" => .ok (.symbol (← json.getObjValAs? String "text"))
    | "list" => do
      let items ← json.getObjValAs? (Array Json) "items"
      return (.list (← items.toList.mapM (valueOfJson fuel)))
    | "array" => do
      let items ← json.getObjValAs? (Array Json) "items"
      let constructor ← ofHex (← json.getObjValAs? String "constructor")
      match constructor.toList with
      | [code] => return (.array code (← items.toList.mapM (valueOfJson fuel)))
      | _ => .error "an array's constructor is one octet"
    | "described" => do
      let descriptorJson ← json.getObjVal? "descriptor"
      let valueJson ← json.getObjVal? "value"
      let descriptor ← valueOfJson fuel descriptorJson
      let value ← valueOfJson fuel valueJson
      return (.described descriptor value)
    | "map" => do
      let pairsJson ← json.getObjValAs? (Array (Array Json)) "pairs"
      let pairs ← pairsJson.toList.mapM (fun pair =>
        match pair.toList with
        | [key, value] => .ok (key, value)
        | _ => .error "a map pair is two values")
      let values ← pairs.mapM (fun (key, value) => do
        let key' ← valueOfJson fuel key
        let value' ← valueOfJson fuel value
        return (key', value'))
      return (.map values)
    | other => .error s!"the corpus vocabulary has no value type '{other}'"

/-! ## Writing

The writer emits the narrowest form the table offers, and takes every octet it
emits from a row of the table. Sizes count the octets that follow the size field,
which is what the reader measures. -/

/-- A variable-width payload: its length in the declaration's own width, then the
payload. The length's width is the array constructor's where this writes element
data, not the element's own preference. -/
def lengthPrefixed (decl : EncodingDecl) (payload : List UInt8) : Except String (List UInt8) := do
  let length ← filled decl.width payload.length
  return length ++ payload

/-- A raw payload written unchanged, provided it is as wide as the declaration says:
an array whose constructor is `float` carries four-octet elements, not whatever
width an element would choose alone. -/
def rawPayload (decl : EncodingDecl) (bits : Octets) : Except String (List UInt8) :=
  if bits.size = decl.width then .ok bits.toList
  else .error s!"a {decl.owner} payload is {decl.width} octet(s) and the value has {bits.size}"

/-- A compound's octets under a declaration: the size field, the count field, then
the body. The size counts the octets after it, so it is the count field's width plus
the body's length. -/
def compoundOctets (decl : EncodingDecl) (count : Nat) (body : List UInt8) :
    Except String (List UInt8) := do
  let size := decl.width + body.length
  if size < 2 ^ (8 * decl.width) ∧ count < 2 ^ (8 * decl.width) then
    return beOctets decl.width size ++ beOctets decl.width count ++ body
  else
    .error s!"no {decl.owner} encoding of width {decl.width} carries {count} item(s) \
      in {body.length} octet(s)"

/-- An array's octets under a declaration: the size field, the count field, the
element constructor, then the elements' data. The size counts the count field, the
constructor and the elements. -/
def arrayOctets (decl : EncodingDecl) (constructor : UInt8) (count : Nat)
    (elements : List UInt8) : Except String (List UInt8) := do
  let size := decl.width + 1 + elements.length
  if size < 2 ^ (8 * decl.width) ∧ count < 2 ^ (8 * decl.width) then
    return beOctets decl.width size ++ beOctets decl.width count ++
      [constructor] ++ elements
  else
    .error s!"no array encoding of width {decl.width} carries {count} element(s) \
      in {elements.length} octet(s)"

/-- A fixed-width declaration's data: as many octets as the row declares, in the
type's own form. A value of another type is refused rather than written short. -/
def writeFixedData (decl : EncodingDecl) (value : Value) : Except String (List UInt8) :=
  match decl.owner, value with
  | "null", .null => .ok []
  | "boolean", .boolean b => if decl.width = 0 then .ok [] else .ok [if b then 1 else 0]
  | "ubyte", .ubyte n => filled decl.width n
  | "ushort", .ushort n => filled decl.width n
  | "uint", .uint n => filled decl.width n
  | "ulong", .ulong n => filled decl.width n
  | "byte", .byte i => twosComplement decl.width i
  | "short", .short i => twosComplement decl.width i
  | "int", .int i => twosComplement decl.width i
  | "long", .long i => twosComplement decl.width i
  | "char", .char codepoint => filled decl.width codepoint
  | "timestamp", .timestamp milliseconds => twosComplement decl.width milliseconds
  | "float", .float bits => rawPayload decl bits
  | "double", .double bits => rawPayload decl bits
  | "decimal32", .decimal32 bits => rawPayload decl bits
  | "decimal64", .decimal64 bits => rawPayload decl bits
  | "decimal128", .decimal128 bits => rawPayload decl bits
  | "uuid", .uuid bits => rawPayload decl bits
  | "list", .list [] => .ok []
  | owner, other =>
    .error s!"the declared surface calls octet 0x{toHex #[UInt8.ofNat decl.code]} a \
      {owner} encoding, which cannot carry {typeName other}"

/-- A variable-width declaration's data: the length in the row's width, then the
payload. -/
def writeVariableData (decl : EncodingDecl) (value : Value) : Except String (List UInt8) :=
  match decl.owner, value with
  | "binary", .binary payload => lengthPrefixed decl payload.toList
  | "string", .string text => lengthPrefixed decl text.toUTF8.toList
  | "symbol", .symbol text => lengthPrefixed decl text.toUTF8.toList
  | owner, other =>
    .error s!"the declared surface calls octet 0x{toHex #[UInt8.ofNat decl.code]} a \
      {owner} encoding, which cannot carry {typeName other}"

/-- A scalar value's octets under the declaration the table gives it: the constructor
octet, then the row's data form. -/
def emitScalar (value : Value) (decl : EncodingDecl) : Except String (List UInt8) := do
  let data ←
    match decl.category with
    | .fixed => writeFixedData decl value
    | .variable => writeVariableData decl value
    | _ =>
      .error s!"the declared surface calls octet 0x{toHex #[UInt8.ofNat decl.code]} a \
        {categoryName decl.category} encoding, whose data is not written as a scalar"
  return tagOf decl ++ data

mutual

/-- A value's octets, constructor octet first, in the narrowest form the declared
surface offers it. Each recursive call is on a strictly smaller subterm of the value
being written, which is the measure `termination_by` names. -/
def writeValue : Value → Except String (List UInt8)
  | .described descriptor inner => do
    let head ← writeValue descriptor
    let tail ← writeValue inner
    return [descriptorPrefix] ++ head ++ tail
  | .null => do
    emitScalar .null (← rowOf "null" 0)
  | .boolean b => do
    emitScalar (.boolean b) (← booleanRow b)
  | .ubyte n => do
    emitScalar (.ubyte n) (← rowOf "ubyte" 1)
  | .ushort n => do
    emitScalar (.ushort n) (← rowOf "ushort" 2)
  | .uint n => do
    emitScalar (.uint n) (← rowOf "uint" (if n = 0 then 0 else if n ≤ 255 then 1 else 4))
  | .ulong n => do
    emitScalar (.ulong n) (← rowOf "ulong" (if n = 0 then 0 else if n ≤ 255 then 1 else 8))
  | .byte i => do
    emitScalar (.byte i) (← rowOf "byte" 1)
  | .short i => do
    emitScalar (.short i) (← rowOf "short" 2)
  | .int i => do
    emitScalar (.int i) (← rowOf "int" 4)
  | .long i => do
    emitScalar (.long i) (← rowOf "long" 8)
  | .float bits => do
    emitScalar (.float bits) (← rowOf "float" bits.size)
  | .double bits => do
    emitScalar (.double bits) (← rowOf "double" bits.size)
  | .decimal32 bits => do
    emitScalar (.decimal32 bits) (← rowOf "decimal32" bits.size)
  | .decimal64 bits => do
    emitScalar (.decimal64 bits) (← rowOf "decimal64" bits.size)
  | .decimal128 bits => do
    emitScalar (.decimal128 bits) (← rowOf "decimal128" bits.size)
  | .char codepoint => do
    emitScalar (.char codepoint) (← rowOf "char" 4)
  | .timestamp milliseconds => do
    emitScalar (.timestamp milliseconds) (← rowOf "timestamp" 8)
  | .uuid bits => do
    emitScalar (.uuid bits) (← rowOf "uuid" bits.size)
  | .binary payload => do
    emitScalar (.binary payload) (← rowOf "binary" (if payload.size ≤ 255 then 1 else 4))
  | .string text => do
    let payload := text.toUTF8.toList
    let decl ← rowOf "string" (if payload.length ≤ 255 then 1 else 4)
    return tagOf decl ++ (← lengthPrefixed decl payload)
  | .symbol text => do
    let payload := text.toUTF8.toList
    let decl ← rowOf "symbol" (if payload.length ≤ 255 then 1 else 4)
    return tagOf decl ++ (← lengthPrefixed decl payload)
  | .list items => do
    if items.isEmpty then emitScalar (.list items) (← rowOf "list" 0)
    else
      let body ← writeItems items
      let decl ← rowOf "list" (if body.length + 1 ≤ 255 && items.length ≤ 255 then 1 else 4)
      return tagOf decl ++ (← compoundOctets decl items.length body)
  | .map pairs => do
    let body ← writePairs pairs
    let count := 2 * pairs.length
    let decl ← rowOf "map" (if body.length + 1 ≤ 255 && count ≤ 255 then 1 else 4)
    return tagOf decl ++ (← compoundOctets decl count body)
  | .array constructor items => do
    if items.length > arrayElementLimit then
      .error (refusal "limit" s!"an array of {items.length} element(s): this writer \
        materialises at most {arrayElementLimit}")
    else
      let elementDecl ← elementDecl? constructor
      let elements ← writeElements items elementDecl constructor
      let decl ← rowOf "array"
        (if elements.length + 2 ≤ 255 && items.length ≤ 255 then 1 else 4)
      return tagOf decl ++ (← arrayOctets decl constructor items.length elements)
termination_by value => sizeOf value

/-- Items in order, each carrying its own constructor. -/
def writeItems : List Value → Except String (List UInt8)
  | [] => .ok []
  | item :: rest => do
    let head ← writeValue item
    let tail ← writeItems rest
    return head ++ tail
termination_by items => sizeOf items

/-- A map's pairs in wire order. -/
def writePairs : List (Value × Value) → Except String (List UInt8)
  | [] => .ok []
  | (key, value) :: rest => do
    let head ← writeValue key
    let middle ← writeValue value
    let tail ← writePairs rest
    return head ++ middle ++ tail
termination_by pairs => sizeOf pairs

/-- Array elements' data, each in the array's declared constructor form. -/
def writeElements : List Value → Option EncodingDecl → UInt8 → Except String (List UInt8)
  | [], _, _ => .ok []
  | item :: rest, elementDecl, constructor => do
    let head ← writeDeclared item elementDecl constructor
    let tail ← writeElements rest elementDecl constructor
    return head ++ tail
termination_by items _ _ => sizeOf items + 1

/-- One element's data: the array's constructor is already written, so what follows is
either the row that constructor names or, under the descriptor prefix, the element's
own descriptor and value. -/
def writeDeclared : Value → Option EncodingDecl → UInt8 → Except String (List UInt8)
  | .described descriptor inner, none, _ => do
    let head ← writeValue descriptor
    let tail ← writeValue inner
    return head ++ tail
  | item, none, constructor =>
    .error s!"an array whose element constructor is 0x{toHex #[constructor]} carries \
      described values, not {typeName item}"
  | item, some decl, _ =>
    match decl.category with
    | .fixed => writeFixedData decl item
    | .variable => writeVariableData decl item
    | .compound => writeCompoundData item decl
    | .array => writeArrayData item decl
termination_by item _ _ => sizeOf item + 1

/-- A compound's data: its items, then the size and count fields that announce them. -/
def writeCompoundData : Value → EncodingDecl → Except String (List UInt8)
  | .list items, decl => do
    let body ← writeItems items
    compoundOctets decl items.length body
  | .map pairs, decl => do
    let body ← writePairs pairs
    compoundOctets decl (2 * pairs.length) body
  | item, decl =>
    .error s!"the declared surface calls octet 0x{toHex #[UInt8.ofNat decl.code]} a \
      {decl.owner} encoding, which cannot carry {typeName item}"
termination_by item _ => sizeOf item

/-- An array's data: its elements' data, then the size and count fields that
announce them. -/
def writeArrayData : Value → EncodingDecl → Except String (List UInt8)
  | .array constructor items, decl => do
    if items.length > arrayElementLimit then
      .error (refusal "limit" s!"an array of {items.length} element(s): this writer \
        materialises at most {arrayElementLimit}")
    else
      let elementDecl ← elementDecl? constructor
      let elements ← writeElements items elementDecl constructor
      arrayOctets decl constructor items.length elements
  | item, _ => .error s!"an array encoding cannot carry {typeName item}"
termination_by item _ => sizeOf item

end

/-- Encode a value in the narrowest form the declared surface offers for it. -/
def encodeValue (value : Value) : Except String Octets := do
  return (← writeValue value).toArray

/-- The specification behind the corpus interface: `Spec.Value`'s classification and
`Generated.Oasis.Encodings`' declared surface, read and written. -/
def specCodec : Codec where
  name := "specification"
  decode := fun bytes =>
    match decodeValue bytes with
    | .ok (value, consumed) => .ok (toJson value, consumed)
    | .error e => .error e
  encode := fun json => do
    let value ← valueOfJson 64 json
    encodeValue value

end SpecAMQP.Spec.Codec
