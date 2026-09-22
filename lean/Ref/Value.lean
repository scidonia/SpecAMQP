/-!
# A reference implementation of the AMQP 1.0 type system

This is a reference *implementation*, written from the OASIS clauses, not derived
from `Spec.*`: it shares no definition with the specification, so agreement
between the two is evidence rather than a tautology. Where the clauses mandate a
behaviour it must match them; where they leave latitude this module makes a
definite choice and records it.

It is written to be extracted: plain data, structural recursion, no proofs, no
`Spec` import, no `partial`. `lake exe amqp-ref` runs it over the vector corpus.

Deliberate choices, none of which a clause fixes:

* **Narrowest encoding where the type has a choice, and that choice is ours.**
  A writer emits the smallest encoding that carries the value for the unsigned and
  variable-width forms (`uint 0` as `0x43`, `uint 300` as `0x70`, `ulong 0` as
  `0x44`, a 30-octet string as `0xa1`), the specificity-preserving reading of
  Part 1's subcategory table. For signed `int` and `long` it always emits the
  fixed four- and eight-octet forms (`0x71`, `0x81`), because nothing in the
  clauses says which of a type's encodings to prefer: a reader accepts every
  declared encoding (`0x54`/`0x55` included), and the choice of form to write is
  an implementation's, not a requirement. The corpus pins these octets.
* **Unassigned octets are rejected**, including the twelve escape octets the
  constructor grammar reserves for future formats, rather than skipped.
* **A legal constructor this implementation cannot read is reported as
  `unsupported`**, not as `unassigned`: an octet outside the grammar and a gap in
  the reader are different facts, and conflating them would make the reader's
  error say something false about the grammar. The type reader reads every
  constructor the table assigns, so it raises `unsupported` nowhere; the frame
  layer raises it for a legal constructor that is not a frame type or not the
  performative a body's descriptor names, and the variant stays in the taxonomy
  for a form a later revision of the artifact could add.
* **Arrays carry a constructor octet** rather than a resolved element type; a
  reader requires every element's data to be well formed under that constructor.
* **Sizes count the octets that follow the size field** — count, the array
  element constructor, then the encoded items — the reading recorded in
  `ledger/ambiguities/compound-size-field.json`.
* **A compound value must match its declared size**; a mismatch is a decode error
  rather than something to resynchronise past.
* **Strings and symbols must be valid UTF-8** (symbols are ASCII on the wire, so
  this is the stricter of the two rules and makes both agree).
* **Float, double, the three decimals and uuid are carried as their payload
  octets**, never as numbers: the artifact fixes those encodings' framing, and
  nothing here does arithmetic on a decimal. A reader takes the width the
  constructor fixes and does not interpret what it read.
* **A char is a code point written UTF-32BE.** The reader takes the four octets
  and does not adjudicate whether the code point is an assigned Unicode scalar:
  the artifact fixes the framing of the character, and the corpus vocabulary
  range-checks the code point on the way in.
* **A map keeps its pairs in wire order** and its count field counts *items*, so a
  pair contributes two, exactly as Part 1's compound layout counts them. An odd
  item count is malformed — Part 1 requires an even number of items — and the size
  agreement a list needs applies unchanged.
* **An array's elements are read in the array's declared constructor form**, and
  that form is read for every constructor the grammar assigns: a scalar is its
  width or its length prefix, the descriptor prefix `%x00` carries the element's
  own descriptor and value, a compound carries its own size and count, and an array
  carries its own size, count, element constructor and elements. Nothing but
  `arrayElementLimit` bounds an array's breadth, and nothing but the octet count
  bounds its depth.
* **A writer writes the array's declared element form, never the element's own
  preference**, down to the width of a size or count field: an array whose element
  constructor is `list8` writes one-octet sizes and counts, and an array whose
  element constructor is a narrow small integer writes one octet. Where the
  declared form cannot carry an element — a value of another type, or a compound
  or array whose size or count does not fit the declared width — the writer refuses
  it by name rather than masking a field or writing a different form, so the
  writer's domain stays inside what the reader accepts.
-/

namespace SpecAMQP.Ref

/-- Bytes on the wire. -/
abbrev Octets := Array UInt8

/-- A decoded AMQP value, in the shapes this implementation handles. -/
inductive Value where
  | null
  | boolean (b : Bool)
  | ubyte (n : UInt8)
  | ushort (n : UInt16)
  | uint (n : UInt32)
  | ulong (n : UInt64)
  | byte (n : Int8)
  | short (n : Int16)
  | int (n : Int32)
  | long (n : Int64)
  | string (s : String)
  | symbol (s : String)
  | binary (b : List UInt8)
  /-- A single Unicode character, carried as its code point and written UTF-32BE. -/
  | char (codepoint : UInt32)
  /-- Milliseconds since the Unix epoch, a signed 64-bit quantity written in
  two's complement. -/
  | timestamp (milliseconds : Int64)
  /-- IEEE 754-2008 binary32, carried as its four payload octets. The artifact
  fixes the framing of this encoding, not arithmetic on its value. -/
  | float (octets : Octets)
  /-- IEEE 754-2008 binary64, carried as its eight payload octets. -/
  | double (octets : Octets)
  /-- IEEE 754-2008 decimal32 in the Binary Integer Decimal encoding, carried as
  its four payload octets. -/
  | decimal32 (octets : Octets)
  /-- IEEE 754-2008 decimal64 in the Binary Integer Decimal encoding, carried as
  its eight payload octets. -/
  | decimal64 (octets : Octets)
  /-- IEEE 754-2008 decimal128 in the Binary Integer Decimal encoding, carried as
  its sixteen payload octets. -/
  | decimal128 (octets : Octets)
  /-- A UUID as defined by RFC-4122 section 4.1.2, carried as its sixteen octets:
  the artifact fixes the width and the octet order, not the fields' meaning. -/
  | uuid (octets : Octets)
  | list (items : List Value)
  /-- A map, as an ordered sequence of key-value pairs. Part 1 requires the pairs'
  order to be preserved unless the map is known to be unordered, so this holds
  them in the order they appeared and the derived `BEq` compares that sequence:
  two maps differing only in pair order are different values. -/
  | map (pairs : List (Value × Value))
  /-- An array as it appears on the wire: one constructor octet and the element
  data, without the elements' own constructors. -/
  | array (constructor : UInt8) (items : List Value)
  | described (descriptor : Value) (value : Value)
deriving Repr, BEq, Inhabited
-- `DecidableEq` is deliberately not derived: it does not apply to an inductive
-- with nested occurrences of itself. The runner compares values with `BEq`.

/-- Why a decode failed. Every variant is `amqp:decode-error` on the wire; the
detail exists for diagnostics and for vectors to name what they expect. -/
inductive DecodeError where
  | truncated (context : String)
  /-- The octet is not an encoding the constructor grammar assigns: below every
  format-code range, one of the escapes reserved for future formats, or a format
  code the table leaves unassigned. -/
  | unassigned (octet : UInt8)
  /-- The octet is a legal constructor, but in a form this implementation does not
  read yet. Distinct from `unassigned` so that a gap in the reader is never
  reported as a claim about the grammar — an array of compound elements, for
  instance, is legal and simply unsupported here. -/
  | unsupported (octet : UInt8)
  | sizeMismatch (context : String) (declared : Nat) (observed : Nat)
  | malformed (reason : String)
  /-- A count this reader will not materialise. An array's element count is bounded by
  the width of its count field and by nothing in the data, so a legal encoding can
  declare billions of zero-width elements in ten octets; the declared
  `arrayElementLimit` bounds what this implementation materialises, and exceeding it is
  its own class rather than a grammar error, a truncation or a gap. -/
  | limit (context : String)
deriving Repr, BEq

/-- A cursor over the input. -/
structure Cursor where
  data : Octets
  pos : Nat
deriving Repr

/-- Reading either yields a value and the rest of the input, or fails.

A notation rather than an abbreviation, deliberately: a parameterised `abbrev`
hides the monad from instance search, so `do` blocks over it fail to find `Bind`.
A notation expands during elaboration, so the monad below is visibly
`Except DecodeError` and `do` works. -/
notation "Result" α:max => Except DecodeError (α × Cursor)

/-- One octet. -/
def takeU8 (c : Cursor) : Result UInt8 :=
  if h : c.pos < c.data.size then
    .ok (c.data[c.pos]'h, ⟨c.data, c.pos + 1⟩)
  else
    .error (.truncated "octet")

/-- Exactly `n` octets. -/
def takeBytes (n : Nat) (c : Cursor) : Result Octets :=
  if c.pos + n ≤ c.data.size then
    .ok (c.data.extract c.pos (c.pos + n), ⟨c.data, c.pos + n⟩)
  else
    .error (.truncated s!"{n} octets")

/-- `n` big-endian octets as a number. Every AMQP numeric encoding is big-endian. -/
def takeBeU (width : Nat) (c : Cursor) : Result Nat := do
  let (bytes, c) ← takeBytes width c
  return (bytes.foldl (fun acc byte => acc * 256 + byte.toNat) 0, c)

/-- Big-endian writers for each width. -/
def u16be (n : Nat) : Octets := #[(n / 256).toUInt8, n.toUInt8]

def u32be (n : Nat) : Octets :=
  #[(n / 16777216).toUInt8, (n / 65536).toUInt8, (n / 256).toUInt8, n.toUInt8]

def u64be (n : Nat) : Octets :=
  #[(n / 72057594037927936).toUInt8, (n / 281474976710656).toUInt8,
    (n / 1099511627776).toUInt8, (n / 4294967296).toUInt8,
    (n / 16777216).toUInt8, (n / 65536).toUInt8, (n / 256).toUInt8, n.toUInt8]

/-- Bytes as a `String`, or a malformed-input error. -/
def decodeString (bytes : Octets) (kind : String) : Except DecodeError String :=
  match String.fromUTF8? (ByteArray.mk bytes) with
  | some s => .ok s
  | none => .error (.malformed s!"{kind} is not valid UTF-8")

/-- A string or symbol payload decoded against the cursor it was taken from. The
decoder consumes nothing — the length prefix was already taken — so it hands the
cursor back unchanged, which is what lets a reader bind a value and a cursor in one
`do` step rather than re-pairing them at every call site. -/
def decodeStringAt (bytes : Octets) (kind : String) (c : Cursor) :
    Except DecodeError (String × Cursor) :=
  match decodeString bytes kind with
  | .ok s => .ok (s, c)
  | .error e => .error e

/-- A one-octet two's-complement integer as a number. The narrow `smallint` and
`smalllong` forms carry a signed octet, and both the types that use them are wider
than the octet, so the sign must be extended rather than read as an unsigned byte. -/
def signedOctet (n : UInt8) : Int :=
  (Int8.ofBitVec (BitVec.ofNat 8 n.toNat)).toInt

/-- Whether an octet is a constructor an array element can carry: the descriptor
prefix, or one of the format codes the table assigns.

Part 1's grammar makes an array's element constructor a *constructor* — a
`format-code` or the descriptor prefix — and its `format-code` production admits all
four categories, so a scalar, a compound and an array are each legal as element data.
Anything else is not a constructor the grammar assigns: an octet below `%x40`, one of
the escapes reserved for future formats, or a format code the table leaves unassigned.
An array is refused on this before its first element is read, which is what makes an
array with no elements and an unassigned constructor a refusal rather than empty. -/
def assignedConstructor (octet : UInt8) : Bool :=
  match octet with
  | 0x00                                                          -- the descriptor prefix
  | 0x40 | 0x41 | 0x42 | 0x43 | 0x44 | 0x45
  | 0x50 | 0x51 | 0x52 | 0x53 | 0x54 | 0x55 | 0x56
  | 0x60 | 0x61 | 0x70 | 0x71 | 0x72 | 0x73 | 0x74
  | 0x80 | 0x81 | 0x82 | 0x83 | 0x84 | 0x94 | 0x98
  | 0xA0 | 0xA1 | 0xA3 | 0xB0 | 0xB1 | 0xB3
  | 0xC0 | 0xC1 | 0xD0 | 0xD1
  | 0xE0 | 0xF0 => true
  | _ => false

mutual

/-- Read one value.

`fuel` bounds the recursion and decreases at every recursive call, including the
iterator that reads a compound's items, which is what makes this reader total
without `partial`. Callers pass the number of octets in the input: every step
consumes at least one octet, so a well-formed encoding never exhausts it, and a
malformed one fails on truncation rather than looping. -/
def readValue : Nat → Cursor → Result Value
  | 0, _ => .error (.truncated "no octets left")
  | fuel + 1, c => do
    let (code, c) ← takeU8 c
    match code with
    | 0x00 =>                                   -- described: descriptor, then value
      let (descriptor, c) ← readValue fuel c
      let (value, c) ← readValue fuel c
      return (.described descriptor value, c)
    | 0x40 => return (.null, c)
    | 0x41 => return (.boolean true, c)
    | 0x42 => return (.boolean false, c)
    | 0x43 => return (.uint 0, c)
    | 0x44 => return (.ulong 0, c)
    | 0x45 => return (.list [], c)
    | 0x56 =>
      let (octet, c) ← takeU8 c
      return (.boolean (octet != 0x00), c)      -- any non-zero octet is true
    | 0x50 => let (n, c) ← takeU8 c; return (.ubyte n, c)
    | 0x51 => let (n, c) ← takeU8 c
              return (.byte (Int8.ofBitVec (BitVec.ofNat 8 n.toNat)), c)
    | 0x52 => let (n, c) ← takeU8 c; return (.uint n.toUInt32, c)
    | 0x53 => let (n, c) ← takeU8 c; return (.ulong n.toUInt64, c)
    | 0x54 => let (n, c) ← takeU8 c
              return (.int (Int32.ofBitVec
                (BitVec.ofNat 32 (signedOctet n % 4294967296).toNat)), c)
    | 0x55 => let (n, c) ← takeU8 c
              return (.long (Int64.ofBitVec
                (BitVec.ofNat 64 (signedOctet n % 18446744073709551616).toNat)), c)
    | 0x60 => let (n, c) ← takeBeU 2 c; return (.ushort n.toUInt16, c)
    | 0x61 => let (n, c) ← takeBeU 2 c
              return (.short (Int16.ofBitVec (BitVec.ofNat 16 n)), c)
    | 0x70 => let (n, c) ← takeBeU 4 c; return (.uint n.toUInt32, c)
    | 0x71 => let (n, c) ← takeBeU 4 c
              return (.int (Int32.ofBitVec (BitVec.ofNat 32 n)), c)
    | 0x72 => let (b, c) ← takeBytes 4 c; return (.float b, c)
    | 0x73 => let (n, c) ← takeBeU 4 c;  return (.char n.toUInt32, c)
    | 0x74 => let (b, c) ← takeBytes 4 c; return (.decimal32 b, c)
    | 0x80 => let (n, c) ← takeBeU 8 c; return (.ulong n.toUInt64, c)
    | 0x81 => let (n, c) ← takeBeU 8 c
              return (.long (Int64.ofBitVec (BitVec.ofNat 64 n)), c)
    | 0x82 => let (b, c) ← takeBytes 8 c;  return (.double b, c)
    | 0x83 => let (n, c) ← takeBeU 8 c
              return (.timestamp (Int64.ofBitVec (BitVec.ofNat 64 n)), c)
    | 0x84 => let (b, c) ← takeBytes 8 c;  return (.decimal64 b, c)
    | 0x94 => let (b, c) ← takeBytes 16 c; return (.decimal128 b, c)
    | 0x98 => let (b, c) ← takeBytes 16 c; return (.uuid b, c)
    | 0xA0 => let (n, c) ← takeU8 c;      let (b, c) ← takeBytes n.toNat c
              return (.binary b.toList, c)
    | 0xB0 => let (n, c) ← takeBeU 4 c;   let (b, c) ← takeBytes n c
              return (.binary b.toList, c)
    | 0xA1 => let (n, c) ← takeU8 c;      let (b, c) ← takeBytes n.toNat c
              let (s, c) ← decodeStringAt b "string" c
              return (.string s, c)
    | 0xB1 => let (n, c) ← takeBeU 4 c;   let (b, c) ← takeBytes n c
              let (s, c) ← decodeStringAt b "string" c
              return (.string s, c)
    | 0xA3 => let (n, c) ← takeU8 c;      let (b, c) ← takeBytes n.toNat c
              let (s, c) ← decodeStringAt b "symbol" c
              return (.symbol s, c)
    | 0xB3 => let (n, c) ← takeBeU 4 c;   let (b, c) ← takeBytes n c
              let (s, c) ← decodeStringAt b "symbol" c
              return (.symbol s, c)
    | 0xC0 => readCompound fuel 1 c
    | 0xC1 => readMap fuel 1 c
    | 0xD0 => readCompound fuel 4 c
    | 0xD1 => readMap fuel 4 c
    | 0xE0 => readArray fuel 1 c
    | 0xF0 => readArray fuel 4 c
    | other => .error (.unassigned other)
termination_by fuel _ => (fuel, 0)

/-- `count` items, each with its own constructor.

Both components of the measure decrease here: the fuel, once per item, and the count.
The pair is what makes the measure decrease at every call in this block — the item
loop needs fuel to fall, the element loop needs a count that falls without spending
the fuel a zero-width element must not cost, and a single Nat cannot serve both. -/
def readItems : Nat → Nat → Cursor → Result (List Value)
  | 0, _, _ => .error (.truncated "no octets left")
  | _, 0, c => .ok ([], c)
  | fuel + 1, count + 1, c => do
    let (item, c) ← readValue fuel c
    let (rest, c) ← readItems fuel count c
    return (item :: rest, c)
termination_by fuel count _ => (fuel, count)

/-- A compound list: `size`, `count`, then `count` constructed items. The size
counts the octets that follow it, so it must agree with what was read. One unit of
fuel is spent for the header, which occupies at least two octets. -/
def readCompound : Nat → Nat → Cursor → Result Value
  | 0, _, _ => .error (.truncated "no octets left")
  | fuel + 1, width, c => do
    let (size, c) ← takeBeU width c
    let start := c.pos                  -- the size counts what follows it
    let (count, c) ← takeBeU width c
    let (items, c) ← readItems fuel count c
    if c.pos - start != size then
      .error (.sizeMismatch "list" size (c.pos - start))
    else
      return (.list items, c)
termination_by fuel _ _ => (fuel, 0)

/-- A map: `size`, `count` constructed items, then the same size agreement a list
requires. Part 1 requires an even number of items, so an odd count is malformed
rather than a map with a dangling key. Pairs keep the order they arrived in. -/
def readMap : Nat → Nat → Cursor → Result Value
  | 0, _, _ => .error (.truncated "no octets left")
  | fuel + 1, width, c => do
    let (size, c) ← takeBeU width c
    let start := c.pos                  -- the size counts what follows it
    let (count, c) ← takeBeU width c
    let (items, c) ← readItems fuel count c
    if c.pos - start != size then
      .error (.sizeMismatch "map" size (c.pos - start))
    else
      match pairUp items with
      | some pairs => return (.map pairs, c)
      | none => .error (.malformed "a map must have an even number of items")
termination_by fuel _ _ => (fuel, 0)

/-- Items taken two at a time, key then value: the pairing a map encoding
requires. `none` is an odd item count, which is not a map. -/
def pairUp : List Value → Option (List (Value × Value))
  | [] => some []
  | key :: value :: rest => (pairUp rest).map (fun pairs => (key, value) :: pairs)
  | [_] => none

/-- The most array elements this reader materialises.

Part 1 fixes an array as `size`, `count`, one element constructor, then `count`
elements in that constructor's form, and its table assigns width zero to six legal
element constructors (`null`, `true`, `false` and the zero forms of the integers and
of `list`). Those two rules together admit an encoding that declares billions of
elements in ten octets, because the count is bounded by the width of the count field
and by nothing in the data. This implementation models an array as a list of values,
so it declares the count it will materialise rather than discovering a bound in
whatever recursion device the reader happens to use.

The same number is declared by the specification (`SpecAMQP.Spec.Codec.arrayElementLimit`),
because a limit that differed between the two would make the differential contract
compare two different specifications. The decision is recorded in
`ledger/ambiguities/zero-width-array-count.json`. -/
def arrayElementLimit : Nat := 65536

/-- An array: `size`, `count`, one element constructor, then `count` element data
blocks in that constructor's form, each without its own constructor. One unit of fuel
is spent for the array's own header, which occupies at least three octets.

The element constructor is checked before the first element is read, so an array whose
constructor is not a format code the grammar assigns is refused even when it declares
no elements — the same refusal the specification's element-constructor lookup makes,
and the reason `readElement`'s own `unassigned` clause is a second line of defence
rather than the one an array reader reaches. -/
def readArray : Nat → Nat → Cursor → Result Value
  | 0, _, _ => .error (.truncated "no octets left")
  | fuel + 1, width, c => do
    let (size, c) ← takeBeU width c
    let start := c.pos                  -- the size counts what follows it
    let (count, c) ← takeBeU width c
    if count > arrayElementLimit then
      .error (.limit s!"an array declares {count} element(s): this reader materialises \
        at most {arrayElementLimit}")
    else do
      let (constructor, c) ← takeU8 c
      if !assignedConstructor constructor then
        .error (.unassigned constructor)
      else do
        let (items, c) ← readElements fuel constructor count c
        if c.pos - start != size then
          .error (.sizeMismatch "array" size (c.pos - start))
        else
          return (.array constructor items, c)
termination_by fuel _ _ => (fuel, 0)

/-- `count` array elements, each in the array's element constructor form. The count is
what decreases here, so an element whose data occupies no octets is still an element:
such an array is bounded by `arrayElementLimit`, not by the buffer. The fuel is handed
to each element unchanged, and spent only where an element opens a container of its
own, so an array of `count` zero-width elements reads however short the buffer is. -/
def readElements : Nat → UInt8 → Nat → Cursor → Result (List Value)
  | _, _, 0, c => .ok ([], c)
  | fuel, constructor, count + 1, c => do
    let (item, c) ← readElement fuel constructor c
    let (rest, c) ← readElements fuel constructor count c
    return (item :: rest, c)
termination_by fuel _ count _ => (fuel, count)

/-- One array element: the data its constructor fixes, without the constructor's own
octet, because the array states that octet once.

Each category's element data is what its own encoding would carry after its
constructor: a fixed form is its width of octets, a variable form carries its own
length prefix, the descriptor prefix `%x00` carries the element's own descriptor and
value, a compound form carries its own size and count, and an array form carries its
own size, count, element constructor and elements. Only the container forms spend
fuel, so a zero-width element costs the array nothing but its count. -/
def readElement : Nat → UInt8 → Cursor → Result Value
  | _, 0x40, c => .ok (.null, c)
  | _, 0x41, c => .ok (.boolean true, c)
  | _, 0x42, c => .ok (.boolean false, c)
  | _, 0x43, c => .ok (.uint 0, c)
  | _, 0x44, c => .ok (.ulong 0, c)
  | _, 0x45, c => .ok (.list [], c)
  | _, 0x50, c => do let (n, c) ← takeU8 c; return (.ubyte n, c)
  | _, 0x51, c => do
    let (n, c) ← takeU8 c
    return (.byte (Int8.ofBitVec (BitVec.ofNat 8 n.toNat)), c)
  | _, 0x52, c => do let (n, c) ← takeU8 c; return (.uint n.toUInt32, c)
  | _, 0x53, c => do let (n, c) ← takeU8 c; return (.ulong n.toUInt64, c)
  | _, 0x54, c => do
    let (n, c) ← takeU8 c
    return (.int (Int32.ofBitVec
      (BitVec.ofNat 32 (signedOctet n % 4294967296).toNat)), c)
  | _, 0x55, c => do
    let (n, c) ← takeU8 c
    return (.long (Int64.ofBitVec
      (BitVec.ofNat 64 (signedOctet n % 18446744073709551616).toNat)), c)
  | _, 0x56, c => do
    let (octet, c) ← takeU8 c
    return (.boolean (octet != 0x00), c)
  | _, 0x60, c => do let (n, c) ← takeBeU 2 c; return (.ushort n.toUInt16, c)
  | _, 0x61, c => do
    let (n, c) ← takeBeU 2 c
    return (.short (Int16.ofBitVec (BitVec.ofNat 16 n)), c)
  | _, 0x70, c => do let (n, c) ← takeBeU 4 c; return (.uint n.toUInt32, c)
  | _, 0x71, c => do
    let (n, c) ← takeBeU 4 c
    return (.int (Int32.ofBitVec (BitVec.ofNat 32 n)), c)
  | _, 0x72, c => do let (b, c) ← takeBytes 4 c; return (.float b, c)
  | _, 0x73, c => do let (n, c) ← takeBeU 4 c; return (.char n.toUInt32, c)
  | _, 0x74, c => do let (b, c) ← takeBytes 4 c; return (.decimal32 b, c)
  | _, 0x80, c => do let (n, c) ← takeBeU 8 c; return (.ulong n.toUInt64, c)
  | _, 0x81, c => do
    let (n, c) ← takeBeU 8 c
    return (.long (Int64.ofBitVec (BitVec.ofNat 64 n)), c)
  | _, 0x82, c => do let (b, c) ← takeBytes 8 c; return (.double b, c)
  | _, 0x83, c => do
    let (n, c) ← takeBeU 8 c
    return (.timestamp (Int64.ofBitVec (BitVec.ofNat 64 n)), c)
  | _, 0x84, c => do let (b, c) ← takeBytes 8 c; return (.decimal64 b, c)
  | _, 0x94, c => do let (b, c) ← takeBytes 16 c; return (.decimal128 b, c)
  | _, 0x98, c => do let (b, c) ← takeBytes 16 c; return (.uuid b, c)
  | _, 0xA0, c => do
    let (n, c) ← takeU8 c
    let (b, c) ← takeBytes n.toNat c
    return (.binary b.toList, c)
  | _, 0xA1, c => do
    let (n, c) ← takeU8 c
    let (b, c) ← takeBytes n.toNat c
    let (s, c) ← decodeStringAt b "string" c
    return (.string s, c)
  | _, 0xA3, c => do
    let (n, c) ← takeU8 c
    let (b, c) ← takeBytes n.toNat c
    let (s, c) ← decodeStringAt b "symbol" c
    return (.symbol s, c)
  | _, 0xB0, c => do
    let (n, c) ← takeBeU 4 c
    let (b, c) ← takeBytes n c
    return (.binary b.toList, c)
  | _, 0xB1, c => do
    let (n, c) ← takeBeU 4 c
    let (b, c) ← takeBytes n c
    let (s, c) ← decodeStringAt b "string" c
    return (.string s, c)
  | _, 0xB3, c => do
    let (n, c) ← takeBeU 4 c
    let (b, c) ← takeBytes n c
    let (s, c) ← decodeStringAt b "symbol" c
    return (.symbol s, c)
  | fuel + 1, 0x00, c => do                 -- described: descriptor, then value
    let (descriptor, c) ← readValue fuel c
    let (value, c) ← readValue fuel c
    return (.described descriptor value, c)
  | fuel + 1, 0xC0, c => readCompound fuel 1 c
  | fuel + 1, 0xC1, c => readMap fuel 1 c
  | fuel + 1, 0xD0, c => readCompound fuel 4 c
  | fuel + 1, 0xD1, c => readMap fuel 4 c
  | fuel + 1, 0xE0, c => readArray fuel 1 c
  | fuel + 1, 0xF0, c => readArray fuel 4 c
  -- A container or described element with no fuel left: the octet count bounds the
  -- depth of these forms, so no octets remain for one to open.
  | 0, 0x00, _ | 0, 0xC0, _ | 0, 0xC1, _ | 0, 0xD0, _ | 0, 0xD1, _ | 0, 0xE0, _ | 0, 0xF0, _ =>
    .error (.truncated "no octets left")
  | _, other, _ => .error (.unassigned other)
termination_by fuel _ _ => (fuel, 0)

end

/-- Decode a buffer: the value, and how many octets it consumed. -/
def decode (bytes : Octets) : Except DecodeError (Value × Nat) :=
  match readValue bytes.size ⟨bytes, 0⟩ with
  | .ok (value, c) => .ok (value, c.pos)
  | .error e => .error e

/-! ## Writing

Encoders emit the narrowest encoding that carries the value, and sizes count the
octets that follow the size field — the count field (whose width depends on the
form), the array element constructor, then the items — exactly as the reader
requires. -/

/-- A variable-width encoding: the narrow form when the payload fits its octet,
the wide form otherwise, constructor included. -/
def variableData (narrow wide : UInt8) (payload : List UInt8) : Octets :=
  if payload.length ≤ 255 then
    #[narrow, payload.length.toUInt8] ++ payload.toArray
  else
    #[wide] ++ u32be payload.length ++ payload.toArray

/-- Variable-width element data, whose length width is the array's constructor's, not
the element's preference: an array of `str8` elements carries one-octet lengths, an
array of `str32` elements four-octet ones. A payload whose length does not fit the
declared width is refused rather than masked into a shorter length, which would
announce a payload the octets do not carry. -/
def elementVariableData (constructor : UInt8) (form : String) (payload : List UInt8) :
    Except String Octets :=
  if constructor == 0xB0 || constructor == 0xB1 || constructor == 0xB3 then
    .ok (u32be payload.length ++ payload.toArray)
  else if payload.length ≤ 255 then
    .ok (#[payload.length.toUInt8] ++ payload.toArray)
  else
    .error s!"limit: a {form} element carries {payload.length} octet(s), which a \
      one-octet length field cannot announce"

/-- A value's type in the corpus's own words: what a refusal names when the value and the
constructor disagree. -/
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
  | .string _ => "string"
  | .symbol _ => "symbol"
  | .binary _ => "binary"
  | .char _ => "char"
  | .timestamp _ => "timestamp"
  | .float _ => "float"
  | .double _ => "double"
  | .decimal32 _ => "decimal32"
  | .decimal64 _ => "decimal64"
  | .decimal128 _ => "decimal128"
  | .uuid _ => "uuid"
  | .list _ => "list"
  | .map _ => "map"
  | .array _ _ => "array"
  | .described _ _ => "described"

/-- A one-octet unsigned element, refused by name when the value does not fit the octet
the array's declared constructor gives it: masking the value would write a different
value, which a reader would then accept. -/
def elementOctet (kind : String) (n : Nat) : Except String Octets :=
  if n ≤ 255 then .ok #[n.toUInt8]
  else .error s!"limit: a {kind} element carries one octet and {n} does not fit"

/-- A one-octet signed element, on the same terms. -/
def elementSignedOctet (kind : String) (n : Int) : Except String Octets :=
  if -128 ≤ n && n ≤ 127 then .ok #[(n % 256).toNat.toUInt8]
  else .error s!"limit: a {kind} element carries one signed octet and {n} does not fit"

/-- A compound element's data: its items' octets, announced by the size and count
fields of the width the array's constructor fixes. A count or a size the declared width
cannot announce is refused rather than masked. -/
def elementCompoundData (width : Nat) (kind : String) (count : Nat) (body : Octets) :
    Except String Octets :=
  let size := width + body.size
  if width = 1 then
    if size ≤ 255 && count ≤ 255 then .ok (#[size.toUInt8, count.toUInt8] ++ body)
    else .error s!"limit: a {kind}8 element carries {count} item(s) in {body.size} \
      octet(s), which a one-octet size or count field cannot announce"
  else
    .ok (u32be size ++ u32be count ++ body)

mutual

/-- The constructor-and-data encoding of a value. Equation-style clauses rather
than a `match`: a mutual block's `termination_by` hint binds the function's
parameters, and a body that abstracts them itself leaves the hint with nothing to
bind.

Two values are refused rather than written: an array whose element count exceeds
`arrayElementLimit`, and an array whose declared element form cannot carry one of its
elements. The writer's domain has to sit inside what the reader accepts, and emitting
octets the reader would then refuse — or masking a value into a different one — would
make this implementation's own output unreadable or untrue. -/
def encode : Value → Except String Octets
  | .null => .ok #[0x40]
  | .boolean true => .ok #[0x41]
  | .boolean false => .ok #[0x42]
  | .ubyte n => .ok #[0x50, n]
  | .byte n => .ok #[0x51, (n.toBitVec.toNat % 256).toUInt8]
  | .ushort n => .ok (#[0x60] ++ u16be n.toNat)
  | .short n => .ok (#[0x61] ++ u16be (n.toBitVec.toNat % 65536))
  | .uint 0 => .ok #[0x43]
  | .uint n => .ok (if n.toNat ≤ 255 then #[0x52, n.toUInt8] else #[0x70] ++ u32be n.toNat)
  | .int n => .ok (#[0x71] ++ u32be (n.toBitVec.toNat % 4294967296))
  | .ulong 0 => .ok #[0x44]
  | .ulong n => .ok (if n.toNat ≤ 255 then #[0x53, n.toUInt8] else #[0x80] ++ u64be n.toNat)
  | .long n => .ok (#[0x81] ++ u64be (n.toBitVec.toNat % 18446744073709551616))
  | .char n => .ok (#[0x73] ++ u32be n.toNat)
  | .timestamp ms => .ok (#[0x83] ++ u64be (ms.toBitVec.toNat % 18446744073709551616))
  | .float b => .ok (#[0x72] ++ b)
  | .double b => .ok (#[0x82] ++ b)
  | .decimal32 b => .ok (#[0x74] ++ b)
  | .decimal64 b => .ok (#[0x84] ++ b)
  | .decimal128 b => .ok (#[0x94] ++ b)
  | .uuid b => .ok (#[0x98] ++ b)
  | .binary b => .ok (variableData 0xA0 0xB0 b)
  | .string s => .ok (variableData 0xA1 0xB1 s.toUTF8.toList)
  | .symbol s => .ok (variableData 0xA3 0xB3 s.toUTF8.toList)
  | .list [] => .ok #[0x45]
  | .list items => do
    let body ← encodeAll items
    let count := items.length
    return if 1 + body.size ≤ 255 && count ≤ 255 then
      #[0xC0, (1 + body.size).toUInt8, count.toUInt8] ++ body
    else
      #[0xD0] ++ u32be (4 + body.size) ++ u32be count ++ body
  -- There is no map0 form, so even the empty map is a map8 with an empty item
  -- sequence: size 1 (the count octet), count 0.
  | .map [] => .ok #[0xC1, 0x01, 0x00]
  | .map pairs => do
    let body ← encodePairs pairs
    let count := 2 * pairs.length           -- the count field counts items, not pairs
    return if 1 + body.size ≤ 255 && count ≤ 255 then
      #[0xC1, (1 + body.size).toUInt8, count.toUInt8] ++ body
    else
      #[0xD1] ++ u32be (4 + body.size) ++ u32be count ++ body
  | .array constructor items =>
    if items.length > arrayElementLimit then
      .error s!"limit: an array of {items.length} element(s): this writer materialises \
        at most {arrayElementLimit}"
    else do
      let body ← arrayElementItems constructor items
      let count := items.length
      .ok (if 2 + body.size ≤ 255 && count ≤ 255 then
        #[0xE0, (2 + body.size).toUInt8, count.toUInt8, constructor] ++ body
      else
        #[0xF0] ++ u32be (5 + body.size) ++ u32be count ++ #[constructor] ++ body)
  | .described descriptor value => do
    let head ← encode descriptor
    let tail ← encode value
    return #[0x00] ++ head ++ tail
termination_by value => sizeOf value

/-- Items concatenated in order. Structural recursion over the list, so that the
mutual block's measure is `sizeOf` on each function's own argument. -/
def encodeAll : List Value → Except String Octets
  | [] => .ok #[]
  | item :: rest => do
    let head ← encode item
    let tail ← encodeAll rest
    return head ++ tail
termination_by items => sizeOf items

/-- A map's items concatenated in order: each key followed by its value, both with
their own constructors, exactly as a compound's items are written. -/
def encodePairs : List (Value × Value) → Except String Octets
  | [] => .ok #[]
  | (key, value) :: rest => do
    let head ← encode key
    let middle ← encode value
    let tail ← encodePairs rest
    return head ++ middle ++ tail
termination_by pairs => sizeOf pairs

/-- An array's elements, each in the array's declared element constructor form: what an
array's octets carry after its size, its count and its one constructor octet. -/
def arrayElementItems (constructor : UInt8) : List Value → Except String Octets
  | [] => .ok #[]
  | item :: rest => do
    let head ← arrayElement constructor item
    let tail ← arrayElementItems constructor rest
    return head ++ tail
termination_by items => sizeOf items

/-- One array element's data, in the array's declared constructor form.

An array states its element constructor once, so every element's data is in that form
and only that form: `list8` elements carry one-octet sizes and counts, `str32` elements
four-octet lengths, a `smalluint` element one octet, and an array element its own size,
count, element constructor and elements. A value of another type, or a size or count the
declared width cannot announce, is refused by name rather than written in another form —
writing each element in whatever form it would choose alone produces an array no reader
can follow, which the corpus caught. -/
def arrayElement : UInt8 → Value → Except String Octets
  | 0x00, .described descriptor value => do
    let head ← encode descriptor
    let tail ← encode value
    return head ++ tail
  | 0x40, _ => .ok #[]
  | 0x41, _ => .ok #[]
  | 0x42, _ => .ok #[]
  | 0x43, .uint 0 => .ok #[]
  | 0x44, .ulong 0 => .ok #[]
  | 0x45, .list [] => .ok #[]
  | 0x50, .ubyte n => .ok #[n]
  | 0x51, .byte n => .ok #[(n.toBitVec.toNat % 256).toUInt8]
  | 0x52, .uint n => elementOctet "smalluint" n.toNat
  | 0x53, .ulong n => elementOctet "smallulong" n.toNat
  | 0x54, .int n => elementSignedOctet "smallint" n.toInt
  | 0x55, .long n => elementSignedOctet "smalllong" n.toInt
  | 0x56, .boolean b => .ok #[if b then 1 else 0]
  | 0x60, .ushort n => .ok (u16be n.toNat)
  | 0x61, .short n => .ok (u16be (n.toBitVec.toNat % 65536))
  | 0x70, .uint n => .ok (u32be n.toNat)
  | 0x71, .int n => .ok (u32be (n.toBitVec.toNat % 4294967296))
  | 0x72, .float b => .ok b
  | 0x73, .char n => .ok (u32be n.toNat)
  | 0x74, .decimal32 b => .ok b
  | 0x80, .ulong n => .ok (u64be n.toNat)
  | 0x81, .long n => .ok (u64be (n.toBitVec.toNat % 18446744073709551616))
  | 0x82, .double b => .ok b
  | 0x83, .timestamp ms => .ok (u64be (ms.toBitVec.toNat % 18446744073709551616))
  | 0x84, .decimal64 b => .ok b
  | 0x94, .decimal128 b => .ok b
  | 0x98, .uuid b => .ok b
  | 0xA0, .binary b => elementVariableData 0xA0 "vbin8" b
  | 0xA1, .string s => elementVariableData 0xA1 "str8" s.toUTF8.toList
  | 0xA3, .symbol s => elementVariableData 0xA3 "sym8" s.toUTF8.toList
  | 0xB0, .binary b => elementVariableData 0xB0 "vbin32" b
  | 0xB1, .string s => elementVariableData 0xB1 "str32" s.toUTF8.toList
  | 0xB3, .symbol s => elementVariableData 0xB3 "sym32" s.toUTF8.toList
  | 0xC0, .list items => do let body ← encodeAll items
                            elementCompoundData 1 "list" items.length body
  | 0xC1, .map pairs => do let body ← encodePairs pairs
                           elementCompoundData 1 "map" (2 * pairs.length) body
  | 0xD0, .list items => do let body ← encodeAll items
                            elementCompoundData 4 "list" items.length body
  | 0xD1, .map pairs => do let body ← encodePairs pairs
                           elementCompoundData 4 "map" (2 * pairs.length) body
  -- An array element carries its own size, count, element constructor and elements, in
  -- the width the outer array's constructor fixes: the inner array's own narrowest form
  -- is not available to it, and a count or size the declared width cannot announce is
  -- refused rather than written wide.
  | 0xE0, .array constructor items =>
    if items.length > arrayElementLimit then
      .error s!"limit: an array of {items.length} element(s): this writer materialises \
        at most {arrayElementLimit}"
    else do
      let body ← arrayElementItems constructor items
      let count := items.length
      let size := 2 + body.size
      if size ≤ 255 && count ≤ 255 then
        return #[size.toUInt8, count.toUInt8, constructor] ++ body
      else
        .error s!"limit: an array8 element carries {count} element(s) in \
          {body.size} octet(s), which a one-octet size or count field cannot announce"
  | 0xF0, .array constructor items =>
    if items.length > arrayElementLimit then
      .error s!"limit: an array of {items.length} element(s): this writer materialises \
        at most {arrayElementLimit}"
    else do
      let body ← arrayElementItems constructor items
      let count := items.length
      return u32be (5 + body.size) ++ u32be count ++ #[constructor] ++ body
  | constructor, value =>
    .error s!"limit: an array whose element constructor is {constructor.toNat} cannot \
      carry a {typeName value}"
termination_by _ value => sizeOf value

end

end SpecAMQP.Ref
