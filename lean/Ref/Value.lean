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
* **A legal constructor this implementation cannot read yet is reported as
  `unsupported`**, not as `unassigned`: an octet outside the grammar and a gap in
  the reader are different facts, and conflating them would make the reader's
  error say something false about the grammar.
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
* **Arrays hold scalars.** An element constructor naming a compound's data form
  (list or map) is reported as `unsupported` — legal, but a form this
  implementation does not read yet — rather than guessed at.
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

/-- A one-octet two's-complement integer as a number. The narrow `smallint` and
`smalllong` forms carry a signed octet, and both the types that use them are wider
than the octet, so the sign must be extended rather than read as an unsigned byte. -/
def signedOctet (n : UInt8) : Int :=
  (Int8.ofBitVec (BitVec.ofNat 8 n.toNat)).toInt

/-- One array element: its constructor is given by the array, so only the element
data follows. Scalars only — the data form of a compound element is not something
this implementation reads yet, so an array of lists or maps is rejected as an
unassigned constructor rather than guessed at. -/
def readElement (constructor : UInt8) (c : Cursor) : Result Value := do
  match constructor with
  | 0x40 => return (.null, c)
  | 0x41 => return (.boolean true, c)
  | 0x42 => return (.boolean false, c)
  | 0x50 => let (n, c) ← takeU8 c; return (.ubyte n, c)
  | 0x51 => let (n, c) ← takeU8 c
            return (.byte (Int8.ofBitVec (BitVec.ofNat 8 n.toNat)), c)
  | 0x54 => let (n, c) ← takeU8 c
            return (.int (Int32.ofBitVec
              (BitVec.ofNat 32 (signedOctet n % 4294967296).toNat)), c)
  | 0x55 => let (n, c) ← takeU8 c
            return (.long (Int64.ofBitVec
              (BitVec.ofNat 64 (signedOctet n % 18446744073709551616).toNat)), c)
  | 0x60 => let (n, c) ← takeBeU 2 c; return (.ushort n.toUInt16, c)
  | 0x70 => let (n, c) ← takeBeU 4 c; return (.uint n.toUInt32, c)
  | 0x72 => let (b, c) ← takeBytes 4 c; return (.float b, c)
  | 0x73 => let (n, c) ← takeBeU 4 c; return (.char n.toUInt32, c)
  | 0x74 => let (b, c) ← takeBytes 4 c; return (.decimal32 b, c)
  | 0x80 => let (n, c) ← takeBeU 8 c; return (.ulong n.toUInt64, c)
  | 0x82 => let (b, c) ← takeBytes 8 c; return (.double b, c)
  | 0x83 => let (n, c) ← takeBeU 8 c
            return (.timestamp (Int64.ofBitVec (BitVec.ofNat 64 n)), c)
  | 0x84 => let (b, c) ← takeBytes 8 c; return (.decimal64 b, c)
  | 0x94 => let (b, c) ← takeBytes 16 c; return (.decimal128 b, c)
  | 0x98 => let (b, c) ← takeBytes 16 c; return (.uuid b, c)
  | 0xA0 => let (n, c) ← takeU8 c; let (b, c) ← takeBytes n.toNat c
            return (.binary b.toList, c)
  | 0xA1 => let (n, c) ← takeU8 c; let (b, c) ← takeBytes n.toNat c
            let (s, c) ← match decodeString b "string" with
                         | .ok s => .ok (s, c)
                         | .error e => .error e
            return (.string s, c)
  | 0xA3 => let (n, c) ← takeU8 c; let (b, c) ← takeBytes n.toNat c
            let (s, c) ← match decodeString b "symbol" with
                         | .ok s => .ok (s, c)
                         | .error e => .error e
            return (.symbol s, c)
  -- Legal constructors whose element-data form this implementation does not read
  -- yet: a described value's (0x00), the zero-data forms, the fixed-width signed
  -- forms, the wide variable forms, a compound's data, and an array's. Each names
  -- a form the grammar admits, so calling it unassigned would be false.
  | 0x00 | 0x43 | 0x44 | 0x45 | 0x52 | 0x53 | 0x56
  | 0x61 | 0x71 | 0x81
  | 0xB0 | 0xB1 | 0xB3
  | 0xC0 | 0xC1 | 0xD0 | 0xD1
  | 0xE0 | 0xF0 => .error (.unsupported constructor)
  | other => .error (.unassigned other)

mutual

/-- Read one value.

`fuel` bounds the recursion and decreases at every recursive call, including the
iterator that reads a compound's items, which is what makes this reader total
without `partial`. Callers pass the number of octets in the input: every step
consumes at least one octet, so a well-formed encoding never exhausts it, and a
malformed one fails on truncation rather than looping. -/
def readValue (fuel : Nat) (c : Cursor) : Result Value :=
  match fuel with
  | 0 => .error (.truncated "no octets left")
  | fuel + 1 => do
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
              let (s, c) ← match decodeString b "string" with
                           | .ok s => .ok (s, c)
                           | .error e => .error e
              return (.string s, c)
    | 0xB1 => let (n, c) ← takeBeU 4 c;   let (b, c) ← takeBytes n c
              let (s, c) ← match decodeString b "string" with
                           | .ok s => .ok (s, c)
                           | .error e => .error e
              return (.string s, c)
    | 0xA3 => let (n, c) ← takeU8 c;      let (b, c) ← takeBytes n.toNat c
              let (s, c) ← match decodeString b "symbol" with
                           | .ok s => .ok (s, c)
                           | .error e => .error e
              return (.symbol s, c)
    | 0xB3 => let (n, c) ← takeBeU 4 c;   let (b, c) ← takeBytes n c
              let (s, c) ← match decodeString b "symbol" with
                           | .ok s => .ok (s, c)
                           | .error e => .error e
              return (.symbol s, c)
    | 0xC0 => readCompound fuel 1 c
    | 0xC1 => readMap fuel 1 c
    | 0xD0 => readCompound fuel 4 c
    | 0xD1 => readMap fuel 4 c
    | 0xE0 => readArray fuel 1 c
    | 0xF0 => readArray fuel 4 c
    | other => .error (.unassigned other)

/-- `count` items, each with its own constructor. Both the fuel and the item
count decrease, so a header whose count exceeds the input fails on truncation. -/
def readItems (fuel : Nat) (count : Nat) (c : Cursor) : Result (List Value) :=
  match fuel, count with
  | 0, _ => .error (.truncated "no octets left")
  | _, 0 => .ok ([], c)
  | fuel + 1, count + 1 => do
    let (item, c) ← readValue fuel c
    let (rest, c) ← readItems fuel count c
    return (item :: rest, c)

/-- A compound list: `size`, `count`, then `count` constructed items. The size
counts the octets that follow it, so it must agree with what was read. -/
def readCompound (fuel width : Nat) (c : Cursor) : Result Value := do
  let (size, c) ← takeBeU width c
  let start := c.pos                    -- the size counts what follows it
  let (count, c) ← takeBeU width c
  let (items, c) ← readItems fuel count c
  if c.pos - start != size then
    .error (.sizeMismatch "list" size (c.pos - start))
  else
    return (.list items, c)

/-- A map: `size`, `count` constructed items, then the same size agreement a list
requires. Part 1 requires an even number of items, so an odd count is malformed
rather than a map with a dangling key. Pairs keep the order they arrived in. -/
def readMap (fuel width : Nat) (c : Cursor) : Result Value := do
  let (size, c) ← takeBeU width c
  let start := c.pos                    -- the size counts what follows it
  let (count, c) ← takeBeU width c
  let (items, c) ← readItems fuel count c
  if c.pos - start != size then
    .error (.sizeMismatch "map" size (c.pos - start))
  else
    match pairUp items with
    | some pairs => return (.map pairs, c)
    | none => .error (.malformed "a map must have an even number of items")

/-- Items taken two at a time, key then value: the pairing a map encoding
requires. `none` is an odd item count, which is not a map. -/
def pairUp : List Value → Option (List (Value × Value))
  | [] => some []
  | key :: value :: rest => (pairUp rest).map (fun pairs => (key, value) :: pairs)
  | [_] => none

/-- An array: `size`, `count`, one element constructor, then `count` element data
blocks in that constructor's form, each without its own constructor. -/
def readArray (fuel width : Nat) (c : Cursor) : Result Value := do
  let (size, c) ← takeBeU width c
  let start := c.pos                    -- the size counts what follows it
  let (count, c) ← takeBeU width c
  let (constructor, c) ← takeU8 c
  let (items, c) ← readElements fuel constructor count c
  if c.pos - start != size then
    .error (.sizeMismatch "array" size (c.pos - start))
  else
    return (.array constructor items, c)

/-- `count` array elements, each in the array's element constructor form. -/
def readElements (fuel : Nat) (constructor : UInt8) (count : Nat) (c : Cursor) :
    Result (List Value) :=
  match fuel, count with
  | 0, _ => .error (.truncated "no octets left")
  | _, 0 => .ok ([], c)
  | fuel + 1, count + 1 => do
    let (item, c) ← readElement constructor c
    let (rest, c) ← readElements fuel constructor count c
    return (item :: rest, c)

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

/-- Variable-width element data, whose length width is the array's constructor's,
not the element's preference: an array of `str8` elements carries one-octet
lengths, an array of `str32` elements four-octet ones. -/
def elementVariableData (constructor : UInt8) (payload : List UInt8) : Octets :=
  match constructor with
  | 0xB0 | 0xB1 | 0xB3 => u32be payload.length ++ payload.toArray
  | _ => #[payload.length.toUInt8] ++ payload.toArray

/-- A value's data octets in its own narrowest form, without a constructor octet.
Used where an array's declared constructor does not match an element's type: such
an element cannot be written faithfully, so it is written with empty data, which a
reader rejects loudly rather than accepting a plausible-looking array.

A compound value has no case here either: an array of compounds is outside what
this implementation writes, so it falls to the empty data below. -/
def dataOf (value : Value) : Octets :=
  match value with
  | .null => #[]
  | .boolean _ => #[]
  | .ubyte n => #[n]
  | .byte n => #[(n.toBitVec.toNat % 256).toUInt8]
  | .ushort n => u16be n.toNat
  | .short n => u16be (n.toBitVec.toNat % 65536)
  | .uint 0 => #[]
  | .uint n => if n.toNat ≤ 255 then #[n.toUInt8] else u32be n.toNat
  | .int n => u32be (n.toBitVec.toNat % 4294967296)
  | .ulong 0 => #[]
  | .ulong n => if n.toNat ≤ 255 then #[n.toUInt8] else u64be n.toNat
  | .long n => u64be (n.toBitVec.toNat % 18446744073709551616)
  | .char n => u32be n.toNat
  | .timestamp ms => u64be (ms.toBitVec.toNat % 18446744073709551616)
  | .float b => b
  | .double b => b
  | .decimal32 b => b
  | .decimal64 b => b
  | .decimal128 b => b
  | .uuid b => b
  | .binary b => (variableData 0xA0 0xB0 b).extract 1
                   (variableData 0xA0 0xB0 b).size
  | .string s => (variableData 0xA1 0xB1 s.toUTF8.toList).extract 1
                   (variableData 0xA1 0xB1 s.toUTF8.toList).size
  | .symbol s => (variableData 0xA3 0xB3 s.toUTF8.toList).extract 1
                   (variableData 0xA3 0xB3 s.toUTF8.toList).size
  | _ => #[]

mutual

/-- The constructor-and-data encoding of a value. -/
def encode (value : Value) : Octets :=
  match value with
  | .null => #[0x40]
  | .boolean true => #[0x41]
  | .boolean false => #[0x42]
  | .ubyte n => #[0x50, n]
  | .byte n => #[0x51, (n.toBitVec.toNat % 256).toUInt8]
  | .ushort n => #[0x60] ++ u16be n.toNat
  | .short n => #[0x61] ++ u16be (n.toBitVec.toNat % 65536)
  | .uint 0 => #[0x43]
  | .uint n => if n.toNat ≤ 255 then #[0x52, n.toUInt8] else #[0x70] ++ u32be n.toNat
  | .int n => #[0x71] ++ u32be (n.toBitVec.toNat % 4294967296)
  | .ulong 0 => #[0x44]
  | .ulong n => if n.toNat ≤ 255 then #[0x53, n.toUInt8] else #[0x80] ++ u64be n.toNat
  | .long n => #[0x81] ++ u64be (n.toBitVec.toNat % 18446744073709551616)
  | .char n => #[0x73] ++ u32be n.toNat
  | .timestamp ms => #[0x83] ++ u64be (ms.toBitVec.toNat % 18446744073709551616)
  | .float b => #[0x72] ++ b
  | .double b => #[0x82] ++ b
  | .decimal32 b => #[0x74] ++ b
  | .decimal64 b => #[0x84] ++ b
  | .decimal128 b => #[0x94] ++ b
  | .uuid b => #[0x98] ++ b
  | .binary b => variableData 0xA0 0xB0 b
  | .string s => variableData 0xA1 0xB1 s.toUTF8.toList
  | .symbol s => variableData 0xA3 0xB3 s.toUTF8.toList
  | .list [] => #[0x45]
  | .list items =>
    let body := encodeAll items
    let count := items.length
    if 1 + body.size ≤ 255 && count ≤ 255 then
      #[0xC0, (1 + body.size).toUInt8, count.toUInt8] ++ body
    else
      #[0xD0] ++ u32be (4 + body.size) ++ u32be count ++ body
  -- There is no map0 form, so even the empty map is a map8 with an empty item
  -- sequence: size 1 (the count octet), count 0.
  | .map [] => #[0xC1, 0x01, 0x00]
  | .map pairs =>
    let body := encodePairs pairs
    let count := 2 * pairs.length           -- the count field counts items, not pairs
    if 1 + body.size ≤ 255 && count ≤ 255 then
      #[0xC1, (1 + body.size).toUInt8, count.toUInt8] ++ body
    else
      #[0xD1] ++ u32be (4 + body.size) ++ u32be count ++ body
  | .array constructor items =>
    let body := items.foldl (fun acc item => acc ++ arrayElement constructor item) #[]
    let count := items.length
    if 2 + body.size ≤ 255 && count ≤ 255 then
      #[0xE0, (2 + body.size).toUInt8, count.toUInt8, constructor] ++ body
    else
      #[0xF0] ++ u32be (5 + body.size) ++ u32be count ++ #[constructor] ++ body
  | .described descriptor value => #[0x00] ++ encode descriptor ++ encode value

/-- Items concatenated in order. -/
def encodeAll (items : List Value) : Octets :=
  items.foldl (fun acc item => acc ++ encode item) #[]

/-- A map's items concatenated in order: each key followed by its value, both with
their own constructors, exactly as a compound's items are written. -/
def encodePairs (pairs : List (Value × Value)) : Octets :=
  pairs.foldl (fun acc (key, value) => acc ++ encode key ++ encode value) #[]

/-- Array element data, written in the array's declared constructor form.

An array states its element constructor once, so every element's data must be in
that form: writing each element in whatever form it would choose alone produces
an array no reader can follow, which the corpus caught. -/
def arrayElement (constructor : UInt8) (value : Value) : Octets :=
  match constructor, value with
  | 0x40, _ | 0x41, _ | 0x42, _ => #[]
  | 0x50, .ubyte n => #[n]
  | 0x51, .byte n => #[(n.toBitVec.toNat % 256).toUInt8]
  -- A smallint or smalllong element carries one signed octet. A value outside that
  -- range is not masked into a different value — which a reader would accept as a
  -- plausible-looking array — but falls to the unfaithful-data path, whose extra
  -- octets the reader's size check rejects.
  | 0x54, .int n =>
    if -128 ≤ n.toInt && n.toInt ≤ 127 then #[(n.toBitVec.toNat % 256).toUInt8]
    else dataOf value
  | 0x55, .long n =>
    if -128 ≤ n.toInt && n.toInt ≤ 127 then #[(n.toBitVec.toNat % 256).toUInt8]
    else dataOf value
  | 0x60, .ushort n => u16be n.toNat
  | 0x70, .uint n => u32be n.toNat
  | 0x72, .float b => b
  | 0x73, .char n => u32be n.toNat
  | 0x74, .decimal32 b => b
  | 0x80, .ulong n => u64be n.toNat
  | 0x82, .double b => b
  | 0x83, .timestamp ms => u64be (ms.toBitVec.toNat % 18446744073709551616)
  | 0x84, .decimal64 b => b
  | 0x94, .decimal128 b => b
  | 0x98, .uuid b => b
  | 0xA0, .binary b => elementVariableData 0xA0 b
  | 0xB0, .binary b => elementVariableData 0xB0 b
  | 0xA1, .string s => elementVariableData 0xA1 s.toUTF8.toList
  | 0xB1, .string s => elementVariableData 0xB1 s.toUTF8.toList
  | 0xA3, .symbol s => elementVariableData 0xA3 s.toUTF8.toList
  | 0xB3, .symbol s => elementVariableData 0xB3 s.toUTF8.toList
  | _, _ => dataOf value

end

end SpecAMQP.Ref
