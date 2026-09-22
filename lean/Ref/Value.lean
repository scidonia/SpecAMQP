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

* **Narrowest encoding.** A writer emits the smallest encoding that carries the
  value (`uint 0` as `0x43`, `uint 300` as `0x70`, `ulong 0` as `0x44`), the
  specificity-preserving reading of Part 1's subcategory table.
* **Unassigned octets are rejected**, including the twelve escape octets the
  constructor grammar reserves for future formats, rather than skipped.
* **Arrays carry a constructor octet** rather than a resolved element type; a
  reader requires every element's data to be well formed under that constructor.
* **Sizes count the octets that follow the size field** — count, the array
  element constructor, then the encoded items — the reading recorded in
  `ledger/ambiguities/compound-size-field.json`.
* **A compound value must match its declared size**; a mismatch is a decode error
  rather than something to resynchronise past.
* **Strings and symbols must be valid UTF-8** (symbols are ASCII on the wire, so
  this is the stricter of the two rules and makes both agree).
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
  | list (items : List Value)
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
  | unassigned (octet : UInt8)
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

/-- One array element: its constructor is given by the array, so only the element
data follows. Scalars only — an array of arrays is not something this
implementation reads yet. -/
def readElement (constructor : UInt8) (c : Cursor) : Result Value := do
  match constructor with
  | 0x40 => return (.null, c)
  | 0x41 => return (.boolean true, c)
  | 0x42 => return (.boolean false, c)
  | 0x50 => let (n, c) ← takeU8 c; return (.ubyte n, c)
  | 0x51 => let (n, c) ← takeU8 c
            return (.byte (Int8.ofBitVec (BitVec.ofNat 8 n.toNat)), c)
  | 0x60 => let (n, c) ← takeBeU 2 c; return (.ushort n.toUInt16, c)
  | 0x70 => let (n, c) ← takeBeU 4 c; return (.uint n.toUInt32, c)
  | 0x80 => let (n, c) ← takeBeU 8 c; return (.ulong n.toUInt64, c)
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
    | 0x60 => let (n, c) ← takeBeU 2 c; return (.ushort n.toUInt16, c)
    | 0x61 => let (n, c) ← takeBeU 2 c
              return (.short (Int16.ofBitVec (BitVec.ofNat 16 n)), c)
    | 0x70 => let (n, c) ← takeBeU 4 c; return (.uint n.toUInt32, c)
    | 0x71 => let (n, c) ← takeBeU 4 c
              return (.int (Int32.ofBitVec (BitVec.ofNat 32 n)), c)
    | 0x80 => let (n, c) ← takeBeU 8 c; return (.ulong n.toUInt64, c)
    | 0x81 => let (n, c) ← takeBeU 8 c
              return (.long (Int64.ofBitVec (BitVec.ofNat 64 n)), c)
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
    | 0xD0 => readCompound fuel 4 c
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
octets that follow the size field, exactly as the reader requires. -/

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
  | .binary b => encodeVariable 0xA0 0xB0 b
  | .string s => encodeVariable 0xA1 0xB1 s.toUTF8.toList
  | .symbol s => encodeVariable 0xA3 0xB3 s.toUTF8.toList
  | .list [] => #[0x45]
  | .list items =>
    let body := encodeAll items
    let count := items.length
    let size := 1 + body.size
    if size ≤ 255 && count ≤ 255 then
      #[0xC0, size.toUInt8, count.toUInt8] ++ body
    else
      #[0xD0] ++ u32be size ++ u32be count ++ body
  | .array constructor items =>
    let body := items.foldl (fun acc item => acc ++ arrayElement constructor item) #[]
    let count := items.length
    let size := 2 + body.size
    if size ≤ 255 && count ≤ 255 then
      #[0xE0, size.toUInt8, count.toUInt8, constructor] ++ body
    else
      #[0xF0] ++ u32be size ++ u32be count ++ #[constructor] ++ body
  | .described descriptor value => #[0x00] ++ encode descriptor ++ encode value

/-- Items concatenated in order. -/
def encodeAll (items : List Value) : Octets :=
  items.foldl (fun acc item => acc ++ encode item) #[]

/-- A variable-width encoding: a narrow form when the payload fits its octet, the
wide form otherwise. -/
def encodeVariable (narrow wide : UInt8) (payload : List UInt8) : Octets :=
  if payload.length ≤ 255 then
    #[narrow, payload.length.toUInt8] ++ payload.toArray
  else
    #[wide] ++ u32be payload.length ++ payload.toArray

/-- Array element data, without the element constructor. -/
def arrayElement (constructor : UInt8) (value : Value) : Octets :=
  match constructor with
  | 0x40 | 0x41 | 0x42 => #[]
  | _ => let full := encode value; full.extract 1 full.size

end

end SpecAMQP.Ref
