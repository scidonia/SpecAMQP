/-
The class-divergence sweep: every buffer in a generated family, decoded by both value
readers, with the class each reader names compared.

Why this is a check and not a proof. Until the specification's reason class became a
*field* of its refusal, the two artefacts' classes could not be compared by the kernel at
all — the specification's was the head token of a sentence, recovered by `String.splitOn`,
which no kernel tactic reduces (see `Spec/Codec.lean`'s refusal section and
`Proofs/ValueLayerLaws.lean`). Now the comparison is decidably a term on both sides: the
specification's class is `Refusal.reasonClass` and the reference's reader names its class
with a variant of `Ref.DecodeError`. So a divergence between the two readers is *findable*
by exhaustion over a family, and this is that exhaustion. It is evidence about the family
it sweeps and not a claim about every buffer: the value layer's own `Conforms` instance is
what would state agreement universally, and it does not exist.

Run it with `scripts/run-class-divergence-sweep.sh` inside the `spec` shell. It prints the
number of buffers swept, the number of class mismatches, and how many buffers each side
refused — the last so that a family which happens to contain few refusals is visible as
the weaker check it is — and exits non-zero if any buffer's two classes differ.

No network, no clock, no randomness: the buffers are generated, and the alphabet and the
structured family below are the whole of the search space's definition.
-/
import Spec.Codec
import Ref.Value
import Ref.Frame

open SpecAMQP

/-- The class the specification's reader names for a buffer, or `accepted`. -/
def specClass (bytes : Array UInt8) : String :=
  match Spec.Codec.decodeValue bytes with
  | .ok _ => "accepted"
  | .error refusal => refusal.reasonClass

/-- The class the reference's reader names for a buffer, or `accepted`. The class is the
one its own variant carries, mapped by the frame layer's `valueFailure` — the same
mapping the frame layer reports a value-layer failure with. -/
def refClass (bytes : Array UInt8) : String :=
  match Ref.decode bytes with
  | .ok _ => "accepted"
  | .error e => (Ref.Frame.valueFailure e).reasonClass

/-- Every buffer of length 1..3 over an interesting alphabet: every assigned format code,
an unassigned octet inside each range, the escapes, and the container forms. -/
def alphabet : List UInt8 :=
  [0x00, 0x01, 0x10, 0x3F, 0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x50, 0x51, 0x52, 0x53, 0x54,
   0x55, 0x56, 0x57, 0x60, 0x61, 0x70, 0x71, 0x72, 0x73, 0x74, 0x80, 0x81, 0x82, 0x83, 0x84,
   0x94, 0x98, 0xA0, 0xA1, 0xA3, 0xB0, 0xB1, 0xB3, 0xC0, 0xC1, 0xD0, 0xD1, 0xE0, 0xF0, 0xFF]

/-- A smaller alphabet for length four, where the container and variable forms have all
their fields and one item present. -/
def shortAlphabet : List UInt8 :=
  [0x00, 0x01, 0x40, 0x45, 0x50, 0x57, 0xA0, 0xA1, 0xC0, 0xC1, 0xE0, 0xF0]

/-- The buffers of length `n` over `alpha`, in an arbitrary but fixed order. -/
def ofLength (n : Nat) (alpha : List UInt8) : List (Array UInt8) :=
  match n with
  | 0 => [#[]]
  | n + 1 => (ofLength n alpha).flatMap (fun pfx => alpha.map (fun b => pfx.push b))

/-- The array-and-compound family: an array's declared element constructor is the octet
that decides which class a reader names for a form it cannot read, and a compound's
declared size and count decide the order of its own two checks. -/
def structured : List (Array UInt8) :=
  -- arrays, with every octet the element field can carry and no element data
  (List.range 256).map (fun n => #[0xE0, 0x02, 0x00, UInt8.ofNat n]) ++
  [-- an array with one or two zero-width elements, and a count with no elements behind it
   #[0xE0, 0x02, 0x00, 0x40], #[0xE0, 0x03, 0x01, 0x40], #[0xE0, 0x04, 0x02, 0x40],
   #[0xE0, 0x02, 0x00, 0x00], #[0xE0, 0x03, 0x00, 0x40], #[0xE0, 0x05, 0x01, 0x40, 0x40],
   -- an array of arrays, an array of described values, an array of compounds
   #[0xE0, 0x02, 0x01, 0xE0], #[0xE0, 0x02, 0x01, 0x00], #[0xE0, 0x02, 0x01, 0xC0],
   -- the four-octet array form, count and size in four octets
   #[0xF0, 0x00, 0x00, 0x00, 0x0B, 0x00, 0x00, 0x00, 0x02, 0x40, 0x40],
   -- compounds: size and count crossed, for a list and for a map
   #[0xC0, 0x00, 0x00], #[0xC0, 0x01, 0x00], #[0xC0, 0x01, 0x01], #[0xC0, 0x02, 0x00],
   #[0xC0, 0x00, 0x01], #[0xC0, 0x03, 0x01, 0x40], #[0xC0, 0x02, 0x01, 0x40],
   #[0xC1, 0x03, 0x01, 0x40], #[0xC1, 0x02, 0x01, 0x40], #[0xC1, 0x03, 0x02, 0x40],
   #[0xC1, 0x06, 0x01, 0x40, 0x40, 0x40], #[0xC1, 0x08, 0x03, 0x40, 0x40, 0x40],
   #[0xC1, 0x04, 0x02, 0x40, 0x40], #[0xD0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
   -- described values: every descriptor form over a null
   #[0x00, 0x40, 0x40], #[0x00, 0x50, 0x01, 0x40], #[0x00, 0xA1, 0x00, 0x40],
   #[0x00, 0x00, 0x40, 0x40], #[0x00, 0x01, 0x40],
   -- variable forms whose length prefix overruns, and payloads that are not UTF-8
   #[0xA1, 0x02, 0xFF, 0xFE], #[0xA3, 0x01, 0x80], #[0xB1, 0x00, 0x00, 0x00, 0x02, 0xFF, 0xFE],
   #[0xA0, 0x02, 0xFF, 0xFE],
   -- an unassigned octet inside each range, and the escapes
   #[0x57, 0x01], #[0xEF, 0x00], #[0x46, 0x00], #[0x0F], #[0x30]]

/-- The whole search space, in a fixed order. -/
def family : List (Array UInt8) :=
  ofLength 1 alphabet ++ ofLength 2 alphabet ++ ofLength 3 alphabet ++
    ofLength 4 shortAlphabet ++ structured

/-- A buffer's octets, for a divergence report. -/
def renderOctets (bytes : Array UInt8) : String :=
  String.intercalate " " (bytes.toList.map (fun b => s!"{b.toNat}"))

def main : IO Unit := do
  let all := family
  let mismatches := all.filter (fun bytes => specClass bytes != refClass bytes)
  let refusedSpec := all.filter (fun b => specClass b != "accepted")
  let refusedRef := all.filter (fun b => refClass b != "accepted")
  IO.println s!"buffers swept: {all.length}"
  IO.println s!"class mismatches: {mismatches.length}"
  IO.println s!"refused by spec: {refusedSpec.length}, by ref: {refusedRef.length}"
  if mismatches.isEmpty then
    IO.println "the two value readers name the same class for every buffer swept"
  else
    for bytes in mismatches.take 20 do
      IO.eprintln s!"class divergence: {renderOctets bytes} spec={specClass bytes} \
        ref={refClass bytes}"
    IO.Process.exit 1
