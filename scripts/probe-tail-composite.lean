import Spec.Message

/-! A probe for `composite-type-representation.2`'s mandatory half, which no message
section can reach: no section type declares a mandatory field, so the site that decides
mandatory presence is exercised through a composite the layer reads directly.

`received` declares field 1 `section-number` (uint, mandatory) and field 2
`section-offset` (ulong, mandatory). Three rows, quoted in the ticket's before/after runs:

* the field carried as `null`, which is the absence the mandatory rule already refuses;
* the field carried as a zero-length array of uint elements (`0x43` is uint0's
  constructor, so the elements have the field's own declared type), which the types
  section makes the *same* absence;
* `properties.subject` (declared string, not mandatory) carried as a zero-length array of
  str8 elements, where the identity is what admits it.

Nothing here asserts: it prints what the two artefacts' shared reader answered. -/

open SpecAMQP.Spec.Message
open SpecAMQP.Spec.Codec (Value)

def report (label : String) (r : Except SpecAMQP.Harness.Refusal (List Value)) : IO Unit :=
  match r with
  | .ok _ => IO.println s!"  {label}: admitted"
  | .error refusal => IO.println s!"  {label}: {refusal.detail}"

def main : IO UInt32 := do
  IO.println "received: field 1 section-number (uint, mandatory), field 2 section-offset (ulong, mandatory)"
  report "section-number carried as null                  " (checkFieldList "received" [.null, .ulong 5])
  report "section-number carried as a zero-length uint array" (checkFieldList "received" [.array 0x43 [], .ulong 5])
  IO.println "properties: field 4 subject (string, not mandatory)"
  report "subject carried as null                        " (checkFieldList "properties" [.null, .null, .null, .null])
  report "subject carried as a zero-length str8 array    " (checkFieldList "properties" [.null, .null, .null, .array 0xa1 []])
  return 0
