import Spec.Codec
import Generated.Oasis.Choices
import Generated.Oasis.Fields
import Generated.Oasis.Types

/-!
# Part 3: message sections and delivery states

`Spec.Value` classifies a leading octet, `Spec.Codec` reads and writes the type system, and
this module is the messaging layer on top of both: the nine section types the artifact
declares, the codec that reads and writes them, the delivery states, and the machine that
applies a state to a delivery.

**Table-driven, not transcribed.** The section kinds are the types the declared surface
gives the `section` role, which is a fact this module checks rather than asserts; a
section's descriptor, its field order, its mandatory fields and each field's declared type
all come from `Generated.Oasis`, so a mistyped code or a reordered field is a table change
rather than a semantic one. Nothing here writes a descriptor code, an `amqp:` symbol or a
field index: `SectionKind.typeName` is the only place a section is named, and it names the
*type*, which is the key its row is looked up by.

**What the layer is, and what it is not.** A section is a described value, and a message is
a sequence of them. The reader here is a function from octets to sections and back: it
does not know about transfers, sessions or links, does not fragment or reassemble payloads, and
does not act on what it reads beyond refusing. Where a clause mandates an *action* — the
link detach for an annotation key the receiver does not understand — the refusal is what
this layer produces and the link layer is what acts, which is the same boundary the frame
layer draws around the conditions it raises. It reads one thing that is not a section: the two
*terminus* types Part 3's addressing section defines, `source` and `target`, as field records with
the rules their documentation states. Their rules are conditioned on which endpoint sent the frame
that carried them, so the sender is an input to that reader exactly as the annotation policy is an
input to the section reader.

**Readings.** Three things the artifact leaves open are decided here, each marked at the
point of use, and each is a reading rather than a citation:

* **A structural violation is `amqp:decode-error`.** The occurrence and order rules are
  stated in the message-format section's own text and it names no condition for a
  violation of them; the shared condition set's `decode-error` — "data could not be
  decoded" — is the one whose definition fits. Everything the layer refuses for a reason
  of structure, arity or declared type carries it.
* **The condition for a section whose rule names none** is the same `amqp:decode-error`;
  the clause-backed refusals are the annotation key rules (`annotations.1`, `.2`) and the
  `rejected` annotation's value type (`delivery-annotations.2`).
* **An annotation key the endpoint does not implement is `amqp:not-implemented`.** The
clause mandates a detach "with a «amqp-error» error", which names the shared condition
family rather than a member of it; `not-implemented` ("the peer tried to use
functionality that is not implemented in its partner") is the member whose definition
fits a peer's use of a key this endpoint does not implement.
* **The rules that relate a field to something outside its own section carry the first
reading.** The `content-encoding` rules read a properties field and the body's section kind
together, and the terminus rules read a source's or target's fields against the declared tables;
Part 3 states each and names no condition, so each is refused as the structure rules are — with
`amqp:decode-error`.

**What is modelled and what is passed through.** The five delivery states the messaging
layer defines are modelled. The two the *transaction* layer defines (`declared`,
`transactional-state`) fill the same role and are read as opaque states: this module
records them and moves nothing, because their terminality and their effect on a delivery
belong to the transaction layer's rules rather than to an invention here.

**Totality.** Nothing here is `partial` or `noncomputable`. The reader's recursion is
bounded by the octets it is given — every section consumes at least one — and the message
reader additionally carries the count so a buffer of sections is walked by their own
arithmetic.
-/

namespace SpecAMQP.Spec.Message

open Lean
open SpecAMQP.Harness (Octets Refusal ofHex toHex)
-- The codec's names are opened selectively, because this module spells `Refusal` with
-- the harness's shape (a condition and a class-led detail) while `Spec.Codec` now spells
-- it with the class as a field: an unrestricted open would make the bare name ambiguous.
open SpecAMQP.Spec.Codec (Value typeName toJson toJsonPairs decodeValue encodeValue valueOfJson)
open SpecAMQP.Generated.Oasis

/-! ## Conditions, read from the declared choice table

No condition symbol is typed here. The artifact declares the shared conditions as a
`choice` under the `amqp-error` type, so a condition is a table lookup, and a table that
stopped declaring one yields a string that is not a protocol condition at all — which the
corpus reports as a mismatch rather than silently accepting. -/

/-- One condition symbol from a declared error family, by name. -/
def conditionOf (family name : String) : String :=
  match (errorConditionsOf family).find? (fun choice => choice.name == name) with
  | some choice => choice.value
  | none => s!"the {family} choice declares no {name}"

/-- The shared condition the artifact defines as "data could not be decoded", which every
structural, arity and declared-type refusal in this module carries. -/
def decodeError : String := conditionOf "amqp-error" "decode-error"

/-- The shared condition for functionality the peer's partner does not implement, which the
annotation key rules' mandated detach is read as. -/
def notImplemented : String := conditionOf "amqp-error" "not-implemented"

/-- The shared condition for what is not permitted in the current state, which the
terminal-attempt refusals carry. -/
def illegalState : String := conditionOf "amqp-error" "illegal-state"

/-- A refusal with a condition and a class-led detail: the detail's first token is the
reason class the corpus compares. -/
def refusal (condition reasonClass prose : String) : Refusal :=
  ⟨condition, s!"{reasonClass}: {prose}"⟩

/-- A refusal of the layer's default reading: the shared `decode-error` condition. -/
def decodeRefusal (reasonClass prose : String) : Refusal :=
  refusal decodeError reasonClass prose

/-- A table lookup's failure becomes a refusal with the same class-led detail, so a corpus
never sees a bare internal error for a table the artifact does not have. -/
def liftRefusal {α : Type} (lookup : Except String α) : Except Refusal α :=
  match lookup with
  | .ok value => .ok value
  | .error message => .error (decodeRefusal "malformed" message)

/-- What an endpoint understands about a message: the annotation keys it implements, in the
form they appear on the wire (a symbol's text, or a ulong's decimal digits). The
annotations text mandates a detach for a key the receiver does not understand, so this
knowledge is an explicit input to the reader rather than a decision hidden in it. -/
structure Policy where
  /-- The annotation keys this endpoint implements. -/
  understood : List String
deriving Repr, Inhabited

/-- An endpoint that implements no annotation beyond the `x-opt` keys it may ignore. -/
def Policy.empty : Policy := ⟨[]⟩

/-! ## The nine section types

Part 3 declares each of them with the `section` role, so the kinds are the declared
surface's own list rather than a list of names this module remembers. -/

/-- The section types message format 0 defines. -/
inductive SectionKind where
  | header
  | deliveryAnnotations
  | messageAnnotations
  | properties
  | applicationProperties
  | data
  | sequence
  | value
  | footer
deriving Repr, DecidableEq, BEq

/-- Every section kind, in the order the artifact's structure list presents them. -/
def SectionKind.all : List SectionKind :=
  [.header, .deliveryAnnotations, .messageAnnotations, .properties, .applicationProperties,
   .data, .sequence, .value, .footer]

/-- The declared type a section kind names. The *type name* is the artifact's identifier
for it; codes and symbols come from the table it is looked up in. -/
def SectionKind.typeName : SectionKind → String
  | .header => "header"
  | .deliveryAnnotations => "delivery-annotations"
  | .messageAnnotations => "message-annotations"
  | .properties => "properties"
  | .applicationProperties => "application-properties"
  | .data => "data"
  | .sequence => "amqp-sequence"
  | .value => "amqp-value"
  | .footer => "footer"

/-- The declared type of a section kind, from the generated table. -/
def typeDeclOf (name : String) : Except String TypeDecl :=
  match types.find? (fun entry => entry.name == name) with
  | some entry => .ok entry
  | none => .error s!"the declared surface has no type named {name}"

/-- A section's body shape, which its declaration fixes: a composite declares a field
list, a restricted type declares the shape of the type it restricts. The distinction
between the two map shapes is the declaration's own: `application-properties` restricts
`map` directly and its text restricts the keys to strings, while the three annotation
sections restrict `annotations`, which restricts `map` and whose keys are symbols or
ulongs. -/
inductive SectionShape where
  /-- A composite: a list of declared fields, in declared order. -/
  | fieldList
  /-- An `annotations`-shaped map: symbol or ulong keys in the reserved space. -/
  | annotationMap
  /-- A plain map whose keys the type's own text restricts to strings. -/
  | stringKeyMap
  /-- A `binary`. -/
  | octets
  /-- A `list`. -/
  | elements
  /-- The wildcard: one value of any type. -/
  | single
deriving Repr, DecidableEq, BEq

/-- The shape a declared type's body takes, from its class and the source it restricts. -/
def shapeOfType (name : String) : Except String SectionShape := do
  let decl ← typeDeclOf name
  if decl.typeClass = .composite then return .fieldList
  else
    match decl.source with
    | some "annotations" => return .annotationMap
    | some "map" => return .stringKeyMap
    | some "binary" => return .octets
    | some "list" => return .elements
    | some "*" => return .single
    | some other =>
      -- A restricted type may restrict another restricted type; the annotation sections
      -- are the case that matters and are matched above, so anything else is a shape this
      -- module has no reader for rather than one it may guess at.
      .error s!"{name} restricts {other}, whose body shape this module does not read"
    | none => .error s!"{name} declares no source type"

/-- A section kind's body shape. -/
def SectionKind.shape (kind : SectionKind) : Except String SectionShape :=
  shapeOfType kind.typeName

/-- The descriptor the declared surface gives a section kind: the ulong an encoded
section begins with. -/
def SectionKind.descriptorCode (kind : SectionKind) : Except String Nat := do
  let decl ← typeDeclOf kind.typeName
  match decl.descriptor with
  | some descriptor => return descriptor.code
  | none => .error s!"the declared surface gives {kind.typeName} no descriptor"

/-- The section kind a descriptor code names, if any. -/
def kindOfDescriptorCode? (code : Nat) : Option SectionKind :=
  SectionKind.all.find? (fun kind => kind.descriptorCode.toOption == some code)

/-- The declared types the surface gives the `section` role. -/
def tableSectionTypes : List String :=
  (types.filter (fun entry => entry.provides.contains "section")).map (fun entry => entry.name)

/-- The section kinds are exactly the types the declared surface gives the `section` role:
every kind's name is in that role's list, every name in the list is a kind, and the two
lists are the same length. A type added to or removed from the role in the artifact
therefore changes this module's kind list rather than leaving it behind. -/
theorem sectionKinds_match_table :
    (SectionKind.all.map SectionKind.typeName).all
        (fun name => tableSectionTypes.contains name) = true
      ∧ tableSectionTypes.all
        (fun name => (SectionKind.all.map SectionKind.typeName).contains name) = true
      ∧ SectionKind.all.length = tableSectionTypes.length := by
  decide

/-- Every section kind has a descriptor in the declared surface. -/
theorem sectionKinds_have_descriptors :
    SectionKind.all.all (fun kind => kind.descriptorCode.isOk) = true := by
  decide

/-- Every section kind's body has a shape this module reads. -/
theorem sectionKinds_have_shapes :
    SectionKind.all.all (fun kind => kind.shape.isOk) = true := by
  decide

/-- The kinds' names are pairwise distinct, which is a claim about the names and not about
list lengths: `List.map` preserves a list's length for *any* function, so a length equation
would hold whatever names the kinds carried, and it would say nothing about the descriptor
lookup being a function. This is the proposition that does: two kinds sharing a type name
would make `kindOfTypeName?` and `kindOfDescriptorCode?` order-dependent, and a descriptor
would name more than one section type. -/
theorem sectionKinds_distinct :
    (SectionKind.all.map SectionKind.typeName).Nodup = true := by
  decide

/-- The descriptors the kinds are looked up by are distinct too, so `kindOfDescriptorCode?`
answers with one kind rather than the first of several. -/
theorem sectionKinds_distinct_descriptors :
    (SectionKind.all.map (fun kind => kind.descriptorCode.toOption)).Nodup = true := by
  decide

/-! ## Fields, and the type rules the declared surface states

A composite's body is a list whose length may not exceed the declared field count, whose
mandatory fields may not be absent, and whose present fields may not contradict the type
declared for them. All three rules are read from `Generated.Oasis.Fields`, so a field
added to the artifact is a field this reader requires a type for. -/

/-- The declared fields of a type, in wire order. -/
def fieldDeclsOf (name : String) : Except String (List FieldDecl) := do
  let decl ← typeDeclOf name
  return fieldsOf decl.path

/-- The choices a declared type carries, read from the generated table. A choice is keyed by its
owner's *path* rather than by a name, so a type's choices are found through the path its own
declaration records; a type the table does not carry has none rather than an invented set. -/
def choicesOf (typeName : String) : List ChoiceDecl :=
  match typeDeclOf typeName with
  | .ok decl => choices.filter (fun choice => choice.ownerPath == decl.path)
  | .error _ => []

/-- The primitive type a declared type resolves to, following the restricted chain:
`ttl`'s declared type is `milliseconds`, which restricts `uint`. A wildcard stays a
wildcard. -/
def primitiveOf (name : String) : Except String String :=
  let rec go (fuel : Nat) (name : String) : Except String String :=
    match fuel with
    | 0 => .error s!"the restricted chain through {name} is longer than the declared surface"
    | fuel + 1 =>
      match types.find? (fun entry => entry.name == name) with
      | none => .ok name
      | some entry =>
        if entry.typeClass = .primitive then .ok entry.name
        else
          match entry.source with
          | some source => go fuel source
          | none => .error s!"{name} declares no source type"
  go 8 name

/-- The declared type name a descriptor value names, resolved through the table: the ulong
code or the symbolic name the artifact's `descriptor` element carries. A described value
whose descriptor names no declared type is not a described type of the surface at all. -/
def descriptorTypeName? (descriptor : Value) : Option String :=
  match descriptor with
  | .ulong code =>
    (types.find? (fun entry => entry.descriptor.map (·.code) == some code)).map (·.name)
  | .symbol text =>
    (types.find? (fun entry => entry.descriptor.map (·.name) == some text)).map (·.name)
  | _ => none

/-- Whether a value satisfies a declared field's type. A composite's declared type means
the value must be that type's described form; anything else resolves through the
restricted chain to the primitive the value's own constructor must be. -/
def typeAccepts (declared : String) (value : Value) : Except String Bool := do
  if declared = "*" then return true
  match types.find? (fun entry => entry.name == declared) with
  | some entry =>
    if entry.typeClass = .composite then
      match value with
      | .described descriptor _ => return (descriptorTypeName? descriptor) == some declared
      | _ => return false
    else
      let primitive ← primitiveOf declared
      return primitive == "*" || typeName value == primitive
  | none => return declared == "*" || typeName value == declared

/-- Whether a value satisfies a field's `requires` role. A role is filled either by a type
the surface declares as providing it — a described value whose descriptor resolves to that
type — or by a primitive whose own declared type provides it: `message-id`, for instance,
is provided by four restricted types over `ulong`, `uuid`, `binary` and `string`, and a
plain value of one of those primitives is what a sender can actually put on the wire. -/
def satisfiesRequires (role : String) (value : Value) : Except String Bool := do
  let providers := types.filter (fun entry => entry.provides.contains role)
  if providers.isEmpty then return false
  else
    if providers.any (fun entry => entry.typeClass = .composite) then
      match value with
      | .described descriptor _ =>
        match descriptorTypeName? descriptor with
        | some name => return (providers.any (fun entry => entry.name == name))
        | none => return false
      | _ => return false
    else
      let primitives ← providers.mapM (fun entry => primitiveOf entry.name)
      return primitives.contains (typeName value) || primitives.contains "*"

/-- Whether a value satisfies the declared type of a field the artifact declares `multiple`. The
types section states the attribute's meaning: *a single element of the type specified in the field
description is always permitted*, and multiple values are carried as an array whose elements are
that type. So an array is admitted exactly when every entry is, and an array with an entry that is
not is refused as a value of the wrong type — which is what makes the entries of such a field
readable at all. -/
def multipleAccepts (declared : String) (value : Value) : Except String Bool :=
  match value with
  | .array _ items => items.allM (typeAccepts declared)
  | single => typeAccepts declared single

/-! ## The defaults a receiver assumes for an omitted section

`header.1` is the one rule Part 3 states about a section a message *omits*: "if the header section
is omitted the receiver MUST assume the appropriate default values (or the meaning implied by no
value being set) for the fields within the «header»". The defaults are the declared surface's own —
`Generated.Oasis.Fields` carries every field's `default` attribute — so assuming them is a table
read rather than a list of values this module believes in, and a field the artifact declares no
default for is assumed to have no value rather than one chosen here.

A default is *text* in the table, and what a receiver assumes is a value: `durable`'s default is
the name `none`, which is the `terminus-durability` choice carrying the number 0, while
`delivery-count`'s is the digit `0` itself. So the text is read in the form the field's declared
type resolves to, and a default that names a declared choice is read as that choice's value. A text
the declared form cannot read is an error the caller sees: a receiver that assumed a wrongly-typed
default would be inventing the field it filled. -/

/-- The default the artifact declares for a field of a named type, as the raw attribute text. -/
def declaredDefaultOf (owner fieldName : String) : Except String (Option String) := do
  let decls ← fieldDeclsOf owner
  match decls.find? (fun decl => decl.name == fieldName) with
  | some decl => return decl.defaultValue
  | none => .error s!"the declared surface gives {owner} no field named {fieldName}"

/-- A numeric default's text as the number it spells, or an error naming the form it could not be
read as. -/
def numericDefault (primitive text : String) : Except String Nat :=
  match text.toNat? with
  | some n => .ok n
  | none => .error s!"the declared default {text} is not a number a {primitive} field carries"

/-- A default's text as a value of the primitive form a field's declared type resolves to. -/
def defaultValueOfText (primitive text : String) : Except String Value := do
  match primitive with
  | "boolean" => return .boolean (text == "true")
  | "ubyte" => return .ubyte (← numericDefault primitive text)
  | "ushort" => return .ushort (← numericDefault primitive text)
  | "uint" => return .uint (← numericDefault primitive text)
  | "ulong" => return .ulong (← numericDefault primitive text)
  | "symbol" => return .symbol text
  | "string" => return .string text
  | other => .error s!"this layer assumes no default of the {other} form"

/-- The declared choice a default's text names, where it names one. -/
def declaredChoiceOf? (typeName text : String) : Option ChoiceDecl :=
  (choicesOf typeName).find? (fun choice => choice.name == text)

/-- The value a receiver assumes for a field of a section a message omits: the default the artifact
declares, read as a value of the field's declared type — or as the value of the declared choice the
default names, since a choice's default is written by name. `none` where the artifact declares no
default, which is the sentence's "or the meaning implied by no value being set". -/
def assumedDefaultOf (decl : FieldDecl) : Except String (Option Value) :=
  match decl.defaultValue with
  | none => .ok none
  | some text =>
    match primitiveOf decl.typeName with
    | .error message => .error message
    | .ok primitive =>
      match declaredChoiceOf? decl.typeName text with
      | some choice => do return some (← defaultValueOfText primitive choice.value)
      | none => do return some (← defaultValueOfText primitive text)

/-- The header a receiver assumes when a message carries none: every field the artifact declares for
`header`, in declared order, at the value assumed for it or `none` where no default is declared.
This is the sentence as a value, which is what makes it usable by a reader that has to answer what a
header field's value is for a message that carried no header. -/
def assumedHeaderFields : Except String (List (String × Option Value)) := do
  let decls ← fieldDeclsOf "header"
  decls.mapM (fun decl => do
    let assumed ← assumedDefaultOf decl
    return (decl.name, assumed))

/-- A field the artifact declares no default for is assumed to have no value: the second half of the
sentence, at the assumption. Nothing in this layer fills a field the declared surface leaves
unfilled. -/
theorem assumedDefaultOf_none (decl : FieldDecl) (declared : decl.defaultValue = none) :
    assumedDefaultOf decl = .ok none := by
  rw [assumedDefaultOf, declared]

/-- A declared default the field's type can read is the value the receiver assumes. -/
theorem assumedDefaultOf_some (decl : FieldDecl) (text primitive : String) (value : Value)
    (declared : decl.defaultValue = some text)
    (primitiveIs : primitiveOf decl.typeName = .ok primitive)
    (notAChoice : declaredChoiceOf? decl.typeName text = none)
    (parsed : defaultValueOfText primitive text = .ok value) :
    assumedDefaultOf decl = .ok (some value) := by
  simp [assumedDefaultOf, declared, primitiveIs, notAChoice, parsed]
  all_goals rfl

/-- Check one present, non-null field against its declaration. A field the artifact declares
`multiple` is judged by `multipleAccepts`, because the attribute widens what the declared type
admits: its value is one element of the type or an array of them. The `requires` test follows the
same rule, because the types section conditions the *permitted element values* on the type
specification "and multiplicity of the corresponding field definition" — so a role is asked of
each element rather than of the array that carries them. -/
def checkField (decl : FieldDecl) (value : Value) : Except Refusal Unit := do
  let accepted ← liftRefusal
    (if decl.multiple then multipleAccepts decl.typeName value
     else typeAccepts decl.typeName value)
  if !accepted then
    .error (decodeRefusal "malformed"
      s!"{decl.owner}.{decl.name} is declared {decl.typeName} and the section carries a \
        {typeName value}")
  else
    match decl.requires with
    | none => pure ()
    | some role =>
      let satisfied ← liftRefusal
        (match value, decl.multiple with
         | .array _ items, true => items.allM (satisfiesRequires role)
         | _, _ => satisfiesRequires role value)
      if !satisfied then
        .error (decodeRefusal "malformed"
          s!"{decl.owner}.{decl.name} requires a value providing {role} and the section \
            carries a {typeName value}")
      else pure ()

/-- Whether a field's value is one that describes an absence of a value: the `null` that says
"not set", and a zero-length array, which the types section states describes the same absence —
"a null value and a zero-length array (with a correct type for its elements) both describe an
absence of a value and MUST be treated as semantically identical".

The array's element constructor is deliberately not consulted: this is the reading the two
carried sites already apply (`terminusFieldIsSet` and `multipleEntries` both treat any
zero-length array as the absence), and an array with no elements carries nothing whose type
the absence could turn on. A *non-empty* array is not an absence whatever its elements: it
states values, and it is judged by the field's declared type and multiplicity instead. -/
def isAbsentValue : Value → Bool
  | .null => true
  | .array _ [] => true
  | _ => false

/-- Check a composite's body: a list no longer than the declared field count, whose
mandatory fields are present and carry a value, and whose present fields match their declared
types and roles. A field is absent when it is null or a zero-length array — the two the types
section makes the same absence — and trailing absent fields are the encoding's way of saying
"not set", which is why a short list is admitted and a long one is not. -/
def checkFieldList (name : String) (items : List Value) : Except Refusal (List Value) := do
  let decls ← liftRefusal (fieldDeclsOf name)
  if items.length > decls.length then
    .error (decodeRefusal "malformed"
      s!"{name} declares {decls.length} field(s) and the section carries {items.length}")
  else
    let _ ← decls.mapM (fun decl =>
      match items[decl.index - 1]? with
      | none =>
        if decl.mandatory then
          .error (decodeRefusal "malformed"
            s!"{name} declares {decl.name} mandatory and the section omits it")
        else pure ()
      | some value =>
        if isAbsentValue value then
          if decl.mandatory then
            .error (decodeRefusal "malformed"
              s!"{name} declares {decl.name} mandatory and the section carries \
                {typeName value}, which states no value")
          else pure ()
        else checkField decl value)
    return items

/-! ## Messages: the structure the artifact's format-0 list states

The message-format section states which sections a message consists of, in order: at most
one each of the five head sections, a body that is one of three choices, and at most one
footer. That list is the whole of the structure rule, and it is what this pass enforces —
including the reading, stated at the head of this module, that a violation is
`amqp:decode-error`.
-/

/-- Where a section sits in the artifact's structure list. -/
inductive Slot where
  | header
  | deliveryAnnotations
  | messageAnnotations
  | properties
  | applicationProperties
  | body
  | footer
deriving Repr, DecidableEq, BEq

/-- The slot a section kind occupies: the five head sections in the order the artifact
lists them, the three body kinds, and the footer. -/
def SectionKind.slot (kind : SectionKind) : Slot :=
  match kind with
  | .header => .header
  | .deliveryAnnotations => .deliveryAnnotations
  | .messageAnnotations => .messageAnnotations
  | .properties => .properties
  | .applicationProperties => .applicationProperties
  | .data | .sequence | .value => .body
  | .footer => .footer

/-- Whether a slot is a head section, which the structure list admits at most once each. -/
def Slot.isHead : Slot → Bool
  | .header | .deliveryAnnotations | .messageAnnotations | .properties
  | .applicationProperties => true
  | .body | .footer => false

/-- The position of a slot in the structure list: a message's sections must not decrease. -/
def Slot.position : Slot → Nat
  | .header => 0
  | .deliveryAnnotations => 1
  | .messageAnnotations => 2
  | .properties => 3
  | .applicationProperties => 4
  | .body => 5
  | .footer => 6

/-- What a message's structure has accumulated so far. -/
structure Assembly where
  /-- The head kinds already present, which the structure list admits at most once each. -/
  heads : List SectionKind
  /-- The body choice already made: `data` and `sequence` may repeat, `value` may not. -/
  body : Option SectionKind
  /-- How many body sections have been read, because a single `amqp-value` section admits
  no second body section of any kind. -/
  bodyCount : Nat
  /-- The last position passed, so an out-of-order section is refused. -/
  position : Nat
  /-- Whether the footer has been read, after which no section may follow. -/
  closed : Bool
  /-- Whether the payload carried any section at all. A payload that carried sections and no
  body is refused; a payload that carried none is no message rather than a message without a
  body, which is the exemption the zero-octet payload needs. -/
  any : Bool
deriving Repr

/-- The structure state before any section. -/
def Assembly.empty : Assembly := ⟨[], none, 0, 0, false, false⟩

/-- The structure state's closing obligation: a payload that carried any section at all must
have carried a body. The structure list presents the body as one of the three choices in a
sequence — head sections, the body, the footer — so a payload carrying a header and nothing
else is not a message; reading that clause as a constraint on which *kinds* may appear as a
body instead would leave the sequence with a hole only that reading needs. The empty payload
is the one exemption and is not a fudge: a transfer with no payload carries no message at
all, which is a different thing from a message missing its body. -/
def Assembly.requireBody (state : Assembly) : Except Refusal Unit :=
  if !state.any then .ok ()
  else if state.body.isSome then .ok ()
  else
    .error (decodeRefusal "malformed"
      "the payload carries sections and no body, and the structure list gives the body as         one of the three choices: a message that carries any section carries a body")

/-- Add one section to the structure state, or refuse with the reason the structure list
gives. Each refusal names the rule it breaks, so a decoder that got the order wrong says
which section and which rule rather than "malformed message". -/
def Assembly.add (state : Assembly) (kind : SectionKind) : Except Refusal Assembly :=
  if state.closed then
    .error (decodeRefusal "malformed"
      s!"a {kind.typeName} section follows the footer, and the footer is the last section")
  else
    let slot := kind.slot
    if slot.position < state.position then
      .error (decodeRefusal "malformed"
        s!"a {kind.typeName} section appears after a section the structure list places later")
    else if slot.isHead then
      if state.heads.contains kind then
        .error (decodeRefusal "malformed"
          s!"a second {kind.typeName} section: the structure list admits at most one")
      else
        .ok { state with heads := kind :: state.heads, position := slot.position, any := true }
    else
      match slot with
      | .body =>
        match state.body with
        | some chosen =>
          if chosen = .value then
            .error (decodeRefusal "malformed"
              "a single amqp-value section is the whole body, and another section follows")
          else if chosen ≠ kind then
            .error (decodeRefusal "malformed"
              s!"a {kind.typeName} section in a body of {chosen.typeName} sections: the body \
                is one of the three choices, not a mixture")
          else
            .ok { state with bodyCount := state.bodyCount + 1, position := slot.position, any := true }
        | none =>
          .ok { state with body := some kind, bodyCount := 1, position := slot.position, any := true }
      | _ => .ok { state with closed := true, position := slot.position, any := true }

/-! ## The section type -/

/-- A decoded section. Each constructor carries its kind, because a section's kind decides
what its rule is — which is why an `annotations`-shaped body carries its pairs here rather
than as an untyped map that no rule could distinguish between the two map shapes. -/
inductive Section where
  /-- A composite section: its fields in declared order, trailing absent fields omitted. -/
  | fieldList (kind : SectionKind) (fields : List Value)
  /-- An `annotations`-shaped section: its pairs in wire order. -/
  | annotationMap (kind : SectionKind) (pairs : List (Value × Value))
  /-- A plain map section, whose keys are strings. -/
  | stringKeyMap (kind : SectionKind) (pairs : List (Value × Value))
  /-- A `data` section's payload. -/
  | octets (kind : SectionKind) (payload : Octets)
  /-- An `amqp-sequence` section's elements. -/
  | elements (kind : SectionKind) (items : List Value)
  /-- An `amqp-value` section's value. -/
  | single (kind : SectionKind) (value : Value)
deriving Repr

/-- A section's kind. -/
def Section.kind : Section → SectionKind
  | .fieldList kind _ => kind
  | .annotationMap kind _ => kind
  | .stringKeyMap kind _ => kind
  | .octets kind _ => kind
  | .elements kind _ => kind
  | .single kind _ => kind

/-! ## Rules that span two sections, or a message and a state

Two of Part 3's rules relate something a section carries to something outside that section. The
`content-encoding` field of `properties` is conditioned on the *body's* section kind, and the
`message-annotations` of a `modified` outcome are combined with the annotations the message
already carries. A section reader holds one section and a delivery-state reader holds one state,
which is why neither rule lives in either of them: both are stated here, at the level where the
two things each rule relates are both in hand.

**The refusals are the layer's readings.** Part 3 states these rules and names no condition for
breaking them, and this module's standing reading is that a rule of structure or of declared
field type it refuses carries `amqp:decode-error`. Both rules below are of that kind: the artifact
constrains what a message may carry, and a receiver that finds the constraint broken has octets it
cannot read as the message they claim to be. -/

/-- The `properties` section a message carries, where it carries one. -/
def propertiesSection? (sections : List Section) : Option Section :=
  sections.find? (fun sec => Section.kind sec == .properties)

/-- The value a message's `properties` section gives a field: none where the message carries no
properties section, where the section's list stops before the field, or where it carries a null
for it. A null and an omitted trailing field both say the field is not set, which is the reading
the composite rules and the delivery states already rest on. -/
def propertiesField? (sections : List Section) (name : String) : Option Value :=
  match propertiesSection? sections with
  | some (.fieldList _ fields) =>
    match (fieldDeclsOf "properties").toOption with
    | some decls =>
      (decls.find? (fun decl => decl.name == name)).bind (fun decl =>
        match fields[decl.index - 1]? with
        | some .null => none
        | other => other)
    | none => none
  | _ => none

/-- The section kinds a message's body carries: the structure list gives the body as one of three
choices, so this is the list of body sections in the order they appear. -/
def bodyKinds (sections : List Section) : List SectionKind :=
  (sections.filter (fun sec => (Section.kind sec).slot = .body)).map Section.kind

/-- The encoding the artifact's `content-encoding` documentation names as one implementations must
not use. The name is prose in the field's documentation rather than a declared choice — the
artifact declares no encoding vocabulary — so it cannot be a table lookup the way a descriptor
code can. -/
def identityEncoding : String := "identity"

/-- The two rules the `content-encoding` field's documentation states, applied where the field and
the body are both in hand:

* the field MUST NOT be set when the application-data section is other than `data`, so a message
  whose body is `amqp-sequence` or `amqp-value` sections and whose properties carry an encoding is
  refused; and
* implementations MUST NOT use the `identity` encoding, so a message carrying it is refused.

The body's kinds are read rather than assumed, because a body of `data` sections is the only body
the first rule permits. A payload carrying no body at all never reaches the second rule: the
structure list requires a body of any message that carries a section. -/
def checkContentEncoding (sections : List Section) : Except Refusal (List Section) :=
  match propertiesField? sections "content-encoding" with
  | none => .ok sections
  | some value =>
    let body := bodyKinds sections
    if !body.all (fun kind => kind == .data) then
      .error (decodeRefusal "malformed"
        s!"the properties section sets content-encoding and the body is {body.length} \
          section(s) that are not data sections, and the field MUST NOT be set when the \
          application-data section is other than data")
    else
      match value with
      | .symbol text =>
        if text == identityEncoding then
          .error (decodeRefusal "malformed"
            s!"the content-encoding is {identityEncoding}, and implementations MUST NOT use the \
              identity encoding")
        else .ok sections
      -- The field is declared a symbol, so this is unreachable through either reader; a value of
      -- another type is refused rather than passed as though it were an encoding.
      | other =>
        .error (decodeRefusal "malformed"
          s!"a content-encoding is a symbol and the properties section carries a {typeName other}")

/-- Whether two annotation keys are the same key. The two key types the annotations rules admit
are symbols and ulongs, and this compares those; a value of neither type is not a key any rule
admits, so it shares no key with anything, including itself. The comparison is on the keys rather
than on whole pairs because that is exactly what the merge decides: two entries for one key differ
in the value, and which of them survives is the rule. -/
def sameKey : Value → Value → Bool
  | .symbol left, .symbol right => left == right
  | .ulong left, .ulong right => left == right
  | _, _ => false

/-- The prefix that puts a symbolic annotation key *outside* the reserved space: the annotations
type's text is "all ulong keys, and all symbolic keys except those beginning with `x-` are
reserved". This is not the prefix the mandated detach is written against — that one is `x-opt` —
and the two are deliberately separate names here, because a key can be unreserved and still be one
the receiver must understand. -/
def unreservedPrefix : String := "x-"

/-- Whether an annotation key is reserved: every ulong key is, and a symbolic key is unless it
begins with `x-`. `none` where the value is not a key at all — neither a symbol nor a ulong — which
the key rule refuses on its type before this question is asked. -/
def reservedKey? : Value → Option Bool
  | .symbol text => some (!text.startsWith unreservedPrefix)
  | .ulong _ => some true
  | _ => none

/-- Whether a value is an annotation key at all: the annotations type admits symbols and ulongs, and
nothing else. -/
def isAnnotationKey : Value → Bool
  | .symbol _ => true
  | .ulong _ => true
  | _ => false

/-- **The reserved question is asked of keys and only of keys.** A value the reserved space has no
answer for is exactly one the key rule refuses on its type, so the two halves of the annotations
type's text — which keys exist, and which of them are reserved — cannot disagree about the set. -/
theorem reservedKey_isAskedOfKeys (value : Value) :
    (reservedKey? value).isSome = isAnnotationKey value := by
  cases value <;> rfl

/-- **Every ulong key is reserved**, which is the sentence's first half, at the lookup. -/
theorem ulongKeysAreReserved (code : Nat) : reservedKey? (.ulong code) = some true := rfl

/-- The message-annotations a message carries after a `modified` outcome's `message-annotations`
field is applied to them — the artifact's own rule for that field: an entry whose key the message
already carries *replaces* the message's entry for that key, and an entry whose key it does not
carry is *added*. Everything the message carried under a key the field does not name survives
untouched, which is the propagation half of the annotations rule with the augmentation the
sentence names as its exception. -/
def mergeAnnotations (existing augment : List (Value × Value)) : List (Value × Value) :=
  augment ++ existing.filter (fun pair => !(augment.any (fun entry => sameKey entry.1 pair.1)))

/-- The structure rules applied to a list of sections, which is what makes a writer's
domain sit inside a reader's: a caller that hands over an illegal order is refused rather
than producing octets its own reader would reject. -/
def checkStructure (sections : List Section) : Except Refusal (List Section) :=
  match sections.foldlM (fun state sec => state.add (Section.kind sec)) Assembly.empty with
  | .error reason => .error reason
  | .ok state =>
    match state.requireBody with
    | .error reason => .error reason
    | .ok () => checkContentEncoding sections

/-- A section as a corpus value: the shape its kind's declaration gives it. The vocabulary
is the type-system corpus's, so a section and the value it carries are written the same
way and a single comparison covers both. -/
def sectionToJson (sec : Section) : Json :=
  let named (kind : SectionKind) (extra : List (String × Json)) : Json :=
    Json.mkObj (("kind", kind.typeName) :: extra)
  match sec with
  | .fieldList kind fields => named kind [("fields", Json.arr (fields.map toJson).toArray)]
  | .annotationMap kind pairs => named kind [("pairs", Json.arr (toJsonPairs pairs).toArray)]
  | .stringKeyMap kind pairs => named kind [("pairs", Json.arr (toJsonPairs pairs).toArray)]
  | .octets kind payload => named kind [("payload", toHex payload)]
  | .elements kind items => named kind [("items", Json.arr (items.map toJson).toArray)]
  | .single kind value => named kind [("value", toJson value)]

/-- The section kind a corpus section's `kind` names. -/
def kindOfTypeName? (name : String) : Option SectionKind :=
  SectionKind.all.find? (fun kind => kind.typeName == name)

/-- A corpus value list read as values. -/
def valuesOfJson (fuel : Nat) (json : Json) (key : String) : Except String (List Value) := do
  let items ← json.getObjValAs? (Array Json) key
  items.toList.mapM (valueOfJson fuel)

/-- A corpus pair list read as pairs: each pair is a two-element array, in wire order,
because a map's order is significant and a JSON object could not keep it. -/
def pairsOfJson (fuel : Nat) (json : Json) : Except String (List (Value × Value)) := do
  let pairs ← json.getObjValAs? (Array (Array Json)) "pairs"
  pairs.toList.mapM (fun pair => do
    let items ← pair.toList.mapM (valueOfJson fuel)
    match items with
    | [key, value] => return (key, value)
    | _ => .error "a section's pair is exactly two values")

/-- A corpus section read as a section. The `kind` names the section type, which is what
tells the reader which body shape to expect. -/
def sectionOfJson (fuel : Nat) (json : Json) : Except String Section := do
  let name ← json.getObjValAs? String "kind"
  let kind ←
    match kindOfTypeName? name with
    | some kind => .ok kind
    | none => .error s!"'{name}' is not a section type this specification declares"
  let shape ← kind.shape
  match shape with
  | .fieldList => return .fieldList kind (← valuesOfJson fuel json "fields")
  | .annotationMap => return .annotationMap kind (← pairsOfJson fuel json)
  | .stringKeyMap => return .stringKeyMap kind (← pairsOfJson fuel json)
  | .octets => return .octets kind (← ofHex (← json.getObjValAs? String "payload"))
  | .elements => return .elements kind (← valuesOfJson fuel json "items")
  | .single => return .single kind (← valueOfJson fuel (← json.getObjVal? "value"))

/-! ## Reading a section

A section is a described value, so reading one is: read the value, resolve the descriptor
against the declared surface, check the role is `section`, and then read the body in the
shape the declaration gives. -/

/-- Resolve a descriptor value to the section kind it names, refusing a descriptor the
surface does not place on any section type. -/
def sectionKindOfDescriptor (descriptor : Value) : Except Refusal SectionKind :=
  match descriptorTypeName? descriptor with
  | none =>
    .error (decodeRefusal "malformed"
      "the descriptor names no type the declared surface carries")
  | some name =>
    match kindOfTypeName? name with
    | some kind => .ok kind
    | none =>
      .error (decodeRefusal "malformed"
        s!"{name} is a declared type that provides no section role, so a described value \
          of it is not a message section")

/-- Check an annotation key against the endpoint's policy. The artifact's rule has three
cases and this is all three: a symbolic key beginning with `x-opt` may be ignored; a key
the endpoint implements is understood; and any other key is one it does not understand, for
which the clause mandates a detach. A key that is neither a symbol nor a ulong is not an
annotation key at all. -/
def checkAnnotationKey (policy : Policy) (key : Value) : Except Refusal Unit :=
  let implemented (name : String) : Bool := policy.understood.contains name
  match key with
  | .symbol text =>
    if text.startsWith "x-opt" then pure ()
    else if implemented text then pure ()
    else
      .error (refusal notImplemented "unsupported"
        s!"the symbolic annotation key {text} is reserved and this endpoint does not \
          implement it, which the annotations text makes a detach")
  | .ulong code =>
    if implemented (toString code) then pure ()
    else
      .error (refusal notImplemented "unsupported"
        s!"the ulong annotation key {code} is reserved and this endpoint does not \
          implement it, which the annotations text makes a detach")
  | other =>
    .error (decodeRefusal "malformed"
      s!"an annotation key is a symbol or a ulong, and the section carries a \
        {typeName other}")

/-- Check one annotation pair: its key against the policy, and — for the one section whose
text names a key's value type — the value the key's own rule requires. -/
def checkAnnotationPair (kind : SectionKind) (policy : Policy) (pair : Value × Value) :
    Except Refusal Unit := do
  checkAnnotationKey policy pair.1
  if kind = .deliveryAnnotations then
    match pair.1 with
    | .symbol "rejected" =>
      let accepted ← liftRefusal (typeAccepts "error" pair.2)
      if !accepted then
        .error (decodeRefusal "malformed"
          s!"the value of the rejected annotation MUST be of type error and the section \
            carries a {typeName pair.2}")
      else pure ()
    | _ => pure ()
  else pure ()

/-- Check the pairs of an `annotations`-shaped section. -/
def checkAnnotationPairs (kind : SectionKind) (policy : Policy)
    (pairs : List (Value × Value)) : Except Refusal (List (Value × Value)) := do
  let _ ← pairs.mapM (checkAnnotationPair kind policy)
  return pairs

/-- Check the pairs of a plain map section whose text restricts the keys to strings and the
values to simple types, excluding `map`, `list` and `array`. -/
def checkStringKeyPairs (pairs : List (Value × Value)) : Except Refusal (List (Value × Value)) := do
  let _ ← pairs.mapM (fun pair =>
    match pair.1 with
    | .string _ => pure ()
    | other =>
      .error (decodeRefusal "malformed"
        s!"an application-properties key is a string and the section carries a {typeName other}")
    )
  let _ ← pairs.mapM (fun pair =>
    match pair.2 with
    | .map _ | .list _ | .array _ _ | .described _ _ =>
      .error (decodeRefusal "malformed"
        s!"an application-properties value is a simple type, and the section carries a \
          {typeName pair.2}")
    | _ => pure ())
  return pairs

/-- A body shape's name in a diagnostic, so a refusal says which shape was read for. -/
def shapeNameOf : SectionShape → String
  | .fieldList => "field list"
  | .annotationMap => "annotation map"
  | .stringKeyMap => "string-keyed map"
  | .octets => "binary"
  | .elements => "list"
  | .single => "wildcard value"

/-- Read one section from an already-decoded value. The octets it consumed are the caller's
business. -/
def sectionOfValue (policy : Policy) (value : Value) : Except Refusal Section :=
  match value with
  | .described descriptor body =>
    match sectionKindOfDescriptor descriptor with
    | .error reason => .error reason
    | .ok kind =>
      match kind.shape with
      | .error message => .error (decodeRefusal "malformed" message)
      | .ok shape =>
        match shape, body with
        | .fieldList, .list items =>
          (checkFieldList kind.typeName items).map (fun fields => .fieldList kind fields)
        | .annotationMap, .map pairs =>
          (checkAnnotationPairs kind policy pairs).map (fun pairs => .annotationMap kind pairs)
        | .stringKeyMap, .map pairs =>
          (checkStringKeyPairs pairs).map (fun pairs => .stringKeyMap kind pairs)
        | .octets, .binary payload => .ok (.octets kind payload)
        | .elements, .list items => .ok (.elements kind items)
        | .single, body => .ok (.single kind body)
        | shape, body =>
          .error (decodeRefusal "malformed"
            s!"a {kind.typeName} section's body is a {shapeNameOf shape} and the section \
              carries a {typeName body}")
  | other =>
    .error (decodeRefusal "malformed"
      s!"a section is a described value and the octets carry a {typeName other}")

/-- Octets to one section and the number of octets it consumed. The whole of the section's
decoding is the type system's reader plus the checks above: nothing here re-reads an octet
the value codec has read. -/
def decodeSection (policy : Policy) (bytes : Octets) : Except Refusal (Section × Nat) :=
  match decodeValue bytes with
  | .error refusal => .error ⟨decodeError, refusal.message⟩
  | .ok (value, consumed) =>
    match sectionOfValue policy value with
    | .error reason => .error reason
    | .ok decoded => .ok (decoded, consumed)

/-- Octets to the sections of a message, in order, with the structure rules applied as they
are read. `fuel` is the octet count: every section consumes at least one octet, so a
well-formed buffer is never refused for want of fuel and no input makes the reader
diverge. -/
def decodeMessage (policy : Policy) (bytes : Octets) : Except Refusal (List Section) :=
  let rec go (fuel : Nat) (offset : Nat) (state : Assembly) (acc : List Section) :
      Except Refusal (List Section) :=
    match fuel with
    | 0 =>
      .error (decodeRefusal "truncated"
        "the octets end inside a section, or the sections consume more than they carry")
    | fuel + 1 =>
      if offset ≥ bytes.size then
        match state.requireBody with
        | .error reason => .error reason
        | .ok () => .ok acc.reverse
      else
        match decodeSection policy (bytes.extract offset bytes.size) with
        | .error reason => .error reason
        | .ok (decoded, consumed) =>
          match state.add decoded.kind with
          | .error reason => .error reason
          | .ok next => go fuel (offset + consumed) next (decoded :: acc)
  -- The sections are read and the structure applied as they are; the rules that relate two of
  -- them are applied once the whole message is in hand, which is where the body's kinds are known.
  (go (bytes.size + 1) 0 Assembly.empty []).bind checkContentEncoding

/-- A payload whose body is exactly one `amqp-value` section, as its value. This is the
shape a payload-carried performative arrives in, so the transaction layer dispatches on the
value this returns rather than repeating the section's rule. -/
def bodyValue (policy : Policy) (bytes : Octets) : Except Refusal Value := do
  let decoded ← decodeMessage policy bytes
  match decoded with
  | [.single .value value] => return value
  | other =>
    .error (decodeRefusal "malformed"
      s!"a payload carrying one value is a single amqp-value section, and this one carries \
        {other.length} section(s)")

/-- The value an `amqp-value` section carries, where the section is one. -/
def valueCarried : Section → Option Value
  | .single _ value => some value
  | _ => none

/-- The `amqp-value` section carrying a value. -/
def amqpValue (value : Value) : Section := .single .value value

/-! ## A described composite, against the declared surface

Reading a described composite's fields by hand is what a transaction performative's caller
would otherwise do: this resolves the descriptor, checks the type is a composite the
surface declares, validates the body against the declared fields, and hands back the fields
in declared order. -/

/-- A described composite value, resolved. -/
structure Composite where
  /-- The declared type's name. -/
  typeName : String
  /-- Its declared fields, in wire order. -/
  decls : List FieldDecl
  /-- Its fields as the value carries them, trailing absent fields omitted. -/
  fields : List Value
deriving Repr

/-- The field a composite carries under a declared name, where the value carried it. -/
def Composite.field? (composite : Composite) (name : String) : Option Value :=
  match composite.decls.findIdx? (fun decl => decl.name == name) with
  | some position => composite.fields[position]?
  | none => none

/-- A described value read as a declared composite, with its body checked against the
declared fields. -/
def compositeOfValue (value : Value) : Except Refusal Composite :=
  match value with
  | .described descriptor body =>
    match descriptorTypeName? descriptor with
    | none =>
      .error (decodeRefusal "malformed"
        "the descriptor names no type the declared surface carries")
    | some name =>
      match fieldDeclsOf name with
      | .error message => .error (decodeRefusal "malformed" message)
      | .ok decls =>
        match body with
        | .list items =>
          (checkFieldList name items).map (fun fields => ⟨name, decls, fields⟩)
        | other =>
          .error (decodeRefusal "malformed"
            s!"{name} is a composite whose body is a field list and the value carries a \
              {typeName other}")
  | other =>
    .error (decodeRefusal "malformed"
      s!"a composite is a described value and the value carries a {typeName other}")

/-! ## Writing

A section is written as the described value its declaration gives: the descriptor code from
the table, then the body. The type system's writer chooses the narrowest form of every
encoding, so two implementations that both write a section this way write the same octets
and the corpus can compare them. -/

/-- A section's octets: its declared descriptor, then its body. The value layer's writer
answers with a classed refusal, and this layer's own refusal carries a condition and a
class-led detail, so the class travels in the detail exactly as it always has. -/
def encodeSection (sec : Section) : Except String Octets := do
  let kind := Section.kind sec
  let code ← kind.descriptorCode
  let body :=
    match sec with
    | .fieldList _ fields => Value.list fields
    | .annotationMap _ pairs => Value.map pairs
    | .stringKeyMap _ pairs => Value.map pairs
    | .octets _ payload => Value.binary payload
    | .elements _ items => Value.list items
    | .single _ value => value
  (encodeValue (.described (.ulong code) body)).mapError (fun refusal => refusal.message)

/-- A message's octets: its sections in the order given. The order is not recomputed from
the structure list, because a caller that hands over an illegal order is refused by
`checkStructure` rather than having its sections silently reordered — an intermediary MUST
NOT modify the bare message's sections. -/
def encodeMessage (sections : List Section) : Except String Octets := do
  let parts ← sections.mapM encodeSection
  return parts.foldl (· ++ ·) #[]

/-! ## Delivery states

The five states the messaging layer defines, and the machine that applies them. The
transaction layer's two states fill the same role and are recorded opaquely: their
terminality is the transaction layer's rule to state. -/

/-- The terminal outcomes the messaging layer defines. -/
inductive Outcome where
  /-- The message was processed successfully. -/
  | accepted
  /-- The message was invalid and unprocessable. The error the state carries is a
  **maintained but currently inert** quantity: the artifact's own words are that the field
  contains diagnostic information about the cause of the rejection, no rule in this layer
  consults it, and it is carried so that a decoded state is not silently narrower than the
  one it was read from. -/
  | rejected (error : Option Value)
  /-- The message was not, and will not be, processed. -/
  | released
  /-- The message was modified but not processed. `annotations` is the attributes the node is
  asked to combine with the message's own annotations, and it is **consulted**: the field is the
  artifact's named example of an augmentation, so `augmentAnnotations` merges it into the
  delivery's annotation map rather than recording it and moving nothing. That is what makes this
  the annotations rule's exception a rule about this layer instead of about an absent
  intermediary. -/
  | modified (deliveryFailed : Bool) (undeliverableHere : Bool)
      (annotations : Option (List (Value × Value)))
deriving Repr

/-- A delivery state: the non-terminal one the messaging layer defines, the terminal ones,
and a state the transaction layer defines recorded unmodelled. -/
inductive DeliveryState where
  | received (sectionNumber : Nat) (sectionOffset : Nat)
  | outcome (outcome : Outcome)
  /-- A declared delivery state this layer does not model: the transaction layer's. -/
  | unmodelled (typeName : String)
deriving Repr

/-- A delivery state's name, as the corpus's state vocabulary spells it. -/
def DeliveryState.name : DeliveryState → String
  | .received _ _ => "delivery:RECEIVED"
  | .outcome .accepted => "delivery:ACCEPTED"
  | .outcome (.rejected _) => "delivery:REJECTED"
  | .outcome .released => "delivery:RELEASED"
  | .outcome (.modified _ _ _) => "delivery:MODIFIED"
  | .unmodelled name => s!"delivery:{name}"

/-- Whether a delivery state is terminal: an outcome is, the non-terminal state and an
opaque state are not. The artifact's words are that delivery states are either terminal or
non-terminal, and that once a delivery reaches a terminal delivery state the state for that
delivery will no longer change. -/
def DeliveryState.terminal : DeliveryState → Bool
  | .outcome _ => true
  | .received _ _ => false
  | .unmodelled _ => false

/-- An unsigned integer field of a composite the declared surface has already validated. -/
def unsignedField (composite : Composite) (name : String) : Except Refusal Nat :=
  match composite.field? name with
  | some (.uint n) => .ok n
  | some (.ulong n) => .ok n
  | some other =>
    .error (decodeRefusal "malformed"
      s!"{composite.typeName}.{name} is an unsigned integer and the state carries a \
        {typeName other}")
  | none =>
    .error (decodeRefusal "malformed" s!"{composite.typeName} omits the mandatory {name}")

/-- A boolean field of a composite the declared surface has already validated. An absent
field and an explicit null both mean the field was not set, which for these fields is false:
a composite encoding omits trailing absent fields and may spell an absent one as null, and
the two must not read differently. -/
def booleanField (composite : Composite) (name : String) : Except Refusal Bool :=
  match composite.field? name with
  | some (.boolean b) => .ok b
  | some .null => .ok false
  | some other =>
    .error (decodeRefusal "malformed"
      s!"{composite.typeName}.{name} is a boolean and the state carries a {typeName other}")
  | none => .ok false

/-- The delivery state a described value names, validated against the declared surface: the
type must provide the `delivery-state` role, and its fields are checked as a composite's
are. The five the messaging layer defines are decoded; the transaction layer's two are
recorded opaquely; anything else is refused. -/
def deliveryStateOfValue (value : Value) : Except Refusal DeliveryState :=
  match compositeOfValue value with
  | .error reason => .error reason
  | .ok composite =>
    let providers := types.filter (fun entry => entry.provides.contains "delivery-state")
    if !(providers.any (fun entry => entry.name == composite.typeName)) then
      .error (decodeRefusal "malformed"
        s!"{composite.typeName} is a declared type that provides no delivery-state role")
    else
      match composite.typeName with
      | "received" => do
        let number ← unsignedField composite "section-number"
        let offset ← unsignedField composite "section-offset"
        return .received number offset
      | "accepted" => .ok (.outcome .accepted)
      | "rejected" => .ok (.outcome (.rejected (composite.field? "error")))
      | "released" => .ok (.outcome .released)
      | "modified" => do
        let deliveryFailed ← booleanField composite "delivery-failed"
        let undeliverableHere ← booleanField composite "undeliverable-here"
        let annotations ←
          match composite.field? "message-annotations" with
          | some (.map pairs) => .ok (some pairs)
          | some other =>
            .error (decodeRefusal "malformed"
              s!"modified.message-annotations is a map and the state carries a \
                {typeName other}")
          | none => .ok none
        return .outcome (.modified deliveryFailed undeliverableHere annotations)
      | other => .ok (.unmodelled other)

/-- A delivery, as the machine carries it. -/
structure Delivery where
  /-- The delivery-count the header of this delivery's message now carries. -/
  deliveryCount : Nat
  /-- The state recorded for the delivery, or none where no state is. -/
  state : Option DeliveryState
  /-- Whether the delivery is settled: **maintained and vector-observed, consulted by no
  rule in this slice**. It is reported to the corpus at every step, so a delivery that lost
  its settlement between two steps fails a vector; the rules that make settlement absorbing
  belong to the session's disposition handling, and inventing one here would be a reading
  the artifact does not state. -/
  settled : Bool
  /-- Whether the delivery's message may be delivered to this link again: the accepted
  outcome retires it at the node, rejected makes it unprocessable, released makes it
  available again, and modified says which of the two by its own fields. -/
  redeliveryAllowed : Bool
  /-- The message-annotations the delivery's message carries: what it arrived with, with a
  `modified` outcome's `message-annotations` field merged in when such an outcome is applied.
  This is the one quantity a delivery state *rewrites* rather than reports, which is why the
  artifact's rule for that field is a rule about a merge rather than about a record. -/
  annotations : List (Value × Value)
deriving Repr

/-- A delivery before any state has been applied. -/
def Delivery.empty : Delivery := ⟨0, none, false, true, []⟩

/-- **The delivery machine starts at the count the header declares.** A delivery that has applied no
state carries the delivery-count a receiver assumes when the message carries no header, and the
artifact declares that field's default as the text "0": the left half is the declared surface's own
answer and the right half is the machine's start, stated together so the two cannot drift. This is
the one header default any rule in this layer consults, and `assumedDefaultOf` is the rule that reads
the text as the value a receiver assumes. -/
theorem deliveryStartsAtTheDeclaredDefault :
    (declaredDefaultOf "header" "delivery-count").toOption = some (some "0")
      ∧ Delivery.empty.deliveryCount = 0 :=
  ⟨by decide, rfl⟩

/-- How much an outcome increments the delivery-count: `rejected` counts the attempt, and
`modified` counts it exactly when the peer said the delivery failed. The artifact's other two
outcomes state the opposite and are the reason this is a rule rather than a default. -/
def incrementOf : Outcome → Nat
  | .rejected _ => 1
  | .modified deliveryFailed _ _ => if deliveryFailed then 1 else 0
  | _ => 0

/-- Whether an outcome leaves the message deliverable to this link again: `accepted` retires
it at the node and `rejected` makes it unprocessable, while `released` makes it available
again and `modified` says so by its own `undeliverable-here` field. -/
def allowedOf : Outcome → Bool
  | .accepted => false
  | .rejected _ => false
  | .released => true
  | .modified _ undeliverableHere _ => !undeliverableHere

/-- The annotations an outcome leaves the delivery's message with: a `modified` outcome whose
`message-annotations` field is set merges them into what the message already carried, and every
other outcome — and a `modified` whose field is unset — leaves them as they were. This is the site
at which the annotations rule's exception lives: the clause says annotations are propagated unless
explicitly augmented or modified, and the one place this layer rewrites a message's annotations is
here. -/
def augmentAnnotations (outcome : Outcome) (existing : List (Value × Value)) :
    List (Value × Value) :=
  match outcome with
  | .modified _ _ (some augment) => mergeAnnotations existing augment
  | _ => existing

/-- A delivery with one state recorded, and the quantities that state's own rule moves:
`rejected` increments the delivery-count, `modified` increments it when `delivery-failed`
is set and forbids redelivery to this link when `undeliverable-here` is set, `released`
does neither, and `accepted` retires the message. -/
def recordState (delivery : Delivery) (state : DeliveryState) (settled : Bool) : Delivery :=
  match state with
  | .received _ _ =>
    { delivery with state := some state, settled := delivery.settled || settled }
  | .unmodelled _ =>
    { delivery with state := some state, settled := delivery.settled || settled }
  | .outcome outcome =>
    { delivery with
      state := some state
      settled := delivery.settled || settled
      deliveryCount := delivery.deliveryCount + incrementOf outcome
      redeliveryAllowed := allowedOf outcome
      annotations := augmentAnnotations outcome delivery.annotations }

/-- Apply a delivery state to a delivery, with settlement as the caller states it. The one
rule that governs the application itself, from the delivery-state section's own text, is
that a terminal state does not change: applying anything to a delivery whose state is
terminal is refused with the shared condition for what the current state does not permit.
Every other rule lives in `recordState`. -/
def applyState (delivery : Delivery) (state : DeliveryState) (settled : Bool) :
    Except Refusal Delivery :=
  match delivery.state with
  | some current =>
    if current.terminal then
      .error (refusal illegalState "illegalState"
        s!"the delivery's state is {current.name}, a terminal outcome, and a terminal \
          delivery state does not change")
    else .ok (recordState delivery state settled)
  | none => .ok (recordState delivery state settled)

/-- Settlement after a step: the disjunction of what the delivery carried and what the
state stated. It is a named function because it is the quantity the invariant below is
about, and because a reader looking for "when does a delivery become settled" should find
one place to look. -/
def settle (delivery : Delivery) (settled : Bool) : Bool := delivery.settled || settled

/-- `recordState` takes settlement as the disjunction of what the delivery carried and what
the state stated; this is that fact, which is what makes settlement absorbing. -/
theorem recordState_settled (delivery : Delivery) (state : DeliveryState) (settled : Bool) :
    (recordState delivery state settled).settled = settle delivery settled := by
  unfold settle
  cases state with
  | received number offset => simp [recordState]
  | unmodelled typeName => simp [recordState]
  | outcome outcome => cases outcome <;> simp [recordState]

/-- Settlement never returns to false: whatever state is applied, a delivery that was
settled stays settled. -/
theorem settled_monotone (delivery : Delivery) (state : DeliveryState) (settled : Bool)
    (result : Delivery) (applied : applyState delivery state settled = .ok result)
    (carried : delivery.settled = true) : result.settled = true := by
  have record : result = recordState delivery state settled := by
    unfold applyState at applied
    split at applied
    · split at applied
      · exact absurd applied (by simp)
      · exact (Except.ok.inj applied).symm
    · exact (Except.ok.inj applied).symm
  rw [record, recordState_settled]
  unfold settle
  rw [carried]
  rfl

/-- A terminal delivery state is absorbing: whatever state is applied to a delivery whose
state is terminal, the machine refuses it. -/
theorem terminal_absorbing (delivery : Delivery) (state : DeliveryState) (settled : Bool)
    (current : DeliveryState) (held : delivery.state = some current)
    (terminal : current.terminal = true) :
    ∃ reason : Refusal, applyState delivery state settled = .error reason := by
  unfold applyState
  rw [held]
  simp only [terminal, if_true]
  exact ⟨_, rfl⟩

/-! ## The terminus field sets (Part 3, addressing)

The addressing section's `source` and `target` are the messaging layer's other protocol-visible
field sets: the two composites an `attach` carries, whose fields the artifact's documentation
constrains beyond their declared types. The rules are of three kinds — coexistences on the record
(the address/dynamic pair, and node properties that may be sent only with the dynamic flag), role
membership for `default-outcome` and `distribution-mode`, and the readings the declared tables
give `durable` and `outcomes`. All of them are rules about the *record*; what a node then does
with the node a terminus names is the standard's own boundary and is not modelled here.

**The sender is an input.** The address rules are conditioned on *which link endpoint sent the
frame*, and that is not in the record: the same fields are legal in one direction and illegal in
the other. So the caller states it, exactly as it states the annotation policy — and for the same
reason, that a rule conditioned on knowledge the octets do not carry must be handed that knowledge
rather than guessed at. -/

/-- The two roles the artifact gives its terminus composites, and the declared outcome a source
must support when its record names none. They are type names, which is the vocabulary the declared
table is keyed by. -/
def sourceTypeName : String := "source"

def targetTypeName : String := "target"

def acceptedOutcomeTypeName : String := "accepted"

/-- Which link endpoint sent the frame a terminus arrived on. The two names are the artifact's own
`role` vocabulary, so the pair is looked up in the declared table rather than spelled out in a
rule. -/
inductive SendingEndpoint where
  | sender
  | receiver
deriving Repr, DecidableEq, BEq

/-- Both link endpoints, for the table check below. -/
def SendingEndpoint.all : List SendingEndpoint := [.sender, .receiver]

/-- An endpoint's name, which is a declared `role` choice's name. -/
def SendingEndpoint.name : SendingEndpoint → String
  | .sender => "sender"
  | .receiver => "receiver"

/-- The role value the declared `role` type gives an endpoint. -/
def SendingEndpoint.roleValue (endpoint : SendingEndpoint) : Except String String :=
  match (choicesOf "role").find? (fun choice => choice.name == endpoint.name) with
  | some choice => .ok choice.value
  | none => .error s!"the declared surface's role type carries no {endpoint.name} choice"

/-- The two endpoints' names are the declared `role` choices, so a role added to the artifact's
table is visible here rather than leaving the two lists to drift apart. -/
theorem sendingEndpoints_areTheDeclaredRoles :
    (SendingEndpoint.all.map SendingEndpoint.name).all
      (fun name => (choicesOf "role").any (fun choice => choice.name == name)) = true := by
  decide

/-- Whether a terminus field is set. A field the record omits and a field it carries a null for
both say "not set" — the reading the composite rules and the delivery states' flags already rest
on — and a zero-length array says the same, which the types section states outright: a null value
and a zero-length array both describe an absence of a value. -/
def terminusFieldIsSet (composite : Composite) (name : String) : Bool :=
  match composite.field? name with
  | some .null => false
  | some (.array _ []) => false
  | some _ => true
  | none => false

/-- The entries a field the artifact declares `multiple` carries: one element of the declared
type, or an array of them, which are the two encodings the types section gives the attribute. A
field that is not set carries no entries, which is the same "none" a zero-length array states. -/
def multipleEntries (composite : Composite) (name : String) : List Value :=
  match composite.field? name with
  | some (.array _ items) => items
  | some .null | none => []
  | some single => [single]

/-- The durability a value names, read from the `terminus-durability` type's declared choices. The
three meanings the field's documentation enumerates — the state of durable messages, only the
existence and configuration of the terminus, or no state at all — are the three choices the
artifact declares, so this is a lookup rather than a list of names kept in step by hand. -/
def durabilityName? (value : Value) : Option String :=
  match value with
  | .uint n =>
    ((choicesOf "terminus-durability").find?
      (fun choice => choice.value == toString n)).map (fun choice => choice.name)
  | _ => none

/-- The declared durabilities name three distinct states, so the lookup above answers with one
choice rather than the first of several. -/
theorem durabilities_areDistinct :
    ((choicesOf "terminus-durability").map (fun choice => choice.name)).Nodup = true
      ∧ ((choicesOf "terminus-durability").map (fun choice => choice.value)).Nodup = true := by
  decide

/-- The declared type a symbolic outcome descriptor names, where it names one that provides the
outcome role. The artifact writes an `outcomes` entry as a descriptor *name* —
`amqp:accepted:list` — so the lookup is against the declared surface's names, and a name no type
carries, or one whose type provides no outcome, is not a valid outcome descriptor. -/
def outcomeDescriptorOf? (text : String) : Option String :=
  match types.find?
      (fun entry => entry.descriptor.map (fun descriptor => descriptor.name) == some text) with
  | some entry => if entry.provides.contains "outcome" then some entry.name else none
  | none => none

/-- The descriptor value a declared outcome is named by: this is how the assumed-outcome rule
reaches the accepted outcome without writing its descriptor down. -/
def outcomeDescriptorValue? (typeName : String) : Option Value :=
  match types.find? (fun entry => entry.name == typeName) with
  | some entry => entry.descriptor.map (fun descriptor => Value.symbol descriptor.name)
  | none => none

/-- Check a terminus's `outcomes` field against the field documentation's second rule: when
present, the values must be a symbolic descriptor of a valid outcome. -/
def checkOutcomeDescriptors (composite : Composite) : Except Refusal Unit :=
  match (multipleEntries composite "outcomes").find? (fun entry =>
      match entry with
      | .symbol text => (outcomeDescriptorOf? text).isNone
      | _ => true) with
  | some (.symbol text) =>
    .error (decodeRefusal "malformed"
      s!"{composite.typeName}.outcomes names {text}, which is not the symbolic descriptor of a \
        declared outcome")
  | some other =>
    .error (decodeRefusal "malformed"
      s!"{composite.typeName}.outcomes carries a {typeName other}, and the field's values must be \
        symbolic descriptors")
  | none => .ok ()

/-- Check a terminus's `durable` field: when set, its value must name one of the declared
`terminus-durability` choices, which is what makes the three states the field's documentation
enumerates the three the artifact declares rather than three this module believes in. -/
def checkDurability (composite : Composite) : Except Refusal Unit :=
  match composite.field? "durable" with
  | some .null | none => .ok ()
  | some value =>
    match durabilityName? value with
    | some _ => .ok ()
    | none =>
      .error (decodeRefusal "malformed"
        s!"{composite.typeName}.durable carries a {typeName value}, and the value MUST name one \
          of the declared terminus-durability choices")

/-- Check a terminus field against the role its documentation and its declared `requires`
attribute both name: `default-outcome` must be a valid outcome, and `distribution-mode` a
distribution mode. -/
def checkTerminusRole (composite : Composite) (field role : String) : Except Refusal Unit :=
  match composite.field? field with
  | some .null | none => .ok ()
  | some value => do
    let satisfied ← liftRefusal (satisfiesRequires role value)
    if satisfied then .ok ()
    else
      .error (decodeRefusal "malformed"
        s!"{composite.typeName}.{field} carries a {typeName value}, and the field's value MUST \
          be a valid {role}")

/-- The rules Part 3's `source` and `target` field documentation states, applied to a record.
`sentBy` is the endpoint that sent the frame, because the address rules are conditioned on it and
nothing in the record carries it.

The address rule is one rule written twice in the artifact: the endpoint that *creates* a dynamic
node communicates its address, and the endpoint that *requests* creation must leave the field
unset — and which endpoint that is mirrors between the two types, because the receiver requests a
source's node and the sender requests a target's. So the pair of fields is judged against the one
role that created the node, and the six sentences of the two types' documentation are its six
instances. -/
def checkTerminus (sentBy : SendingEndpoint) (composite : Composite) : Except Refusal Unit := do
  let name := composite.typeName
  let dynamic ← booleanField composite "dynamic"
  let addressSet := terminusFieldIsSet composite "address"
  let creator := (name == sourceTypeName && sentBy == .sender)
    || (name == targetTypeName && sentBy == .receiver)
  if dynamic && creator && !addressSet then
    .error (decodeRefusal "malformed"
      s!"a dynamic {name} sent by the {sentBy.name} endpoint leaves the address unset, and the \
        endpoint that created the node is the one communicating its address")
  else if dynamic && !creator && addressSet then
    .error (decodeRefusal "malformed"
      s!"a dynamic {name} sent by the {sentBy.name} endpoint sets the address, and the endpoint \
        that requested creation MUST NOT set it")
  else if !dynamic && terminusFieldIsSet composite "dynamic-node-properties" then
    .error (decodeRefusal "malformed"
      s!"{name}.dynamic-node-properties is set while the dynamic field is not, and the field MUST \
        be left unset unless the dynamic field is set to true")
  else do
    checkTerminusRole composite "default-outcome" "outcome"
    checkTerminusRole composite "distribution-mode" "distribution-mode"
    checkDurability composite
    checkOutcomeDescriptors composite

/-- The outcomes a source's record leaves choosable, which is the rule the `outcomes` field's
documentation states for its empty case: an empty field means the default-outcome is assumed for
every transfer, and where neither that field nor the default-outcome is set the *accepted* outcome
is the one the source must support. The fallback's descriptor is read from the declared table
rather than written down, so a surface without it is an error the reader reports instead of a
value it invents. So the list is never empty — a reader of a source always has an outcome to
apply, and the one it falls back to is the artifact's own. -/
def assumedOutcomes (composite : Composite) : Except Refusal (List Value) :=
  match multipleEntries composite "outcomes" with
  | [] =>
    match composite.field? "default-outcome" with
    | some value => .ok [value]
    | none =>
      match outcomeDescriptorValue? acceptedOutcomeTypeName with
      | some value => .ok [value]
      | none =>
        .error (decodeRefusal "malformed"
          s!"the declared surface carries no {acceptedOutcomeTypeName} outcome descriptor for a \
            source that announces no outcomes to fall back on")
  | announced => .ok announced

/-- The assumed-outcome rule really does leave a reader something to apply: whatever a source's
record announces, the list this returns has at least the field's documentation's fallback in it. -/
theorem assumedOutcomes_nonEmpty (composite : Composite) (assumed : List Value)
    (result : assumedOutcomes composite = .ok assumed) : assumed ≠ [] := by
  intro empty
  rw [empty] at result
  unfold assumedOutcomes at result
  split at result <;> (try (split at result)) <;> (try (split at result)) <;> simp_all

/-- A described value read as a terminus: the composite checked against the declared fields, the
type's role confirmed to be one of the two terminus roles the artifact declares, and the field
documentation's rules applied. -/
def terminusOfValue (sentBy : SendingEndpoint) (value : Value) : Except Refusal Composite := do
  let composite ← compositeOfValue value
  let decl ← liftRefusal (typeDeclOf composite.typeName)
  if !(decl.provides.contains sourceTypeName || decl.provides.contains targetTypeName) then
    .error (decodeRefusal "malformed"
      s!"{composite.typeName} is a declared type that provides neither the source nor the target \
        role, so a described value of it is not a terminus")
  else do
    checkTerminus sentBy composite
    return composite

/-! ## The layer's corpus interface -/

/-- The policy a vector hands the message layer. The vocabulary is the corpus's: a list of
the annotation keys the endpoint implements, in the form they appear on the wire — a
symbol's text, or a ulong's decimal digits. -/
def policyOfJson (json : Json) : Except String Policy :=
  match (json.getObjVal? "understood").toOption with
  | none => .ok Policy.empty
  | some keys => do
    let keys ← keys.getArr?
    return ⟨← keys.toList.mapM (fun key => key.getStr?)⟩

/-- The specification's Part 3 layer behind the corpus interface. A corpus defect — a
policy, a section or a message the vocabulary cannot express — is reported as a refusal
with the layer's own condition rather than as a harness error, so a caller cannot mistake a
malformed vector for a protocol verdict. -/
def specMessageCodec : SpecAMQP.Harness.MessageCodec where
  name := "specification"
  decodeSection := fun policy bytes => do
    let policy ← liftRefusal (policyOfJson policy)
    let (decoded, consumed) ← decodeSection policy bytes
    return (sectionToJson decoded, consumed)
  encodeSection := fun json => do
    let decoded ← sectionOfJson 64 json
    encodeSection decoded
  decodeMessage := fun policy bytes => do
    let policy ← liftRefusal (policyOfJson policy)
    let decoded ← decodeMessage policy bytes
    return decoded.map sectionToJson
  encodeMessage := fun json => do
    let raw ← json.getArr?
    let sections ← raw.toList.mapM (sectionOfJson 64)
    let sections ← match checkStructure sections with
      | .ok sections => .ok sections
      | .error reason => .error reason.detail
    encodeMessage sections

/-- What a delivery looks like after a state was applied, in the corpus vocabulary: the
state it is in, the count it carries, its settlement, the resume point it reports, whether
redelivery is allowed, and the refusal where one was raised. -/
def deliveryOutcomeOf (delivery : Delivery) (refusal? : Option Refusal)
    (applied : Option String) : SpecAMQP.Harness.DeliveryOutcome :=
  let resume :=
    match delivery.state with
    | some (.received number offset) => (some number, some offset)
    | _ => (none, none)
  { admitted := refusal?.isNone
    state :=
      match delivery.state with
      | some state => state.name
      | none => "delivery:UNSETTLED"
    deliveryCount := delivery.deliveryCount
    settled := delivery.settled
    sectionNumber := resume.1
    sectionOffset := resume.2
    redeliveryAllowed := delivery.redeliveryAllowed
    condition := refusal?.map (·.condition)
    detail :=
      match refusal? with
      | some reason => reason.detail
      | none => s!"applied {applied.getD "a state"}" }

/-- The specification's delivery-state machine behind the corpus interface. -/
def specDeliveryCodec : SpecAMQP.Harness.DeliveryCodec where
  name := "specification"
  St := Delivery
  start := fun name =>
    match name with
    | "delivery:UNSETTLED" => .ok Delivery.empty
    | other => .error s!"'{other}' is not a delivery state this machine starts in"
  apply := fun delivery step => do
    let applied ← step.getObjVal? "apply"
    let settled := (step.getObjValAs? Bool "settled").toOption.getD false
    let decoded ← valueOfJson 64 applied
    match deliveryStateOfValue decoded with
    | .error reason => return (deliveryOutcomeOf delivery (some reason) none, delivery)
    | .ok state =>
      match applyState delivery state settled with
      | .ok next => return (deliveryOutcomeOf next none (some state.name), next)
      | .error reason => return (deliveryOutcomeOf delivery (some reason) none, delivery)

end SpecAMQP.Spec.Message
