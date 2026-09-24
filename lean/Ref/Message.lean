import Generated.Oasis.Choices
import Generated.Oasis.Fields
import Ref.Frame
import Ref.Vectors

/-!
# A reference implementation of the AMQP 1.0 message layer

This is a reference *implementation* of Part 3's message format and delivery states,
written from the OASIS clauses and independently of `Spec.Message`: the two artefacts
share no definition, so their agreement over the message corpus is evidence about the
artifact rather than a tautology.

The declared surface is data, so this layer reads it. The nine section types are
exactly the declared types the generated table gives the `section` role; a section's
descriptor, field order, mandatory flags and field types come from
`Generated.Oasis.Fields`; the error conditions a refusal names come from
`Generated.Oasis.Choices`. Nothing here writes a descriptor code or an `amqp:`-shaped
symbol: a name is looked up in the table it came from.

Deliberate choices, none of which a clause fixes:

* **A section's body must have the shape its declared type's source fixes.** A data
  section's body is binary, an amqp-sequence's is a compound list, an amqp-value's is
  one value, an annotations-sourced section's is a map, and a composite's is its
  declared field list. A body of another shape is refused rather than dispatched on
  the descriptor alone, because the section's name and its body would then disagree.
* **A composite's body may be shorter than the declared field count** — trailing
  absent fields are omitted — **but never longer**, and a field the artifact declares
  mandatory must be present and not null. A null in a non-mandatory position means
  the field is not set, which is why a null passes any declared type: the artifact
  gives `null` the meaning "no value", so it is the absence of a field and not a
  value of the field's type.
* **A message that carries any section carries a body**, because the artifact's
  occurrence list gives the body as one of three choices rather than as an optional
  section. The empty payload is the one message with no sections, which the corpus
  pins and peers do send.
* **The head sections are ordered.** The artifact's list and its diagram both give
  the order header, delivery-annotations, message-annotations, properties,
  application-properties, and an intermediary that may not reorder a bare message
  cannot tell a reordered one from a different message.
* **The annotation key rule is the reader's, and the policy is an input.** The
  annotations clause mandates a detach for a key the receiver does not understand
  unless it begins with `x-opt`, so "which keys this endpoint implements" cannot be
  decided inside the decoder: it is a `Policy`, and both artefacts must be handed the
  same one to be comparable. The writer applies the key's *type* rule and not this
  one, because the corpus hands the writer no policy — a canonical re-encoding is
  written from what the reader admitted, and a writer that refused a reserved key the
  reader had just accepted would make every such vector unrepresentable.
* **An application-properties value must be a simple type.** The artifact excludes
  map, list and array by name; a described value is a composite's encoding and is
  excluded with them.
* **A field declared `multiple` carries one element or an array of them.** The types section
  states the attribute's meaning outright, so an array is judged entry by entry there and is
  refused in a field that is not `multiple`; reading it is what makes a source's announced
  outcomes readable at all.
* **The rules that span two sections are applied where both are in hand.** The
  `content-encoding` field is judged against the body's section kind once the message has been
  read, and a `modified` outcome's `message-annotations` are merged into the annotations the
  message already carried rather than recorded beside them.
* **A terminus is a field record with the sender as an input.** The `source` and `target`
  composites' documentation conditions the address rules on which link endpoint sent the frame,
  so `terminusOfValue` takes that endpoint and the record does not: a rule conditioned on
  knowledge the octets do not carry is handed it rather than guessed at.
-/

namespace SpecAMQP.Ref.Message

open Lean
open SpecAMQP.Harness
open SpecAMQP.Ref.Frame (typeOfDescriptor)
open SpecAMQP.Ref.Vectors (jsonOfValue refusalText valueOfJson)
open SpecAMQP.Generated.Oasis

/-! ## Refusals

A refusal is the condition the corpus compares and a detail whose leading token is the
reason class the differential contract reads. Conditions are looked up in the shared
error family rather than written down, so a condition cannot drift from the table.
-/

/-- The value of a condition name in the family the artifact declares for shared errors.
A name the table does not carry is returned as it was given, which makes the lookup's
failure visible in a verdict rather than silent. -/
def errorCondition (name : String) : String :=
  ((errorConditionsOf "amqp-error").find? (fun decl => decl.name == name)).map
    (fun decl => decl.value) |>.getD name

/-- A structural, arity or declared-type violation: the artifact states these rules and
names no condition for violating them, so the refusal is the shared decode error. -/
def malformed (prose : String) : Refusal :=
  ⟨errorCondition "decode-error", s!"malformed: {prose}"⟩

/-- A key this endpoint does not implement: the annotations clause mandates a detach
"with a not-implemented error" and names no member of the family that would narrow it. -/
def unsupported (prose : String) : Refusal :=
  ⟨errorCondition "not-implemented", s!"unsupported: {prose}"⟩

/-- A state applied to a delivery whose state is terminal, which the delivery-state
section says will no longer change. -/
def illegalState (prose : String) : Refusal :=
  ⟨errorCondition "illegal-state", s!"illegalState: {prose}"⟩

/-- A failure the value layer raised, as this layer reports it: every variant is a decode
error on the wire, and the class-led detail is the value layer's own. -/
def ofDecodeError (error : DecodeError) : Refusal :=
  ⟨errorCondition "decode-error", refusalText error⟩

/-! ## The names the artifact uses

The artifact states these as type names, not as descriptor codes: the wildcard a
restricted type may be sourced from, the annotations type whose key rule the three
annotations-sourced sections inherit, the application-properties type whose value rule
is its own, the reserved annotation key and its value's declared type, and the prefix
that exempts a symbolic key from the key rule. -/

/-- The wildcard: a type sourced from it carries any value. -/
def wildcardName : String := "*"

/-- The annotations type: a map whose keys are symbols or ulongs, with the key rule the
delivery-annotations, message-annotations and footer sections inherit. -/
def annotationsType : String := "annotations"

/-- The application-properties type, whose own text restricts its keys and values. -/
def applicationPropertiesType : String := "application-properties"

/-- The reserved symbolic annotation key that carries error information. -/
def rejectedKey : String := "rejected"

/-- The type the reserved key's values must have. -/
def errorTypeName : String := "error"

/-- The prefix that exempts a symbolic annotation key from the key rule. -/
def xOptPrefix : String := "x-opt"

/-! ## The endpoint's policy -/

/-- The annotation keys this endpoint implements, as the corpus writes them: a symbol's
text, or a ulong's digits. The annotations clause mandates a detach for a key the
receiver does not understand, so this is the receiver's own knowledge and cannot be
decided from the octets; making it an input is what lets two artefacts be compared. -/
structure Policy where
  understood : List String
deriving Repr, BEq

namespace Policy

/-- An endpoint that implements none of the reserved keys, so only the `x-opt` keys the
clause says to ignore are admitted. -/
def empty : Policy := ⟨[]⟩

/-- The policy a vector hands the message layer, absent meaning none. -/
def ofJson (json : Json) : Policy :=
  match (json.getObjValAs? (Array Json) "understood").toOption with
  | some keys => ⟨keys.toList.filterMap (fun key => key.getStr?.toOption)⟩
  | none => empty

/-- Whether this endpoint implements a key: a symbolic key by its text, a ulong key by
its digits. Any other key is not a key this policy has a word about, and the key rule
refuses it on its type before asking. -/
def understands (policy : Policy) (key : Value) : Bool :=
  match key with
  | .symbol text => policy.understood.contains text
  | .ulong n => policy.understood.contains (toString n.toNat)
  | _ => false

end Policy

/-! ## The declared surface, read as data -/

/-- The declared type of an artifact name. -/
def declaredType? (name : String) : Option TypeDecl :=
  types.find? (fun decl => decl.name == name)

/-- The restricted chain from a declared name to the type it is ultimately sourced from:
`delivery-annotations` reaches `map` through `annotations`, which is what makes the key
rule and the wire shape both readable from the table. The walk is bounded by the table's
length, because the table is data and a cycle in it would otherwise make this diverge. -/
def chainOfFuel (fuel : Nat) (name : String) : List String :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    name :: (match declaredType? name with
      | some decl =>
        match decl.typeClass with
        | .restricted => chainOfFuel fuel (decl.source.getD wildcardName)
        | _ => []
      | none => [])

/-- A declared type's restricted chain. -/
def chainOf (name : String) : List String := chainOfFuel types.length name

/-- The wire shape a declared type's value takes: the wildcard carries any value, a
primitive carries its own, a composite is a described field list, and a restricted type
takes the shape of the type it is sourced from. -/
inductive Shape where
  | wildcard
  | primitive (name : String)
  | composite (name : String)
deriving Repr, BEq, DecidableEq

/-- The shape of a declared name, read off the end of its chain. -/
def shapeOf (name : String) : Option Shape :=
  match (chainOf name).reverse with
  | [] => none
  | last :: _ =>
    if last == wildcardName then some .wildcard
    else match declaredType? last with
      | some decl =>
        match decl.typeClass with
        | .primitive => some (.primitive decl.name)
        | .composite => some (.composite decl.name)
        -- The chain stops at a restricted type only if the walk ran out of fuel.
        | .restricted => none
      | none => none

/-- Whether a value's type provides a declared role: a described value says so through the
type its descriptor names, and a bare value says so through a declared type whose wire
shape is the value's own constructor and which provides the role. Part 3's fields with a
`requires` attribute are the ones this decides. -/
def providesRole (value : Value) (role : String) : Bool :=
  match value with
  | .described descriptor _ =>
    match typeOfDescriptor descriptor with
    | some decl => decl.provides.contains role
    | none => false
  | _ =>
    types.any (fun decl => decl.provides.contains role &&
      match shapeOf decl.name with
      | some (.primitive name) => name == typeName value
      | _ => false)

/-! ## The nine section types

The artifact's occurrence list names nine section types, and the generated table gives
exactly those nine the `section` role. The kinds below are those types; each one's name
is checked against the table before it is read, so a kind and a declared type cannot
disagree. -/

/-- One of the nine section types of message format 0. -/
inductive SectionKind where
  | header
  | deliveryAnnotations
  | messageAnnotations
  | properties
  | applicationProperties
  | data
  | amqpSequence
  | amqpValue
  | footer
deriving Repr, BEq, DecidableEq

namespace SectionKind

/-- The artifact's name for the section type, which is also the corpus's `kind` text. -/
def name : SectionKind → String
  | .header => "header"
  | .deliveryAnnotations => "delivery-annotations"
  | .messageAnnotations => "message-annotations"
  | .properties => "properties"
  | .applicationProperties => "application-properties"
  | .data => "data"
  | .amqpSequence => "amqp-sequence"
  | .amqpValue => "amqp-value"
  | .footer => "footer"

/-- The nine kinds, in the order the artifact's own list gives them. -/
def all : List SectionKind :=
  [.header, .deliveryAnnotations, .messageAnnotations, .properties, .applicationProperties,
   .data, .amqpSequence, .amqpValue, .footer]

/-- The declared type a kind names, provided the generated surface gives that type the
`section` role: a name the table does not carry as a section is not one this layer reads. -/
def decl? (kind : SectionKind) : Option TypeDecl :=
  match declaredType? kind.name with
  | some decl => if decl.provides.contains "section" then some decl else none
  | none => none

/-- A kind from the artifact's own name, checked against the table rather than against a
second list of names. -/
def ofName (text : String) : Option SectionKind :=
  match all.find? (fun kind => kind.name == text) with
  | some kind => if (decl? kind).isSome then some kind else none
  | none => none

/-- A head section's position in the artifact's list, which is also its order in the
message; `none` for the three body choices and the footer. -/
def headOrder : SectionKind → Option Nat
  | .header => some 0
  | .deliveryAnnotations => some 1
  | .messageAnnotations => some 2
  | .properties => some 3
  | .applicationProperties => some 4
  | _ => none

end SectionKind

/-! ## A value against its declared type

The rules the artifact states for a composite's body: the fields are the declared ones in
declared order, a mandatory one is present and not null, a present one matches its
declared type along the restricted chain, and a field carrying a `requires` role is
satisfied by a value whose type provides that role. Deliberately not stated: a maximum
depth. The recursion follows the value, which the octets bound.
-/

mutual

/-- One field's value against the declared type at its position. A null states no value, so
it is the absence of the field: forbidden where the artifact declares the field mandatory,
and otherwise the same as omitting a trailing one. -/
def checkTyped (declared : String) (requires : Option String) (mandatory : Bool)
    (value : Value) : Except Refusal Unit :=
  if value == .null then
    if mandatory then
      .error (malformed s!"a field declared {declared} is mandatory and is carried as a null, \
        which does not state a value")
    else .ok ()
  else
    match shapeOf declared with
    | none =>
      .error (malformed s!"the declared type {declared} is not one the generated surface \
        carries")
    | some .wildcard =>
      match requires with
      | none => .ok ()
      | some role =>
        if providesRole value role then .ok ()
        else
          .error (malformed s!"a field requiring the {role} role carries a {typeName value}, \
            whose type provides it not")
    | some (.primitive name) =>
      if typeName value == name then .ok ()
      else
        .error (malformed s!"a field declared {declared} carries a {typeName value}, and the \
          declared type's shape is {name}")
    | some (.composite name) =>
      match value with
      | .described descriptor body =>
        match typeOfDescriptor descriptor with
        | none =>
          .error (malformed s!"a field declared {name} carries a described value whose \
            descriptor names no declared type")
        | some decl =>
          if decl.name == name then checkBody decl body
          else
            .error (malformed s!"a field declared {name} carries a {decl.name}, so the field \
              and its value disagree about the type")
      | _ =>
        .error (malformed s!"a field declared {name} carries a {typeName value}, and a \
          composite is carried as a described field list")
termination_by sizeOf value

/-- A composite's body: its declared fields against the values the body carries. -/
def checkBody (decl : TypeDecl) (body : Value) : Except Refusal Unit :=
  match body with
  | .list values => checkFields (fieldsOf decl.path) values
  | _ =>
    .error (malformed s!"{decl.name} is a composite and its body is a {typeName body} \
      rather than a field list")
termination_by sizeOf body

/-- The declared fields against the body's values, position by position. A body may stop
before the declared field count; it may not run past it, because the values after the last
declared field are values the type does not have. A mandatory field the body stops before is
the one absence the artifact forbids.

A field the artifact declares `multiple` is judged by the types section's own reading of the
attribute — a single element of the declared type is always permitted, and multiple values are an
array whose elements are the type the field defines — so an array is judged entry by entry. An
array in a field that is *not* `multiple` is refused, because the attribute is what permits it. -/
def checkFields : List FieldDecl → List Value → Except Refusal Unit
  | decls, [] =>
    match decls.find? (fun field => field.mandatory) with
    | some field =>
      .error (malformed s!"the mandatory field {field.name} of {field.owner} is not present \
        in a body that stops before it")
    | none => .ok ()
  | [], _ :: _ =>
    .error (malformed "a body carries more values than the type declares fields")
  | decl :: rest, value :: values => do
    let _ ←
      match value with
      | .array _ items =>
        if decl.multiple then do
          let _ ← items.mapM (fun item => checkTyped decl.typeName decl.requires false item)
          pure ()
        else
          .error (malformed s!"a field declared {decl.typeName} carries an array of \
            {items.length} entr(ies), and the types section permits multiple values only in a \
            field the artifact declares multiple")
      | other => checkTyped decl.typeName decl.requires decl.mandatory other
    checkFields rest values
termination_by _ vs => sizeOf vs

end

/-! ## Map-sourced sections

An annotations map restricts its keys to symbols and ulongs, and mandates a detach for a
key the receiver does not understand unless it begins with `x-opt`; the reserved symbolic
key `rejected` carries error information and its value must be of type `error`.
Application-properties restricts its keys to strings and its values to simple types. The
two rules are told apart by the chain the section's declared type reaches, which is where
the artifact states which of the two a section inherits.
-/

/-- An annotation key's type: a symbol or a ulong. The endpoint's comprehension of the key
is the reader's own rule and is applied where the policy is an input; this much is the
section's shape and holds in both directions. -/
def checkAnnotationKey (key : Value) : Except Refusal Unit :=
  match key with
  | .symbol _ => .ok ()
  | .ulong _ => .ok ()
  | _ =>
    .error (malformed s!"an annotation key is a symbol or a ulong, and this one is a \
      {typeName key}")

/-- The one value rule the artifact states for an annotation: a value associated with the
reserved symbolic key `rejected` must be of type error. -/
def checkAnnotationValue (key value : Value) : Except Refusal Unit :=
  match key with
  | .symbol text => if text == rejectedKey then checkTyped errorTypeName none false value else .ok ()
  | _ => .ok ()

/-- One annotation pair: a key of one of the two types, and the value rule for the reserved
key that carries error information. -/
def checkAnnotationPair (pair : Value × Value) : Except Refusal Unit := do
  checkAnnotationKey pair.1
  checkAnnotationValue pair.1 pair.2

/-- The endpoint's comprehension of an annotation's key: the clause mandates a detach for a
key the receiver does not understand unless it begins with `x-opt`. This is the receiver's
knowledge, so it holds where a policy is an input and not where the writer writes what it was
handed: a corpus's canonical re-encoding is written without one. -/
def checkAnnotationPolicy (policy : Policy) (key : Value) : Except Refusal Unit :=
  match key with
  | .symbol text =>
    if text.startsWith xOptPrefix || policy.understands key then .ok ()
    else
      .error (unsupported s!"the annotation key {text} is reserved, and this endpoint does \
        not implement it")
  | .ulong n =>
    if policy.understands key then .ok ()
    else
      .error (unsupported s!"the annotation key {n.toNat} is reserved, and this endpoint \
        does not implement it")
  | _ => checkAnnotationKey key

/-- An application-properties value: a simple type, which the artifact spells as excluding
map, list and array. -/
def checkSimpleValue (value : Value) : Except Refusal Unit :=
  match value with
  | .map _ => .error (malformed "an application-properties value is a map, and the section \
      restricts its values to simple types")
  | .list _ => .error (malformed "an application-properties value is a list, and the section \
      restricts its values to simple types")
  | .array _ _ => .error (malformed "an application-properties value is an array, and the \
      section restricts its values to simple types")
  | .described _ _ => .error (malformed "an application-properties value is a described \
      type, and the section restricts its values to simple types")
  | _ => .ok ()

/-- One application property: a string key and a simple value. -/
def checkApplicationProperty (pair : Value × Value) : Except Refusal Unit :=
  match pair.1 with
  | .string _ => checkSimpleValue pair.2
  | .null =>
    .error (malformed "an application-properties key is a string, which excludes a null key")
  | key =>
    .error (malformed s!"an application-properties key is a string, and this one is a \
      {typeName key}")

/-- The pairs of a map-sourced section, under the value rule its declared type inherits. A
section whose declared type reaches neither of the two is one this layer has no rule for, and
is refused rather than read as if its keys and values were unconstrained. -/
def checkPairs (decl : TypeDecl) (pairs : List (Value × Value)) : Except Refusal Unit := do
  let chain := chainOf decl.name
  if chain.contains annotationsType then
    let _ ← pairs.mapM checkAnnotationPair
    pure ()
  else if chain.contains applicationPropertiesType then
    let _ ← pairs.mapM checkApplicationProperty
    pure ()
  else
    .error (unsupported s!"{decl.name} is a map whose declared type inherits neither the \
      annotations key rule nor the application-properties value rule")

/-- The endpoint's comprehension of every annotation key in a map-sourced section, which the
annotations clause makes the reader's rule. -/
def checkPairPolicy (policy : Policy) (decl : TypeDecl) (pairs : List (Value × Value)) :
    Except Refusal Unit := do
  if (chainOf decl.name).contains annotationsType then
    let _ ← pairs.mapM (fun pair => checkAnnotationPolicy policy pair.1)
    pure ()
  else pure ()

/-! ## A section -/

/-- A section's body: the one shape its declared type's source fixes. -/
inductive SectionBody where
  /-- A composite's fields, in declared order, present ones only. -/
  | fields (values : List Value)
  /-- A map's pairs, in wire order. -/
  | pairs (entries : List (Value × Value))
  /-- A binary-sourced section's octets. -/
  | payload (octets : List UInt8)
  /-- A list-sourced section's items. -/
  | items (values : List Value)
  /-- The wildcard, which a section may carry as one value of any type. -/
  | carried (value : Value)
deriving Repr, BEq

/-- One section: which of the nine types it is, and the body that type fixes. -/
structure Section where
  kind : SectionKind
  body : SectionBody
deriving Repr, BEq

/-- The value an amqp-value section carries, `none` for the other eight kinds: they carry
fields, pairs, a payload or items instead. This is the section-level projection a
payload-carried performative arrives through. -/
def valueCarried (sec : Section) : Option Value :=
  match sec.kind, sec.body with
  | .amqpValue, .carried value => some value
  | _, _ => none

/-- The writer's counterpart: the amqp-value section that carries a value. A constructor
rather than an unwrap, because the writer of a payload-carried performative needs to build
the section the reader takes apart. -/
def amqpValue (value : Value) : Section := ⟨.amqpValue, .carried value⟩

/-- The shape a section's body has, read off its declared type: a composite is its field
list, a binary-sourced type is octets, a list-sourced one is items, a map-sourced one is
pairs, and the wildcard is one value of any type. -/
inductive BodyForm where
  | fields
  | entries
  | octets
  | items
  | carried
deriving Repr, BEq, DecidableEq

/-- The form of a declared section type. -/
def formOf (decl : TypeDecl) : Option BodyForm :=
  match shapeOf decl.name with
  | some (.composite _) => some .fields
  | some (.primitive "binary") => some .octets
  | some (.primitive "list") => some .items
  | some (.primitive "map") => some .entries
  | some .wildcard => some .carried
  | _ => none

/-- The section a described value is: its descriptor must name a declared type carrying
the `section` role, and its body must have the shape that type fixes. -/
def sectionOfValue (policy : Policy) (value : Value) : Except Refusal Section :=
  match value with
  | .described descriptor body =>
    match typeOfDescriptor descriptor with
    | none =>
      .error (malformed "a section's descriptor names no type the declared surface carries")
    | some decl =>
      if !decl.provides.contains "section" then
        .error (malformed s!"the descriptor names {decl.name}, whose declared roles are \
          {decl.provides}, which does not include the section role")
      else
        match SectionKind.ofName decl.name with
        | none =>
          .error (malformed s!"{decl.name} carries the section role and is not one of the \
            nine kinds of message format 0")
        | some kind =>
          match formOf decl with
          | none =>
            .error (unsupported s!"{decl.name} is a section whose declared type is neither \
              a field list, a map, a binary, a list nor the wildcard")
          | some .fields =>
            match body with
            | .list values =>
              match checkFields (fieldsOf decl.path) values with
              | .error refusal => .error refusal
              | .ok () => .ok ⟨kind, .fields values⟩
            | _ =>
              .error (malformed s!"{decl.name} is a composite and its body is a \
                {typeName body} rather than a field list")
          | some .entries =>
            match body with
            | .map pairs =>
              match checkPairPolicy policy decl pairs with
              | .error refusal => .error refusal
              | .ok () =>
                match checkPairs decl pairs with
                | .error refusal => .error refusal
                | .ok () => .ok ⟨kind, .pairs pairs⟩
            | _ =>
              .error (malformed s!"{decl.name} restricts a map and its body is a \
                {typeName body} rather than a map")
          | some .octets =>
            match body with
            | .binary octets => .ok ⟨kind, .payload octets⟩
            | _ =>
              .error (malformed s!"{decl.name} restricts binary and its body is a \
                {typeName body}")
          | some .items =>
            match body with
            | .list items => .ok ⟨kind, .items items⟩
            | _ =>
              .error (malformed s!"{decl.name} restricts a list and its body is a \
                {typeName body}")
          | some .carried => .ok ⟨kind, .carried body⟩
  | _ =>
    .error (malformed s!"a section is a described type, and these octets are a \
      {typeName value}")

/-! ## Reading a section and a message -/

/-- One section from the front of a buffer, and the octets it consumed. -/
def decodeSection (policy : Policy) (bytes : Octets) : Except Refusal (Section × Nat) :=
  match decode bytes with
  | .error error => .error (ofDecodeError error)
  | .ok (value, consumed) =>
    match sectionOfValue policy value with
    | .error refusal => .error refusal
    | .ok sec => .ok (sec, consumed)

/-- A section at an offset, with the octets it consumed: the reader is handed the rest of
the buffer, so a section is read to the end of its own value and the counts add up. -/
def decodeSectionAt (policy : Policy) (bytes : Octets) (pos : Nat) :
    Except Refusal (Section × Nat) :=
  decodeSection policy (bytes.extract pos bytes.size)

/-- The sections of a payload, in the order they appear. Each step consumes at least the
descriptor's own octet, so the recursion is bounded by the octets that remain. -/
def readSections (policy : Policy) (bytes : Octets) (pos : Nat) (acc : List Section) :
    Except Refusal (List Section) :=
  if bytes.size ≤ pos then
    .ok acc.reverse
  else
    match decodeSectionAt policy bytes pos with
    | .error refusal => .error refusal
    | .ok (sec, consumed) =>
      if consumed = 0 ∨ bytes.size < pos + consumed then
        .error (malformed s!"a section at octet {pos} reports {consumed} octet(s) consumed, \
          which does not advance through the remaining {bytes.size - pos}")
      else
        readSections policy bytes (pos + consumed) (sec :: acc)
termination_by bytes.size - pos
decreasing_by
  simp_wf
  omega

/-- The state of the message structure: which head sections have been seen, as the position
the artifact's list gives each; whether the body has begun and which of the three choices it
took; and whether the footer has closed the annotated message. -/
structure Structure where
  headIndex : Option Nat
  bodySeen : Bool
  bodyKind : Option SectionKind
  closed : Bool
deriving Repr, BEq

/-- One more section in the structure: the head sections come first, at most once each and
in the order the artifact lists them; then one body of a single choice; then at most one
footer, last. -/
def stepStructure (state : Structure) (kind : SectionKind) : Except Refusal Structure :=
  if state.closed then
    .error (malformed s!"the section {kind.name} follows the footer, and the footer is the \
      tail of the annotated message")
  else
    match SectionKind.headOrder kind with
    | some index =>
      if state.bodySeen then
        .error (malformed s!"the head section {kind.name} follows the body, and the head \
          sections precede it")
      else
        match state.headIndex with
        | some seen =>
          if index ≤ seen then
            .error (malformed s!"the head section {kind.name} is a second one or comes after \
              a section the artifact's list puts later")
          else .ok { state with headIndex := some index }
        | none => .ok { state with headIndex := some index }
    | none =>
      if kind == .footer then .ok { state with closed := true }
      else
        match state.bodyKind with
        | none => .ok { state with bodySeen := true, bodyKind := some kind }
        | some seen =>
          if seen == kind && seen != .amqpValue then .ok state
          else
            .error (malformed s!"the message's body is one of three choices, and a \
              {kind.name} section does not continue a body of {seen.name} sections")

/-- The values a message's properties section carries, where the message carries one. -/
def propertiesFields? (sections : List Section) : Option (List Value) :=
  match sections.find? (fun sec => sec.kind == .properties) with
  | some sec => match sec.body with
    | .fields values => some values
    | _ => none
  | none => none

/-- The value a message's properties section gives a field: none where the message carries no
properties section, where its list stops before the field, or where it carries a null for it —
a null and an omitted trailing field both saying the field is not set. -/
def propertiesValue? (sections : List Section) (fieldName : String) : Option Value :=
  match propertiesFields? sections, declaredType? "properties" with
  | some values, some decl =>
    match (fieldsOf decl.path).find? (fun field => field.name == fieldName) with
    | some field =>
      match values[field.index - 1]? with
      | some .null => none
      | other => other
    | none => none
  | _, _ => none

/-- The section kinds a message's body carries: the artifact's occurrence list puts the three
body choices after the head sections and before the footer, so a body kind is one that is neither
a head nor the footer. -/
def bodyKinds (sections : List Section) : List SectionKind :=
  (sections.filter (fun sec => sec.kind.headOrder.isNone && sec.kind != .footer)).map (·.kind)

/-- The encoding the `content-encoding` documentation names as one implementations must not use.
The artifact declares no encoding vocabulary, so the name is prose in the field's documentation
rather than a choice this layer could look up. -/
def identityEncoding : String := "identity"

/-- The two rules the `content-encoding` field's documentation states, applied where the field
and the body are both in hand: the field may be set only when the application-data section is
`data`, and the `identity` encoding is not to be used. Part 3 states these rules and names no
condition for breaking them, so the refusal is the shared decode error, which is what this layer
carries for a rule of structure or declared field type. -/
def checkContentEncoding (sections : List Section) : Except Refusal Unit :=
  match propertiesValue? sections "content-encoding" with
  | none => .ok ()
  | some value =>
    let body := bodyKinds sections
    if !body.all (fun kind => kind == .data) then
      .error (malformed s!"the properties section sets content-encoding and the message's body \
        is {body.length} section(s) that are not data sections, and the field may be set only \
        when the application-data section is data")
    else
      match value with
      | .symbol text =>
        if text == identityEncoding then
          .error (malformed s!"the content-encoding is {identityEncoding}, and implementations \
            must not use the identity encoding")
        else .ok ()
      | other =>
        .error (malformed s!"a content-encoding is a symbol and the section carries a \
          {typeName other}")

/-- The message structure the artifact's occurrence list gives. A message that carries any
section carries a body, because the list gives the body as one of three choices rather than
as an optional section; the empty payload is the one message with no sections. -/
def checkStructure (sections : List Section) : Except Refusal Unit :=
  match sections.foldlM (fun state sec => stepStructure state sec.kind)
      ⟨none, false, none, false⟩ with
  | .error refusal => .error refusal
  | .ok final =>
    if !final.bodySeen && !sections.isEmpty then
      .error (malformed "the message carries no body, and the artifact's list gives the body \
        as one of three choices")
    else checkContentEncoding sections

/-- A payload's sections, in the order they appear, with the message structure checked over
them. The empty payload is the empty section list. -/
def decodeMessage (policy : Policy) (bytes : Octets) : Except Refusal (List Section) :=
  match readSections policy bytes 0 [] with
  | .error refusal => .error refusal
  | .ok sections =>
    match checkStructure sections with
    | .error refusal => .error refusal
    | .ok () => .ok sections

/-- The value a payload's body carries, where the body is exactly one amqp-value section:
the shape a payload-carried performative arrives in. Anything else — a payload that carries
another section, more than one, or no section at all — is refused rather than read as a
value, because the caller is asking what the body is and there is a definite answer. -/
def bodyValue (policy : Policy) (bytes : Octets) : Except Refusal Value :=
  match decodeMessage policy bytes with
  | .error refusal => .error refusal
  | .ok sections =>
    match sections with
    | [sec] =>
      match valueCarried sec with
      | some value => .ok value
      | none =>
        .error (malformed s!"the payload's body is a single {sec.kind.name} section, and \
          a body value is what a single amqp-value section carries")
    | _ =>
      .error (malformed s!"a payload carries {sections.length} section(s), and a body value \
        is what a payload of exactly one amqp-value section carries")

/-- A section's body as the value it is on the wire: a composite's is its field list, a
list-sourced type's is a list, an annotations map's is a map, a binary's is binary, and the
wildcard's is itself. -/
def SectionBody.bodyAsValue : SectionBody → Value
  | .fields values => .list values
  | .items values => .list values
  | .pairs entries => .map entries
  | .payload octets => .binary octets
  | .carried value => value

namespace Section

/-- The section in the corpus's vocabulary. Which key carries the body is the shape the
section's declared source fixes, so a reader of the vocabulary is not guessing which of the
five the octets mean. -/
def toJson (sec : Section) : Json :=
  match sec.body with
  | .fields values =>
    Json.mkObj [("kind", sec.kind.name),
                ("fields", Json.arr (values.map jsonOfValue).toArray)]
  | .pairs pairs =>
    Json.mkObj [("kind", sec.kind.name),
                ("pairs", Json.arr (pairs.map (fun pair =>
                  Json.arr #[jsonOfValue pair.1, jsonOfValue pair.2])).toArray)]
  | .payload octets =>
    Json.mkObj [("kind", sec.kind.name), ("payload", toHex octets.toArray)]
  | .items values =>
    Json.mkObj [("kind", sec.kind.name),
                ("items", Json.arr (values.map jsonOfValue).toArray)]
  | .carried value =>
    Json.mkObj [("kind", sec.kind.name), ("value", jsonOfValue value)]

end Section

/-- The depth a corpus value is read at. The corpus vocabulary nests, so reading it needs a
bound; a value nested past it is refused rather than read partially. -/
def corpusDepth : Nat := 64

/-- A corpus-vocabulary read failure, as the reader reports it: the value the corpus handed
this layer is not one it reads. -/
def read {α : Type} (result : Except String α) : Except Refusal α :=
  match result with
  | .ok value => .ok value
  | .error message => .error (malformed s!"the corpus value is not one this layer reads: {message}")

/-- A refusal as the writer's side reports it. The reader's refusals carry a condition
because the corpus compares it; the writer has no condition to compare, so its message
carries both parts. -/
def refusalMessage (refusal : Refusal) : String := s!"{refusal.condition}: {refusal.detail}"

/-- A reader-side step inside the writer: the writer's domain has to sit inside the reader's,
so a value the reader refuses is one the writer does not write. -/
def written {α : Type} (result : Except Refusal α) : Except String α :=
  match result with
  | .ok value => .ok value
  | .error refusal => .error (refusalMessage refusal)

/-- A section's pairs in the corpus vocabulary: two values per pair, in wire order. -/
def pairsOfJson (json : Json) : Except String (List (Value × Value)) := do
  let raw ← json.getObjValAs? (Array Json) "pairs"
  raw.toList.mapM (fun pair => do
    let items ← pair.getArr?
    match items.toList with
    | [key, value] => return (← valueOfJson corpusDepth key, ← valueOfJson corpusDepth value)
    | _ => .error "a pair is exactly two values")

/-- The section a corpus value is. The body's key is the one the declared type's shape fixes,
and the body is checked against the type exactly as the octets are, so the two directions
accept the same sections. The endpoint's comprehension of an annotation key is not checked
here: the policy is an input to *reading octets*, and a writer handed a section writes it. -/
def sectionOfJson (json : Json) : Except Refusal Section := do
  let kindText ← read (json.getObjValAs? String "kind")
  let kind ← match SectionKind.ofName kindText with
    | some kind => .ok kind
    | none =>
      .error (malformed s!"{kindText} is not one of the nine section types of message format 0")
  let decl ← match kind.decl? with
    | some decl => .ok decl
    | none =>
      .error (malformed s!"{kind.name} is not a section type the declared surface carries")
  match formOf decl with
  | none =>
    .error (unsupported s!"{decl.name} is a section whose declared type is neither a field \
      list, a map, a binary, a list nor the wildcard")
  | some .fields => do
    let raw ← read (json.getObjValAs? (Array Json) "fields")
    let values ← read (raw.toList.mapM (valueOfJson corpusDepth))
    let _ ← checkFields (fieldsOf decl.path) values
    return ⟨kind, .fields values⟩
  | some .entries => do
    let pairs ← read (pairsOfJson json)
    let _ ← checkPairs decl pairs
    return ⟨kind, .pairs pairs⟩
  | some .octets => do
    let octets ← read (ofHex (← read (json.getObjValAs? String "payload")))
    return ⟨kind, .payload octets.toList⟩
  | some .items => do
    let raw ← read (json.getObjValAs? (Array Json) "items")
    let values ← read (raw.toList.mapM (valueOfJson corpusDepth))
    return ⟨kind, .items values⟩
  | some .carried => do
    let value ← read (valueOfJson corpusDepth (← read (json.getObjVal? "value")))
    return ⟨kind, .carried value⟩

/-- A section written as its descriptor and the value its body is. -/
def encodeSectionValue (sec : Section) : Except String Octets :=
  match sec.kind.decl? with
  | none => .error s!"{sec.kind.name} is not a section type the declared surface carries"
  | some decl =>
    match decl.descriptor with
    | none => .error s!"{decl.name} carries no descriptor, so it is not a section of a message"
    | some descriptor =>
      let code := descriptor.domain * 2 ^ 32 + descriptor.code
      (encode (.described (.ulong (UInt64.ofNat code)) sec.body.bodyAsValue)).mapError
        SpecAMQP.Ref.EncodeRefusal.message

/-- Sections written one after the other, which is what a payload is. -/
def encodeSections : List Section → Except String Octets
  | [] => .ok #[]
  | sec :: rest => do
    let head ← encodeSectionValue sec
    let tail ← encodeSections rest
    return head ++ tail

/-! ## Delivery states

The delivery-state section defines a concrete set of states, and the machine here is that
set: `received` is the non-terminal one, carrying the resume point; the outcomes are
terminal, and the artifact says which of them move the delivery-count and which forbid
redelivery. The two states the transaction layer declares fill the same role, so they are
recorded and move no quantity.

Two things this layer does not do: it does not decide which deliveries may be settled, and
it does not keep a history of the states applied. The corpus compares the state, the count,
the resume point, the settlement and whether redelivery is allowed, and those are the
observables each rule moves.
-/

/-- The layer prefix the corpus gives a delivery state's name, which is what keeps a name
from colliding with a session's or a connection's. -/
def deliveryLayerName : String := "delivery"

/-- The name of the state a delivery is in before any delivery state has been applied. -/
def unsettledStateName : String := s!"{deliveryLayerName}:UNSETTLED"

/-- The state a delivery has applied, and every quantity the delivery states move. -/
structure Delivery where
  /-- The recorded state's type name, absent before any state has been applied. -/
  state? : Option String
  /-- The delivery-count the outcomes move, which starts at zero: the header's declared
  default, applied to a message whose header said nothing. -/
  deliveryCount : Nat
  /-- Whether the delivery is settled. -/
  settled : Bool
  /-- The resume point a `received` state carries: the section and the offset within it. -/
  resume? : Option (Nat × Nat)
  /-- Whether the delivery's message may be delivered to this link again. -/
  redeliveryAllowed : Bool
  /-- Whether the recorded state is terminal, which is the artifact's own distinction: an
  outcome provides the role both the delivery-state section and the `outcome` role name. -/
  terminal : Bool
  /-- The message-annotations the delivery's message carries: the ones it arrived with, with a
  `modified` outcome's `message-annotations` field merged in when one is applied. It is the one
  quantity a delivery state rewrites rather than reports. -/
  annotations : List (Value × Value)
deriving Repr, BEq

namespace Delivery

/-- A delivery with no state applied: unsettled, its count at zero, no resume point, no
annotations beyond the ones the message arrived with, and its message available for delivery
again. -/
def initial : Delivery :=
  ⟨none, 0, false, none, true, false, []⟩

/-- The state's name as the corpus gives it. -/
def stateName (delivery : Delivery) : String :=
  match delivery.state? with
  | some name => s!"{deliveryLayerName}:{name.toUpper}"
  | none => unsettledStateName

end Delivery

/-- A field's value in a composite body, by the name the artifact declares for it: absent
when the body stops before the field or carries a null where it would be. -/
def fieldValue? (decl : TypeDecl) (body : Value) (fieldName : String) : Option Value :=
  match body with
  | .list values =>
    match (fieldsOf decl.path).find? (fun field => field.name == fieldName) with
    | some field =>
      match values[field.index - 1]? with
      | some .null => none
      | other => other
    | none => none
  | _ => none

/-- A boolean field of a state's body. The artifact makes both of the flags of `modified`
optional and conditions its rules on the flag being set, so a field that is absent — or
carried as a null — is not set, and the rule it guards does not apply. -/
def boolField (decl : TypeDecl) (body : Value) (fieldName : String) : Bool :=
  match fieldValue? decl body fieldName with
  | some (.boolean b) => b
  | _ => false

/-- A numeric field of a state's body, in either of the widths the declared type has. -/
def natField? (decl : TypeDecl) (body : Value) (fieldName : String) : Option Nat :=
  match fieldValue? decl body fieldName with
  | some (.uint n) => some n.toNat
  | some (.ulong n) => some n.toNat
  | _ => none

/-- The delivery state a value is: a described value whose descriptor names a declared type
carrying the delivery-state role, with a body that satisfies the fields that type declares.
The states the transaction layer declares pass this too, which is what makes them states
this machine records rather than states it refuses. -/
def deliveryStateOfValue (value : Value) : Except Refusal (TypeDecl × Value) :=
  match value with
  | .described descriptor body =>
    match typeOfDescriptor descriptor with
    | none =>
      .error (malformed "a delivery state's descriptor names no type the declared surface \
        carries")
    | some decl =>
      if !decl.provides.contains "delivery-state" then
        .error (malformed s!"the descriptor names {decl.name}, whose declared roles are \
          {decl.provides}, which does not include the delivery-state role")
      else
        match checkBody decl body with
        | .error refusal => .error refusal
        | .ok () => .ok (decl, body)
  | _ =>
    .error (malformed s!"a delivery state is a described type, and this value is a \
      {typeName value}")

/-- The type names whose outcomes the artifact's own text gives a rule for. The rules
themselves are below; the names are the artifact's. -/
def receivedName : String := "received"
def acceptedName : String := "accepted"
def rejectedName : String := "rejected"
def releasedName : String := "released"
def modifiedName : String := "modified"

/-- Whether two annotation keys are the same key: the annotation rules admit symbols and ulongs,
and the comparison is on the keys rather than on whole pairs because that is what the merge
decides — two entries for one key differ in the value, and which survives is the rule. -/
def sameKey (left right : Value) : Bool :=
  match left, right with
  | .symbol a, .symbol b => a == b
  | .ulong a, .ulong b => a == b
  | _, _ => false

/-- The prefix that puts a symbolic annotation key outside the reserved space: the annotations type
reserves every ulong key and every symbolic key except those beginning with `x-`. It is not the
`x-opt` prefix the mandated detach is conditioned on, which is why both are named. -/
def unreservedPrefix : String := "x-"

/-- Whether an annotation key is reserved, and `none` for a value that is not a key at all. -/
def reservedKey? : Value → Option Bool
  | .symbol text => some (!text.startsWith unreservedPrefix)
  | .ulong _ => some true
  | _ => none

/-- The message-annotations a message carries after a `modified` outcome's `message-annotations`
field is applied to them: an entry whose key the message already carries replaces the message's
entry for that key, and an entry whose key it does not carry is added. Everything the message
carried under a key the field does not name survives untouched, which is the propagation half of
the annotations rule with the augmentation the sentence names as its exception. -/
def mergeAnnotations (existing augment : List (Value × Value)) : List (Value × Value) :=
  augment ++ existing.filter (fun pair => !(augment.any (fun entry => sameKey entry.1 pair.1)))

/-- The delivery a state leaves behind. The resume point is a property of the `received`
state, so it is carried while that state is recorded and dropped when another replaces it;
the count moves on `rejected` and on `modified` with `delivery-failed`; redelivery is
forbidden by `accepted`, by `rejected`, and by `modified` with `undeliverable-here`, and
allowed by `released`; the settlement the step states is recorded as the delivery's
settlement; and a `modified` outcome whose `message-annotations` field is set merges it into
the annotations the message already carried. A state the table declares that none of those
rules names — the transaction layer's — is recorded and moves nothing. -/
def moveDelivery (delivery : Delivery) (decl : TypeDecl) (body : Value) (settled : Bool) :
    Delivery :=
  let name := decl.name
  let resumed : Option (Nat × Nat) :=
    match natField? decl body "section-number", natField? decl body "section-offset" with
    | some sectionNumber, some sectionOffset => some (sectionNumber, sectionOffset)
    | _, _ => none
  { state? := some name
    deliveryCount :=
      if name == rejectedName then delivery.deliveryCount + 1
      else if name == modifiedName && boolField decl body "delivery-failed" then
        delivery.deliveryCount + 1
      else delivery.deliveryCount
    settled := delivery.settled || settled
    resume? := if name == receivedName then resumed else none
    redeliveryAllowed :=
      if name == acceptedName then false
      else if name == rejectedName then false
      else if name == releasedName then true
      else if name == modifiedName then !(boolField decl body "undeliverable-here")
      else if name == receivedName then true
      else delivery.redeliveryAllowed
    terminal := decl.provides.contains "outcome"
    annotations :=
      match name, fieldValue? decl body "message-annotations" with
      | "modified", some (.map pairs) => mergeAnnotations delivery.annotations pairs
      | _, _ => delivery.annotations }

/-- The machine a state name from the corpus denotes. The unsettled name is the delivery
before any state has been applied; any other delivery state denotes a delivery that has
applied it, so the quantities come out of the same rules the steps use, with the flags the
state makes optional unset — there is no disposition for a start state to read them from. A
name outside both is refused rather than read as some default. -/
def startDelivery (name : String) : Except String Delivery :=
  if name == unsettledStateName then .ok Delivery.initial
  else
    .error s!"{name} is not a start state this machine has: a delivery vector starts from the \
      delivery with no state, and the artifact describes no delivery machine entered from an \
      arbitrary state name, so a name outside that one is refused rather than read as some \
      default"

/-- The delivery in the corpus vocabulary: the state's name, the count, the settlement, the
resume point, whether redelivery is allowed, and — on a refusal — the condition and the
class-led detail. -/
def outcomeOf (delivery : Delivery) (admitted : Bool) (condition : Option String)
    (detail : String) : DeliveryOutcome :=
  { admitted := admitted
    state := delivery.stateName
    deliveryCount := delivery.deliveryCount
    settled := delivery.settled
    sectionNumber := delivery.resume?.map (fun point => point.1)
    sectionOffset := delivery.resume?.map (fun point => point.2)
    redeliveryAllowed := delivery.redeliveryAllowed
    condition := condition
    detail := detail }

/-- One delivery step applied to the machine: the state the corpus writes, and whether it is
settled. A refusal moves nothing, which is the law the harness holds a refusal to: the
outcome reports the delivery as it was, and the machine is returned unchanged. -/
def applyDelivery (delivery : Delivery) (step : Json) : Except String (DeliveryOutcome × Delivery) := do
  let value ← valueOfJson corpusDepth (← step.getObjVal? "apply")
  let settled := (step.getObjValAs? Bool "settled").toOption.getD false
  match deliveryStateOfValue value with
  | .error refusal => return (outcomeOf delivery false (some refusal.condition) refusal.detail, delivery)
  | .ok (decl, body) =>
    if delivery.terminal then
      let detail := illegalState s!"the delivery is in {delivery.stateName}, and the artifact \
        says a terminal delivery state no longer changes"
      return (outcomeOf delivery false (some detail.condition) detail.detail, delivery)
    else
      let moved := moveDelivery delivery decl body settled
      return (outcomeOf moved true none s!"applied {decl.name}", moved)

/-! ## The terminus field sets (Part 3, addressing)

The two composites an `attach` carries, whose fields the artifact's documentation constrains
beyond their declared types: the address/dynamic pair, node properties that may be sent only with
the dynamic flag, the roles `default-outcome` and `distribution-mode` must fill, the `durable`
choices, and the `outcomes` descriptors. Which endpoint sent the frame is an input, because the
address rules are conditioned on it and nothing in the record carries it. What a node then does
with the node a terminus names is the standard's own boundary and is not modelled.
-/

/-- Which link endpoint sent a frame. The names are the `role` type's declared choices. -/
inductive SentBy where
  | sender
  | receiver
deriving Repr, BEq, DecidableEq

/-- An endpoint's name, which is a declared `role` choice's name. -/
def SentBy.label : SentBy → String
  | .sender => "sender"
  | .receiver => "receiver"

/-- The two composites the artifact declares as termini. -/
def sourceName : String := "source"

def targetName : String := "target"

/-- A terminus record: the declared type and the body it carries. -/
structure Terminus where
  decl : TypeDecl
  body : Value
deriving Repr

/-- The declared durabilities, read from the type that declares them. -/
def durabilityChoices : List ChoiceDecl :=
  match declaredType? "terminus-durability" with
  | some decl => choices.filter (fun choice => choice.ownerPath == decl.path)
  | none => []

/-- The durability a value names, where it names one of the declared choices. -/
def durabilityOf? (value : Value) : Option String :=
  match value with
  | .uint n =>
    (durabilityChoices.find? (fun choice => choice.value == toString n.toNat)).map (·.name)
  | _ => none

/-- The declared type a symbolic outcome descriptor names, where that type provides the outcome
role. -/
def outcomeDescriptor? (text : String) : Option String :=
  match types.find? (fun decl => decl.descriptor.map (·.name) == some text) with
  | some decl => if decl.provides.contains "outcome" then some decl.name else none
  | none => none

/-- The descriptor value of a declared outcome, by name: this is how the fallback below reaches
the accepted outcome without writing its descriptor down. -/
def outcomeDescriptorValue? (typeName : String) : Option Value :=
  (declaredType? typeName).bind (fun decl =>
    decl.descriptor.map (fun descriptor => .symbol descriptor.name))

namespace Terminus

/-- A terminus field's value, by the declared index: a body that stops before the field and a
null where the field would be both say the field is not set. -/
def value? (terminus : Terminus) (fieldName : String) : Option Value :=
  match (fieldsOf terminus.decl.path).find? (fun field => field.name == fieldName),
      terminus.body with
  | some field, .list values =>
    match values[field.index - 1]? with
    | some .null => none
    | other => other
  | _, _ => none

/-- Whether a field is set: present and not null, and — for a `multiple` field — not an empty
array, which the types section says describes the same absence a null does. -/
def isSet (terminus : Terminus) (fieldName : String) : Bool :=
  match terminus.value? fieldName with
  | some (.array _ []) => false
  | some _ => true
  | none => false

/-- The entries a field carries: a `multiple` field's array entries or its single value, and
nothing at all for a field that is not set. -/
def entries (terminus : Terminus) (fieldName : String) : List Value :=
  match terminus.value? fieldName with
  | some (.array _ items) => items
  | some single => [single]
  | none => []

/-- A boolean field, false when the field is absent or null, which is `dynamic`'s declared
default. -/
def flag (terminus : Terminus) (fieldName : String) : Bool :=
  match terminus.value? fieldName with
  | some (.boolean b) => b
  | _ => false

/-- A field that must fill a role: `default-outcome` a valid outcome, `distribution-mode` a
distribution mode. -/
def checkRole (terminus : Terminus) (fieldName role : String) : Except Refusal Unit :=
  match terminus.value? fieldName with
  | none => .ok ()
  | some value =>
    if providesRole value role then .ok ()
    else
      .error (malformed s!"{terminus.decl.name}.{fieldName} carries a {typeName value}, and the \
        field's value must be a valid {role}")

/-- The rules the `source` and `target` field documentation states. The address rule is one rule
written twice in the artifact: the endpoint that *creates* a dynamic node communicates its
address and the endpoint that *requests* creation leaves the field unset, and which endpoint that
is mirrors between the two types. -/
def check (sentBy : SentBy) (terminus : Terminus) : Except Refusal Unit := do
  let name := terminus.decl.name
  let dynamic := terminus.flag "dynamic"
  let creator := (name == sourceName && sentBy == .sender)
    || (name == targetName && sentBy == .receiver)
  if dynamic && creator && !terminus.isSet "address" then
    .error (malformed s!"a dynamic {name} sent by the {sentBy.label} endpoint carries no address, \
      and the endpoint that created the node is the one communicating it")
  else if dynamic && !creator && terminus.isSet "address" then
    .error (malformed s!"a dynamic {name} sent by the {sentBy.label} endpoint sets the address, \
      and the endpoint that requested creation must not set it")
  else if !dynamic && terminus.isSet "dynamic-node-properties" then
    .error (malformed s!"{name}.dynamic-node-properties is set while the dynamic field is not, \
      and the field must be left unset unless the dynamic field is set to true")
  else do
    checkRole terminus "default-outcome" "outcome"
    checkRole terminus "distribution-mode" "distribution-mode"
    match terminus.value? "durable" with
    | some value =>
      if (durabilityOf? value).isNone then
        .error (malformed s!"{name}.durable carries a {typeName value}, and the value must name \
          one of the declared terminus-durability choices")
      else pure ()
    | none => pure ()
    match (terminus.entries "outcomes").find? (fun entry =>
        match entry with
        | .symbol text => (outcomeDescriptor? text).isNone
        | _ => true) with
    | some (.symbol text) =>
      .error (malformed s!"{name}.outcomes names {text}, which is not the symbolic descriptor of \
        a declared outcome")
    | some other =>
      .error (malformed s!"{name}.outcomes carries a {typeName other}, and the field's values \
        must be symbolic descriptors")
    | none => pure ()

/-- The outcomes a source's record leaves choosable: the announced ones, or the default-outcome
where that field is set and the list is empty, or the accepted outcome where neither is set —
which the field's documentation says such a source must support. -/
def assumedOutcomes (terminus : Terminus) : Except Refusal (List Value) :=
  match terminus.entries "outcomes" with
  | [] =>
    match terminus.value? "default-outcome" with
    | some value => .ok [value]
    | none =>
      match outcomeDescriptorValue? acceptedName with
      | some value => .ok [value]
      | none =>
        .error (malformed s!"the declared surface carries no {acceptedName} outcome descriptor \
          for a source that announces no outcomes to fall back on")
  | announced => .ok announced

end Terminus

/-- A described value read as a terminus: the body checked against the declared fields, the type's
role confirmed to be one of the two terminus roles the artifact declares, and the field
documentation's rules applied. -/
def terminusOfValue (sentBy : SentBy) (value : Value) : Except Refusal Terminus :=
  match value with
  | .described descriptor body =>
    match typeOfDescriptor descriptor with
    | none =>
      .error (malformed "a terminus's descriptor names no type the declared surface carries")
    | some decl =>
      if !(decl.provides.contains sourceName || decl.provides.contains targetName) then
        .error (malformed s!"{decl.name} provides neither the source nor the target role, so a \
          described value of it is not a terminus")
      else
        match checkBody decl body with
        | .error refusal => .error refusal
        | .ok () => do
          Terminus.check sentBy ⟨decl, body⟩
          return ⟨decl, body⟩
  | _ =>
    .error (malformed s!"a terminus is a described type, and this value is a {typeName value}")

/-! ## The corpus interface -/

/-- The reference implementation's message layer behind the corpus interface. Both
directions go through the same structure and field rules, so the writer's domain sits inside
what the reader accepts. The writer has no policy input and so applies no key policy: which
keys an endpoint implements is the reader's knowledge, and a canonical re-encoding is written
from what the reader admitted. -/
def refMessageCodec : MessageCodec where
  name := "reference"
  decodeSection := fun policy bytes => do
    let (sec, consumed) ← decodeSection (Policy.ofJson policy) bytes
    return (sec.toJson, consumed)
  encodeSection := fun json => do
    let sec ← written (sectionOfJson json)
    encodeSectionValue sec
  decodeMessage := fun policy bytes => do
    let sections ← decodeMessage (Policy.ofJson policy) bytes
    return sections.map Section.toJson
  encodeMessage := fun json => do
    let raw ← json.getArr?
    let sections ← raw.toList.mapM (fun item => written (sectionOfJson item))
    written (checkStructure sections)
    encodeSections sections

/-- The reference implementation's delivery-state machine behind the corpus interface. -/
def refDeliveryCodec : DeliveryCodec where
  name := "reference"
  St := Delivery
  start := startDelivery
  apply := applyDelivery

end SpecAMQP.Ref.Message
