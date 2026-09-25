/-
# The unsettled-index and disposition-coverage instrument

A **preserved instrument**, not a gate and not part of acceptance. It replays a corpus through
**both** readings' own codecs — the same replay convention the drivers use, `ExchangeCodec` plus
`Harness.exchangeStepOf` — and after every step of every vector checks three clauses:

1. **Index completeness.** For every registered link in the post-step session: `unsettledKeys` is
   duplicate-free; every tag it names has a `some` entry in the table; and every tag a *wire-derived*
   monitor believes the link holds an entry for is in the index. The monitor reads only the transfer
   frames (`handle` resolved through the pre-step handle maps, `delivery-id`, `delivery-tag`,
   `settled`, `aborted`), so the last conjunct is independent of the index itself.
2. **Disposition coverage** — the property `disposition.4` states and the corpus cannot see. For
   every settled disposition step, for every link whose local role the frame's `role` names, every
   live unsettled entry whose `deliveryId` lies in `first..last` **before** the step must be absent
   **after** it. The covered set is enumerated twice, from the link's index and from the monitor's
   candidate tags.
3. **The pre-fix guard** (informational, never a failure): what the pre-fix `applyDisposition` body —
   which released only the link's in-progress delivery and cleared only its tag — would have left
   behind on the same trace, computed by running that body's rule over the pre-step link. This is
   **not** failure-first evidence; it is a different-future guard, so that a weakened traversal
   reports itself.

It is kept in the repository so that the claim it witnesses is **reproducible** by anyone with this
checkout: the run it was written for happened once, from a file in `/tmp`, and a reboot would have
erased it. It is not a gate, nothing runs it as one, and it does **not** replace the corpus scenario
as the permanent carrier for `disposition.4` — the planner's ruling that a second permanent replay
convention would be a new contract stands unaltered. Whether it ever becomes a gate is a planner
decision, not something this file asserts or implies.

## Running it

Run it from `lean/`, inside the pinned `spec` shell, with the Lake environment. `LAKE_NO_CACHE=1`
because this build prints evidence:

```sh
nix --extra-experimental-features "nix-command flakes" develop --offline --no-update-lock-file \
  .#spec --command \
  bash -c 'cd lean && LAKE_NO_CACHE=1 lake env lean --run ../scripts/check-unsettled-index.lean \
    ../vectors/slice.ndjson ../vectors/generated-exchanges.ndjson'
```

or, already inside that shell:

```sh
cd lean
LAKE_NO_CACHE=1 lake env lean --run ../scripts/check-unsettled-index.lean \
  ../vectors/slice.ndjson ../vectors/generated-exchanges.ndjson
```

Every path argument is read as an NDJSON corpus; `--dump` prints each post-step link table. The exit
status is 0 when the replay found no index+coverage violations (the pre-fix guard survivors are
informational and never set it), 1 otherwise.
-/
import Spec.SessionCodec
import Ref.SessionCodec
import Lean

open Lean
open SpecAMQP.Harness

namespace UnsettledDispositionCheck

/-- Lower-case hex, for the tags a violation line names. -/
def tagHex (tag : List UInt8) : String :=
  String.join (tag.map (fun b =>
    let s := String.ofList (Nat.toDigits 16 b.toNat)
    if s.length < 2 then "0" ++ s else s))

/-- What the run counted, per reading. -/
structure Counts where
  vectors : Nat := 0
  steps : Nat := 0
  dispositions : Nat := 0
  indexChecks : Nat := 0
  coverageChecks : Nat := 0
  uncoveredChecks : Nat := 0
  guardChecks : Nat := 0
deriving Repr

/- One reading's check: the specification reading. -/
namespace SpecSide

open SpecAMQP.Spec.Codec (Value)
open SpecAMQP.Spec.Connection (fieldBool fieldValue valueNat valueOctets)
open SpecAMQP.Spec.Session (LinkRole Performative isDisposition)

abbrev WidenedSession := SpecAMQP.Spec.WidenedSession
abbrev Link := SpecAMQP.Spec.WidenedLink

def linkKey (id : SpecAMQP.Spec.LinkId) : String :=
  s!"{id.name}/{if id.localRole == LinkRole.sender then "sender" else "receiver"}"

def roleLabel (sender : Bool) : String := if sender then "sender" else "receiver"

/-- A monitor observation: the link (identity rendered), the tag, and the sender's id the tag last
named on a transfer that left the delivery unsettled. -/
abbrev Obs := String × List UInt8 × Nat

def dumpLink (where_ : String) (id : SpecAMQP.Spec.LinkId) (link : Link) : IO Unit :=
  let entries := link.unsettledKeys.map (fun tag =>
    s!"{tagHex tag.data.toList}->{(link.unsettled tag).map (fun e => e.deliveryId)}")
  IO.println s!"    {where_} {linkKey id} delivery={link.delivery.map (fun d => d.id)} \
    tag={link.deliveryTag.map (fun t => tagHex t.data.toList)} index={entries}"

def dump (where_ : String) (session : WidenedSession) : IO Unit := do
  for key in session.linkKeys do
    match session.links key with
    | none => IO.println s!"    {where_} {linkKey key} (no record)"
    | some link => dumpLink where_ key link

def checkVector (json : Json) (found guard : IO.Ref (List String)) (counts : IO.Ref Counts)
    (verbose : Bool) : IO Unit := do
  let id := (json.getObjValAs? String "vector").toOption.getD "?"
  let startName := (json.getObjValAs? String "start").toOption.getD "?"
  let steps := (json.getObjValAs? (Array Json) "steps").toOption.getD #[]
  match SpecAMQP.Spec.SessionCodec.specExchangeCodec.start startName with
  | .error e => found.modify (s!"spec {id}: start failed: {e}" :: ·)
  | .ok st =>
    counts.modify (fun c => { c with vectors := c.vectors + 1 })
    let mut state := st
    let mut obs : List Obs := []
    let mut n := 0
    for stepJson in steps.toList do
      n := n + 1
      let where_ := s!"spec {id}#{n}"
      match exchangeStepOf stepJson with
      | .error e => found.modify (s!"{where_}: step parse failed: {e}" :: ·)
      | .ok step =>
        let body? : Option Value :=
          match SpecAMQP.Spec.SessionCodec.targetOf step with
          | .ok (.session _ body _) => some body
          | _ => none
        let pre := state.session
        -- the monitor: what the wire has declared unsettled, read before the step
        match body? with
        | some body =>
          if Performative.ofBody body == .transfer then
            let handle? := (fieldValue "transfer" "handle" body).bind valueNat
            match handle?.bind (fun h =>
                (SpecAMQP.Spec.Protocol.resolveHandle pre step.send h).bind
                  (fun i => pre.links i)) with
            | none => pure ()
            | some link =>
              let tag? : Option (List UInt8) :=
                if link.delivery.isSome then link.deliveryTag.map (fun t => t.data.toList)
                else ((fieldValue "transfer" "delivery-tag" body).bind valueOctets).map
                  (fun octets => octets.toList)
              let deliveryId? : Option Nat :=
                match (fieldValue "transfer" "delivery-id" body).bind valueNat with
                | some i => some i
                | none => link.delivery.map (fun d => d.id)
              let settled := fieldBool "transfer" "settled" body
              let aborted := fieldBool "transfer" "aborted" body
              let key := linkKey link.id
              match tag?, deliveryId? with
              | some tag, some deliveryId =>
                obs := obs.filter (fun o => !(o.1 == key && o.2.1 == tag))
                if !(settled || aborted) then obs := (key, tag, deliveryId) :: obs
              | _, _ => pure ()
        | none => pure ()
        -- the settled disposition this step carries, if any: (role is sender, first, last, settled)
        let disposition? : Option (Bool × Nat × Nat × Bool) :=
          match body? with
          | some body =>
            if isDisposition body then
              let first := ((fieldValue "disposition" "first" body).bind valueNat).getD 0
              let last := ((fieldValue "disposition" "last" body).bind valueNat).getD first
              some ((fieldValue "disposition" "role" body).bind LinkRole.ofValue == some .sender,
                    first, last, fieldBool "disposition" "settled" body)
            else none
          | none => none
        match SpecAMQP.Spec.SessionCodec.specExchangeCodec.step state step with
        | .error e => found.modify (s!"{where_}: step failed: {e}" :: ·)
        | .ok (_, next) => do
          counts.modify (fun c => { c with steps := c.steps + 1 })
          let post := next.session
          if verbose then dump where_ post else pure ()
          -- clause 1: the index is exact, and holds every tag the wire declares live
          for key in post.linkKeys do
            match post.links key with
            | none =>
              found.modify (s!"INDEX {where_}: {linkKey key} is in linkKeys with no record" :: ·)
            | some link => do
              counts.modify (fun c => { c with indexChecks := c.indexChecks + 1 })
              if link.unsettledKeys.eraseDups.length != link.unsettledKeys.length then
                found.modify (s!"INDEX {where_}: {linkKey key}: unsettledKeys has a duplicate" :: ·)
              for tag in link.unsettledKeys do
                if (link.unsettled tag).isNone then
                  found.modify (s!"INDEX {where_}: {linkKey key}: the index names tag \
                    {tagHex tag.data.toList} with no entry in the table" :: ·)
              for o in obs do
                if o.1 == linkKey key then
                  if (link.unsettled (ByteArray.mk o.2.1.toArray)).isSome &&
                      !(link.unsettledKeys.contains (ByteArray.mk o.2.1.toArray)) then
                    found.modify (s!"INDEX {where_}: {linkKey key}: tag {tagHex o.2.1} holds an \
                      entry and is absent from the index" :: ·)
          -- clauses 2 and 3, on a settled disposition
          match disposition? with
          | none => pure ()
          | some (roleSender, first, last, settled) =>
            if !settled then pure ()
            else do
              counts.modify (fun c => { c with dispositions := c.dispositions + 1 })
              for key in pre.linkKeys do
                if (key.localRole == LinkRole.sender) == roleSender then
                  match pre.links key with
                  | none => pure ()
                  | some before => do
                    let fromIndex := before.unsettledKeys.filterMap (fun tag =>
                      match before.unsettled tag with
                      | some entry =>
                        if first ≤ entry.deliveryId && entry.deliveryId ≤ last then
                          some (tag, entry.deliveryId)
                        else none
                      | none => none)
                    let fromMonitor := (obs.filter (fun o => o.1 == linkKey key)).filterMap
                      (fun o =>
                        if first ≤ o.2.2 && o.2.2 ≤ last then
                          some (ByteArray.mk o.2.1.toArray, o.2.2)
                        else none)
                    -- clause 2: no covered live entry survives the disposition
                    for (tag, deliveryId) in fromIndex ++ fromMonitor do
                      counts.modify (fun c => { c with coverageChecks := c.coverageChecks + 1 })
                      match post.links key with
                      | none => pure ()
                      | some after =>
                        match after.unsettled tag with
                        | some entry =>
                          if entry.deliveryId == deliveryId then
                            found.modify (s!"COVERAGE {where_}: a settled disposition for role \
                              {roleLabel roleSender} over [{first},{last}] left tag \
                              {tagHex tag.data.toList} (delivery {deliveryId}) in {linkKey key}'s \
                              unsettled table" :: ·)
                        | none => pure ()
                    -- clause 4: an entry the range does not cover must survive, which is what
                    -- separates an exact traversal from a clearing of the whole table
                    let uncovered := before.unsettledKeys.filterMap (fun tag =>
                      match before.unsettled tag with
                      | some entry =>
                        if first ≤ entry.deliveryId && entry.deliveryId ≤ last then none
                        else some (tag, entry.deliveryId)
                      | none => none)
                    for (tag, deliveryId) in uncovered do
                      counts.modify (fun c => { c with uncoveredChecks := c.uncoveredChecks + 1 })
                      match post.links key with
                      | none => pure ()
                      | some after =>
                        match after.unsettled tag with
                        | some entry =>
                          if entry.deliveryId != deliveryId then
                            found.modify (s!"OVER-CLEAR {where_}: a settled disposition for role \
                              {roleLabel roleSender} over [{first},{last}] changed tag \
                              {tagHex tag.data.toList}, whose delivery {deliveryId} is outside the \
                              range" :: ·)
                        | none =>
                          found.modify (s!"OVER-CLEAR {where_}: a settled disposition for role \
                            {roleLabel roleSender} over [{first},{last}] cleared tag \
                            {tagHex tag.data.toList} (delivery {deliveryId}), which is outside the \
                            range" :: ·)
                    -- clause 3: the pre-fix body's rule over the pre-step link, informational
                    let survivors := fromIndex.filter (fun (tag, _) =>
                      match before.delivery, before.deliveryTag with
                      | some _, some t => t != tag
                      | _, _ => true)
                    for (tag, deliveryId) in survivors do
                      counts.modify (fun c => { c with guardChecks := c.guardChecks + 1 })
                      guard.modify (s!"GUARD {where_}: the pre-fix body would leave tag \
                        {tagHex tag.data.toList} (delivery {deliveryId}) in {linkKey key}'s table after \
                        a settled disposition over [{first},{last}], so the resumed send of that \
                        delivery is admitted instead of refused" :: ·)
          state := next

end SpecSide

/- The same three clauses over the reference reading's own state. -/
namespace RefSide

open SpecAMQP.Ref.Connection (numberOf octetsOf valueOfField)
open SpecAMQP.Ref.Session (Role booleanAtField isDisposition)

abbrev WidenedSession := SpecAMQP.Ref.Protocol.WidenedSession
abbrev Link := SpecAMQP.Ref.Protocol.Link

def linkKey (id : SpecAMQP.Ref.Protocol.LinkId) : String :=
  s!"{id.name}/{if id.localRole == Role.sender then "sender" else "receiver"}"

def roleLabel (sender : Bool) : String := if sender then "sender" else "receiver"

abbrev Obs := String × List UInt8 × Nat

def dumpLink (where_ : String) (id : SpecAMQP.Ref.Protocol.LinkId) (link : Link) : IO Unit :=
  let entries := link.unsettledKeys.map (fun tag =>
    s!"{tagHex tag}->{(link.unsettled tag).map (fun e => e.deliveryId)}")
  IO.println s!"    {where_} {linkKey id} delivery={link.delivery.map (fun d => d.id)} \
    tag={link.deliveryTag.map tagHex} index={entries}"

def dump (where_ : String) (session : WidenedSession) : IO Unit := do
  for key in session.linkKeys do
    match session.links key with
    | none => IO.println s!"    {where_} {linkKey key} (no record)"
    | some link => dumpLink where_ key link

def checkVector (json : Json) (found guard : IO.Ref (List String)) (counts : IO.Ref Counts)
    (verbose : Bool) : IO Unit := do
  let id := (json.getObjValAs? String "vector").toOption.getD "?"
  let startName := (json.getObjValAs? String "start").toOption.getD "?"
  let steps := (json.getObjValAs? (Array Json) "steps").toOption.getD #[]
  match SpecAMQP.Ref.SessionCodec.refExchangeCodec.start startName with
  | .error e => found.modify (s!"ref {id}: start failed: {e}" :: ·)
  | .ok st =>
    counts.modify (fun c => { c with vectors := c.vectors + 1 })
    let mut state := st
    let mut obs : List Obs := []
    let mut n := 0
    for stepJson in steps.toList do
      n := n + 1
      let where_ := s!"ref {id}#{n}"
      match exchangeStepOf stepJson with
      | .error e => found.modify (s!"{where_}: step parse failed: {e}" :: ·)
      | .ok step =>
        let body? : Option SpecAMQP.Ref.Value :=
          match SpecAMQP.Ref.SessionCodec.targetOf step with
          | .ok (.session _ body _) => some body
          | _ => none
        let pre := state.session
        match body? with
        | some body =>
          if (match SpecAMQP.Ref.Session.frameOf body with
              | .transfer => true
              | _ => false) then
            let handle? := (valueOfField "transfer" "handle" body).bind numberOf
            match handle?.bind (fun h =>
                (SpecAMQP.Ref.Protocol.resolveHandle pre step.send h).bind
                  (fun i => pre.links i)) with
            | none => pure ()
            | some link =>
              let tag? : Option (List UInt8) :=
                if link.delivery.isSome then link.deliveryTag
                else (valueOfField "transfer" "delivery-tag" body).bind octetsOf
              let deliveryId? : Option Nat :=
                match (valueOfField "transfer" "delivery-id" body).bind numberOf with
                | some i => some i
                | none => link.delivery.map (fun d => d.id)
              let settled := booleanAtField "transfer" "settled" body
              let aborted := booleanAtField "transfer" "aborted" body
              let key := linkKey link.id
              match tag?, deliveryId? with
              | some tag, some deliveryId =>
                obs := obs.filter (fun o => !(o.1 == key && o.2.1 == tag))
                if !(settled || aborted) then obs := (key, tag, deliveryId) :: obs
              | _, _ => pure ()
        | none => pure ()
        let disposition? : Option (Bool × Nat × Nat × Bool) :=
          match body? with
          | some body =>
            if isDisposition body then
              let first := ((valueOfField "disposition" "first" body).bind numberOf).getD 0
              let last := ((valueOfField "disposition" "last" body).bind numberOf).getD first
              some ((valueOfField "disposition" "role" body).bind Role.ofValue == some .sender,
                    first, last, booleanAtField "disposition" "settled" body)
            else none
          | none => none
        match SpecAMQP.Ref.SessionCodec.refExchangeCodec.step state step with
        | .error e => found.modify (s!"{where_}: step failed: {e}" :: ·)
        | .ok (_, next) => do
          counts.modify (fun c => { c with steps := c.steps + 1 })
          let post := next.session
          if verbose then dump where_ post else pure ()
          for key in post.linkKeys do
            match post.links key with
            | none =>
              found.modify (s!"INDEX {where_}: {linkKey key} is in linkKeys with no record" :: ·)
            | some link => do
              counts.modify (fun c => { c with indexChecks := c.indexChecks + 1 })
              if link.unsettledKeys.eraseDups.length != link.unsettledKeys.length then
                found.modify (s!"INDEX {where_}: {linkKey key}: unsettledKeys has a duplicate" :: ·)
              for tag in link.unsettledKeys do
                if (link.unsettled tag).isNone then
                  found.modify (s!"INDEX {where_}: {linkKey key}: the index names tag \
                    {tagHex tag} with no entry in the table" :: ·)
              for o in obs do
                if o.1 == linkKey key then
                  if (link.unsettled o.2.1).isSome && !(link.unsettledKeys.contains o.2.1) then
                    found.modify (s!"INDEX {where_}: {linkKey key}: tag {tagHex o.2.1} holds an \
                      entry and is absent from the index" :: ·)
          match disposition? with
          | none => pure ()
          | some (roleSender, first, last, settled) =>
            if !settled then pure ()
            else do
              counts.modify (fun c => { c with dispositions := c.dispositions + 1 })
              for key in pre.linkKeys do
                if (key.localRole == Role.sender) == roleSender then
                  match pre.links key with
                  | none => pure ()
                  | some before => do
                    let fromIndex := before.unsettledKeys.filterMap (fun tag =>
                      match before.unsettled tag with
                      | some entry =>
                        if first ≤ entry.deliveryId && entry.deliveryId ≤ last then
                          some (tag, entry.deliveryId)
                        else none
                      | none => none)
                    let fromMonitor := (obs.filter (fun o => o.1 == linkKey key)).filterMap
                      (fun o =>
                        if first ≤ o.2.2 && o.2.2 ≤ last then some (o.2.1, o.2.2) else none)
                    for (tag, deliveryId) in fromIndex ++ fromMonitor do
                      counts.modify (fun c => { c with coverageChecks := c.coverageChecks + 1 })
                      match post.links key with
                      | none => pure ()
                      | some after =>
                        match after.unsettled tag with
                        | some entry =>
                          if entry.deliveryId == deliveryId then
                            found.modify (s!"COVERAGE {where_}: a settled disposition for role \
                              {roleLabel roleSender} over [{first},{last}] left tag {tagHex tag} \
                              (delivery {deliveryId}) in {linkKey key}'s unsettled table" :: ·)
                        | none => pure ()
                    let uncovered := before.unsettledKeys.filterMap (fun tag =>
                      match before.unsettled tag with
                      | some entry =>
                        if first ≤ entry.deliveryId && entry.deliveryId ≤ last then none
                        else some (tag, entry.deliveryId)
                      | none => none)
                    for (tag, deliveryId) in uncovered do
                      counts.modify (fun c => { c with uncoveredChecks := c.uncoveredChecks + 1 })
                      match post.links key with
                      | none => pure ()
                      | some after =>
                        match after.unsettled tag with
                        | some entry =>
                          if entry.deliveryId != deliveryId then
                            found.modify (s!"OVER-CLEAR {where_}: a settled disposition for role \
                              {roleLabel roleSender} over [{first},{last}] changed tag \
                              {tagHex tag}, whose delivery {deliveryId} is outside the range" :: ·)
                        | none =>
                          found.modify (s!"OVER-CLEAR {where_}: a settled disposition for role \
                            {roleLabel roleSender} over [{first},{last}] cleared tag {tagHex tag} \
                            (delivery {deliveryId}), which is outside the range" :: ·)
                    let survivors := fromIndex.filter (fun (tag, _) =>
                      match before.delivery, before.deliveryTag with
                      | some _, some t => t != tag
                      | _, _ => true)
                    for (tag, deliveryId) in survivors do
                      counts.modify (fun c => { c with guardChecks := c.guardChecks + 1 })
                      guard.modify (s!"GUARD {where_}: the pre-fix body would leave tag \
                        {tagHex tag} (delivery {deliveryId}) in {linkKey key}'s table after a \
                        settled disposition over [{first},{last}], so the resumed send of that \
                        delivery is admitted instead of refused" :: ·)
          state := next

end RefSide

def report (label path : String) (found guard : List String) (c : Counts) : IO Unit := do
  IO.println s!"{label} {path}: vectors={c.vectors} steps={c.steps} \
    disposition-steps={c.dispositions} index-checks={c.indexChecks} \
    coverage-checks={c.coverageChecks} uncovered-checks={c.uncoveredChecks} guard-checks={c.guardChecks}"
  IO.println s!"  index+coverage violations: {found.length}"
  for m in found.take 20 do IO.println s!"    {m}"
  IO.println s!"  pre-fix guard survivors (informational, not a failure): {guard.length}"
  for m in guard.take 12 do IO.println s!"    {m}"

def main (args : List String) : IO UInt32 := do
  let paths := args.filter (fun a => !a.startsWith "--")
  let verbose := args.contains "--dump"
  let specFound ← IO.mkRef ([] : List String)
  let specGuard ← IO.mkRef ([] : List String)
  let specCounts ← IO.mkRef ({} : Counts)
  let refFound ← IO.mkRef ([] : List String)
  let refGuard ← IO.mkRef ([] : List String)
  let refCounts ← IO.mkRef ({} : Counts)
  for path in paths do
    let text ← IO.FS.readFile path
    for line in text.splitOn "\n" do
      if line.trim.isEmpty then continue
      match Json.parse line with
      | .error e => specFound.modify (s!"parse: {e}" :: ·)
      | .ok json =>
        SpecSide.checkVector json specFound specGuard specCounts verbose
        RefSide.checkVector json refFound refGuard refCounts verbose
  report "specification" (String.intercalate " " paths) (← specFound.get) (← specGuard.get)
    (← specCounts.get)
  report "reference    " (String.intercalate " " paths) (← refFound.get) (← refGuard.get)
    (← refCounts.get)
  let violations := (← specFound.get).length + (← refFound.get).length
  IO.println s!"total index+coverage violations: {violations}"
  return (if violations == 0 then 0 else 1)

end UnsettledDispositionCheck

def main (args : List String) : IO UInt32 := UnsettledDispositionCheck.main args
