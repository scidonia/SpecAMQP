import Spec.Session

/-!
# The settlement contract: what a disposition does, and what settlement is

This file is the planner's acceptance declaration for the session layer's `disposition` exchange
and the delivery-state bookkeeping it moves. Like `Contracts/FrameCodec.lean` and
`Contracts/MessageFormat.lean`, it separates what is *proved* from what is only *stated*, and it
names where each proof lives rather than leaving a reader to infer it from a theorem's presence.

## The citation convention, and a gap it exposes in the ledger

Every clause this file cites is a registered id from `ledger/clauses.json`, written in full —
artifact, anchor, index. Nothing here cites `section:disposition`, a fragment such as
`disposition.2`, or any other derived spelling; the corpus's citations were checked for exactly
this and 163 stale ones were found the same way.

The gap is worth stating because it constrains what this contract can cite. The ledger keys
**four** clauses for the `disposition` performative —
`amqp-core-transport-v1.0-os.xml#amqp:transport/section:performatives/type:disposition.1` (the
directionality MAY), `amqp-core-transport-v1.0-os.xml#amqp:transport/section:performatives/type:disposition.2` (the same sentence's MUST), `amqp-core-transport-v1.0-os.xml#amqp:transport/section:performatives/type:disposition.3` (a disposition MAY refer
to deliveries on links no longer attached) and `amqp-core-transport-v1.0-os.xml#amqp:transport/section:performatives/type:disposition.4` (those deliveries are still live and the
updated state MUST be applied) — plus one hint's clauses under `field:batchable`. The fields that carry the
*mechanics* of settlement (`role`, `first`, `last`, `settled`, `state`) have no keyed clause at
all: the artifact writes their docs as descriptions, so the ledger has nothing to key. The
consequence is that a rule about the delivery range or about the settled flag cannot be cited to
a clause, and this file does not invent one — it states such rules as *readings* and says which
field's doc each is a reading of.

## Settlement's own law, and where it is proved

The artifact's account of settlement is that it is **absorbing**. The links section says settling
"is an idempotent idempotent, i.e., a delivery can transition from unsettled to settled, but never
the reverse"; `amqp-core-messaging-v1.0-os.xml#amqp:messaging/section:delivery-state.u1` says
"[o]nce a delivery reaches a terminal delivery state, the state for that delivery will no longer
change"; and
`amqp-core-messaging-v1.0-os.xml#amqp:messaging/section:delivery-state/doc:more-resuming-deliveries.15`
makes it a MUST NOT — "[o]nce the sender has arrived at a terminal outcome it MUST NOT change".

Nothing in either artifact names a condition for breaking that, which is why the register carries
it as a reading: `ledger/ambiguities/settlement-is-absorbing.json`, adopted, with the second
reading — that a step's own flag is authoritative and may unsettle — rejected. The reading's
carrier at the message layer is `SpecAMQP.Spec.Message.settled_monotone`, re-exported by
`Contracts.MessageFormat.settled_monotone_public`; the session layer's carrier of the *transfer*
half of it is `delivery_settlement_is_monotone` below, which is proved here rather than
re-exported, because it is stated over this layer's own `Delivery.step` and would otherwise have
no carrier at all.
-/

namespace SpecAMQP.Contracts

open SpecAMQP.Spec.Session
open SpecAMQP.Spec.Connection
  (fieldValue fieldSet invalidField missingMandatory valueNat)
open SpecAMQP.Spec.Codec (Value)

/-! ## Proved: the settlement the session carries across a delivery's transfers

`amqp-core-transport-v1.0-os.xml#amqp:transport/section:performatives/type:transfer/field:settled.2`
and `amqp-core-transport-v1.0-os.xml#amqp:transport/section:performatives/type:transfer/field:settled.3` are one sentence about a continuation whose flag is left unset: it "MUST be interpreted as
true if and only if the value of the settled flag on any of the preceding transfers was true; if no
preceding transfer was sent with settled being true then the value when unset MUST be taken as
false". `Delivery.step` is that interpretation — `carried || step` — and the theorem below is the
"if and only if the value on any preceding transfer was true" half stated as the law it is: once a
delivery's carried flag is true, no later transfer of that delivery reports it false, whatever the
later frame sets. -/

/-- **Settlement accumulates and never returns to false**, at the type the session layer carries
it. The hypothesis names the delivery held before the step, so the statement is about the flag the
session is actually carrying rather than about an arbitrary one. -/
theorem delivery_settlement_is_monotone (current : Option Delivery) (delivery : Delivery)
    (id : Nat) (settled : Bool) (held : current = some delivery) (carried : delivery.settled = true) :
    (Delivery.step current id settled).settled = true := by
  subst held
  simp [Delivery.step, carried]

/-- The first transfer's half of the same pair,
`amqp-core-transport-v1.0-os.xml#amqp:transport/section:performatives/type:transfer/field:settled.1`:
a delivery whose first transfer leaves the flag unset is not settled by that transfer. The
interpretation is the step's own argument, so this is the statement that the session's constructor
does not invent a value where the frame left none. -/
theorem unsettled_first_transfer_stays_unsettled (id : Nat) :
    (Delivery.step none id false).settled = false := rfl

/-! ## Stated: the disposition exchange's rules

Each proposition below is over the specification's own `dispositionLink` (or the session's
`transferLink` for the settlement mode), so a reader can tell exactly what is claimed and a proof
module has something precise to discharge. None is proved today, and none is a paraphrase of the
code: each is the clause's requirement, with the hypotheses the clause needs. -/

/-- **A disposition whose role is the other end's is refused.** The role field "identifies whether
the disposition frame contains information about sending link endpoints or receiving link
endpoints", and the sentence that makes it a rule is
`amqp-core-transport-v1.0-os.xml#amqp:transport/section:performatives/type:disposition.2`, whose
MUST half reads "all links MUST have the directionality indicated by the specified role". So a
disposition this endpoint receives that names the role *it* attached as is one about deliveries it
is not the end of, and the refusal is the field-rule refusal the layer uses for a body that breaks
a rule the declared surface states.

**A reading, and stated as one**: no clause says which end may *issue* which role, so what the
directionality means for the issuing end is read from the field's own doc rather than cited. -/
def DispositionsInTheOtherDirectionAreRefused : Prop :=
  ∀ (session : Session) (outbound : Bool) (body : Value),
    session.role = some LinkRole.sender →
    (fieldValue "disposition" "role" body).bind LinkRole.ofValue = some LinkRole.receiver →
    ∃ reason : Refusal,
      dispositionLink session outbound body = .error reason ∧
        reason.condition = invalidField

/-- **A settled disposition releases the delivery it covers.** The disposition's `settled` field
means "the referenced deliveries are considered settled by the issuing endpoint" (the field's own
doc — unkeyed, so a reading rather than a citation) and the range it covers is `first` to `last`,
where an unset `last` "is taken to be the same as `first`" (the same doc, likewise unkeyed). The
obligation stated here is the one the session can observe: a disposition that settles the delivery
the session is holding releases it, and the delivery it does *not* cover is left where it was.

Read with `settlement-is-absorbing`'s adopted reading, this is settlement doing what the reading
says it does — removing the delivery rather than re-labelling it, since the artifact's account of
the unsettled map is an account of removal and not of re-insertion. -/
def SettledDispositionsReleaseTheDeliveryTheyCover : Prop :=
  ∀ (session session' : Session) (outbound : Bool) (body : Value) (delivery : Delivery),
    session.delivery = some delivery →
    session.role = some LinkRole.sender →
    (fieldValue "disposition" "role" body).bind LinkRole.ofValue = some LinkRole.sender →
    fieldSet "disposition" "settled" body = true →
    (fieldValue "disposition" "first" body).bind valueNat = some delivery.id →
    (fieldValue "disposition" "last" body).bind valueNat = none →
    dispositionLink session outbound body = .ok session' →
    session'.delivery = none

/-- **A disposition that does not cover the delivery leaves it held.** The other half of the same
rule, and the half that keeps the first from being a claim about *any* settled disposition: the
range's ends are `first` and `last`, an unset `last` is `first`, and a delivery outside them is not
one the issuer settled. Without this proposition a model that released the held delivery on any
settled disposition would satisfy the law above, which is the shape of a check that decays into a
restatement of whichever branch the code happens to take. -/
def DispositionsThatDoNotCoverTheDeliveryLeaveItHeld : Prop :=
  ∀ (session session' : Session) (outbound : Bool) (body : Value) (delivery : Delivery)
    (first last : Nat),
    session.delivery = some delivery →
    session.role = some LinkRole.sender →
    (fieldValue "disposition" "role" body).bind LinkRole.ofValue = some LinkRole.sender →
    (fieldValue "disposition" "first" body).bind valueNat = some first →
    (fieldValue "disposition" "last" body).bind valueNat = some last →
    first ≤ last →
    (delivery.id < first ∨ last < delivery.id) →
    fieldSet "disposition" "settled" body = true →
    dispositionLink session outbound body = .ok session' →
    session'.delivery = some delivery

/-- **A delivery whose negotiated mode is `sender-settle-mode` is settled on one of its
transfers.**
`amqp-core-transport-v1.0-os.xml#amqp:transport/section:performatives/type:transfer/field:settled.4`:
"If the negotiated value for snd-settle-mode at attachment is «sender-settle-mode», then this field
MUST be true on at least one transfer frame for a delivery (i.e., the delivery MUST be settled at
the sender before the receiver can settle it)". The mode is negotiated at `attach`, and the
session records it as `senderSettleMode`; the obligation is stated for the transfer that completes
a delivery, which is the moment the mode can be checked — a continuation may settle later. -/
def SenderSettleModeDeliveriesAreSettledOnATransfer : Prop :=
  ∀ (session : Session) (body : Value) (deliveryId : Nat),
    session.role = some LinkRole.sender →
    session.senderSettleMode = true →
    session.delivery = none →
    (fieldValue "transfer" "delivery-id" body).bind valueNat = some deliveryId →
    fieldSet "transfer" "delivery-tag" body = true →
    fieldSet "transfer" "message-format" body = true →
    fieldSet "transfer" "aborted" body = false →
    fieldSet "transfer" "more" body = false →
    fieldSet "transfer" "settled" body = false →
    ∃ reason : Refusal,
      transferLink session true body = .error reason ∧
        reason.condition = invalidField

/-! ## What this file deliberately does not claim

* **The outcome state machine is not this file's.** `received`, `accepted`, `rejected`,
  `released` and `modified`, with their terminality, are Part 3's and are carried by
  `SpecAMQP.Spec.Message` and declared in `Contracts/MessageFormat.lean`. What a disposition's
  `state` field carries is a value of that machine; this file is about the frame's other fields and
  the bookkeeping they move.
* **`rcv-settle-mode` is not modelled.** The attach field negotiates when the *receiver* settles,
  and the session records only the sender's side of that negotiation, so a rule about the
  receiver's settlement has no subject here.
* **The sender's unsettled map is not modelled.** The session holds one delivery
  (`Session.delivery`), not a map from delivery-tags to states, which is the model restriction the
  register records at `ledger/ambiguities/link-uniqueness-vacuous.json` and which the fragmentation
  family's docstring names again: the clauses that talk about *entries* — resumption, in-doubt
  resolution, `unsettled`'s completeness — have no state to range over.
* **Errors a detach carries are carried, not judged.** A detach whose `error` field is set ends the
  link with that error, and the model keeps no per-link error afterwards, so
  `amqp-core-transport-v1.0-os.xml#amqp:transport/section:definitions/type:session-error/choice:errant-link.u1`
  ("Input was received for a link that was detached with an error") has no carrier: later input for
  that handle is refused with `unattached-handle`, which is
  `amqp-core-transport-v1.0-os.xml#amqp:transport/section:links.15` read for a destroyed endpoint.
  A model that distinguished released from destroyed-with-error links would need a field the
  session does not have, and the gap is reported as the plan question it is rather than approximated
  here.
-/

end SpecAMQP.Contracts
