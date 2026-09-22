# The corpus's negative vectors, classified by whether they isolate a rule

A negative vector counts as evidence for a rule R only if **disabling R makes the vector stop failing for
R's reason**. Where that cannot be arranged the vector is not evidence for R at all: it is *broad
conformance evidence*, which is a label rather than a claim, and the difference is what stops a corpus
that passes from being read as a corpus that proves.

65 hand-authored negative vectors are classified below: 8 isolated, **6 of them
witnessed by a disabling experiment actually run**, 2 reasoned from construction with no
experiment run. 57 are broad, 1 of those broad **and** witnessed. The generated value
corpus's negatives are not listed: the label would be uniform and therefore uninformative.

## The witnesses, and what they cost

* **`exchange-link-handle-in-use`** — the attach guard removed (`Spec/Session.lean:621-624`, the answer to
  an attach on an already-associated handle) failed **exactly one step** in the whole corpus,
  `exchange-link-handle-in-use#4`, out of 278 step verdicts in one corpus run and 29 in the other, the
  reference untouched. That is what rule-isolated evidence looks like: one rule, one failure.
* **`exchange-link-credit-granted-and-spent`** and **`exchange-link-credit-counts-messages-not-frames`** —
  removing the spend failed both, where the plan records **three** failures for this experiment. The
  difference is not a disagreement: the plan measured the layer *before the fourth defect was fixed*,
  where a delivery whose single transfer left `more` unset never incremented the delivery-count, so a
  second delivery was admitted free and its vector failed too. Reported before the table was touched.
* **`exchange-session-channel-above-the-declared-bound`** — widening the channel bound by one stopped that
  vector alone from failing, and its revert restored it.
* **`exchange-session-refusal-in-end-sent-discards`** — the isolating vector the layer work wrote, which
  failed on its first run until the second placement site was widened.
* **`exchange-session-window-spent-by-sent-transfers`** and **`exchange-link-handle-at-bound-plus-one`** —
  isolated by construction, no experiment run against them yet, and labelled as reasoning rather than
  witnessed.

## The two witnessed-broad rows are the ones worth keeping

`exchange-link-handle-out-of-range` and `exchange-session-transfer-one-data-section` each name a rule, and
each stays green when that rule is disabled — the first because a value of 5 is refused by the true bound
and the widened one alike, the second because the role rule answers first with a different condition. They
are not corpus defects; they are proofs of the label, each a vector that no mutation of its named rule can
kill.

## One trap the experiments hit, recorded because it has now cost three runs

A plant that does not typecheck leaves the previously built binary in place, and the corpus runs behind it
print `0 failures` — which reads exactly like a mutant that changed nothing, and is really a mutant that
never ran. One of the two credit plants failed this way (`credit := current.credit` left the `if` unused
and the codec failed to build) and the run was discarded rather than counted, then re-planted in a
well-typed form. The build is shown every time for this reason.

## Limit, stated rather than implied

The rule column for entries under `generated-exchanges.ndjson` carries the file-level rule rather than a
per-vector one, because the classification is a claim about evidence and no experiment has been run for
those vectors; per-vector precision is owed before their experiments are run, and the three groups named as
first candidates — the header/version rules, the sizing and channel limits in `exchange-pipelined-*`, and
`exchange-link-credit-counts-messages-not-frames` — each cite a rule another rule in the same layer can
plausibly answer first, which is the failure mode this classification exists to expose.

Drafted by the vector slice, whose experiments these are; reviewed, applied and committed by the planner as
`vectors/**` requires.

| file | vector | rule cited | classification | the disabling experiment |
|---|---|---|---|---|
| `generated-exchanges` | `exchange-link-handle-in-use` | `attach/field:handle.2` | **isolated (witnessed, re-run tonight)** | removing the guard at `Spec/Session.lean:621-624` failed **exactly this vector's step 4** and nothing else — across 278 step verdicts in `generated-exchanges.ndjson` and 29 in `slice.ndjson`, with the reference green throughout. The plan's record and the re-run agree. |
| `generated-exchanges` | `exchange-link-credit-granted-and-spent` | the credit arithmetic (`Position.creditFor`; the spend at `Spec/Session.lean:809`) | **isolated (witnessed, re-run tonight)** | removing the credit spend failed **this vector's step 5** and one other, `exchange-link-credit-counts-messages-not-frames#7`. The plan records three failures for this experiment — the two continuation steps plus step 5. **The difference is a finding, not an error on either side**: the plan measured the pre-fix layer, where a delivery whose single transfer leaves `more` unset never incremented the delivery-count, so a second delivery was admitted free; that defect has since been fixed, and its extra failure is gone. |
| `generated-exchanges` | `exchange-link-credit-counts-messages-not-frames` | the same | **isolated (witnessed, re-run tonight)** | the same experiment; its step 7 is the second of the two failures. |
| generated-exchanges.ndjson | `exchange-header-protocol-id-unsupported` | picture.24 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-header-protocol-id-unassigned` | picture.24 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-header-version-unsupported` | picture.24 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-header-truncated` | picture.24 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-header-malformed` | picture.24 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-open-before-header` | picture.24 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-open-twice` | picture.24 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-open-on-channel-one-send` | picture.24 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-open-on-channel-one-receive` | picture.24 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-frame-where-header-belongs` | picture.24 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-two-headers` | picture.24 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-header-mismatch-in-hdr-sent` | picture.24 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-conforming-frame-in-open-sent` | picture.24 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-frame-in-end-refused` | picture.24 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-pipelined-channel-limit` | picture.24 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-pipelined-frame-size-limit` | picture.24 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-oversized-frame-received` | picture.24 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-sasl-mechanism-not-offered` | picture.24 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-sasl-mechanism-case-sensitive` | picture.24 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-sasl-frame-before-header` | picture.24 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-amqp-frame-in-sasl-layer` | picture.24 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-sasl-frame-in-amqp-layer` | picture.24 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-discarding-ignores-frames` | picture.24 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-session-end-with-error-discards` | amqp:transport/section:sessions.7 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-session-transfer-one-data-section` | amqp:transport/section:sessions.7 | **broad (witnessed)** | dropping linkHandleOf left it green: the role rule answers first with a different condition, so it is not evidence for the handle rule it names |
| generated-exchanges.ndjson | `exchange-session-attach-missing-role` | amqp:transport/section:sessions.7 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-session-flow-missing-next-incoming-id` | amqp:transport/section:performatives/type:flow/field:next-incoming-id.1 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-session-transfer-before-begin` | amqp:transport/section:sessions.7 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-session-frame-on-unmapped-channel` | amqp:transport/section:sessions.7 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-session-window-remote-incoming` | amqp:transport/section:sessions/doc:session-flow-control.3 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-session-window-recomputed` | amqp:transport/section:sessions/doc:session-flow-control.7 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-session-window-incoming-exhausted` | amqp:transport/section:sessions/doc:session-flow-control.5 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-connection-discarding-discards-session-frames` | picture.10 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-link-handle-in-use` | amqp:transport/section:link-handles | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-link-handle-out-of-range` | amqp:transport/section:link-handles | **broad** | the same mutant that killed the bound + 1 vector left this one green: 5 is refused by the true bound and the widened one alike |
| generated-exchanges.ndjson | `exchange-link-credit-granted-and-spent` | amqp:transport/section:flow-control | **isolated (witnessed)** | reverting the credit accounting failed this vector's step 5 as well as its predicted two, per the plan's record |
| generated-exchanges.ndjson | `exchange-link-sender-settle-mode-unmet` | amqp:transport/section:link-handles | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-link-first-transfer-needs-its-fields` | amqp:transport/section:link-handles | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-link-detach-releases-handle` | amqp:transport/section:link-handles | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-link-disposition-direction` | amqp:transport/section:link-handles | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-link-flow-unattached-handle` | amqp:transport/section:flow-control | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-link-flow-field-without-handle` | amqp:transport/section:flow-control | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-link-credit-echoed` | amqp:transport/section:flow-control | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-link-credit-counts-messages-not-frames` | amqp:transport/section:flow-control | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-link-transfer-direction-received` | amqp:transport/section:sessions.7 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-link-transfer-direction-sent` | amqp:transport/section:sessions.7 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-session-send-end-in-begin-sent` | amqp:transport/section:sessions.7 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-session-refusal-in-end-sent-discards` | amqp:transport/section:sessions.7 | **isolated (witnessed)** | the isolating vector the layer work wrote, which failed on its first run until the second placement site was widened |
| primitives.ndjson | `book-composite-wrong-size-rejected` | picture.19 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| primitives.ndjson | `escape-octet-rejected` | picture.3 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| primitives.ndjson | `reserved-octet-rejected` | picture.3 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| primitives.ndjson | `truncated-string-rejected` | picture.1 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| primitives.ndjson | `arr8-nulls-10-bad-size` | amqp:types/section:encodings.1 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| primitives.ndjson | `arr32-nulls-over-limit` | amqp:types/section:encodings.1 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| slice.ndjson | `slice-open-missing-container-id` | amqp:transport/section:connections.2 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| slice.ndjson | `slice-open-channel-max-wrong-type` | amqp:transport/section:connections.1 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| slice.ndjson | `slice-sasl-challenge-from-client` | amqp:security/section:sasl.3 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| slice.ndjson | `slice-sasl-mechanisms-empty` | amqp:security/section:sasl.3 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| slice.ndjson | `slice-open-before-header` | amqp:transport/section:version-negotiation.1 | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| slice.ndjson | `exchange-session-channel-above-the-declared-bound` | picture.10 | **isolated (witnessed)** | mutant 5 widened the channel bound by one; this vector alone stopped failing, and its revert restored it |
| slice.ndjson | `exchange-session-window-spent-by-sent-transfers` | picture.30 | **isolated (reasoned, not witnessed)** | the window spend's disabling experiment ran before this vector existed; its own construction isolates the window from the credit, but no experiment has been run against it |
| slice.ndjson | `exchange-link-handle-at-bound-plus-one` | amqp:transport/section:performatives/type:begin/field:handle-max.2 | **isolated (reasoned, not witnessed)** | sits at exactly bound + 1, which the corpus's range vector at 5 does not; experiment not run |
