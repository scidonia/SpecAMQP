# The corpus's negative vectors, classified by whether they isolate a rule

A negative vector counts as evidence for a rule R only if **disabling R makes the vector stop failing for
R's reason**. Where that cannot be arranged the vector is not evidence for R at all: it is *broad
conformance evidence*, which is a label rather than a claim, and the difference is what stops a corpus that
passes from being read as a corpus that proves.

68 rows, covering 68 distinct vectors — the corpus's hand-authored negatives *and*, since the session
layer's sweep, the exchange corpus's generated ones, whose labels stopped being uniform once experiments
were run on them. 53 are broad with no experiment run; 12 are isolated, of which 10 are **witnessed by a
disabling experiment actually run** and 2 are reasoned from construction with none; and 3 are broad **and**
witnessed. That last label is a result rather than a gap: the experiment ran, the vector stayed green, and
it is therefore not evidence for the rule it was meant to isolate. The value corpus's negatives are still
not listed: there the label would be uniform and uninformative.

## The witnesses, and what they cost

* **`exchange-link-handle-in-use`** — the attach guard removed (`Spec/Session.lean:696-699`) failed
  **exactly one step** in the whole corpus out of 307 step verdicts across two runs, the reference
  untouched. That is what rule-isolated evidence looks like: one rule, one failure.
* **`exchange-link-credit-granted-and-spent`** and **`exchange-link-credit-counts-messages-not-frames`** —
  removing the spend failed both, where the plan records **three** failures for this experiment. Not a
  disagreement: the plan measured the layer *before the fourth defect was fixed*, where a delivery whose
  single transfer left `more` unset never incremented the delivery-count, so a second delivery was admitted
  free and its vector failed too. Reported before the table was touched.
* **`exchange-session-channel-above-the-declared-bound`** — widening the channel bound by one stopped that
  vector alone from failing; the revert restored it.
* **`exchange-session-refusal-in-end-sent-discards`** — the isolating vector the layer work wrote, which
  failed on its first run until the second placement site was widened.

## A mutation that survived, and what surviving means here

The message slice's mutation window ran six mutants across the four classes; four were killed by corpus
vectors, one did not build, and one survived with no observable verdict changing. That survivor is worth
recording because it is not a coverage hole and not a corpus defect — it is a rule with two enforcers.

The removed branch was the composite reader's "a mandatory field is absent" case. The only composites in the
declared surface with a mandatory field are the delivery-state types, and `deliveryStateOfValue` reads those
by name through `unsignedField`, whose `none` arm enforces the same rule and produces the same condition and
reason class — so the deleted branch was **shadowed by an identical one**, and no vector could have failed.
The classification is therefore the same label the rules above carry and for the same reason: **broad
conformance evidence, not rule-isolated evidence**. A vector that fails if *both* guards go cannot distinguish
them, so no vector isolates this rule today; the one that would is a section type that declares a mandatory
field, at which point the branch becomes observable and the generator's descriptor sweep already carries the
case. Recording this is the point: a survivor that is understood is evidence about the specification's shape,
and a survivor that is merely written down as equivalent would be an assumption.

## The same two-enforcer shape, seen from the corpus side

The security slice's mutation tier found the phenomenon above from the other direction, and it is worth its
own section because it is the label's clearest instance yet. Its mutant **M2** disabled the mandatory-field
guard on the five SASL performatives. Three of the five vectors written for that rule failed —
`sasl-init-without-mechanism`, refused as an *unoffered mechanism* under `framing-error`, which is the
original defect reappearing; and `sasl-challenge-without-challenge` and `sasl-response-without-response`,
both admitted — while **two stayed green**: `sasl-outcome-without-code` and `sasl-mechanisms-null`.

Those two are refused by a *second* enforcer with the same condition and class — `intField`'s unset-field
arm and the empty-list arm respectively — so with the mandatory guard gone they pin the same behaviour
through the other enforcer. By this file's test they are therefore **broad conformance evidence, not
rule-isolated evidence**: neither can distinguish the guard it was written for from the guard that answers
first. No vector in that family isolates the mandatory-field rule today; a fifth performative whose fields no
other arm inspects would, and the shape to watch for when one is added is that its vector fails under M2
while the others do not.

The slice reported this rather than presenting five failing vectors as five witnesses, which is the reason it
belongs here — a family whose members are green under their own rule's mutant looks like five pieces of
evidence and is three.

## The two broad-witnessed rows are the ones worth keeping

Each names a rule and stays green when that rule is disabled — one because a value of 5 is refused by the
true bound and the widened one alike, the other because the role rule answers first with a different
condition. They are not corpus defects; they are proofs of the label, each a vector that no mutation of its
named rule can kill.

## One trap the experiments hit, recorded because it has now cost three runs

A plant that does not typecheck leaves the previously built binary in place, and the runs behind it print
`0 failures` — which reads exactly like a mutant that changed nothing, and is really a mutant that never
ran. One credit plant failed this way and its run was discarded rather than counted, then re-planted in a
well-typed form. The build is shown every time for this reason.

## A second trap, in this file's own first draft

An automated pass treated the word "disabling" as evidence of a run — which every default cell contains, in
the phrase "no disabling experiment run" — and labelled 54 vectors witnessed where the evidence covers
nine. It was caught by reconciling the totals against the corpus rather than against the table's rows. The
labels here are derived from the experiment cells, and the counts above are computed from the labels rather
than typed.

## Limit, stated rather than implied

The rule column for entries under `generated-exchanges.ndjson` carries the file-level rule rather than a
per-vector one. Six of them carry per-vector precision now because experiments were run on them, run the way
the rest of this file's were: patch one guard in `lean/Spec/Session.lean`, rebuild, run both corpora,
restore, and report exactly which steps moved. The patched file was restored byte-identical after each.

**And the limit that remains is a property of the vector's expectation rather than of the experiment.** The
corpus pins a refusal's *class* and the state it leaves, which is what the differential compares — so a
vector cannot isolate a rule when a second rule can refuse the same frame as `malformed`. The `properties`
row above is the witnessed instance: the experiment ran, the vector stayed green, and it is `broad
(witnessed)` permanently rather than as a debt, because sharpening it would mean pinning prose the
differential deliberately does not compare.

Drafted by the vector slice, whose experiments these are; reviewed, applied and committed by the planner as
`vectors/**` requires.

| `generated-exchanges` | `exchange-link-handle-in-use` | `attach/field:handle.2` | **isolated (witnessed)** | removing the guard at `Spec/Session.lean:696-699` failed **exactly this vector's step 4** and nothing else — across 278 step verdicts in `generated-exchanges.ndjson` and 29 in `slice.ndjson`, with the reference green throughout. The plan's record and the re-run agree. |
| `generated-exchanges` | `exchange-link-credit-granted-and-spent` | the credit arithmetic (`Position.creditFor`; the spend at `Spec/Session.lean:929`) | **isolated (witnessed)** | removing the credit spend failed **this vector's step 5** and one other, `exchange-link-credit-counts-messages-not-frames#7`. The plan records three failures for this experiment — the two continuation steps plus step 5. **The difference is a finding, not an error on either side**: the plan measured the pre-fix layer, where a delivery whose single transfer leaves `more` unset never incremented the delivery-count, so a second delivery was admitted free; that defect has since been fixed, and its extra failure is gone.**Re-run over the corpus at 383 step verdicts, this experiment fails four steps**: the two above plus the pair promoted today, `exchange-link-aborted-false-spends-no-credit#5` and `exchange-link-aborted-spends-the-credit#5` — the same guard carrying more witnesses rather than a change in its reach. |
| `generated-exchanges` | `exchange-link-credit-counts-messages-not-frames` | the same | **isolated (witnessed)** | the same experiment; its step 7 is the second of the two failures. |
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
| generated-exchanges.ndjson | `exchange-link-handle-out-of-range` | amqp:transport/section:link-handles | **broad (witnessed)** | the same mutant that killed the bound + 1 vector left this one green: 5 is refused by the true bound and the widened one alike |
| generated-exchanges.ndjson | `exchange-link-sender-settle-mode-unmet` | amqp:transport/section:link-handles | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-link-settled-false-under-settled-negotiation` | transfer/field:settled.4 | **isolated (witnessed)** | dropping the `settled.4` guard failed this vector's step 4 and two others — `exchange-link-sender-settle-mode-unmet#4` and `exchange-link-settled-on-a-continuation-suffices#6` — so the guard carries three steps and this vector is one of its three witnesses | |
| generated-exchanges.ndjson | `exchange-link-first-transfer-needs-its-fields` | amqp:transport/section:link-handles | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-link-detach-releases-handle` | amqp:transport/section:link-handles | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-link-disposition-direction` | amqp:transport/section:link-handles | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-link-flow-unattached-handle` | amqp:transport/section:flow-control | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-link-flow-field-without-handle` | amqp:transport/section:flow-control | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-flow-properties-without-handle` | amqp:transport/section:flow-control | **broad (witnessed)** | removing the `properties` entry from the handle-less field list left it **green**: `flowCountRefusal` refuses the same frame as `malformed` first, and the vector's expectation names only the class and the state, so a different rule satisfies it. It is not evidence for `properties.1` — what it witnessed was the reference's missing member, which admitted the frame, and that is a divergence rather than an isolation | |
| generated-exchanges.ndjson | `exchange-flow-sender-count-null` | amqp:transport/section:flow-control | **isolated (witnessed)** | disabling `flowCountRefusal`'s non-integer branch — returning `none` where it refuses — failed **exactly this vector's step 4** and nothing else, across 383 step verdicts in `generated-exchanges.ndjson` and 29 in `slice.ndjson` | |
| generated-exchanges.ndjson | `exchange-link-credit-echoed` | amqp:transport/section:flow-control | **broad** | no disabling experiment run; the label records absence of evidence rather than intent |
| generated-exchanges.ndjson | `exchange-link-aborted-false-spends-no-credit` | amqp:transport/section:flow-control | **isolated (witnessed)** | removing the credit spend failed this vector's step 5 and three others — `exchange-link-credit-granted-and-spent#5`, `exchange-link-credit-counts-messages-not-frames#7` and `exchange-link-aborted-false-spends-the-credit#5` — so the spend carries four steps and this vector is one of its four witnesses | |
| generated-exchanges.ndjson | `exchange-link-aborted-spends-the-credit` | amqp:transport/section:flow-control | **isolated (witnessed)** | removing the credit spend failed this vector's step 5 and three others — `exchange-link-credit-granted-and-spent#5`, `exchange-link-credit-counts-messages-not-frames#7` and `exchange-link-aborted-false-spends-no-credit#5` — so the spend carries four steps and this vector is one of its four witnesses | |
| generated-exchanges.ndjson | `exchange-link-more-false-completes-the-delivery` | links.29 | **isolated (witnessed)** | reading `more` by presence again failed **exactly this vector's step 5** and nothing else, over the same two corpora | |
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
