# V4: specification-mutation controls

Method for every mutant: the tier **declared before the run**, the mutant planted as a text
patch, the build shown with its job count, the tier run, the diagnostic quoted verbatim, the
revert by text, and the tier run again as the revert's own check. No snapshot restores: a `cp`
restore reinstates whatever it captured, which is a state nobody chose.

The plan's rule this produced: **a mutation run is a quiet window**, announced with its start
and end, with the diff as the record — and it is symmetric, so a *measurement* run is a quiet
window too, and a mutant waits for it, because otherwise the numbers being published describe a
tree nobody chose.

| # | mutant | declared tier | actually caught by | diagnostic | verdict |
|---|---|---|---|---|---|
| 6 | `decide` → `sorry` in `reservedCodes_eq`, `Spec/Value.lean:79` | proof integrity | **the declared tier** | `trust: Spec/Value.lean:79: sorry` / `FAIL: the specification contains trust-bearing constructs`, 36 modules scanned | killed; build 3 jobs, Lean warned (a warning, not a gate) |
| 3 | `begin`'s descriptor 17 → 18, `Generated/Oasis/Types.lean` | table fidelity | **the declared tier** | `committed tables differ from a fresh generation: Types.lean: committed copy differs from a fresh generation (regenerate with scripts/gen-oasis-lean.py)` | killed; build 34 jobs — the compiler cannot see it, which is the point |
| 4 | `uint` written in the wide row always, `Spec/Codec.lean:763` | the differential | **the declared tier** | `amqp-spec did not pass primitives.ndjson: 20 vector(s), 2 failure(s)` | killed; build 51 jobs |
| 1 | `linkHandleOf`'s body removed, `Spec/Session.lean:543` | the differential, then the sweep | **the sweep only** | the differential PASSED (68,120 vectors, identical verdicts); the sweep: 29 divergences, 21 of them the signature (14 where the spec admits and the reference refuses with `amqp:session:unattached-handle`, 7 where another rule answers) | **survivor of the differential, killed by the sweep** |
| 5 | `channel ≤ channelMax` → `+ 1`, `Spec/Connection.lean:1057` | the differential, then the connection sweep | **nothing, until the vector landed** | first run: the differential PASSED and the connection sweep's 146 probes use channels 0 and 1 only. Second run, with `driven-channel-above-the-declared-bound` added: `ref refused / limit / OPENED / amqp:connection:framing-error` against `spec admitted / UNMAPPED` — **killed by the new vector** | **survivor, then closed** — and now `exchange-session-channel-above-the-declared-bound` carries it in the corpus |
| 2 | the sent transfer's window spend removed, `Spec/Session.lean:294` | the differential, then the sweep | **nothing** | the differential PASSED — the link's credit answers those vectors first; the sweep's buckets identical to the baseline, because its sent-window cells are *observations* | **survivor** — the repair is `exchange-session-window-spent-by-sent-transfers`, proven passing in both artefacts; its kill of this mutant is reasoned rather than witnessed, since the mutant's window is closed |

## The two suite defects, with their repairs

1. **A bound widened by one is visible only at exactly bound + 1.** The channel rule at
   `Spec/Connection.lean:1057` was exercised on its admitting side and never on its refusing
   side; a frame further above the bound is refused by the true bound and the widened one alike.
   `exchange-session-channel-above-the-declared-bound` is the vector: an `open` declaring
   `channel-max` 1, the peer's answering open, then a frame on channel 2. Proven passing in both
   artefacts, and it kills the mutant that survived every tier.

2. **A rule whose refusal another rule answers first is invisible.** The sent-window spend was
   hidden by the link's credit, which refuses the same vectors. The repair shapes the vector so
   the credit cannot answer: the peer's flow sets the remote window to one transfer *and*
   grants credit of ten, so the second transfer is refused by the window.
   `exchange-session-window-spent-by-sent-transfers`, proven passing in both artefacts.

## Suite-shape findings

- `linkHandleOf` is one function shared by flow, transfer and detach, so a mutation of it needs
  a vector *per performative*. The flow vector exists and did not kill it either: the
  differential compares the two artefacts' answers, and the refusal the mutation removed was not
  the one being produced.
- The corpus's `handle-max` range vector declares 2 and attaches 5. That kills a runaway bound
  but **not a bound widened by one**, since 5 is refused by both. Only bound + 1 distinguishes
  them.

## Bound-boundary audit

For every bound the specification states, the vector at exactly one step outside it, or none:

| bound | status |
|---|---|
| `channel-max` declared by the open | **MISSING**, vector landed above |
| `max-frame-size` declared by the open | **MISSING** |
| MIN-MAX-FRAME-SIZE, an open declaring below 512 | **MISSING** |
| `handle-max` declared by the begin | MISSING at bound + 1 (the corpus tests further above) |
| `arrayElementLimit` | unresolved, not missing: my test is crude and 65537 elements are impractical to express |
| `channel-max` a priori (before any open) | have — `generated-exchanges.ndjson:9`, a frame on channel 256 with no open |
| the `256^width` length ceilings | have — `generated.ndjson:125`, a 256-octet payload |

## Discarded runs

Two of mutant 1's plants were malformed — an unreachable-code early return and a comment inside a
structure record — and both produced failed builds, so those runs are not counted. A mutation that
does not build is not a mutation run.
