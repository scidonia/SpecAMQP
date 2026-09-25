# RECORD — the engineering log of the SpecAMQP programme

`PLAN.md` is forward-only: what to do, and what constrains doing it. This directory is
what was removed from it to make that true — the retrospective. **Nothing was cut:
every section below is the old plan's text, moved verbatim.** Each file names the old
section and line range it holds, so a citation of the old `PLAN.md` still resolves.

## What belongs here

- **Rung narratives** — what happened, in the order it happened, including the
  misdiagnoses corrected rungs later. One file per milestone or rung.
- **Design rationale** — the *argument* for a decision. The decision itself stays in
  `PLAN.md` with a one-line reason; the case for it lives here.
- **Historical numbers** — counts, gate results and rung status, which are true of the
  moment they were written. They are kept *dated, as the record of what was true then*.
  Current numbers come from `ledger/coverage.json` and the gates, never from prose —
  here or in the plan.

What does not belong here: anything prospective — scope, invariants, ownership, work
order, acceptance commands, open questions. That is the plan. If a paragraph here
becomes load-bearing for future work, the plan links to it; the text stays.

## The mapping

| old `PLAN.md` section (lines) | file |
| --- | --- |
| §1's ledger numbers and declared-surface counts (25–40) | `Ledger.md` |
| §6's ledger narrative (108–195) | `Ledger.md` |
| §10 The conformance interface (278–966) | `ConformanceInterface.md` |
| §12's second-prover deliberation (1000–1013) | `SecondProver.md` |
| §13 S0 (1020–1035) | `S0.md` |
| §13 S1 (1036–1092) | `S1.md` |
| §13 S1.5, the codec's proof ladder and the wave records (1093–1381) | `S1.5.md` |
| §13 S2 (1382–1416) | `S2.md` |
| §13 S3 (1417–1460) | `S3.md` |
| §13 S4 (1461–1494) | `S4.md` |
| §13 S5 (1495–1522) | `S5.md` |
| §13 S6 (1523–1530) | `S6.md` |
| §13 S7 (1531–1544) | `S7.md` |
| §13 H1 (1545–1547) | `H1.md` |
| §13's trailing wire-differential record (1548–1613) | `R4.md` |
| §16's working-rules narrative (1660–1935) | `WorkingAgreements.md` |
| §22's wave records (2028–2047) | `WorkingAgreements.md` |
| §23.1 The implementation track, preamble (2060–2084) | `EndpointTrack.md` |
| §23.1 R1, the transport shell (2085–2092) | `R1.md` |
| §23.1 R2, the endpoint core (2093) | `R2.md` |
| §23.1 R3, the conformance theorem (2094–2099) | `R3.md` |
| §23.1 R4, the wire differential (2100) | `R4.md` |
| §23.2 The demonstration server (2104–2121) | `R5.md` |
| §23.3 The server's remaining obligations (2122–2155) | `R5.md` |
| §23.4 The route to a real server (2156–2170) | `Framing.md` |
| §23.5 The second repository (2171–2188) | `Framing.md` |
| §24 The widening's contracts (2189–2251) | `Widening.md` |
| §26 The widened model's shape (2252–2285) | `Widening.md` |
| §27 What the tail trial found (2286–2296) | `FINDINGS.md` |

Sections the new plan keeps in an **edited** forward form — trimmed of counts, status
and narrative — have their original text in `Framing.md`: the Goal's third paragraph
(8–10), §6's rules block (94–107), §8's opening entries (224–234), §9's module note
and starting-state paragraph (259–264, 272–276), §11's vector example (971–979),
§13's preamble (1016–1019), §15's runner bullet (1638), §16's ownership lists
(1642–1652), §17's gate table (1936–1952), §19's risk register (1963–1977), §20's
acceptance block (1978–2006), §21's work order (2008–2016), §22's rules (2018–2027),
and §23's introduction (2051–2058). Two stale locations were corrected rather than
preserved: D-g's `lean/Spec/Conformance.lean` and D-i's `lean/Spec/Exec.lean`, which
the implementation folded into `Contracts/Conformance.lean` and `Spec/Main.lean` —
the fold is documented in §9's own note, preserved in `Framing.md`.

`FINDINGS.md` is the cross-cutting half: the methodological findings that recur across
rungs, quoted verbatim from the rung files with their sources named.

Citations of the old plan found in the ledger and elsewhere — "§13's D4 record",
"§23.1", "§16" — resolve through this table: D4's record is in `S1.5.md`, the
implementation track's rationale in `EndpointTrack.md`, the working rules' history in
`WorkingAgreements.md`.
