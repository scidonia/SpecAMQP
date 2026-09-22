# SpecAMQP — Advice and Recommended Direction

## Executive recommendation

SpecAMQP should remain a **specification-first project**, not turn into an implementation project.

The current architecture is already producing the right kinds of evidence:

- an executable Lean specification;
- an independently written reference artefact;
- clause-level completeness accounting;
- mutation controls;
- authored and generated corpora;
- explicit ambiguity tracking;
- separate verification tiers whose blind spots are now experimentally demonstrated.

The next work should therefore preserve that separation of concerns.

The strongest near-term recommendation is:

1. **continue S4 proof work and begin S5 messaging in parallel;**
2. **keep V3 restricted to genuinely independent third-party evidence;**
3. **leave the UTF-8 round-trip theorem explicit and conditional for now;**
4. **keep the single-link session model until messaging creates a concrete need to widen it;**
5. **do not make a socket server a SpecAMQP deliverable yet.**

The most important principle is:

> Do not spend specification effort on implementation scaffolding while major parts of the AMQP semantic surface remain unwritten.

---

# 1. Current position

SpecAMQP is already more than a prose formalization.

It has:

- executable semantics over octets;
- two independently authored artefacts answering the same vectors;
- a differential harness;
- generated and authored corpora;
- a clause ledger;
- an ambiguity register;
- proof obligations and invariants;
- mutation controls designed to test whether the verification suite can actually catch specification errors.

The central project objective should remain:

> **A complete, executable, auditable formal specification of AMQP 1.0 core whose completeness and fidelity are measurable rather than merely asserted.**

Rust implementation, extraction, and downstream implementation proofs belong elsewhere.

That separation is useful and should be preserved.

---

# 2. Recommendation on D1 — what to widen to next

## Recommendation

Choose:

> **D1(b): continue S4 proof work while starting S5 messaging in parallel.**

Do not wait for S4 to be completely closed before beginning S5.

Do not build the socket runner first.

### Why

The current S4 layer is already operational enough to support progress:

- connection/session machinery exists;
- the corpus is green;
- remaining S4 work is proof-oriented rather than a missing executable core.

At the same time, S5 is strategically important because it unlocks:

- actual AMQP message sections;
- message-bearing transfers;
- the largest remaining protocol family;
- a meaningful downstream server implementation;
- a materially richer TemperMint implementation target.

Running S5 in parallel therefore increases specification breadth without abandoning S4 correctness work.

### Guardrail

Do not allow S5 to become an excuse to leave S4 invariants permanently unfinished.

Track them as separate streams:

```text
S4-proof
S5-semantics
```

and require the S4 obligations to remain visible until closed.

### Recommended sequencing

```text
now
 ├── finish S4 preservation/invariant obligations
 └── begin S5 messaging semantics
          ↓
     message sections
          ↓
     delivery state
          ↓
     transfer / settlement semantics
```

This is preferable to inserting networking work between S4 and S5.

---

# 3. Recommendation on D2 — what counts as independent for V3

## Recommendation

Choose:

> **D2(a): third-party implementation capture only.**

Keep V3 deliberately strict.

If no genuinely independent capture exists, leave V3 empty and explicitly blocked.

### Why

The status report already demonstrates that independence cannot be inferred from language or prover choice.

The important distinction is **independent interpretation of AMQP**, not merely a second implementation of the same interpretation.

A server generated from SpecAMQP would share the same semantic reading and therefore would not provide independent fidelity evidence.

Similarly, a second formalization derived directly from the same local decisions may be a useful cross-check, but it should not automatically count as V3.

### Recommended definition

V3 evidence should come from:

```text
third-party implementation
        ↓
captured request/response exchange
        ↓
recorded immutable vector
        ↓
SpecAMQP prediction
        ↓
comparison
```

The third party should be independently authored and not generated from the SpecAMQP model.

### Optional secondary evidence

A separately authored formal model in another prover can be useful, but classify it separately, for example:

```text
V3b — independent formal cross-model
```

Do not silently broaden V3 to include it.

### Why strictness matters

The project has already shown that two internally independent artefacts can share the same omission.

Therefore V3 must remain the tier that tests something neither local artefact can validate:

> whether the model agrees with independent protocol behaviour in the world.

---

# 4. Recommendation on D3 — the UTF-8 round-trip lemma

## Recommendation

Choose:

> **D3(b): keep the law conditional on the missing UTF-8 lemma.**

Do not turn this into a separate UTF-8 formalization project now.

### Why

The current situation is already honest:

- the higher-level law is assembled;
- exactly one missing lemma is named;
- the missing lemma is external to the interesting AMQP reasoning;
- the absence has been measured rather than guessed;
- nothing else is blocked.

That is an acceptable proof boundary.

### Recommended representation

Keep the theorem explicitly parameterized by the exact UTF-8 round-trip fact the development needs.

Classify it as an external or conditional premise until a library theorem is available.

### Secondary action

D3(c), upstreaming the lemma, is worthwhile only if it is cheap.

Treat that as library improvement, not programme-critical work.

### Do not

Do not reimplement a substantial UTF-8 proof stack merely to remove one explicit premise from the AMQP development.

That would be poor allocation of proof effort unless the same lemma becomes broadly load-bearing across later AMQP layers.

---

# 5. Recommendation on D4 — the single-link session model

## Recommendation

Choose:

> **D4(a): keep the one-link session model for now.**

Revisit it when S5 gives a concrete semantic reason to require multiple links.

### Why

The present model makes some clauses vacuous, particularly uniqueness properties.

That is not ideal, but widening the model pre-emptively would add substantial state-space and proof cost without a demonstrated use case.

The more disciplined approach is:

> widen only when a real protocol slice requires the additional state.

S5 is likely to provide that pressure naturally.

### Required safeguard

The one-link restriction must remain explicit.

Do not let the current model imply:

> AMQP sessions are intrinsically single-link.

Instead record:

```text
MODEL RESTRICTION:
current S4 slice contains at most one link per session.
```

and identify which clauses are:

- fully modeled;
- vacuous under this restriction;
- deferred until a registry exists.

### Trigger for widening

Move to a link registry when one of the following becomes concrete:

- multiple simultaneous deliveries;
- link-handle uniqueness becomes semantically active;
- routing between multiple links matters;
- settlement state must be tracked independently per link;
- a normative S5 clause cannot be faithfully represented by the one-link model.

At that point, widening becomes evidence-driven rather than speculative.

---

# 6. Recommendation on D5 — whether to build a server

## Recommendation

Choose:

> **D5(a): do not make a server a current deliverable.**

A socket runner may be useful later as a smoke consumer, but it should remain explicitly outside the specification deliverable.

### Why

The current specification already has a clean abstraction boundary:

```text
octets
  ↓
decode
  ↓
submission
  ↓
step
  ↓
response + octets to write
```

A network server adds:

- socket ownership;
- listener lifecycle;
- connection multiplexing;
- transport buffering;
- scheduling;
- time;
- timeout policy;
- operational error handling.

None of those materially improve the formal completeness of the AMQP semantics.

They instead create a new implementation project.

### Current limitation

Without S5, such a server would also be semantically incomplete:

- it can negotiate connections;
- create sessions and links;
- transfer frames;
- but cannot yet interpret message bodies.

So building the server now would demonstrate less than it appears to.

### Good future use

After S5, a small socket runner could be worthwhile for:

- exercising the runner interface over a real socket;
- smoke-testing interoperation;
- demonstrating end-to-end consumability of the spec;
- generating local implementation traffic.

But classify it as:

```text
consumer / demonstration
```

not:

```text
formal fidelity evidence
```

and not:

```text
V3
```

---

# 7. Advice on the verification architecture

The present V1–V4 architecture should be retained.

Its strongest finding is that different instruments have different blindness.

The project should continue to preserve that independence.

## V1 — proof/invariant layer

Use for:

- state preservation;
- algebraic laws;
- quantities maintained internally;
- unreachable-state reasoning;
- properties vectors cannot witness.

## V2 — discrimination

Use corpora to prove that executable semantics distinguishes valid from invalid cases.

Mutation testing should continue here.

## V3 — reality check

Keep external and authorship-independent.

Do not replace it with another local model.

## V4 — verification of the verifier

Continue planting deliberate specification defects and requiring the suite to catch them.

This is unusually valuable and should remain part of the programme rather than being treated as temporary scaffolding.

---

# 8. Strengthen the clause-ledger discipline

The clause ledger is one of the strongest architectural decisions in the project.

Continue to require every normative clause to be classified explicitly.

Useful dispositions should remain distinguishable, for example:

```text
formalized
tested
invariant
assumed
deferred
out-of-scope
ambiguous
unreachable
```

Avoid a generic `covered` category.

The recent defects show why: a vector can appear to cover a rule while actually being rejected by a neighbouring rule.

Coverage must therefore state **how** the clause is witnessed.

---

# 9. Preserve the isolation rule for vectors

The isolation rule should become a permanent test-design requirement:

> A negative vector counts as evidence for rule R only if disabling R causes the vector to stop failing for R's reason.

This is much stronger than merely observing a rejection.

Continue requiring each important negative vector to demonstrate that the intended condition is causally responsible.

Where that is impractical, classify the vector as broad conformance evidence rather than rule-isolated evidence.

---

# 10. Keep specification mutations central

The mutation results are particularly important.

Two specification mutations survived the original suite, demonstrating that the suite itself had blind spots.

That is exactly the purpose of V4.

Recommendation:

For every major new semantic layer, require at least:

```text
1 structural mutation
1 semantic boundary mutation
1 omission mutation
1 acceptance/rejection polarity mutation
```

Examples:

- remove a MUST;
- invert a comparison;
- make a mandatory transition optional;
- accept a forbidden frame;
- reject a required frame;
- alter a state assignment.

The point is not mutation count.

The point is to continually ask:

> what class of wrong specification would our current evidence fail to notice?

---

# 11. Treat unread quantities explicitly

The report identifies state values that are maintained but not consulted by any rule.

Those cannot be validated adequately by behavioural vectors.

Continue to mark them explicitly and bind them to invariants where possible.

Do not pretend corpus coverage can validate a quantity that has no effect on observable behaviour.

For each such field, classify it as:

```text
maintained and invariant-checked
maintained but currently semantically inert
deferred semantic use
candidate for removal
```

That prevents dead semantic state from accumulating unnoticed.

---

# 12. Keep the executable spec transport-free

The architecture should preserve this boundary:

```text
transport
   ↓
octet stream
   ↓
SpecAMQP executable semantics
```

rather than:

```text
socket semantics embedded in SpecAMQP
```

The formal specification should define AMQP protocol behaviour, not OS networking behaviour.

This gives downstream consumers freedom to use:

- synchronous sockets;
- async runtimes;
- Rust;
- C;
- test harnesses;
- recorded traces;
- formally verified implementations.

The executable spec remains the semantic authority without becoming an operating system model.

---

# 13. Recommended near-term roadmap

## Track A — finish S4 proof obligations

Close:

- remaining credit-law branches;
- session invariants;
- named preservation obligations.

Do not let these disappear behind S5 activity.

## Track B — start S5 messaging

Prioritize the smallest message-bearing vertical slice:

```text
message sections
      ↓
transfer payload
      ↓
delivery state
      ↓
settlement
```

Aim first for executable semantics and corpus coverage, then proof strengthening.

## Track C — continue V4 mutation work

For each new S5 slice, plant representative semantic mutations.

## Track D — obtain real V3 evidence

Search for or coordinate with an independently authored implementation and commit recorded vectors.

This can proceed opportunistically without blocking S5.

## Track E — keep the UTF-8 theorem conditional

Do not allocate major effort unless later layers make the lemma broadly valuable.

---

# 14. Relationship to TemperMint

The division between SpecAMQP and TemperMint should remain strict.

## SpecAMQP owns

```text
protocol semantics
normative clause interpretation
executable reference semantics
proofs about the specification
corpora
mutation controls
ambiguity ledger
```

## TemperMint owns

```text
Rust implementation
Aeneas/Charon translation
implementation refinement proofs
implementation certificates
native build binding
performance
```

The handoff boundary should be explicit and versioned.

TemperMint should consume stable SpecAMQP interfaces rather than duplicate protocol interpretation.

That gives the programme a clean architecture:

```text
AMQP standard
     ↓
 SpecAMQP
     ↓
formal executable contract
     ↓
 TemperMint
     ↓
certified Rust implementation
```

---

# 15. What not to do

Do not:

- block S5 on finishing every S4 theorem;
- broaden V3 until it loses authorship independence;
- turn one missing UTF-8 lemma into a major subproject;
- generalize to multi-link sessions before a real protocol slice requires it;
- build sockets into the formal specification;
- treat a SpecAMQP-derived server as third-party evidence;
- trust differential agreement as sufficient fidelity evidence;
- count a rejection vector without isolating the rule causing rejection;
- let maintained-but-unused state masquerade as behaviourally tested;
- replace the clause ledger with coarse coverage counts.

---

# 16. Decision summary

| Decision | Recommendation |
|---|---|
| **D1 — next widening** | **Start S5 alongside finishing S4 proofs** |
| **D2 — V3 independence** | **Third-party capture only** |
| **D3 — UTF-8 lemma** | **Keep explicit conditional hypothesis; optionally upstream later** |
| **D4 — single-link session** | **Keep for now; widen only when S5 requires it** |
| **D5 — server** | **Not a current deliverable; optional smoke runner after S5** |

---

# 17. Final recommendation

The project should optimize for:

> **semantic completeness, auditability, and independent falsification of the specification.**

It should not optimize yet for:

> demonstrating a production server.

The most valuable next expansion is S5 messaging because it increases the expressive completeness of the formal model and unlocks meaningful downstream implementations without contaminating SpecAMQP with implementation concerns.

The architecture is strongest when each layer does one job:

```text
standard
   ↓
SpecAMQP
   ↓
executable formal contract
   ↓
TemperMint / other implementations
   ↓
implementation refinement
```

Maintain that separation while expanding the formal AMQP surface.
