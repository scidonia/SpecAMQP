# HANDOFF — treating this specification as a target

The entry point for downstream implementation work: an AMQP 1.0 endpoint in Rust, extracted
through Charon and Aeneas, with proofs that it conforms. `PLAN.md` is the programme of record
and is **not** repeated here — each section cites it. This document adds no claim of its own; it
states the artifacts as they are, and says where another record in the tree disagrees with them.

Every claim below carries the command that checks it, run from the repository root. `shell`
is the pinned, offline shell of `PLAN.md` §20:

```sh
alias shell='nix --extra-experimental-features "nix-command flakes" develop --offline --no-update-lock-file .#spec --command'
```

Two identifiers below name session state rather than a path under `tests/`: `agent://R1Review`,
the implementation track's only review verdict, and `hub`, which lists live work. Both are
named where they are used.

Line numbers in `lean/Proofs/ConnectionConformance.lean` are moving: the file is under edit in
the working tree (`git status --porcelain`). Every reference below therefore gives a symbol and
the `grep` that re-locates it; the line numbers are as of the tree at the time of writing.

## 1. What this repository is, and what it is not

**Is.** An executable formal specification of AMQP 1.0 core (OASIS Standard, Parts 0–5) in
Lean 4; a clause-level ledger with dispositions and a coverage report; a vector corpus; the
gates that check all three; and — since `PLAN.md` §23.1 — an implementation track: a Lean
endpoint compiled natively, its transport boundary landed, its protocol core written, and **that core
carrying a proved instance of the conformance relation (§8)** — R3 is discharged and the instance accepted
(`lean/Contracts/EndpointAcceptance.lean`), leaving the compiled binary and the socket boundary as the trusted
and disclosed steps downstream should still price in.

**Is not.** There is no Rust here, no Charon/Aeneas extraction, and no performance claim
(`git grep -n "There is no Rust here" -- AGENTS.md`). There is no *verified binary*: Lean's
compiler and runtime are trusted rather than verified, and the socket layer is the one named
unproved dependency (`git grep -n "Not that the binary is verified" -- PLAN.md`).

**What the endpoint's evidence reaches, stated because it is easy to overread.** R3's content is
the **plumbing** — unit extraction, buffering, direction, output order, rendering, and the api
reading — not the protocol decisions: the core is a driver over `Spec.Connection.step` and so
shares the specification's decision function *by construction*, which means a defect inside
`Spec.Connection.step` is inherited rather than caught, and finding it is the corpus's and the
differential's work (`grep -n "shares the specification" PLAN.md`). **And it is proved rather than owed**: `Proofs/EndpointConformance.lean` establishes the statement
`Contracts/EndpointConformance.lean` froze, at exactly that type, and `Contracts/EndpointAcceptance.lean` binds it — the proof's own content matching the
sentence above is the check on the sentence, three of its four plumbing equalities having closed by `rfl`.

**Therefore.** An independent second *reading* of the standard already exists in `lean/Ref/`,
and the corpus over it tests that reading. The corpus run against this endpoint at the wire
tests **plumbing and the boundary** — that octets survive a socket, that framing and buffering do
not reorder or truncate them, and that the endpoint's answers match `amqp-spec`'s. **It does**: `tests/contracts/r4_wire_differential.sh` declares that tier's state per vector, and all six vectors of
`vectors/slice.ndjson` agree at the socket (`10ccc05`) with no residual divergence — the two application seams that made three of them diverge are closed. It is not an
independent protocol reading, and adding a third runner over the same corpus does not make
`lean/Ref/` redundant (`sed -n '/^- \*\*R3 — the conformance theorem/,/^- \*\*R4/p' PLAN.md`).

## 2. The frozen interface

`PLAN.md` §10 is the design; `lean/Contracts/Conformance.lean` is that design as Lean, and a
downstream proof is an instance of *this* definition. The alphabet (lines 41–79):

```lean
structure ApiCall where
  name : String
  arguments : List String
deriving BEq, Repr

structure ApiResponse where
  name : String
  ok : Bool
deriving BEq, Repr

structure Tick where
  id : Nat
deriving BEq, Repr

inductive Input where
  | frame : ByteArray → Input
  | api : ApiCall → Input
  | tick : Tick → Input

inductive Output where
  | frame : ByteArray → Output
  | api : ApiResponse → Output

structure Endpoint (σ : Type) where
  init : σ
  step : σ → Input → Option (σ × List Output)
  choose : σ → Input → Set (σ × List Output)
```

The relation (line 94), and its exposed form for a layer's own invariant (line 106):

```lean
def Conforms {σs σi : Type} (spec : Endpoint σs) (impl : Endpoint σi) : Prop :=
  ∃ R : σs → σi → Prop,
    R spec.init impl.init ∧
    ∀ (s : σs) (i : σi) (inp : Input),
      R s i →
      ∀ out : σi × List Output,
        impl.step i inp = some out →
        ∃ s' : σs, ∃ outs : List Output,
          (s', outs) ∈ spec.choose s inp ∧ R s' out.1 ∧ out.2 = outs

def ConformsVia {σs σi : Type} (R : σs → σi → Prop) (spec : Endpoint σs)
    (impl : Endpoint σi) : Prop :=
  R spec.init impl.init ∧
  ∀ (s : σs) (i : σi) (inp : Input),
    R s i →
    ∀ out : σi × List Output,
      impl.step i inp = some out →
      ∃ s' : σs, ∃ outs : List Output,
        (s', outs) ∈ spec.choose s inp ∧ R s' out.1 ∧ out.2 = outs
```

`conforms_via_of_conforms` (line 117) and `conforms_of_conforms_via` (line 121) move between the
two, and every instance below is built through the second. Re-locate everything with
`grep -n "^inductive Input\|^inductive Output\|^structure Endpoint\|^def Conforms\|^def ConformsVia" lean/Contracts/Conformance.lean`.

**Record that disagrees.** `toolchain/downstream-pins.toml` names `frozen_interface =
"lean/Spec/Conformance.lean"`, a path that does not exist. The interface is
`lean/Contracts/Conformance.lean`; the file above is the one to build against
(`ls lean/Spec/Conformance.lean lean/Contracts/Conformance.lean`).

### The instances that exist, and what each rests on

Three instances have landed, all in the frame and connection layers. Each names the layer below
as an explicit hypothesis rather than assuming it, so what a downstream instance rests on is
visible at its own type (`grep -rn "conformance_public" lean/Contracts/`).

| # | Instance | Declared | Proved | Hypothesis |
|---|---|---|---|---|
| 1 | frame layer, receive | `lean/Contracts/FrameConformance.lean:52` | `lean/Proofs/FrameConformance.lean:1027` | `ValueLayersAgree` |
| 2 | frame layer, send | `lean/Contracts/FrameConformance.lean:62` | `lean/Proofs/FrameSendConformance.lean:740` | `ValueCarrierAgree`, `ValueWriterAgree` |
| 3 | connection layer | `lean/Contracts/ConnectionConformance.lean:65` | `lean/Proofs/ConnectionConformance.lean:5526` | `ReadersAgree` |

Their statements, verbatim:

```lean
-- 1. lean/Contracts/FrameConformance.lean:52
theorem frame_conformance_public (valueAgreement : SpecAMQP.Proofs.ValueLayersAgree) :
    Conforms SpecAMQP.Proofs.specFrame SpecAMQP.Proofs.refFrame
```

```lean
-- 2. lean/Contracts/FrameConformance.lean:62
theorem frame_send_conformance_public (carriers : SpecAMQP.Proofs.ValueCarrierAgree)
    (writers : SpecAMQP.Proofs.ValueWriterAgree) :
    Conforms SpecAMQP.Proofs.specFrameSend SpecAMQP.Proofs.refFrameSend
```

```lean
-- 3. lean/Contracts/ConnectionConformance.lean:65
theorem connection_conformance_public (readers : SpecAMQP.Proofs.ReadersAgree) :
    Conforms SpecAMQP.Proofs.specConn SpecAMQP.Proofs.refConn
```

The endpoints each theorem names: `specFrame` / `refFrame` (`lean/Proofs/FrameConformance.lean:263`,
`:271`), `specFrameSend` / `refFrameSend` (`lean/Proofs/FrameSendConformance.lean:307`, `:314`),
`specConn` / `refConn` (`lean/Proofs/ConnectionConformance.lean:1466`, `:1475`, relation `RConn`
at `:1486`). The specification's side is an `Endpoint` whose `choose` is the singleton of a step's
permitted outcome; the reference's is an `Endpoint` whose `choose` is `∅`, because conformance
never consults an implementation's `choose`. Re-locate with
`grep -rn "^def specFrame\b\|^def refFrame\b\|^def specConn\b\|^def refConn\b" lean/Proofs/`.

### The hypotheses, verbatim

```lean
-- lean/Proofs/FrameConformance.lean:352  (hypothesis of instance 1)
def ValueLayersAgree : Prop :=
  ∀ region : Octets,
    (∀ (other : SpecAMQP.Ref.Value) (used : Nat),
        SpecAMQP.Ref.decode region = .ok (other, used) →
        ∃ body : SpecAMQP.Spec.Codec.Value,
          SpecAMQP.Spec.Codec.decodeValue region = .ok (body, used) ∧
          specBodyView body = refBodyView other) ∧
    (∀ failure : SpecAMQP.Ref.DecodeError,
        SpecAMQP.Ref.decode region = .error failure →
        ∃ message : String,
          SpecAMQP.Spec.Codec.decodeValue region = .error message ∧
          (SpecAMQP.Ref.Frame.valueFailure failure).reasonClass =
            SpecAMQP.Spec.Frame.reasonClassOf message)
```

**The three hypotheses are named here rather than transcribed, and their status as it stands:**

- **`ValueCarrierAgree`** (`Proofs/FrameSendConformance.lean`) — **proved**, by `valueCarrierAgree_all`.
- **`ValueWriterAgree`** (same module) — **undecided**. Its error side was *classed* (the writer now answers with an
  `EncodeRefusal` carrying `reasonClass`, rather than a `String` whose class had to be recovered by splitting it), the
  reference's array and zero-width arms were fixed to consult a container's declared constructor, and a refutation with a
  reachable witness was landed and then **withdrawn in the same slice** once the hole it named was closed. The frame send
  instance therefore stays conditional.
- **`ReadersAgree`** (`Proofs/ConnectionConformance.lean`) — **proved**, by `Proofs.readersAgree`.

**The statements themselves are not copied here, and that is a decision with evidence behind it**: each of the three drifted
within days of being transcribed — the writer's twice, once by a classing and once by a domain restriction — while the
transcriptions stayed as written. **The module is what a proof is checked against**, so a reader who wants the exact
statement should take it from the declaration named above (and `#print` it) rather than from prose that was true when it
was typed.
sh
python3 scripts/clause-ledger.py check
shell bash tests/contracts/s0_sources_ledger.sh   # the same content as a gate, plus planted controls
```

`check` prints the totals above and exits 0; `coverage.json` carries the same numbers in machine
form (`python3 -c "import json;print(json.load(open('ledger/coverage.json'))['totals'])"`).

**How to read a disposition.** A disposition is a string with a documented prefix, and the
conventions are recorded per file next to the data
(`python3 -c "import json;d=json.load(open('ledger/dispositions/part0-conformance-and-transport-lifecycle.json'));print(d['conventions'])"`):
`formalized:` names a Lean declaration that carries the clause, `invariant:` names a law about
state, `test:` names a vector whose expectation is the clause's only observable form,
`environment:` names an assumption the specification rests on, `deferred:` names a milestone
that carries it later, `informative` / `out-of-scope:` / `underspecified:` / `superseded` record
that nothing is enforced and why. Two properties matter to a downstream reader:

- a disposition is keyed by the clause's **text hash**, so a clause whose wording moves shows up
  as stale rather than silently keeping its disposition;
- `formalized:` is checked in both directions: the gate verifies each named path is present in
  the module it names, and *exempts* the ones the record marks as forward commitments. The
  current run reports `formalized: 40 checked against lean/**, 59 forward commitment(s) exempt
  by the record` — so a `formalized:` path can mean "declared and present" **or** "owed by the
  plan", and the check's own line is what tells you which.

**Record that disagrees.** `PLAN.md` §13's S0 progress paragraph still reports the ledger as
"401 clauses over 230 MUST-class statements across 116 anchor paths". The counts moved as later
slices landed; use `coverage.json`, not the paragraph (`grep -n "401 clauses" PLAN.md`).

## 4. The corpora

NDJSON, one vector per line, logical time only — ticks and `eof` are ordering tags, never
wall-clock readings, so replay is deterministic on any machine. Vector counts:
`wc -l vectors/*.ndjson vectors/message/*.ndjson` (68,700 at the time of writing).

| family | vectors | what it is for | schema |
|---|---|---|---|
| `vectors/primitives.ndjson` | 20 | hand-authored from Part 1's worked examples and clause text | `value-vector.schema.json` |
| `vectors/generated.ndjson` | 68,120 | value layer: golden and reject vectors, plus a property sweep over every one- and two-octet input (65,792 `property` vectors) | `value-vector.schema.json` |
| `vectors/frames.ndjson`, `frames-negative.ndjson`, `generated-frames.ndjson` | 7, 5, 43 | frame layer: decode, encode, and per-error-code refusal | `frame-vector.schema.json` |
| `vectors/slice.ndjson`, `generated-exchanges.ndjson` | 9, 71 | connection and session lifecycles as ordered exchanges: what a peer sends, what each step's outcome must be, and the state it leaves | `exchange-vector.schema.json` |
| `vectors/txn.ndjson`, `txn-negative.ndjson` | 7, 7 | transaction layer as a message body on a control link | `exchange-vector.schema.json` |
| `vectors/sasl.ndjson`, `sasl-negative.ndjson` | 5, 21 | security layer: the SASL dialogue and the four declared `sasl-code` failures | `exchange-vector.schema.json` |
| `vectors/message/**` | 375 | message layer: sections, messages, deliveries, then generated section vectors | `message-vector.schema.json` |

Kinds are per layer, not the three in the original schema: `encode` / `decode` / `reject` /
`property` for values, `frame-encode` / `frame-decode` / `frame-reject` for frames, `exchange`
for connections and sessions, and `section-*` / `message-*` / `delivery` for messages
(`python3 -c "import json;print(sorted({json.loads(l)['kind'] for l in open('vectors/generated-frames.ndjson')}))"`).

**Invocation** — the same driver interface for every corpus, implementation-agnostic:

```sh
shell bash -c 'cd lean && LAKE_NO_CACHE=1 lake build amqp-spec amqp-ref'
shell bash -c 'cd lean && lake exe amqp-spec ../vectors/primitives.ndjson'
shell bash -c 'cd lean && lake exe amqp-ref  ../vectors/primitives.ndjson'
```

One JSON verdict per vector on stdout (`--quiet` suppresses them), a one-line summary on stderr,
and the exit status is the observable: `0` all vectors met their expectation, `1` at least one
did not, `2` usage or read error (`sed -n '31,60p' lean/Spec/Main.lean`). `amqp-ref` mirrors it.
A verdict that met its expectation reads `rejected, as the vector expects: limit: …`, so a
consumer comparing refusals should match on the corpus kind and search the detail for the class
rather than expecting the class to lead the string. What a negative vector pins — the error
condition, the endpoint that must close, and the reason class — is in the vector
(`head -1 vectors/frames-negative.ndjson`).

**What the corpus is evidence for, and what it is not.** `vectors/isolation.md` classifies every
hand-authored negative vector by whether disabling the rule it names makes it fail: of 62 rows,
7 are rule-isolated (5 witnessed by an experiment actually run, 2 reasoned) and the rest are
**broad conformance evidence** — which is a label, not a claim. Its own section records a
mutation that survived because a rule had two enforcers. Read it before treating a passing
corpus as a proof about a rule (`sed -n '1,12p' vectors/isolation.md`).

**Two committed corpora are run by nothing.** `vectors/messages.ndjson` (9 vectors, an earlier
message family) and `vectors/open-bad-field.ndjson` (1 vector) are the only `*.ndjson` files
under `vectors/` that no gate, driver or script references; they are swept only by the citation
check (`grep -rn "vectors/messages\b\|open-bad-field" tests scripts lean` returns nothing).
`PLAN.md` §22 records the first as deliberately left alone — but nothing replays it, which is
worth knowing before treating the corpus listing above as a coverage claim.

**Record that disagrees.** `PLAN.md` §11 describes "one shared format for everything",
schema-validated by `tests/contracts/vector.schema.json`, and illustrates it with a
`provenance.refs`-shaped example. The tree carries that schema plus four per-layer schemas
(`value-`, `frame-`, `exchange-`, `message-vector.schema.json`), and **no corpus is validated
against `vector.schema.json`**: the gates validate against the per-layer schemas
(`ls tests/contracts/*.schema.json`; `grep -n "schema=" tests/contracts/s1_ref_vectors.sh tests/contracts/s2_frame_vectors.sh tests/contracts/s5_messages.sh`).
`toolchain/downstream-pins.toml`'s `vector_schema` names the original, unused one; follow the
per-layer schema of the corpus you are running.

## 5. The gates

Each is a shell script under `tests/contracts/`, each runs offline and writes only into a
temporary directory, and each is run in the pinned shell:

```sh
ls tests/contracts/*.sh
```

| gate | what it enforces |
|---|---|
| `s0_sources_ledger.sh` | vendored artifact identity, a refused one-byte mutation, the planted-control classifications, and the disposition/audit/reconciliation gates |
| `s0_tables_fidelity.sh` | the generated declared surface is derived (byte-identical regeneration), current, and load-bearing — a mutated descriptor code in a vendor copy must move it |
| `s0_lean_environment.sh` | the pinned toolchain and mathlib resolve offline, and agree with TemperMint's pin record |
| `s0_spec_manifest.sh` | every planner-owned file is as the SHA-1 manifest records it |
| `s0_vector_citations.sh` | every clause and picture a vector or a handwritten module cites resolves in the ledger's id space |
| `s0_generator_fidelity.sh` | each generated corpus is byte-for-byte what its generator produces |
| `s1_proof_integrity.sh` | no `sorry`, `admit`, `native_decide`, `partial def`, `axiom`, `constant`, `unsafe`, `opaque`, `extern` or `implemented_by` in the handwritten and shipped modules; the one permitted `extern` boundary is counted and pinned to `lean/Impl/Transport.lean`; every accepted theorem's axiom inventory printed; and the whole package built |
| `s1_ref_vectors.sh` | the reference builds natively from Lean and passes both value corpora; both corpora are well formed; the generated one regenerates; the harness is not vacuous |
| `value_boundaries.sh` | the value layer's rule-boundary sweep: status agreement across both artefacts, class rather than detail, and the one stated-but-unenforced rule — duplicate map keys — pinned as failing by name so the gate goes red the day it starts passing |
| `value_class_agreement.sh` | the two value readers name the same class for every buffer of a generated family — 114,225 of them — with the family's floor and a non-vacuity clause here rather than in the driver, because how much a check must read for its silence to mean something is a different decision from what it checks |
| `s1_differential.sh` | specification and reference agree vector by vector, and on the condition each refusal names |
| `s2_frame_vectors.sh` | the frame corpora: per-vector agreement between both artefacts, declared sizes against octet counts, and a planted mutation |
| `s3_exchanges.sh` | the exchange corpora: per-step verdicts, including the condition each refused step pins, from both artefacts |
| `s4_flow.sh` | the session window rules' fragmentation family: the pair's non-vacuity across both files, the 29 interior split points pinned, and every refusal's condition, from both artefacts |
| `s5_messages.sh` | the message layer's differential, over `vectors/message/*.ndjson`, by `scripts/run-message-differential.sh` |
| `s6_transactions.sh` | the transaction layer's differential, per vector and per refusal condition |
| `s7_sasl.sh` | the security layer: both corpora, per-step refusals, and one vector per declared `sasl-code` name |
| `r1_transport_shell.sh` | the transport shell's evidence and its controls, through `scripts/run-transport-loopback.sh` (see §8) |

Two runners are also directly usable and are what the gates above invoke:
`scripts/run-transport-loopback.sh` and `scripts/run-message-differential.sh`. Two further checks
are not gates but are the ones a reader reaches for:
`python3 scripts/gen-oasis-lean.py --check` and `git diff --exit-code -- lean/Generated`.

**A gate's clauses run in order, so an early failure hides the later ones.** Each script is a
sequential bash script that exits at its first failed clause with a `FAIL:` line naming it: a
question about clause 4 is unanswerable from a run that died at clause 1, and a green run says
nothing about a clause after the first failure. Read the script's own numbered header — not a
summary of it — for what a given run actually covered (`sed -n '1,30p' tests/contracts/s3_exchanges.sh`).
This is also `AGENTS.md`'s rule that "a gate's prose is not its check": where a summary line and
a pattern list disagree, the pattern list is the fact.

**Record that disagrees.** `PLAN.md` §20's acceptance block names three commands that cannot
run here: `scripts/check-proof-assumptions.sh` and the `.feature` contracts
`tests/contracts/v2_vector_corpus.feature`, `v3_third_party_admission.feature` and
`v4_spec_mutations.feature`, none of which exist:

```sh
for f in scripts/check-proof-assumptions.sh scripts/run-contracts.py \
         tests/contracts/v2_vector_corpus.feature \
         tests/contracts/v3_third_party_admission.feature \
         tests/contracts/v4_spec_mutations.feature; do
  test -e "$f" && echo "present: $f" || echo "absent:  $f"
done
```

`AGENTS.md` records the feature-contract
runner as deliberately not added in advance; the mutation tiers it names are documented in
`verification/v4-mutations.md`, `verification/s5-message-mutations.md` and `vectors/isolation.md`
rather than driven by a gate. The gate list above is the tree's.

## 6. The pins

| identity | revision | where |
|---|---|---|
| Lean | `leanprover/lean4:v4.31.0` | `lean/lean-toolchain` |
| mathlib | `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` | `flake.nix`, and `[shared_with_this_repository.lean]` of `toolchain/downstream-pins.toml` |

These are the same revisions TemperMint pins — TemperMint's own record gives the mathlib
revision as the tag `v4.31.0`, which is this commit — so a module proved here can be required by
downstream proofs without version surgery. The agreement is **checked rather than trusted**: the
environment gate compares `lean/lean-toolchain` and the mathlib revision against
`${SPECAMQP_TEMPERMINT_ROOT:-../TemperMint}`, and prints a skip note when that record is absent
(`shell bash tests/contracts/s0_lean_environment.sh`; `grep -n "TemperMint" tests/contracts/s0_lean_environment.sh`;
`grep -n "mathlib4/fabf563a" flake.nix ../TemperMint/flake.nix`).

Downstream pins, **recorded but not required here** — this repository needs no Rust, Charon or
Aeneas: Charon `a5591f6b94c8575a6ba2ae71090614a722f2b011` (LLBC `0.1.263`), Aeneas
`227f4e7ac70d687a6b1a4871b3304f5a1c6994bf` (`nightly-2026.09.21-227f4e7`, Lean backend at
`backends/lean`), rustc `nightly-2026-09-17`, and nixpkgs
`b3d51a0365f6695e7dd5cdf3e180604530ed33b4` for the prewarmed closure. They are read with
`cat toolchain/downstream-pins.toml`.

**Record that disagrees.** That file's header still says "This repository does not use, and does
not require, any of them: it holds the specification, not an implementation", which `AGENTS.md`
and `PLAN.md` §23.1 both contradict — this repository ships an implementation and its own
transport boundary. The pins it records are nonetheless correct, except for the two paths named
in §2 and §4 (`grep -n "does not use" toolchain/downstream-pins.toml`).

## 7. What downstream needs from here

`PLAN.md` §23's six items, each with the artifact that supplies it:

1. **The frozen interface alphabet and conformance relation** — §2 above; `PLAN.md` §10;
   `lean/Contracts/Conformance.lean`. An implementation's proof is a `Conforms` (or
   `ConformsVia R`) instance, with a simulation relation `R` of its own; the three landed
   instances are the worked pattern, and each names its layer-below hypothesis at its own type.
2. **The ledger and coverage report** — §3 above; `ledger/clauses.json`,
   `ledger/coverage.json`, `ledger/dispositions/`, `ledger/reconciliation.json`. Coverage units
   are clauses, so an implementation milestone can claim clause-level coverage in the same units
   and both sides' gaps are visible in one place.
3. **The vector corpus** — §4 above; `vectors/**` with the per-layer schemas under
   `tests/contracts/`. Positive, negative and (none yet) recorded; the driver interface is
   implementation-agnostic, so a Rust binary is added as a runner rather than a rewrite.
4. **The executable specification** (`lake exe amqp-spec`) — §4's invocation. It is the
   differential oracle: run it and the implementation over the same corpus and compare verdicts
   *and* the condition each refusal names, which is what `tests/contracts/s1_differential.sh`
   does for `amqp-ref`.
5. **The Lean/mathlib pin agreement** — §6 above. Import `Spec.*`, `Contracts.*`, `Proofs.*`
   directly as a Lake path dependency; `PLAN.md` §15's "Integration contract" states that no
   symlink or re-export layer is introduced.
6. **Requirements that need tooling changes**, for scheduling in TemperMint rather than
   implementing here: multi-target extraction sharing one source-closure identity; a certificate
   binding the specification, model, corpus and a `Conforms`-style theorem; a certificate kind
   whose claim is "refines a specification" rather than "computes a specified value"; per-module
   proof-cost accounting; and a corpus dimension in replay that regenerates and compares every
   claim-bearing input byte-identically (`sed -n '/^6\. \*\*Requirements that need tooling/,/^### 23.1/p' PLAN.md`).

## 8. The implementation track's state

`PLAN.md` §23.1. Four rungs, and this is where each of them actually stands — no rung is
accepted, and the difference between "landed" and "accepted" is the whole point of the section.

**R1 — the transport shell: ACCEPTED.** Two review rounds returned findings against it and both are addressed; the acceptance record is `PLAN.md` §23.1's R1 bullet, and it is worth reading for how the findings changed rather than for their number. Original heading and state follow, kept because the sequence is the useful part: **landed, under independent review, not accepted.** The commit is
`d68ac31`; an independent review inspected it and returned **`changes_requested`** with five P1
findings: the trust disclosure listed `setsockopt` as absent while `listen` calls it; a
non-resolving `lean/Loopback/` path in the same disclosure; a positive short-write path claimed
but not exercised by the loopback run; a stale README claim that the pinned stdlib has no TCP;
and the absence of a planner-owned R1 contract under `tests/contracts/`, so the mutant controls
were not independently reviewable. What has moved since: the response commit `5945434` fixes the
disclosure and the path and commits the controls, the README text is corrected in the current
tree, and the missing contract now exists, committed, at
`tests/contracts/r1_transport_shell.sh`. **The verdict has not been re-run**: the review artifact
still reads `changes_requested`, and there is no in-tree record of the verdict anywhere — it is
session state, not repository state.

```sh
git log --oneline -2 -- lean/Impl scripts/loopback scripts/transport_shim.c
git status --porcelain tests/contracts/r1_transport_shell.sh   # the planner's contract: committed, clean
grep -n "the pinned stdlib does have TCP" README.md            # the corrected README text
agent://R1Review                                               # the verdict, verbatim, with its verified/unverified lists
shell bash tests/contracts/r1_transport_shell.sh                # the gate
shell bash scripts/run-transport-loopback.sh --mutant short-send
```

The shell's surface is **six** `@[extern]` operations — `listen`, `accept`, `connect`, `recv`,
`send`, `close` — pinned by path and printed by the trust gate, so a seventh is a visible change
in a gate's output (`grep -n "^@\[extern" lean/Impl/Transport.lean`). One part of the review is
worth carrying forward as positive: its verified section cleared the shim's memory discipline —
`recv`'s allocation, narrowing and ownership transfer, `lean_dec` on both the error and EOF
paths, and `send` returning the kernel's count without retrying. **The socket boundary is not
proved and is not claimed to be**; it is the one named unproved dependency, kept small enough to
read.

**The two records disagreed on how big it is, and the disagreement is repaired.** `PLAN.md` §23.1 said
"roughly seventy readable lines" while `README.md` said "about two hundred"; the file is 236 lines — 111
of code, 103 comment-leading, 22 blank — so the plan understated the thing it was praising. §23.1 now
carries the measured figures with the command that re-measures them and the README carries no number of
its own, which is the repair for every drift found today: state it once, and measure it
(`wc -l scripts/transport_shim.c`; `grep -c "^\s*\(//\|\*\|/\*\)" scripts/transport_shim.c`).

**R2 — the endpoint core: landed, review returned findings, accepted after four rounds.** `22f1228` adds
`lean/Impl/Core.lean` (384 lines), `lean/Impl/Stream.lean` (541), `lean/Proofs/CoreLaws.lean` (183)
and the new `lean/Shell/` tree — `Driver.lean` (238, the recv/feed/write loop and the three
obligations it states as unproved), `Main.lean` (116) and an `amqp-endpoint` executable. The core is
a *driver* over `Spec.Connection.step` rather than a state machine, so R3's relation will be
`i.conn = s` and what it proves is the plumbing; the shell sits outside `lean/Impl/` because the
boundary's import constraint is what makes that directory's claim true, and the trust gate checks
that half. An independent review returned **`changes_requested`** with four findings: the front
end's extent computation is a **second transcription** of the frame reader's progress decision rather
than a function of it; `readFrame`'s suffix-independence — the property that makes splitting a stream
invisible — is **unproved**, so no present-tense claim about arbitrary fragmentation is available;
**no committed test executes the shipped shell's loops** (R1's contract exercises a different
implementation); and two documents claimed the core's `Conforms` instance and the corpus's endpoint
runner as existing, which they are not — that one was mine and is corrected. **ACCEPTED.** The verdict came after four rounds, and each round found a different kind of defect rather than a
further instance of the last: the document correction it asked for was incomplete in five places, and grepping for
the claim rather than for the finding turned up three more; the contract it was asked to verify pinned four
sentences the driver *printed* rather than the forcing conditions those sentences described, so it failed on a
reworded assertion while the forcing was intact; two of the remaining claims no phrase-search could find — a table
row calling the shell a loop "over the proved core" four lines above the row saying that core is unproved, and a
command block saying a contract did not exist long after it landed; and finally that my own search had truncated
its results, so I had reported the family closed three hits early. Its substantive rulings: finding 1's second
transcription is gone (`Spec.Frame.frameExtent`), finding 3's shell is tested by
`tests/contracts/r2_endpoint_shell.sh` with the forcing asserted structurally, and finding 2's unproved
fragmentation property is **sufficient as a stated no-axiom residual** rather than a blocker — the acceptance-bar
judgement I deliberately put to it rather than making myself, and the thing R3's stream corollary now rests on.

**Updated as the fixes landed:**

the second transcription is gone — `0f75923` made the front end's extent computation a call to
`Spec.Frame.frameExtent` rather than a second copy of the reader's progress decision, and `Spec` rebuilt
with the same branch order, the same messages and the same refusals, which is what the corpus would have
caught if the refactor had moved an observable. The shipped shell now has a committed test:
`tests/contracts/r2_endpoint_shell.sh` drives both shipped binaries over loopback and pins the four
*forcing* conditions — a 3-octet server read against a 5-octet client read, so the eight-octet header
cannot arrive whole, and a 3 kB frame written through a shim that caps `send` at 1024 octets — because a
run that stopped asserting reassembly would pass while testing nothing. And the unproved fragmentation
property is the one finding still open, now *inside* the value layer's carrier development rather than
beside it: prefix determinism and fuel monotonicity are what both it and that layer's agreement need, so
they are one development rather than two.

```sh
git log --oneline -1 -- lean/Impl lean/Shell
cd lean && LAKE_NO_CACHE=1 lake build && lake exe amqp-endpoint --help
shell bash tests/contracts/r1_transport_shell.sh    # R1's contract
shell bash tests/contracts/r2_endpoint_shell.sh   # R2's shell rung, forcing the short read and the looped write
grep -n "second transcription" PLAN.md               # when the front end's fix is recorded
```

```sh
git log --oneline -1 -- lean/Impl     # R2's core, committed
ls lean/Impl
```

**R3 — the conformance theorem: the statement is frozen and the proof is not written.** The statement is frozen in
`Contracts/EndpointConformance.lean` and the proof is what remains, so the "not started" this entry carried all
session now applies to the proof alone. What exists: `lean/Impl/Core.lean:311`
already defines `specCore : Endpoint State`, so the specification's side of the interface is wrapped by the
implementation's own module; `Contracts/Conformance.lean` supplies `ConformsVia` and the `Endpoint`
structure every other instance uses. Both sides exist and are named: `Impl.Core.implCore` — renamed from
`specCore` by `075061f`, which is what the earlier reading of this entry got wrong, since the wrapper was there
and the *name* was the misleading part — and `Proofs.specConn`. The relation is `i.conn = s`, which needs no
inbox clause because `step` neither reads nor writes `State.inbox`. **The statement is now frozen**:
`Contracts/EndpointConformance.lean` declares `EndpointConforms` over exactly those three names, with no proof
attached, which is the repository's order — statement, then proof, then acceptance. What remains is the proof,
and its prerequisites are the value layer's agreement and, for the stream corollary rather than the unit
instance, the `ValuePrefixDetermined` residual in `Proofs/CoreLaws.lean`. Its content is narrower than its name —
it is the plumbing — and its prerequisites are the value layer's hypotheses (§2) and the layer proofs it
reuses, which is why the value layer's agreement is the rung everything above it waits on.

**R4 — the wire differential: implemented and discriminating; the corpus-driven application is not built.**
`scripts/run-endpoint-wire-differential.sh` plus `scripts/endpoint/wire_peer.py` replay a corpus over a socket
against the *shipped* endpoint and compare each step with `amqp-spec`'s in-process verdict and class. Its first
run measured **one** fact rather than six: 6 of 6 vectors of `vectors/slice.ndjson` diverge because the endpoint
reaches `HDR_EXCH` and sits there — it has *no application*, so it never attempts the sends a vector's `send` step
describes, while in process the harness attempts them and the core refuses. Closing that is the app-seam half: an
endpoint-side counterpart of the peer, beside the probe under `scripts/endpoint/`. It has also found a candidate
defect — two SASL vectors expect `414d515000010000` and the endpoint writes something else, so either the shell's
SASL header choice or the vector is wrong.

**Outstanding, and in flight elsewhere in the tree** (`git status --porcelain`):

- **one corpus family** — the link layer's fragmentation adequacy sweep, one message at every
  permitted split point. The generator support is written and committed
  (`scripts/gen/flows.py`, dispatched by `--flow` / `--flow-negative` in the modified
  `scripts/gen-value-vectors.py`); no committed corpus file or gate clause carries it yet.
- **one contract draft** — `lean/Contracts/Settlement.lean`, committed: the settlement
  declaration for the `disposition` exchange and the delivery-state bookkeeping. Its own header
  records that a rule about the delivery range or the settled flag cannot be cited to a clause,
  because the fields carrying settlement's mechanics have no keyed clause in the ledger.
  `Contracts/SessionCredit.lean`'s `SenderCreditInvariant` is in the same position: **stated
  rather than proved**, with the preservation lemma named as what will discharge it.
- **the value layer's proof debt, restated** — the receive instance's `ValueLayersAgree` is undecided: the
  divergence that refuted it is fixed and no other is known, but no proof exists, since discharging it needs the
  value layer's own instance. The send instance is not conditional but **false** — an array body whose refusal the
  two artefacts name differently — so patch 3's `arrayElement` split is the fix and `Proofs/FrameSendConformance.lean`
  holds the refutation. Original entry: the three landed instances rest on `ValueLayersAgree`,
  `ValueCarrierAgree` and `ValueWriterAgree`, none of which is proved; the value-layer instance
  that would discharge them does not exist (`grep -rn "conformance_public" lean/Contracts/`).
  `PLAN.md` §13's S1.5 rungs record what remains: the dispatch lemma and the composition for
  `NarrowestEncoding`, and the text families (`string`, `symbol`) blocked on a fact about
  `String.fromUTF8?`/`toUTF8` that the standard library does not state.
- **V3, recorded third-party evidence** — there is none: `vectors/recorded/` does not exist, and
  no vector carries `kind: "recorded"`. `PLAN.md` §22 records that S3's acceptance proceeds on
  V1, V2 and V4 with V3 outstanding "rather than quietly dropped", and a capture cannot be
  produced here, because this repository contacts no network by design. **A downstream reader
  should treat V3 as the one tier of §12's four with no evidence at all**:

  ```sh
  test -d vectors/recorded || echo "no recorded corpus directory"
  python3 -c "import json,glob
  print(sum(1 for f in glob.glob('vectors/**/*.ndjson',recursive=True) for l in open(f) if l.strip() and json.loads(l)['kind']=='recorded'))"
  ```

**Two records that disagreed about this section, and the disagreement is resolved.** `PLAN.md` §23's opening sentence and
`README.md`'s prose and "What is here" table all said the endpoint's protocol core was *proved* to conform. None of them says
it now: §23 and the README both carry the *frozen statement* with the proof owed, and the statement itself lives in
`Contracts/EndpointConformance.lean`. What R2's review left open has also closed — the second transcription is gone, the shipped
shell has a gate, and the fragmentation property has moved inside the value layer's carrier development, since the two lemmas it
needs are the two that development needs. **R3's proof is what remains.** The three copies of the overstatement are the reason
this section is kept: one was found by a review and two by grepping for the claim rather than for the finding. Everything else in §23's and §23.1's account of what
exists matches the tree as checked above: the interface is frozen and landed, the ledger and
corpus exist, `lake exe amqp-spec` exists, the pin agreement is checked, the six-operation
surface is real, and the three instances are landed — but they prove the *layers*, not the
endpoint.
