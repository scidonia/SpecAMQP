# Working agreements — the history behind the evidence rules

> Moved verbatim from `PLAN.md`: §16's narrative block (lines 1660–1935) and §22's
> wave records (lines 2028–2047), on 2026-09-25. The *rules* these episodes produced
> live in `AGENTS.md` and in the plan's §16/§22; this is why they exist, in the order
> they were bought. The opening two paragraphs are the writer-law domain definitions
> (they sat at the head of the same span); the closing two are the instrument
> measurements that `bench/` now owns.

**The writer's domain, as a definition rather than an adjective.** `ValueWriterAgree`'s first conjunct is refuted on the
ill-width family, and the restatement over the reader-reachable domain is now a one-line change with one predicate:

```lean
/-- A body an endpoint can hold: some region decodes to it. The wire is the only source of values, so a body no reader
can produce cannot be sent by a conforming peer nor arise in the implementation answering one. -/
def ReaderReachable (v : SpecAMQP.Ref.Value) : Prop :=
  ∃ region : Octets, ∃ used : Nat, SpecAMQP.Ref.decode region = .ok (v, used)
```

**Two domains, because two consumers receive values by different paths and neither path implies the other.**
`ValueWriterAgree` is the *send instance's* law, and its values arrive through the corpus carrier, so its domain is
**carrier-reachability** — `∃ json, SpecAMQP.Ref.Vectors.valueOfJson 64 json = .ok v` — which is the path the endpoint proof can
supply from `frameOfJson`'s own construction, and which says the same thing in that endpoint's terms: a body the carrier cannot
produce is a body that endpoint cannot send. It keeps its name and its two conjuncts, gains the reachability as a hypothesis on
the body, and takes it as a parameter in `writers_matched`, since that lemma cannot derive it for arbitrary related frames. The
octet-equality conjunct then becomes a candidate theorem rather than a refuted one, and the class-agreement conjunct is unchanged.
`ReaderReachable` stays as written and is the domain of the *wire-level* claims, including the value layer's own agreement, where
the wire reader is the right notion. **Both exclusions go in `FrameSendConformance.lean`'s caveat, named, with their reasons** — a permissive writer's property over
values no protocol path constructs, and carrier-reachability *not* implying wire-reachability, which is a fact about the artefacts:
bridging the two would need a reference writer–reader round trip that `Ref` does not expose, the same absence that makes the writer
law a hypothesis at all. A narrowed hypothesis with an unexplained narrowing is a defect wearing a domain, and a domain whose
boundary is explained only where it excludes something is half-explained — this one excludes nothing on one side and cannot be
derived on the other, so both halves get a sentence.

**Ownership is what makes a window possible, and this session bought that rule three times.** A slice editing a file
another slice needs must say so, and say when the file is buildable again. `ImplCore`'s one line — "frame is green at the
current working tree, holding it still" — cost its author nothing and was worth half an hour to two other slices, which had
spent that half hour unable to verify anything: `ValueLayer` stopped building rather than report a transient as evidence,
and `CodecRefusals` could not run the differential at all. Two of the three collisions here were the same event wearing
different filenames: a proof module repaired by one slice and claimed by another on the strength of a reading taken before
the repair, and a `Spec/` type change whose proof fallout belonged to a third slice that had already claimed those five
statements. The third was a `Spec/**` edit that left the package unbuildable while two slices built against it.

The rule that came out of them: **one window at a time in a shared tree, announced before it opens and closed with a
one-line "green at <state>", and a change to a `Spec/` type together with its proof fallout is one change, so it gets one
window rather than one per file.** The corollary is the conductor's rather than a slice's: naming the file's owner is what
lets anyone declare a window at all, and where ownership was unstated the collision happened — the announcement is what
turned each of these into a message instead of a merge.

**A commit message is written from a file, never inline in a command.** `b361bad`'s body lost every backticked identifier
because it was passed through a shell and the backticks were command-substituted: the subject and the file stats are exact,
and the body says "seven shape and nine capacity" without naming them. Its author disclosed it, tried a guarded
`reset --soft`, found three later commits on top, and stopped rather than rewrite history under other slices' work — which is
the right call and the reason the remedy here is a later commit rather than a rewrite. `git commit -F <file>` or a *quoted*
heredoc avoids it entirely, and a message is the one artefact in a repository whose loss no compiler and no gate can catch.

**Grep the claim, not the finding, and this session bought that rule seven times.** Every correction today was applied where it
was noticed rather than where the claim was repeated. The README's "a pure protocol core proved to conform" was corrected in its
prose while the same sentence stood four lines above it in that document's table. A gate row in `HANDOFF.md`, a layout list in
`PLAN.md` §14, and the conformance contract's own witness paragraph each went stale within hours of being written, and two of
those went stale while the same fact was being corrected in another file. A disposition's vector ids were copied from my own
sentence rather than from the file they were supposed to cite. And a paragraph I wrote myself was falsified by patch 3 inside the
hour, because the fix landed after the sentence and before anyone read it.

**And a claim can be repeated in *different words*, which no grep finds.** Two of the eleven stale claims this session survived every
search for their phrases and were caught only by reading a whole artefact: the README's table called `lean/Shell/` a recv/feed/write
loop "over the proved core" four lines below the row saying that core's conformance is R3 and undischarged — the same table
contradicting itself, in a paraphrase no search for "proved to conform" would match — and a handoff command block still said a contract
did not exist long after it landed, where the stale part is a recipe rather than a sentence. So the rule has two halves and the second
needs a reader: **grep for the words, and read the artefact whole when it is a table, a list or a recipe**, because a second copy is
often a paraphrase rather than a repetition. Eleven instances of this defect in one session, two shapes of remedy, and the second one
found nothing the first could.

**And the counts stay non-zero, which corrects the message that introduced them.** After every fix above, `PLAN.md` still contains
"proved to conform" twice and "over the proved core" once — and every one of those hits is *this section quoting the defect in the past
tense* to explain what went wrong. The message claiming the counts were "now all zero" was wrong about its own subject: zero was never
the target, since a rule that explains a defect has to be able to name it. What the target is: **nothing asserts the overclaim in the
present tense**, which is checkable and was checked, and the legitimate hits are the rule's own history. A count is a way of finding a
truncated search, not a score to drive to zero.

The mechanical form is the one that works: **after changing a claim, grep the repository for its words.** The finding is a pointer
at one copy — it is the copy someone happened to read — and the words are all of them. The words that moved most in this repository
are "refuted", "vacuous", "as a theorem", "not started", and "vacuous" again; each of them was true somewhere and false in a
second place, and only the grep found the second place.

**A check must assert what it means, not that something arrived.** The shell driver's readiness check read *any* first line from
the server as its readiness line, so a server that failed to bind printed `bind: address already in use`, that line was taken as
readiness, and a **dead server was carried into the case**. One port collision therefore arrived as ten unrelated assertion
failures, and the first attempt at diagnosing the collision could not see the collision for them. Readiness is the server's own
announcement now, and an attempt that does not produce it reports the line it got instead.

**Its two follow-on instances, one of which is a different species.** Found in the same harness while the first was being fixed:
the scan helper launched `amqp-endpoint` as *every* case's server, when the short-write case's server must be the probe — the side
that declares limits large enough for the frame — so a refactor **silently replaced the case's subject**, and the run still passed
case 1 and failed case 2 for a reason that had nothing to do with the shell. That is the neighbouring defect, and it needs its own
sentence: **a case's subject is as much of a claim as its expectation, and a helper's default can move it without touching a single
assertion.** Pin what the subject *is*, not only what it does. The third instance is this rule in miniature — the probe printed its
readiness line *before* binding, so a line existing before the port did lets a collision be read as readiness — and that it was found
by looking for the first instance is the argument for writing rules down rather than remembering them.

The general form is what earns this a place beside the other rules here: **a check that accepts *something* where it means *this
thing* converts one real failure into several misleading ones.** That is worse than accepting nothing, because the failure is still
there and the report now points at a dozen places it is not — and it is the same family as the gates whose scope was a list rather
than a walk, and the floors that were reported rather than asserted. Every one of them passed while checking less than it claimed.

**A brief is scoped by its unit of work, and an ordering has to be named — both bought by one ticket.** A batch was scoped as "the next 25
undispositioned must-class clauses in the check's own anchor order (largest first), taking only anchors that sort after
`amqp:transport/section:links`", plus "do not edit a file whose name contains `links`". The agent found two defects in that, both mine.
The **ordering was ambiguous**: "anchor order (largest first)" is the report's printed order and "sort after" is lexicographic, and the two
disagree about which anchors are in range — it resolved them by asking which reading could be satisfied *at all*, and only one ends on an
anchor boundary rather than cutting a group in half. The **scope was over-constrained**: excluding by filename was a proxy for *do not
collide*, and it stranded fifteen clauses between two agents, because their file would have been named after a shared ancestor rather than
after the work.

**The boundary is the unit of work, not the name of the file it lands in**, and **"the next N in order" is not a scope until the order is
named**. Both are this repository's recurring defect — a rule that passes while doing less than it says — arriving in an instruction rather
than in a check, which is where a dispatch is easiest to get wrong and hardest to notice.

**A moving number is never quoted bare in a document.** The ledger's undispositioned count has moved 170 → 145 today and moves by twenty-five
with every batch, and a hand-off table cell carrying it went stale the moment the first batch landed. The remedy is not a schedule of updates:
it is to quote **the command that reports it**, with the number dated if a number is wanted at all — `python3 scripts/clause-ledger.py check`
is the value, and any copy of its output is a claim about a moment.

This is the same defect as the rest of §16 in its purest form — a claim that was true when written and is read as present tense — with the
aggravating factor that its author knows it will move.

**And the escape hatch has to be closed properly**: I wrote "145 at the time of writing" beside the command, and it was 95 two batches later.
*"At the time of writing" is not a date* — it names no moment, so it dates nothing and reads as current forever. A number that deserves to be kept
deserves the commit it was read at; a number nobody will update does not deserve to be written down, because the command beside it already reports
the live value. Counts of completed work, coverage percentages and gate totals all behave this way, so
the rule is about the *kind* of claim rather than about the ledger: **if the number can change without anyone editing the sentence, the
sentence should carry the command rather than the number.**

**A quotation in a document is a copy with an expiry, so quote what is stable and point at what moves.** §23.1 quoted the shell's docstring — "the fixed
header this peer announces" — and the same day's work reworded it to "the fixed header a peer announces *for a layer*", leaving the plan asserting a
sentence that no longer existed while the code containing it said something else. The vendored OASIS artifacts are the opposite case: pinned by byte
identity, so quoting them quotes something that cannot move.

The rule that follows: **quote the artifacts, paraphrase our own code and name where it lives.** A quotation of a moving source is the §16 defect with a
compiler-shaped hole — it reads as authoritative, it is a copy, and nothing checks it — and the longer the quote, the more of it can drift.

**Two agents on one ordered backlog are scoped by assigned *anchors*, not by exclusion sets.** An assignment reading "the next 25, excluding the anchors the
sibling holds and the families already done" cannot work when both agents walk the same list: whatever it takes next, the second takes next, because *next* is
computed from the same point and neither can see the other's choice. The files-per-anchor disjointness that makes the work parallel assumes *different* anchors,
and an exclusion list can only describe what is *already* taken rather than what will be taken while the other works.

The remedy is to name the anchors, which are stable while the order is not. What the mistake cost was one batch written and deleted rather than landed, because
the check caught it — twenty-five `duplicate disposition` problems on clauses another agent had already decided — and **a gate catching a bad dispatch rather
than a bad artefact is the same mechanism working one level out**: the slice that received the assignment noticed, refused to land a second decision on clauses
someone else owned, and re-derived its scope from the tree instead.

**And a *claim* has to be an anchor list too, which is the same rule seen from the other side.** A second collision arrived within the hour, from a claim rather than a scope: one agent
announced "claiming the last 20 refs" precisely to prevent the collision the earlier batch had suffered, and the other already had those nineteen in flight — scouts on eight of them since
before the announcement, twelve entries staged. Both computed *next* from the same point in the same ordered list, so a claim expressed as a count or a position is not a claim at all.

**The family is one rule with two faces**: the anchors are stable and the order is not, so both the *assignment* and the *announcement* must be lists of anchors. Everything else — "the next
N", "the tail", "everything after the ones you hold" — is a race with extra steps. What made this instance cost a message rather than a duplicated decision is worth noting as the mechanism:
one agent had **staged** rather than committed, and the other **asked** before writing. The duplicate rule would have caught it either way, which is the third time today that gate has been
the thing standing between two agents and one decision.

**And a driver's port is arbitrated by the bind, not by a lock.** Every driver that starts a server derives a candidate port from its own process id, **scans forward over a bounded range**,
prints the port it took, and reads the *server's own announcement* as its readiness line rather than merely a first line. No lock and no registry: the bind is already exclusive, so two drivers
scanning concurrently take different ports, and a lock would serialise them to buy nothing. What the derivation contributes is only a starting point, and it is deliberately blind — a
`pid % 300` window collides *systematically* with a driver that ran immediately before it in filename order, which is why the scan exists rather than a cleverer derivation. **A range
exhausted without a bind is a named invalid**, "this run tested nothing", and never a pass; the same separation applies inside a case, where an endpoint that refused to start must be
distinguished by its own words from a port that could not be bound. Each driver names its own `SPECAMQP_*_PORT_BASE` and `*_PORT_ATTEMPTS` — the shape is shared and the ranges are not,
since a shared base would make two suites race for one window instead of settling it by bind.

**And a plan question from a slice goes to the session owner, by the name the session gives it.** There is no separate planner agent in a live session: a slice that tries to mail a
"planner" fails with an unknown agent, which happened to two slices in one afternoon before each routed its question through the session owner instead. The rule is not that the planner
is absent but that the *role* is held rather than spawned — the owner authors the contracts, decides the open choices, and answers within the turn. Some spawned agents also have no
`hub` device at all and can only reply through their result, so a brief should name the channel as well as the owner: the question arrives either as a message or in the final report, and
a slice must not stall waiting for an answer it has no channel to receive.
**What both slices did instead is the part worth keeping**: each named the file and the site its question concerned, stated the decision it needed in a form that could be answered by the
plan owner without re-deriving anything, and **continued on formulation-independent work while it waited**. That is the shape a plan question takes when it is asked well — it costs the
owner a decision and costs the slice no time, which is the opposite of the two collisions earlier in the day, where a claim cost two agents' attention and produced a rule.

**And a brief that says "add a case to the gate" is direction, which is why it must say "propose" when propose is what it means.** A slice asked to pin a property in the ledger's own gate read
the instruction as authorisation, edited `tests/contracts/s0_sources_ledger.sh` — a planner-owned contract — and then disclosed the edit in two places, its file-ownership block and its list of
planner decisions received. The content was right and the disclosure made it reviewable, so it stands; **the wording was mine and it was ambiguous**. A coder may not modify a contract file, and
an ambiguous brief is not an exemption from that rule — it is a reason for the planner to say which side of the line the requested work falls on. The shape to use: name the *property to be
pinned*, and say whether the asserting test is to be *written* (coder-owned files) or *proposed* (contract files, with the diff quoted in the report).

**And the pin that slice corrected was my mistake rather than a mechanical one.** I asked for a case asserting that `settled.4` and `settled.6` render *differently*; they already differ in
their obligation — "MUST be true on at least one transfer frame" against "MUST be false (or unset) on every transfer frame" — so that assertion **passes on the reverted branch**, which is the one
thing a pin must not do. What it pinned instead is the property that actually regresses: each clause names its choice, does not contain the element's name, and records the choice in
`references`. It then ran the assertion against a reverted copy of the tool and observed six problems before the fix and none after, which is the failure-first evidence the literal request
would have made impossible to produce.

**And a control that repeats a run twice proves stability only when the mechanism is not deterministic in the same way both times.** The wire differential's author reported two consecutive
runs "identical line for line" as evidence that a scheduler-dependent comparator had been fixed; the reviewer refuted the general claim by tracing the surviving path instead — a `recv()`
that captures two of the peer's frames yields only the *final* state to the application, so a step keyed to the intermediate state is *never played*, which is a difference in what went on the
wire rather than in the harness's bookkeeping. **Back-to-back loopback writes coalesce the same way run after run**, which is exactly why the original flap went unnoticed for as long as it did:
a two-run control is evidence about the *variance the runs happen to sample*, and it cannot detect a dependence whose two outcomes are selected by a condition no run here varies. Varying the
condition — or stating that it cannot be varied — is the control; repeating the same condition is a sample, and calling it a control is how a green run becomes a fact it never was.

**And "the named instance is fixed" is not "the class is fixed", a distinction the same review kept without dressing it up.** The patched branch really was broken and really is repaired; the
claim built on top of it was about the comparator as a whole. A slice reporting "this instance is fixed, the class is open, here is the trace" gives its reviewer something to refute or confirm;
one reporting "the comparator is stable" asserts what no trace supports, and the cost lands on whoever next reads a green run as a settled fact.

**And a root cause that lives only in a commit message is not a record.** The same review found that all three of the slice's handed-over findings were attributed in commit messages and Lean
docstrings, while the tool's own printed divergence text was generically worded for every cause — so a maintainer reading the run's output could not tell a known seam limitation from a
regression without git archaeology. **A cause belongs in the artefact that will be read when the cause matters**, which is the run's output rather than the history that produced it, and the
same rule applies to this plan: a finding recorded only in a message is a finding that will be rediscovered as a surprise.

**And a pin should hold the artefact under test rather than a record of it.** The ledger gate's new step does exactly that: it reads a *fresh* generation of the clause texts into a temporary
directory rather than the committed `ledger/clauses.json`, so what it pins is the *renderer* — and reverting the branch that renders a choice puts `«sender-settle-mode»` back into both clauses and
fails the step. A pin that read the committed ledger would have been holding a file the same change also updates, and could have gone green on a revert that left the record alone. **Where a check can
read the generator rather than its output, it should**, because the output is precisely what the change is allowed to move: this is the same rule as the generator-fidelity gates, arriving from the other
direction — one says the output must equal what its generator produces, the other says the check must look at the generator when the output is legitimately changing under it.

**And a control has to vary the mechanism, not a proxy for it.** The assignment that fixed the wire comparator named `SPECAMQP_WIRE_READ_OCTETS` as the way to vary the coalescing condition; the
slice measured it and found **identical verdicts at 8 and 4096**, because the read size is what the *client* asks for while the coalescing that matters happens in the *peer's* writes — the control is
the peer's own `SPECAMQP_WIRE_COALESCE=1`. **A control chosen by reasoning about a name rather than by measuring the mechanism is a second guess wearing the shape of a check**, and it was the
pre-fix runs that made the mechanism visible: at `read-octets=8` the refused challenge was attempted five times, at 4096 twice, and with the peer's steps 2 and 3 in one `sendall` the refusals land
after the second `took HDR_EXCH` rather than before it. That is the flap the review predicted, measured rather than argued — and the same runs are what refuted the control I had endorsed.

**And a generated artefact and its generator have to land together or neither.** The rule sounds obvious and it failed twice in one hour in opposite directions: first the regenerated
`ledger/clauses.json` lagged the renderer that produced it, which the manifest caught as a mover; then the renderer itself lagged the ledger it produces, which **nothing** would have caught —
ClauseRender reported its slice complete without a commit id, its outputs were committed, and HEAD held the *old* tool beside the *new* record. The consequence is not cosmetic and the check is
not hypothetical: running HEAD's tool against HEAD's ledger reproduced `check FAILED: 18 problem(s)`, so a clean checkout would have failed its own gate while every working tree looked green.
**The working tree is the one place the inconsistency is invisible**, because there the pair is whole; both times the defect was in what a *checkout* would do rather than in what the tree did. It is
worth naming as the third face of a rule this plan already carries twice — a generated table must equal what its generator produces, and a check that can read the generator should — because neither of
those says anything about *when* the two land.
**And the experiments rule was broken a second time, which is evidence about the habit rather than about the rule.** Three scratch modules — `ProbeTmp`, `WireScratchTmp` and a `.bak` of it — were left
under `lean/Proofs/` while a sitting worked in them, and **the trust gate caught it**: `s1_proof_integrity` failed with `the package does not build: [594/596] Building Proofs.ProbeTmp`, because a module
in that directory sits inside the library's glob and is therefore compiled, scanned and shippable. **It is worth recording precisely because a gate caught it rather than a reading** — the day's other
findings were readings, and this is the case where the rule and the gate agree and the only problem was a tree left in a working state. The rule costs a mover nothing, since `/tmp` imports the project's
modules; what it costs is the discipline of moving a file before the build is treated as evidence, and the second occurrence says that discipline is the part worth stating.

**And an ad-hoc probe tests the built artefact, not the source — which cuts both ways and caught me once.** Verifying the new `frame_receive_conformance` used `lake env lean` on a scratch file that
*imported* `Contracts.FrameConformance`; the import resolved against the `.olean` from before the edit, so the probe reported `unknown constant` for a theorem that was in the source and elaborating
correctly. That direction is harmless — the failure is loud. **The other direction is not**: a probe against a stale olean would report *success* for a claim whose source has since been broken, because the
imported module is the one that was last built rather than the one on disk. The gates are safe from this by construction — every contract script builds with `LAKE_NO_CACHE=1` before it checks anything — but a
scratch verification is not, and the rule is therefore: **build the module before probing it, and treat a probe's silence as evidence about the olean until the build has run.**

**And a correction has to reach every sentence that asserts the old state, which means searching for the claim's own words rather than reading forward from the sentence you came to fix.** This is the
same shape as the `r2` contract paragraph that described landed work as owed and the ledger note that said the model was keyed wrongly — and this time it was against my own commit: I rewrote the bullet
stating `ValueLayersAgree`'s status and left the bullet **immediately above** it, which still said `frame_conformance_public` was "true and vacuous: its hypothesis is false, so the theorem says nothing
about the two artefacts". Two adjacent bullets asserting opposite facts about the same theorem, in the module whose acceptance declaration the commit was landing. **The history is worse than one miss**:
an earlier commit had corrected the same pair once before, editing the adjacent slot rather than the stale one, so **four prose passes over one paragraph each read forward from the sentence they came to
fix**. The remedy is mechanical and was not used — grep for the claim's own words (`vacuous`, `owed`, `is not modelled`) across the paragraph *and* the file, and fix every hit — because a correction that
lands beside its predecessor reads as two facts rather than as one fact and its ghost.

**And an import edge can turn a latent name collision live, which is a failure mode with no owner until it has one.** `Proofs.ConnectionConformance` declares a nullary `SpecAMQP.Proofs.StepAgrees` and
`Proofs.ValueWireAgreement` declares a parameterised one — two different relations sharing a fully-qualified name in a shared namespace, neither module importing the other, so neither had any reason to
notice and neither was wrong. **The discharge of the value layer's instance added `import Proofs.ValueWireAgreement` to `Contracts/FrameConformance.lean`**, which put both modules in one environment for
the first time (the trust gate's axiom probe imports the accepted-theorem modules together), and **the trust gate's probe** failed with `import Proofs.ConnectionConformance failed, environment already contains
'SpecAMQP.Proofs.StepAgrees' from Proofs.ValueWireAgreement` — the *package build* at that same commit is green, which is the distinction the next paragraph turns on. **The class is enumerable in one command, from artefacts the repository already builds** — the `.ilean` declaration tables `lake` writes per module are a per-module inventory, so
`jq -r '.decls|keys[]' .lake/build/lib/lean/*/*.ilean | sort | uniq -d` names every fully-qualified name two modules share. **It is recorded as a check rather than wired as a gate**, for two
reasons: a stale ilean for a module that has been deleted makes it over-report (the safe direction, but a false-positive mode a gate must not have), and **a live collision is caught by the probe that exists for exactly this, not by the build**: `lake build` is *green* with a collision present (measured at the pre-fix HEAD — 594 jobs,
success), because **no module imports both trees** and each compiles in its own environment. What fails is the gate's `Axioms.lean`, whose import list is the only place the two meet, and the gate stops there
under `set -euo pipefail` before it can note that the package builds. **So the detector is the probe, and its coverage is defined by the probe's import list**: a collision between two modules that only a
*future* target imports together stays latent in the tree and invisible to `lake build` until something merges the environments the two trees live in. What the command adds is early warning about a *latent* collision, which is worth having in the
plan and not worth a twentieth contract that can cry wolf. **And the order that matters when fixing one is "who else names this" before "who declares this"**: a name can be pinned from outside — one of
these two was, by a planner-owned contract stating its public theorem over the fully-qualified name — and the compiler points at that break only *after* the annotation has been applied.

**There were two such names, not one, and the reported error was a sample rather than the set.** Fixing the first — `StepAgrees` — revealed
`SpecAMQP.Proofs.ReadersAgree`, declared nullary in the connection module and parameterised in the wire module, because **Lean aborts an import on the first collision it meets and says nothing about the rest**. The
slice that fixed it went to the built `.ilean` declaration tables and enumerated *every* name the two modules share, which is the method that makes the second one a fix rather than another red gate; a single name
handed over from a gate's output is a sample of a class. **And the name was pinned from outside**: `Contracts/ConnectionConformance.lean` states `connection_conformance_public (readers : SpecAMQP.Proofs.ReadersAgree)`,
so for that one the *wire* side had to move and the connection side could not — checked before the annotation was applied rather than after, which is the difference between a local fix and a contract broken three
directories away. The cost of finding out was an import three modules away from either declaration. Lean has no module-private declarations by default; `private` is the annotation that makes
a helper local, and a name only ever used inside one file should carry it — the alternative is a name that is global by accident and a collision that fires wherever two such accidents are first imported together.

**And a fix can be protected by a proof rather than by a gate, which is worth knowing per fix.** The truncation family's refusal branch is reachable by **no corpus case at all** — every one would need a field value of
2^32 or more — so no vector can defend it from regression. What defends it is `ref_fieldOctets_writes`: where a field fits, the guard writes exactly `u32be n`, which makes the change byte-identical on every
corpus-reachable input and the refusal branch statically correct rather than merely untested. **So the repository has three kinds of protection doing distinct work** — a gate over a corpus, a witness in a scenario, and
a theorem over the code — and a fix that looks covered by all three is usually covered by one. Naming which is which is the difference between a claim and a checked one, and it is why "the gates are green" never
answers the question by itself: the suite here is **19 of 19** on a tree carrying the widened corpus, the specification's two writer arms, the truncation closure and the rewired differential, and none of those four
is what makes that number mean anything without the other evidence beside it.


**And the repository now measures its own instruments, off-gate, with the evidence committed.** `bench/run.py` measures the two corpus executables over named workloads, `bench/workloads.json` records why each
workload exists, and `bench/results/corpus-instruments-<date>.json` is the committed record — carrying the environment (CPU, cores, memory, load at run time, toolchain, commit and dirty paths), the SHA-256 of each
binary, each corpus and the runner itself, and min/median/max over seven measured repetitions with one warm-up discarded. **None of it is a gate**: this repository's rules forbid a test from touching a real clock, and a
threshold that depends on host load would be measuring the machine rather than the code.

**And the first run's own method is the part worth copying.** The obvious series — quarter, half, whole — *cannot* answer the complexity question for this corpus, and the measurement said so: `generated.ndjson`'s
first quarter holds **51.9% of the bytes at 25.0% of the vectors** (mean line 466 bytes against 144 in each later quarter), so a prefix series moves volume and mixture together and its ratios mean nothing about cost.
The runner therefore carries a second **growth series**: one fixed 17,598-vector base repeated ×1/×2/×4, mixture held exactly constant and the work ratio exactly 2.0000. **The result is 1.86× time for 2× work, at
both steps and in both artefacts** — linear, with the slight sublinearity being the fixed startup cost amortising — which is precisely the measurement that would have caught the quadratic accumulator this repository
was bitten by. The startup floor is a number worth having too: an empty corpus costs 0.049 s and the twenty-vector worked corpus the same, so any workload under a few thousand vectors measures process start rather
than the code. Full corpus, for the record: 70,390 vectors in 0.726 s median for the reference and 0.688 s for the specification, at ~142 MB peak RSS each.

## The waves, as dispatched

**Wave 1 (running).** The reference's element-constructor gap (`lean/Ref/**`, `scripts/gen-value-vectors.py`); the value codec's round-trip rung R1 and the frame layer's three statements (both `lean/Proofs/**`, separate files so the two proof slices cannot collide); and S3's facts, read from the artifacts rather than remembered.

**Wave 2, after S3's facts land.** Three implementation slices and one enabling change:

* **S3-connection** — `lean/Spec/Connection.lean` and `lean/Ref/Connection.lean`: the protocol header and version negotiation, the SASL ANONYMOUS phase, `open`/`close`, the connection state machine and the connection error conditions; plus harness support for exchange vectors and the slice's generator family. The interfaces the planner fixes first: the state type takes the artifact's own state names, and the observable is the per-step verdict the exchange schema defines.
* **S3-session** — `lean/Spec/Session.lean` and `lean/Ref/Session.lean`: `begin`/`end`, `attach`/`detach`, `flow`, and `transfer` carrying one unfragmented `data` section. It depends on one thing from S3-connection and that thing is fixed before either starts: a frame whose channel is not zero is handed to the session layer, which decides whether the moment is legal.
* **S5-message** — `lean/Spec/Message.lean` and `lean/Ref/Message.lean`, with its corpus under `vectors/message/` (the committed `vectors/messages.ndjson` is a different, earlier family and is left alone): the Part 3 section types and the outcome state machine. It depends on nothing in S3 at all — sections are values carried in a transfer's payload — which is why it can run beside the connection work rather than after it.
* **the generator split** — `scripts/gen/values.py`, `scripts/gen/frames.py`, `scripts/gen/slices.py`, with the existing script becoming the entry point that dispatches to them. This exists so that two slices can add families in the same wave without editing one file; until it lands, families are added by one slice at a time and the second waits.

**Wave 3.** S4's flow control (`lean/Spec/Session.lean`'s window arithmetic, credit conservation and settlement, with the fragmentation adequacy control) on top of S3-session; S6's transactions as its own performative family and state machine, which needs only the session dispatch; S7's full SASL mechanism negotiation and layer-transition rules on top of S3-connection's ANONYMOUS phase. R2–R5 of the proof ladder continue beside them.

**Wave 4.** The handoff, which is H1: what a downstream Rust implementation and its proof need from this repository, with the conformance interface and the frozen lexical surface named rather than described.

**One acceptance item is blocked on something no slice can produce.** S3's plan asks for at least two *recorded third-party* exchanges (V3) of the same slice, admitted, with the mutation controls (V4) firing. Recording requires an independent implementation to talk to, and this repository captures nothing over a network by design: the outputs of a capture are committed data, and there is no capture to commit. S3's acceptance therefore proceeds on V1, V2 and V4 — the authored and generated corpora and the mutation controls — and V3 stays outstanding with its requirement stated here rather than quietly dropped: a capture of the same exchange from an independent implementation, committed under `vectors/recorded/` with its provenance recorded the way the artifacts' identities are.

**Two gate defects found by the slice that hit them, both in contracts of mine.** The first: the differential's reason-class comparison keyed on a verdict status (`reject`) that the harness never emits, because it reports `pass`/`fail` for whether a *vector's* expectation was met. The comparison therefore skipped every vector and had never run — the pinned-reason check caught a wrong pin while two artefacts disagreeing about *why* they refused went unnoticed. It is now keyed on the corpus kind, with the class searched for in the detail because a verdict that met its expectation reads "rejected, as the vector expects: limit: …" rather than starting with the class. It is live and passing, and an honest gap remains: its *sister* check has been observed failing (a wrong pin, found by the slice), while this one has only been observed not-firing on inputs that are non-empty — a planted negative control would need a doctored artefact, and is owed. The second: the value corpus could not express an encode-direction refusal at all, because its shape check requires `bytes` on every vector, which is why the differential has to generate its limit control in a temporary directory instead of committing it. **Both are now closed**: the class comparison is keyed on the corpus kind and passes live over 68,111 vectors, and `bytes` is optional on an encode vector carrying `expectError`, which let the writer's refusal surface enter the corpus as **nine pinned vectors** — the declared form's capacity refusals (`limit`), covering a str8 element that cannot announce 300 octets, a list8 element that cannot announce 300 items, an array8 element that cannot announce 300 elements, a ubyte element constructor asked to carry a uint, `smalluint`/`smallint` out of range, `uint0` carrying a non-zero, `list0` carrying a non-empty, and a list8 element asked to carry a ubyte. The class is `limit` rather than `malformed` because `malformed` would say the octets are not a well-formed value when the value is legal and encodes fine in a wider form: what is unsatisfiable is the *declaration*, which is the same shape as the DOFF refusal and must not carry a different class.

The specification's six writer sites were changed by that slice under an explicit authorisation, on the condition that only the refusal *messages* move. Verified in the diff: every hunk wraps an existing message in the `refusal "limit"` helper, with no branch, condition or value touched.

**The workspace's git index is shared between agents**, and a slice learned it the expensive way: `git add <three paths> && git commit` committed nineteen files because a sibling's staged set was still in the index, and the commit message described three of them. The content was correct and every check had run on it; the *attribution* in the log was wrong. The lesson is in AGENTS.md: stage and commit in one command, never leave a staged set sitting, and amend the message rather than the record when it happens.
