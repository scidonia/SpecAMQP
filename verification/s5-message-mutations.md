# V4: the S5 message slice's mutation controls

Method for every mutant, as this repository's V4 record states it: the tier **declared before
the run**, the mutant planted as a text patch in `lean/Spec/Message.lean`, the build, the run
over the five `vectors/message/` corpora, the diagnostic quoted verbatim, the revert by text,
and the run again as the revert's own check. No snapshot restores. The mutation window was
announced on `hub` at its start and end, because the file is mutated while the run proceeds.

The requirement is one mutant per *class* — structural, semantic-boundary, omission,
acceptance/rejection polarity — because the question is what class of wrong specification the
evidence would fail to notice, not how many mutants were planted.

| # | class | mutant | declared tier | caught by | diagnostic | verdict |
|---|---|---|---|---|---|---|
| M5 | structural | the message structure no longer admits at most one of each head section (`Assembly.add`, the `state.heads.contains kind` branch removed) | the corpus | **the corpus** | `messages-negative: msg-neg-duplicate-header -> expected a refusal, decoded the message` | killed |
| M2 | semantic boundary | the composite arity bound widened by one: `items.length > decls.length` → `items.length > decls.length + 1` | the corpus | **the corpus** | `sections-negative: sec-neg-header-six-fields -> expected a refusal, decoded the section` | killed |
| M6 | omission | the `rejected` outcome no longer counts the delivery attempt: `incrementOf .rejected = 1` → `0` | the corpus | **the corpus** | `deliveries: delivery-rejected-increments-delivery-count#1 -> the delivery-count is 0, and the vector names 1; delivery-received-then-rejected#2 -> the delivery-count is 0, and the vector names 1` | killed |
| M4 | acceptance/rejection polarity | the annotation-key policy test inverted (`understood` means refused and vice versa) | the corpus | **the corpus, on both sides of the rule** | `sections: sec-message-annotations-decode-understood-ulong-key -> expected a section, got amqp:not-implemented unsupported: …` and `sections-negative: sec-neg-message-annotations-reserved-key-without-policy -> expected a refusal, decoded the section` | killed |
| M1 | structural (first plant) | the composite reader no longer requires a mandatory field to be *present*: the `none` arm of `checkFieldList` became `pure ()` | the corpus | **nothing** | all five files: 0 failure(s) | **survivor, behaviour-equivalent** |
| M3 | omission (first plant) | the terminal-absorption rule removed whole from `applyState` | the corpus | **the acceptance theorem, at build time** | `Spec/Message.lean:1007:4: Tactic split failed` / `1024:6: rewrite failed: Did not find an occurrence of the pattern ∃ reason, Except.ok (recordState delivery state settled) = Except.error reason` | killed by V1, not by the corpus |

## The survivor, classified

M1 removes `checkFieldList`'s "a mandatory field is absent" branch and changes **no
observable verdict**, which is why every file stayed green. The reason is a duplicated
guard: the only composites in the declared surface with a mandatory field are the
delivery-state types (`received` alone has two), and `deliveryStateOfValue` reads them by
name through `unsignedField`, whose `none` arm enforces the same rule and produces the same
condition and reason class. So the removed branch is shadowed by an identical one.

The classification the plan asks for is **broad conformance evidence, not rule-isolated
evidence**: `delivery-reject-malformed-received-state` fails if *both* guards go, and nothing
in the corpus can distinguish them. The mutation is behaviour-equivalent within the declared
surface rather than a coverage hole, and the honest conclusion is the one the isolation rule
names: no vector can be authored that isolates this rule until a section type declares a
mandatory field, at which point the branch becomes observable and the generator's descriptor
sweep will already carry the vector (`gen-section-descriptor-<code>-<name>` expects a
refusal for exactly that case).

## The non-building mutant, counted as what it is

M3 does not belong in the table as a corpus run: it does not build, and this record's own
rule is that a mutation which does not build is not a mutation run. It is kept because what
stopped it is informative — the omission is killed by `terminal_absorbing`, the acceptance
theorem, in the V1 tier, before any vector runs. Removing the rule and keeping the theorem
is impossible, which is what a stated invariant is for; the corpus's
`delivery-received-then-accepted#3` covers the same rule as V2 evidence, so the rule has a
carrier in both tiers.

## Suite-shape findings

- **A bound widened by one is visible only at exactly bound + 1**, which is the lesson this
  repository's earlier V4 record already carries: `sec-neg-header-six-fields` carries
  `count 6` against a declaration of five, and it is the vector that kills M2. A vector with
  eight fields would have been refused by the widened bound too.
- **A rule has two sides and one vector per side.** M4 is killed only because
  `sec-message-annotations-decode-understood-ulong-key` and
  `sec-neg-message-annotations-reserved-key-without-policy` are the *same octets* under
  different policies: inverting the test turns the admitted one into a refusal and the
  refused one into an admission, so each vector's failure names the other's rule. The
  generator now sweeps this pair for all three annotation-shaped sections, over the
  narrow and wide ulong-key forms.
- **A quantity has to be an observable or nothing tests it.** M6 is killed by the
  delivery-count alone: the state name is the same in both the mutated and the unmutated
  artefact, and only the count distinguishes them. Every quantity a clause moves is reported
  by the delivery layer for exactly this reason.
