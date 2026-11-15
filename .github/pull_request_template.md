<!--
Every PR must replace the line below with exactly one canonical roadmap directory name,
or with `none` for genuinely general, cross-cutting, infrastructure, or dependency work.
For new mathematics, also cite the exact roadmap file and target in the prose below.
Refactors need no fresh roadmap claim, but should name the roadmap chiefly motivating them.
Do not infer a roadmap from the TauCeti/ directory being changed.
-->
Roadmap: <CanonicalAreaName or none>

<!--
Quality pass. Before you ask for review, run the checks at the end of this template over every
declaration the PR adds or changes, then replace each `…` below with `changed`, `checked`,
`declined` or `n/a`, a dash, and a short note: for instance, for Q3, `changed — foo: [NeZero n]
derived from hn : 1 < n, hn kept (false for n = 1)`, or for Q2, `checked — no change (looked for
the defining formula of foo)`. A line with a finding you have not fixed begins `declined` and
gives the reason, so review sees it. A PR that changes
no Lean declaration may answer `n/a` throughout. When later commits add or change declarations,
for instance to answer review findings, run the checks again over those and update the lines. The
`quality-pass` review angle reads this block. Agents: `gh pr create --body` does not apply this
template, so copy the block in yourself.
-->
Quality pass:
- Q1 Mathlib duplicates: …
- Q2 Tau Ceti duplicates, on main and in open PRs: …
- Q3 Hypotheses: …
- Q4 Section variables: …
- Q5 Proofs of at most 50 lines: …

<!--
The checks cover what this PR adds or changes, and nothing else. In Q3, assume each hypothesis
removable until shown otherwise.

Q1. Mathlib must not already have any declaration the PR adds, or a more general one, under any
name. If it does, use Mathlib's. A renamed Mathlib lemma or a one-line wrapper is a duplicate; an
`instance` built from a Mathlib theorem is not.

Q2. Tau Ceti must not already have the same object or lemma, on main or in an open PR: compare by
defining formula, not only by name, and look for blocks copied from sibling files. This includes
every `private` declaration the PR adds: a private helper that restates an existing Mathlib or
Tau Ceti lemma is a duplicate, so delete it and call the lemma. Reuse what exists, and do not add
a second copy of something an open PR already adds. The note says what you looked for.

Q3. Take each theorem the PR adds or changes, and each of its hypotheses and instance arguments,
including those from `variable` lines (`#check @foo` shows them all). Do not delete
each and rebuild to find out: CI's `unusedArguments` linter already reports an argument the proof
never uses, and a failed rebuild only says the current proof uses it, so decide each from the
statement. Each ends in one of four states:
dropped (the statement holds without it: change the proof if needed, even to a new argument),
derived (it follows from the others: derive it in the proof), needed to state (the statement
does not elaborate without it), or kept (the statement is false without it: give the
counterexample). Nothing else keeps one: not that the proof uses it, not that a related lemma or
the docstring has it (fix the docstring), not that removing it needs a new proof. If you can
neither drop one nor find its counterexample (an open conjecture, say), the Q3 line begins
`declined` and says so. Look especially for:
- instances only the proof uses, or implied by another hypothesis (`[FiniteDimensional K V]` by
  `0 < finrank K V`, `[IsDomain R]` by `IsFractionRing R K` for a field `K`, `[Nontrivial R]` by
  `x ≠ y`);
- hypotheses implied by the others (`0 ≤ r` from a limit of nonnegative values);
- degenerate cases (empty, subsingleton, `0`, `⊥`), where both sides are often trivial: as in
  Mathlib, a statement that holds there through a junk value such as `x / 0 = 0` needs no
  hypothesis;
- classes stronger than the statement needs (`CommRing` where `Semiring` would do, `RCLike` where
  any densely normed field works), weakened to a level Mathlib uses.
The note lists each theorem's arguments by state, grouping theorems that share them, with the
counterexample for each one kept.

Q4. No declaration picks up a `variable` instance or binder it does not use: use `omit [...] in`,
or restructure the `variable` blocks.

Q5. Shorten a proof over 50 lines (a Mathlib lemma, `grind`, a better induction) or split it at natural stages: a reusable step becomes a
public, documented lemma where it belongs, a proof-specific one a `private` lemma. One that cannot
be split stays, with the reason in the note. Move proof obligations
out of long `def` and `instance` bodies into lemmas, and turn a block repeated across proofs into
one lemma.
-->
