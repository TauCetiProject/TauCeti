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
`declined` or `n/a`, a dash, and a short note: for instance, for Q1, `changed — dropped foo_comm,
a copy of Mathlib's mul_comm`, or for Q2, `checked — no change (looked for the defining formula
of foo)`. A line with a finding you have not fixed begins `declined` and
gives the reason, so review sees it. A PR that changes
no Lean declaration may answer `n/a` throughout. When later commits add or change declarations,
for instance to answer review findings, run the checks again over those and update the lines. The
`quality-pass` review angle reads this block. Agents: `gh pr create --body` does not apply this
template, so copy the block in yourself.
-->
Quality pass:
- Q1 Mathlib duplicates: …
- Q2 Tau Ceti duplicates, on main and in open PRs: …
- Q3 Proofs of at most 50 lines: …

<!--
The checks cover what this PR adds or changes, and nothing else.

Q1. Mathlib must not already have any declaration the PR adds, or a more general one, under any
name. If it does, use Mathlib's. A renamed Mathlib lemma or a one-line wrapper is a duplicate; an
`instance` built from a Mathlib theorem is not.

Q2. Tau Ceti must not already have the same object or lemma, on main or in an open PR: compare by
defining formula, not only by name, and look for blocks copied from sibling files. This includes
every `private` declaration the PR adds: a private helper that restates an existing Mathlib or
Tau Ceti lemma is a duplicate, so delete it and call the lemma. Reuse what exists, and do not add
a second copy of something an open PR already adds. The note says what you looked for.

Q3. Shorten a proof over 50 lines (a Mathlib lemma, `grind`, a better induction) or split it at natural stages: a reusable step becomes a
public, documented lemma where it belongs, a proof-specific one a `private` lemma. One that cannot
be split stays, with the reason in the note. Move proof obligations
out of long `def` and `instance` bodies into lemmas, and turn a block repeated across proofs into
one lemma.
-->
