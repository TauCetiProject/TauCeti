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
declaration the PR adds or changes, then replace each `…` below with `changed`, `checked` or
`n/a`, a dash, and a short note: for instance `changed — dropped [NeZero n] from foo, which follows
from hn : 1 < n`, or for Q2 `checked — no change (searched TauCeti/ and the open PRs for the
defining formula of foo)`. A PR that changes no Lean declaration may answer `n/a` throughout.
When later commits add or change declarations, for instance to answer review findings, run the
checks again over those and update the lines. The `quality-pass` review angle reads this block.
Agents: `gh pr create --body` does not apply this template, so copy the block in yourself.
-->
Quality pass:
- Q1 Mathlib duplicates: …
- Q2 Tau Ceti duplicates, on main and in open PRs: …
- Q3 Hypotheses: …
- Q4 Section variables: …
- Q5 Proofs of at most 50 lines: …
- Q6 Elaboration speed: …
- Q7 API for new definitions: …
- Q8 Tidy what the PR adds or changes: …
- Q9 Statements re-read: …

<!--
Do each check with reasonable effort and your own judgment; beyond them, improve anything you can
in what the PR adds or changes. Work a check suggests on code already on `main`, such as
generalising an existing declaration, is a separate PR.

Q1. Search Mathlib for each new declaration, or a more general one, by name and by shape (`exact?`,
`apply?`, grepping the conclusion's constants). If it exists, use it. A renamed Mathlib lemma or a
one-line wrapper is a duplicate; an `instance` built from a Mathlib theorem is not.

Q2. Search `TauCeti/` for the same object or lemma by its defining formula, not only its name, and
for blocks copied from sibling files. Reuse what exists; if it first needs generalising, do that
in its own PR and build on it once merged. Then search the open PRs
(`gh pr list --repo TauCetiProject/TauCeti --search "<term> in:title,body"`, then `gh pr diff` on
candidates). If one adds the same thing, do not add a second copy: build on it once it merges, or
if yours is better, say so on both PRs, each linking the other. The note says what you searched,
on main and in the open PRs.

Q3. Delete each hypothesis and instance argument of each theorem the PR adds or changes, including
those from `variable` lines, and rebuild, before reasoning about whether it is needed. If the proof
still works, leave it out, but check the conclusion is not weaker than the docstring promises
(Q9). If it follows from the others, derive it in the proof: consistency with a related lemma is
no reason to keep it. If the proof breaks only in a degenerate case (empty, `0`, `⊥`), handle that
case. Keep a hypothesis only when the statement needs it to make sense, is false without it (give
the counterexample), or in a degenerate case holds only through a junk value such as `x / 0 = 0`.
Weaken typeclasses to what the proof uses, at a level Mathlib uses (`Field` to `CommRing`, say).
The note says what you dropped or weakened, and why any hypothesis kept for a degenerate case
stays.

Q4. No declaration picks up a `variable` instance or binder it does not use: use `omit [...] in`,
or restructure the `variable` blocks.

Q5. Count each proof's code lines, not blanks or comments. Shorten a proof over 50 lines (a Mathlib
lemma, `grind`, a better induction) or split it at natural stages: a reusable step becomes a
public, documented lemma where it belongs, a proof-specific one a `private` lemma. One that cannot
be split stays, with comments on its structure and the reason in the note. Move proof obligations
out of long `def` and `instance` bodies into lemmas, and turn a block repeated across proofs into
one lemma.

Q6. Time the PR's declarations (time the file, or set `profiler` in a scratch file). Fix anything
over about a second at its cause, often a broad `simp`, `decide`, instance search or unfolding,
without changing the statement or raising `maxHeartbeats`. In a `module` file, `#check @f.eq_1`
from a non-module file should return at once for each new definition.

Q7. Inline a new definition used once with no API, unless the roadmap names it. For every other
new definition, name the lemma that says what it is (`_def`, `_iff`, `_apply`, or the equation its
proofs use). Only such lemmas should unfold it, so a proof that unfolds it by hand shows one is
missing. Add the `ext` and `@[simp]` lemmas callers need. No theorem should hold only because of a
junk value the definition takes on degenerate inputs (empty, zero, the trivial ring). The note
names each definition's lemma.

Q8. Docstrings are accurate, state every hypothesis, do not overclaim, and credit the mathematical
source where there is one. Module docstrings list the file's main results, still match it, and
name no roadmap targets or layers (the roadmap is credited only on the roadmap line). Each added
import is needed, and `public` only if a statement uses it. No unused `open`, `classical` or
`noncomputable`. No commented-out code, `by exact`, single-use `have` that inlines cleanly, or
non-terminal `simp` without `only`; each `show` or `change` has a comment saying why. Names follow
Mathlib's conventions, and a general helper is public in the file where it belongs. Leave the rest
of an existing file alone.

Q9. Read each new statement as a mathematician would. List what its docstring promises and check
each part is in the conclusion, not moved into the hypotheses, with its quantifiers in the order
the docstring implies (one `x` for every `n` is `∃ x, ∀ n`). Check it says what the source says
and is not vacuous: the hypotheses can hold together, and the conclusion is not true for an
unintended reason. A simple, correct lemma is fine.
-->
