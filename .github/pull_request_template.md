<!--
Every PR must replace the line below with exactly one canonical roadmap directory name,
or with `none` for genuinely general, cross-cutting, infrastructure, or dependency work.
For new mathematics, also cite the exact roadmap file and target in the prose below.
Refactors need no fresh roadmap claim, but should name the roadmap chiefly motivating them.
Do not infer a roadmap from the TauCeti/ directory being changed.
-->
Roadmap: <CanonicalAreaName or none>

<!--
Quality pass. Before you ask for review, run the checks explained at the end of this template
over every declaration the PR adds or changes. Then replace each `…` below with `changed`,
`checked` or `n/a`, a dash, and a short note saying what you changed, what you checked, or why
the check does not apply: for instance `changed — dropped [NeZero n] from foo, which follows
from hn : 1 < n`. A PR that changes no Lean declaration may answer `n/a` throughout.

When later commits add or change declarations, for instance to answer review findings, run the
checks again over those and update the lines. The `quality-pass` review angle reads this block.
Agents: `gh pr create --body` does not apply this template, so copy the block into your
description yourself.
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
The checks. Each is a reasonable attempt, not a guarantee: do what is reasonable, then say what
you did. Keep to the PR's topic. A check that suggests reworking code already on main, such as
generalising an existing declaration or tidying the rest of a file, is a separate PR.

Q1. Mathlib duplicates. For each new public declaration, search Mathlib for the same statement or
a more general one: by name pattern, and by statement shape (grep the main constants of the
conclusion, try `exact?` and `apply?`). If one exists, delete yours and use it at every call site.
A new name for a Mathlib lemma, or a one-line wrapper around one, is a duplicate. A lemma about a
Tau Ceti definition, or an `instance` registering a Mathlib theorem, is not.

Q2. Tau Ceti duplicates, on main and in open PRs. Search `TauCeti/` for the same object or lemma:
grep the defining formula and the key constants, not only the name. Look for a second construction
of something another file already builds, a block copied from a sibling file, and a lemma
re-derived locally that is already imported. Reuse the existing one. If it would first need
generalising, that is a prerequisite refactor: open it as its own PR and build on it once it has
merged.
Then search the open pull requests to Tau Ceti, the work not on main yet: search their titles and
descriptions for your declarations' names and the key constants of your statements, list the open
pull requests that touch the same files or directories, and read the diff of any that might add the
same thing (for instance `gh pr list --repo TauCetiProject/TauCeti --state open --search "<name>
in:title,body"`, then `gh pr diff` on each candidate). If one adds it, do not add a second copy.
When it came first or is the better one, drop yours, or build on it once it has merged (never stack
on it). When yours is the better one, say so on both pull requests, each linking the other, so that
a person or the reviewers can choose. The note says what you searched, on main and in the open
pull requests.

Q3. Hypotheses. For every hypothesis and instance binder of every theorem the PR adds or changes,
including those pulled in from `variable` lines:
- Delete it and rebuild. If the proof still works, leave it deleted.
- If it follows from the other hypotheses (`[NeZero n]` from `1 < n`, `[Finite K]` from a
  cardinality bound, `[Module.Free k M]` from a basis, `[T2Space G]` from a Lie group structure),
  derive it inside the proof instead of asking every caller for it.
- If the proof breaks only in a degenerate case (an empty type, `0`, `⊥`, the zero ring), handle
  that case and drop the hypothesis when the statement holds there for a real reason (an empty
  sum, an a.e. statement for the zero measure, contradictory hypotheses). Keep it when the
  statement would hold there only through a junk value (`x / 0 = 0`, `(0 : ℝ)⁻¹ = 0`,
  `ENNReal.toReal ⊤ = 0`, the `finrank` or `Nat.card` of something infinite being `0`).
- Weaken typeclasses to what the proof uses, at the level Mathlib's conventions use: `Field` to
  `CommRing` or `IsDomain`, `CommSemiring` to `Semiring`, `NontriviallyNormedField` to
  `NormedField`.
- A hypothesis that a definition in the statement takes is needed to state it: leave it.
- Before you drop one, check the statement is the intended one. A hypothesis that looks unused can
  be the symptom of a conclusion weaker than the docstring promises: compare them.
Update every caller.

Q4. Section variables. No theorem the PR adds or changes carries an instance from a `variable`
line that it does not use, and no definition takes a binder its body ignores. Use `omit [...] in`,
or restructure the `variable` blocks.

Q5. Proofs of at most 50 lines. Count the code lines of each proof the PR adds or changes, not
blank lines or comments. For a proof over 50 lines, first look for a shorter route: a Mathlib
lemma, `grind`, `positivity`, `fun_prop`, a better induction principle. Otherwise split it at its
natural stages into lemmas of at most 50 lines each: a step that is a reusable result in its own
right becomes a public, documented lemma in the file where it belongs, and a step specific to this
proof becomes a `private` lemma. Keep the main statement unchanged. In the rare case where a proof cannot be split,
keep it, add comments inside it explaining its global structure, and say why in the note. Treat
long `def` and `instance` bodies the same way (move the proof obligations into lemmas), and turn
any block repeated within or across the PR's proofs into one lemma.

Q6. Elaboration speed. Time every declaration the PR adds or changes, for instance with the
`profiler` option set in a scratch file (`set_option` is not allowed in library code) or by timing
the file. For anything over about a second, find the cause and fix it, keeping the statement
unchanged and never raising `maxHeartbeats`. Common causes: a broad `simp` or `simp_all` (use
`simp only [...]` or a sharper lemma), `decide` or `norm_num` on large terms, instance search
through long chains (supply the instance), `rfl` or `exact` forcing definitional unfolding (state
an intermediate `have` with its type, or prove an equation lemma), and `convert` on large terms. In
a `module` file, check that `#check @f.eq_1` from a non-module file returns at once for each new
definition.

Q7. API for new definitions. Give each new definition its characteristic lemmas (`_apply`, `_def`,
`ext`, and `@[simp]` lemmas whose left-hand side is in simp normal form, so that they fire), so that
callers do not re-derive them. Inline a definition that has no API and is used once, unless the
roadmap names it. Evaluate each new definition on degenerate inputs (empty, zero, the trivial
ring): if it returns a junk value there, make sure no theorem holds only because of it.

Q8. Tidy what the PR adds or changes. Leave the rest of an existing file alone.
- The module docstring of each new file lists the main definitions and results in it, and that of
  a changed file still matches; neither names roadmap targets or layer numbers.
- The docstring of each public declaration the PR adds or changes is accurate: it states every
  hypothesis, does not overclaim, and points to the right mathematical reference. The roadmap is
  credited only on the roadmap line of the description.
- The imports the PR adds are needed, and no `public import` is used only in proofs. No unused
  `open`, `classical`, `noncomputable`, or local instance.
- No commented-out code, and no double blank lines.
- `show` and `change` appear only with a comment explaining why, and nothing relies on accidental
  definitional equality across wrappers or coercions.
- No `by exact t` (write `t`), no single-use `have` that inlines cleanly, and no non-terminal `simp`
  without `only`.
- Names follow Mathlib's conventions: they describe the conclusion and sit in the namespace that
  dot notation wants. A general helper is public in the file where it belongs, not `private` in a
  specific one.

Q9. Statements re-read. Read each new statement as a mathematician would. Check that it says what
the docstring and the source say, with nothing moved into the hypotheses, and that it is not
vacuous: the hypotheses can hold together, and the conclusion does not hold for a reason the
docstring does not intend. A simple, correct lemma is fine.
-->
