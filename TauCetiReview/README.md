# TauCetiReview

Human-owned. This is where review of AI-authored `TauCeti/` PRs is specified,
first as written rubrics, later (the ambition) as bots that apply them.

The split with CI: anything in review that *can* be a mechanical check should become
a CI check, so human/automated review is reserved for the judgement calls that can't
be mechanized (is this the right abstraction? is the statement faithful to intent?).

## Status

- `rubric.md`: the initial human-review rubric (skeleton).
- `Axioms.lean`: the axiom-allowlist audit, run in CI as `lake exe axioms`.
- Review bots: TBD.

## Already mechanized in CI (`.github/workflows/ci.yml`)

- Builds against pinned Mathlib.
- **Axiom-allowlist audit** (`Axioms.lean`, `lake exe axioms`): inspects the built
  `TauCeti` environment and asserts every declaration *defined in `TauCeti`* depends only
  on the allowlist `propext`, `Classical.choice`, `Quot.sound`. Because it reads the
  kernel environment, not source text, it catches what a grep cannot: `sorry`/`admit`
  (as `sorryAx`), `native_decide` (as `Lean.ofReduceBool`), and any home-rolled `axiom`,
  including ones reaching in through imports. This subsumes the old textual no-sorry guard.
- `TauCeti/` does not import the roadmap/review trees (so it cannot inherit sorried
  goals, the real trust boundary, since the two-`lean_lib` split alone is only build
  convenience).

## Planned checks (to migrate from rubric → CI)

- **Statement faithfulness.** A lockfile pinning the expected *type* of each roadmap
  milestone, with CI failing if a claimed solution's signature drifts from it, so
  "prove milestone X" can't be won by weakening the statement.
- **AI-PR path guard.** An AI-authored PR may touch only `TauCeti/`.
- Docstring presence; environment linters.
