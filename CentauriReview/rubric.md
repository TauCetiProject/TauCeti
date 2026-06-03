# Review rubric (skeleton)

For reviewing AI-authored PRs into `Centauri/`. CI already enforces build + no-sorry +
the import boundary; reviewers focus on what can't (yet) be mechanized. Mark each PR
against the criteria below.

## 1. Integrity (mostly mechanized; reviewer confirms intent)

- [ ] No `sorry` / `admit` / `sorryAx`; no stray `axiom`.
- [ ] No `native_decide` (or, if present, explicitly justified, since it adds
      `Lean.ofReduceBool` to the trust base).
- [ ] No new dependency on the roadmap/review trees.
- [ ] Statements are not silently weakened: a theorem named for a milestone proves the
      milestone, not a vacuous or strengthened-hypothesis variant. **No assumptions
      smuggled in as hypotheses** that should be theorems.

## 2. Faithfulness (human judgement)

- [ ] Definitions capture the intended mathematical object (the "mind-reading"
      check), cross-checked against worked examples where possible.
- [ ] The statement matches the roadmap's intent and its acceptance criteria.

## 3. Design and reuse

- [ ] Uses existing Mathlib API rather than re-deriving it; no shadow re-definitions
      of things Mathlib already has.
- [ ] Reasonable abstraction level and generality; naming follows Mathlib conventions.
- [ ] Defs/lemmas have docstrings; notation is justified.

## 4. Hygiene

- [ ] Builds against the pinned Mathlib; no new linter warnings.
- [ ] PR touches only `Centauri/`.
- [ ] Reasonable file/module placement and import discipline.

---

*This is a starting point; refine it as patterns (and antipatterns) emerge, and
migrate anything mechanizable into CI per `README.md`.*
