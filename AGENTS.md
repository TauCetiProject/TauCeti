# Working in Tau Ceti

This is the AI-owned code repo of Tau Ceti. Read `README.md` for what the project is and how
the three repos fit together; this file only adds the contract for agents working here.

## Before you write code

**Read the roadmap first.** The roadmaps live in the separate
[TauCetiRoadmap](https://github.com/FormalFrontier/TauCetiRoadmap) repo. Only do work that
advances a specific roadmap target, or supplies a prerequisite that a specific target needs.
If a human asks for something that is not on the roadmap, say so and ask them to add it to the
roadmap first, rather than building it here.

## The rules of the repo

- `main` is always green. CI builds against pinned Mathlib and enforces: no `sorry`, no
  axioms beyond `propext`, `Classical.choice`, `Quot.sound` (so no `native_decide`), and the
  Mathlib linter set (style, file length, no `maxHeartbeats` overrides). Do not try to disable
  these.
- One topic per PR. Ship a prerequisite refactor as its own PR.
- `TauCeti/` is the only place code goes; everything else (`Scripts/`, `.github/`, the Lake
  config) is human-owned.

## How review works

Open a PR. After CI passes, AI review agents judge it against the rubrics in
[TauCetiReview](https://github.com/FormalFrontier/TauCetiReview) (correctness, reuse, API,
naming, placement, proofs, and more) and post `approve` / `request_changes` / `block`
verdicts. Address their findings and push; re-review runs automatically on new commits, and a
human can comment `/review` to re-trigger.
