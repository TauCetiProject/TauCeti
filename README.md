# Tau Ceti

Let's do lots of maths.

Humans own the roadmap, which lives in the
[TauCetiRoadmap](https://github.com/FormalFrontier/TauCetiRoadmap) repo (mostly markdown, a
small amount of Lean); changes to it are made via human-reviewed pull requests there.

AIs own the code in this repo, initiating pull requests and shepherding them through an
AI-driven review process.

Humans can raise issues against the code, and leave implementation (and review) to AIs.

## The three repositories

- **TauCeti** (this repo) — the AI-authored Lean mathematics.
- **[TauCetiRoadmap](https://github.com/FormalFrontier/TauCetiRoadmap)** — the human-controlled
  roadmaps that direct the work.
- **[TauCetiReview](https://github.com/FormalFrontier/TauCetiReview)** — the review rubrics and
  the machinery that runs review.

## Review

This part is still very much an open question, which I'd like input on.

My current idea is that all PRs will be reviewed by AIs running according to a fixed open source rubric (prompt, spec, language model program, whatever you want to call it). The humans involved in this project will write that rubric, and evolve it over time as we see the need.

When a PR is opened, we will automatically launch some combination of frontier models, prompted to review the PR according to the rubric. As replies and further commits are added, we'll feed these back to the same models (possibly even resuming the conversation) for further feedback. The review agents can approve PRs, and PRs automatically merge once approved.

The rubric will be **adversarial**, including instructions to find mis-formalizations, vacuous statements, and "pushing around the lump in the carpet". We'll name specific antipatterns to look for. We'll likely need to avoid letting a frontier model review itself.

I suspect there should be multiple rubrics covering different aspects of review, and merging requires approval from everyone (or perhaps a soft cutoff for more subjective aspects of review).

These review agents' token costs will be covered by some combination of philanthropic donations (in money or in kind), and perhaps eventually on a "billable hours" basis for significant contributors. That is, industrial or academic groups making significant pull requests should expect to donate tokens sufficient to power the review bots in proportion to their contributions. Likely small scale contributions can be reviewed "for free" out of this pool.

## Mathlib dependency

For now we depend on Mathlib's `master` branch. AIs are encouraged to make PRs that bump the pin to new commits on the `master` branch, and fix any resulting problems in the library.

From Tau Ceti's point of view, Mathlib is a long way away, so we don't plan around close coordination: if you're missing something in Mathlib that you need, just build it here. (This includes needing material from Mathlib PRs; it's fine to just vendor it here with appropriate attribution, there's no need to wait.)

Conversely, we don't anticipate actively pushing material from Tau Ceti to Mathlib, even though we aspire to review standards here that are even higher than those at Mathlib. Mathlib contributors are of course welcome to adopt, curate, and modify material from Tau Ceti, and submit it to Mathlib themselves. Everything here is Apache licensed.

## Building

```bash
lake exe cache get   # fetch prebuilt Mathlib oleans
lake build
```

## Roadmaps

The roadmaps live in the [TauCetiRoadmap](https://github.com/FormalFrontier/TauCetiRoadmap)
repo: universal covers, the Jacobian challenge, reductive algebraic groups, and partial
differential equations. When asked to work here, read the roadmap first (see `AGENTS.md`).
