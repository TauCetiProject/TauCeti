# Tau Ceti

Let's do lots of maths.

Humans own the roadmap, which lives in the
[TauCetiRoadmap](https://github.com/FormalFrontier/TauCetiRoadmap) repo (mostly markdown, a
small amount of Lean); changes are made via human-reviewed pull requests there.

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

Review is entirely driven by AIs. These operate according to a fixed open source rubric. The human write the rubric, and update it as the project evolves.

When a PR is opened, we first let CI run, including the full Mathlib linter set. Once CI passes, we can automatically start reviews, which are posted, along with "block", "changes requested", or "approval" status.

PR contributors can push further commits, or respond to review comments, in order to solicit updated reviews.

We've built the infrastructure to run these review, but for now they *do not* fire automatically. You can comment `/review` on a PR to obtain a review.

You can also run the same review yourself from the command line, on your own Claude and/or Codex subscription instead of the project's metered API budget, using the `tauceti-review` tool in [TauCetiReview](https://github.com/FormalFrontier/TauCetiReview). With [uv](https://docs.astral.sh/uv/):

```bash
# print the verdicts for PR #42, posting nothing:
uvx --from git+https://github.com/FormalFrontier/TauCetiReview tauceti-review 42
# add --post to publish the scoreboard and per-rubric threads, as you:
uvx --from git+https://github.com/FormalFrontier/TauCetiReview tauceti-review 42 --post
```

It runs the identical engine and rubrics CI uses, in a clean room that ignores your personal editor configuration so the review stays reproducible. See [REVIEWING.md](https://github.com/FormalFrontier/TauCetiReview/blob/main/REVIEWING.md) for prerequisites, flags, and the contest/re-review flow.

The rubrics are **adversarial**, including instructions to find mis-formalizations, vacuous statements, and "pushing around the lump in the carpet". There are rubrics for many different aspects of review — scope, correctness, reuse, attribution, API design, generality, placement, naming, documentation, proof quality, and deprecation; see [the rubrics directory](https://github.com/FormalFrontier/TauCetiReview/tree/main/rubrics). We'll update these as we see what is most useful!

Eventually, these review agents' token costs will be covered by some combination of philanthropic donations (in money or in kind), and perhaps eventually a "billable hours" basis for significant contributors. That is, industrial or academic groups making significant pull requests should expect to donate tokens sufficient to power the review bots in proportion to their contributions. Likely small scale contributions can be reviewed "for free" out of this pool.

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
