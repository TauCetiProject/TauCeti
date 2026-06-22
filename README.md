<p align="center">
  <img src="assets/header.png" alt="Tau Ceti" width="820">
</p>

# Tau Ceti

Tau Ceti is a repository of formal mathematics, directed by human-written roadmaps,
implemented and maintained by AI contributors, subject to adversarial review.

Tau Ceti is being incubated jointly by the [Lean FRO](https://lean-lang.org/fro/) and the [Mathlib Initiative](https://mathlib-initiative.org/),
in partnership with academic and industry groups.

Our goal is to build as much mathematics as we can in a collaborative, coherent library,
at the highest quality we can, subject to the constraint that everything is written by AIs. It's an experiment, and could use your help!

We hope that by building Tau Ceti we can ensure that a significant part of AI formalization work is performed in an open-source, human curated library. Tau Ceti will be built for reuse and generality. Tau Ceti is a community resource, licensed under the Apache licence, that everyone can build on top of.

We've long dreamt about formalizing all the "basic material" in mathematics.
While we're explicitly **not** aiming here at curating and digesting mathematical knowledge in the way that a human authored library can,
we hope that we can efficiently build a reusable library at significant scale. With Tau Ceti built, we'll be closer to the point where computers can genuinely help us explore the mathematical universe (the Lean kernel verifying, the Lean langauge providing automation in proof construction, AIs assisting with proof exploration, and Tau Ceti providing the knowledge necessary to reach the research frontier).

Humans own the roadmap for Tau Ceti, which lives in the
[TauCetiRoadmap](https://github.com/FormalFrontier/TauCetiRoadmap) repo (mostly markdown, a
small amount of Lean); changes are made via human-reviewed pull requests there.

AIs own the code in this repo, initiating pull requests and shepherding them through an
AI-driven review process.

Humans can raise issues against the code, and leave implementation (and review) to AIs.

*(Tau Ceti is a sun-like star about 12 light years from our own, and a favourite setting for sci-fi stories.)*

## The three repositories

- **TauCeti** (this repo) — the AI-authored Lean mathematics.
- **[TauCetiRoadmap](https://github.com/FormalFrontier/TauCetiRoadmap)** — the human-controlled
  roadmaps that direct the work.
- **[TauCetiReview](https://github.com/FormalFrontier/TauCetiReview)** — the review rubrics and
  the machinery that runs review.

## Review

Review is entirely driven by AIs. These operate according to a fixed open source rubric. Humans write the rubric, and update it as the project evolves.

When a PR is opened, we first let CI run, including the full Mathlib linter set. Once CI passes, a review can be run against the rubrics; its verdicts are posted as "block", "changes requested", or "approval".

PR contributors can push further commits, or respond to review comments, in order to solicit updated reviews.

We've built the infrastructure to fire these reviews automatically on each PR (and on a `/review` comment), but it is currently switched off. For now, reviews are run from the command line.

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

We also have prototype systems for "meta review", using human and AI judges to do A/B testing of reviews, so that we can quantitatively evaluate review quality, and how models and rubrics feed into this quality.

## Mathlib dependency

Tau Ceti depends on Mathlib's `master` branch, and always defers to design decisions made in Mathlib.
AIs are encouraged to make PRs to Tau Ceti that bump the pin to new commits on Mathlib's `master` branch, and fix any resulting problems in Tau Ceti.

We won't push material upstream from Tau Ceti to Mathlib. Mathlib contributors are welcome to adopt, curate, and modify material from Tau Ceti, while preparing PRs to Mathlib. Everything here is Apache licensed.

## Building

```bash
lake exe cache get   # fetch prebuilt Mathlib oleans
lake build
```

## Roadmaps

The roadmaps live in the [TauCetiRoadmap](https://github.com/FormalFrontier/TauCetiRoadmap)
repo: universal covers, the Jacobian challenge, reductive algebraic groups, partial
differential equations, Heegaard Floer and knot Floer homology, and multiquadratic fields and
genus theory. When asked to work here, read the roadmap first (see `AGENTS.md`).

---

<p align="center">
  <img src="assets/tauceti-collaboration.jpg" alt="A hexapus reaching out to touch an AI's hand across a tide pool, beneath twin suns and a ringed planet." width="900">
</p>
