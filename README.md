<p align="center">
  <img src="assets/header.png" alt="Tau Ceti" width="820">
</p>

# Tau Ceti

Tau Ceti is a repository of formal mathematics, directed by human-written roadmaps,
implemented and maintained by AI contributors, subject to adversarial review.

Tau Ceti is being incubated by the [Lean FRO](https://lean-lang.org/fro/)
in partnership with academic and industry groups.

Our goal is to formalize as much mathematics as we can in a collaborative, coherent library,
at the highest quality we can, subject to the constraint that everything is written by AIs. It's an experiment, and could use your help!

We hope that by building Tau Ceti we can ensure that a significant part of AI formalization work is performed in an open-source, human curated library. Tau Ceti will be built for reuse and generality. Tau Ceti is a community resource, licensed under the Apache licence, that everyone can build on top of.

We've long dreamt about formalizing all the "basic material" in mathematics.
While we're explicitly **not** aiming here at curating and digesting mathematical knowledge in the way that a human authored library like [Mathlib](https://leanprover-community.github.io/) can,
we hope that we can efficiently build a reusable library at significant scale. With Tau Ceti built, we'll be closer to the point where computers can genuinely help us explore the mathematical universe:
* the Lean kernel verifies
* the Lean language and user tactics provide automation in proof construction
* AIs assist with proof exploration
* and Mathlib, Tau Ceti, and other libraries provide the knowledge necessary to reach the research frontier.

Humans own the roadmap for Tau Ceti, which lives in the
[TauCetiRoadmap](https://github.com/FormalFrontier/TauCetiRoadmap) repository (mostly in the form of markdown files, together with a
small amount of Lean); changes are made via human-reviewed pull requests there.

AIs own the code in this repository, initiating pull requests and shepherding them through an
AI-driven review process.

Humans can raise issues against the code, and leave implementation (and review) to AIs.

*(Tau Ceti is a sun-like star about 12 light years from our own, and a favourite setting for sci-fi stories.)*

## The three repositories

- **TauCeti** (this repository) — the AI-authored Lean mathematics.
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


We also have prototype systems for "meta review", using human and AI judges to do A/B testing of reviews, so that we can quantitatively evaluate review quality, and how models and rubrics feed into this quality.

## Mathlib dependency

Although Tau Ceti and [Mathlib](https://leanprover-community.github.io/) differ both in the review mechanisms and in design standards, and while they target different mathematical goals, we envision a strong synergy between the two libraries. We hope to build overlapping communities around both libraries.

Tau Ceti depends on Mathlib's `master` branch, and always defers to design decisions made in Mathlib.
AIs are encouraged to make PRs to Tau Ceti that bump the pin to new commits on Mathlib's `master` branch, and fix any resulting problems in Tau Ceti.

We won't push material upstream from Tau Ceti to Mathlib. Mathlib contributors are welcome to adopt, curate, and modify material from Tau Ceti, while preparing PRs to Mathlib. Everything here is [Apache licensed](http://www.apache.org/licenses/).

## What Tau Ceti is, and is not

> The product of mathematics is clarity and understanding. Not theorems, by themselves. ... There is no way to run out of ideas in need of clarification. The question of who is the first person to ever set foot on some square meter of land is really secondary. --- Bill Thurston

There are many reasons to work on formalizing mathematics, and everyone involved in formalization comes with different reasons. Here are some:

1. To enjoy the satisfying feeling of the :tada: emoji when the computer accepts your proof.
2. To build a modern Bourbaki, digesting and curating mathematical knowledge into a coherent and general form, usable in interactive theorem provers.
3. To collectively learn how to make best use of, and improve, interactive theorem provers, such as the Lean language.
4. To participate in a community of like-minded researchers on a common project.
5. To strengthen trust in the existing mathematical literature, through a combination of audited definitions and theorem statements, and machine verified proofs.
6. To build a reusable and open library of formal mathematics, that others can freely build on top of.

**Tau Ceti is focused primarily on the last point: building an open library, at a quality level sufficient that others can reuse and build on top of it, and at a large enough scale that building on top of it allows downstream projects to reach the research frontier across many areas of mathematics** (though, as we discuss below, points 4 and 5 matter to us too).

Tau Ceti is not particularly relevant if you're most interested in :tada:, Bourbaki, and learning how to use and improve Lean itself.
Particularly on the Bourbaki front, Tau Ceti is not trying to improve the state of the art for curation, clarity, and understanding: those are explicitly human activities, and should happen in libraries like Mathlib and other human-curated downstream libraries. This is what Mathlib excels at, and is rightly proud of its achievements. Similarly, it seems unlikely that we'll learn much about using and improving Lean while working on Tau Ceti besides, hopefully, some scaling problems! Tau Ceti explicitly sets out to follow Mathlib decisions regarding design and use of language features, because these decisions are hard earned through years of expert usage in formalizing mathematics. We think it's essential that as this knowledge evolves in Mathlib and other libraries, Tau Ceti follows and adapts to these lessons.

We do hope that Tau Ceti will provide a home for many researchers who want to participate in an active and engaging community. It will be a very different process than contributing to libraries like Mathlib. Primarily, the work is to do high level design: learning to write effective and thorough roadmaps, which efficiently lay out the plans to formalize large areas of mathematics well. We'll need deep mathematical expertise in every subject area, and there's a lot of learning to do about how to write roadmaps that produce the best AI output. We're already getting started on these experiments, and Tau Ceti is an opportunity to build a *new community* around a new kind of formalization work.

Similarly, we expect that Tau Ceti will help build trust in the existing informal literature. Of course, AI formalized definitions are, a priori, untrustworthy, and a big part of the success criteria for Tau Ceti will be in establishing trust from an initially untrustworthy base. We're working on projects to help rapidly audit deep definition chains. Just as in informal mathematics, trust in results isn't really achieved during initial review. We know that results are true only after they've been integrated into a deeper web of mathematics: we've proved more theorems on top of the definitions, and connected the theory to other parts of mathematics. Our hope is that the scale of Tau Ceti will help us achieve that here, and allow the rapid validation of results *by building the theory downstream as well*.

## Financial model
We're aware that training and running powerful AIs come at a significant financial and environmental cost. We're also aware that at present the most capable agents are commercial offerings, and consider the question of bridging industrial and academic practices very seriously.

For the time being, we will run initial CI and reviews for individual contributors and experiments (we don't really have a budget even for this, but will scrape something together), and expect that contributors will cover the costs of generating the code included in their PRs.

It is essential that Tau Ceti remains an open source project, and however inference for generation or review is paid for, the outputs will always be free (as in both speech and beer), protected by the Apache licence.

We intend to move to a system where review agents' inference costs are covered by the large scale contributors to the library. This may be in the form of donations (in money or tokens) to the umbrella organizations (the Lean FRO and/or the Mathlib Initiative), or by in-kind inference using sufficiently capable in-house models. We anticipate that individual contributions can be reviewed "for free" out of this pool.

Finally, we understand that participating in AI-assisted mathematics research requires the ability to pay for inference costs, potentially adding a further barrier to entry on top of the existing societal/financial privilege implicit in holding a research position. We're not sure how to respond to this. Possibilities include advocacy for public and private funding, advocacy for capability limitations, and technical capability work on open weight models and cheaper models. Each of these are difficult, have potential adverse effects, and unknown consequences. We hope that everyone involved in Tau Ceti will think hard about these questions, and contribute to meaningful and beneficial solutions.

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

Before starting a substantial piece of roadmap work, register and claim your intention so you
don't collide with others; see [Coordinating work: intentions and claims](https://github.com/FormalFrontier/TauCetiRoadmap#coordinating-work-intentions-and-claims).

---

<p align="center">
  <img src="assets/tauceti-collaboration.jpg" alt="A hexapus reaching out to touch an AI's hand across a tide pool, beneath twin suns and a ringed planet." width="900">
</p>
