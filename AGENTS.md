# Working in Tau Ceti

This is the AI-owned code repo of Tau Ceti. Read `README.md` for what the project is and how
the three repos fit together; this file only adds the contract for agents working here.

## Before you write code

**Read the roadmap first.** The roadmaps live in the separate
[TauCetiRoadmap](https://github.com/TauCetiProject/TauCetiRoadmap) repo. The roadmap gates
*new* mathematics: only add a new mathematical declaration (definition, theorem, instance,
notation) or file when it advances a specific roadmap target, or supplies a prerequisite that a
specific target needs. If something you want to build is not on the roadmap — whether a human
asked for it or you found the gap yourself — say so and leave it to a human to add, rather than
building it here. Never open a PR or an issue in TauCetiRoadmap yourself; reviewing a roadmap
change needs human attention.

Improving code that already exists is **always in scope** and needs no roadmap entry:
refactoring, simplifying proofs, fixing or modestly generalising an existing lemma (without
expanding the project's mathematical scope), relocating a misplaced declaration, adopting a
cleaner idiom, and documenting existing code are all welcome at any time. The roadmap conditions
what new mathematics gets *added*, not whether already-merged code may be made better.

Every pull request description must also contain one standalone attribution line:

```text
Roadmap: CanonicalAreaName
```

or:

```text
Roadmap: none
```

Use the canonical roadmap directory name. This is attribution, not authorization: new
mathematics must still cite the exact roadmap file and target it advances, while a refactor
needs no fresh roadmap claim but should name the one roadmap chiefly motivating it. Use
`Roadmap: none` for genuinely general, cross-cutting, infrastructure, or dependency work.
Do not infer the association from a `TauCeti/` directory name; code organization and roadmap
scope do not coincide.

## The rules of the repo

- `main` is always green. CI builds against pinned Mathlib and enforces: no `sorry`, no
  axioms beyond `propext`, `Classical.choice`, `Quot.sound` (so no `native_decide`), no
  `meta import`, and the Mathlib linter set (style, file length, no `maxHeartbeats`
  overrides). Do not try to disable these.
- Prefer named definitions, abbreviations, and lemmas to custom term syntax. Local tactic
  macros should remove substantial repeated proof machinery, rather than just shorten a
  couple of small proofs. Keep macro hygiene enabled: `set_option`, including
  `set_option hygiene false`, is forbidden anywhere in library code. Heartbeat-measurement
  syntax (`guard_min_heartbeats`, `#count_heartbeats`, and `#count_heartbeats!`) belongs in
  tooling rather than library code; some command forms disable limits internally. The source
  guard conservatively includes strings, qualified/quoted names, and comments containing
  double quotes, because interpolation can confuse the approximate lexer. Put explanatory
  references in comments without double quotes. A local syntax rule needed for elaboration performance
  should document the concrete need at its declaration.
- One topic per PR. Ship a prerequisite refactor as its own PR.
- Stacked PRs are prohibited, including drafts and PRs labelled keep/hold/human.
  Wait for each prerequisite to land on main before opening its dependent PR;
  then rebase onto current main and include only the new work. Targeting main
  while carrying another unmerged PR's commits or content is still stacking.
  The trusted [no-stacking policy](scripts/stack-policy.md) comments and closes
  confirmed stacks without deleting their branches. Ordinary independent PRs
  may touch the same files or share roadmap areas.
- Tau Ceti does not preserve backwards compatibility. When declarations or modules are moved,
  renamed, replaced, or deleted — including when Mathlib supersedes them — update every
  in-repository use and remove the obsolete names and module paths in the same PR. Do not add or
  retain anything whose only purpose is compatibility: aliases, wrapper declarations, forwarding
  import modules, deprecated shims (including `deprecated_module`), or duplicate theorem names.
  External users of an older revision must update to the canonical API on current `main`;
  breaking their source compatibility is not a reason to keep an obsolete surface.
- `TauCeti/` is the only place code goes, and what goes there is mathematics, not
  metaprogramming: Lean meta code is human-owned and lives in `scripts/`, which is why the
  `meta import` guard above exists. `scripts/`, `.github/`, and the lakefile
  (`lakefile.toml`/`lakefile.lean`) are human-owned. The two Lake *pins* —
  `lake-manifest.json` and `lean-toolchain` — are an exception: a **forward-only** bump of
  them (Mathlib moving forward on the branch the lakefile nominates, with the toolchain moving
  monotonically forward) is machine-validated by the `bump-guard` check and is welcome, but
  never edit the lakefile or move a pin backward. Mathlib's lakefile `rev` must always remain
  `master`; `lake-manifest.json` alone records the exact commit used by dependency bump repair PRs.
- **Never delete a PR's human-owned changes to get it past the build gate.** When a PR
  *intentionally* touches `scripts/`, `.github/`, or the lakefile (for example, a PR that adds
  a new CI check), those changes are the deliverable, not an obstacle. The gate routes such a
  PR to a human on purpose; the correct response is to wait for that human review and merge,
  never to strip the human-owned files so the PR looks auto-mergeable — that throws away the
  work the PR exists to do. This binds automated fix/review agents too: if a PR carries
  human-owned changes, leave it alone (skip it) rather than "fixing" it toward auto-merge.
- **Do not `--admin`-merge AI-authored PRs.** Landing a PR is the review pipeline's job: it
  merges only once every rubric is green (and, for `TauCeti/`-only diffs, CI is green). Using an
  admin override to bypass that gate — even when the reviews have not been run — defeats the
  project's quality control. If the pipeline is not producing verdicts, run the review
  (`tauceti-review`) or leave the PR for a human; never force it through.

## How review works

Open a PR. After CI passes, AI review agents judge it against the rubrics in
[TauCetiReview](https://github.com/TauCetiProject/TauCetiReview) (correctness, reuse, API,
naming, placement, proofs, and more) and post `approve` / `request_changes` / `block`
verdicts. Address their findings and push; re-review runs automatically on new commits, and a
human can comment `/review` to re-trigger.

If two findings contradict — one requires X while another requires not-X, or a later round
reverses a change an earlier finding required — do not silently satisfy one and let the other
re-fire. Contest one of the threads, link the conflicting one, and quote its wording (rubric
and round). Explain why both cannot hold. Show the contradiction; do not just assert one.

When every rubric approves on the current commit and the PR changes only `TauCeti/` (with CI
green), it **merges automatically**. A PR that *also* changes `lake-manifest.json` and/or
`lean-toolchain` can auto-merge too, but only once the `bump-guard` check confirms it is a
forward-only bump and the sandboxed build passes against the new pins. A PR that touches any
other human-owned path (`scripts/`, `.github/`, or the lakefile) always
needs a human review. The
review pipeline is sandboxed so it can run on untrusted PRs; see
[`SECURITY.md`](https://github.com/TauCetiProject/TauCetiReview/blob/main/SECURITY.md) in
TauCetiReview.
