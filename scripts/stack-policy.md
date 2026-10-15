# No stacked PRs

Tau Ceti prohibits carrying unmerged prerequisite PR work, including in drafts
and PRs with keep, hold, wip, human or do-not-close labels. Wait for prerequisites
to land on main, rebase, and open a standalone PR. No label exempts a stack. The
other housekeeping policies retain their own draft, bump and label exemptions.
This policy does not change bors bundle support in other repositories.

`stack_policy.py` reads only TauCetiProject/TauCeti PRs and canonical pull refs.
It never checks out candidate source, runs Lean or candidate tooling, downloads
compiled artifacts, or writes a shared cache. Fork names and PR prose are data.
The only mutable source store is a disposable bare Git repository and index.

## Evidence and limits

One sweep caches an index of at most 2,000 open PRs and 64 explicitly named
closed parents. Candidates come from shared non-main commits, a canonical
repository parent head branch matching the child's base, or affirmative PR-body
prose identifying local prerequisite PRs. A label, author, import, shared file,
branch name, non-main base alone, or mention in code/quoted/negative prose does
not prove stacking. Discovery by prose never suffices for closure.

A confirmed stack must have a current parent identity and the parent's entire
main-fork-relative diff, or a complete individual parent commit patch,
reverse-applicable to the child's current source tree.
It must also have an exact unmerged ancestor head/shared commit, or the explicit
parent/base relationship above. The source diff and its SHA-256 are reported.
Before confirming, the detector checks actual main source history for the same
complete content, including combined bors squashes and later modifications or
reverts. GitHub PR closure/mergedAt is never proof of landing. Closed but
unlanded parents remain candidates. Common main ancestors are excluded before
graph work; identical heads alone are classified as duplicate identity.
An empty or landed aggregate does not skip the individual commit search: a
child may retain prerequisite work subsequently reverted on its parent's branch.
Candidate descendants of the child are excluded so a standalone prerequisite is
not closed merely because another PR includes it. Shared ancestry with ambiguous
direction produces a gap; individual-commit fallback requires an ancestor head or
an explicit current parent/base relationship.

Bounds are 256 non-main commits per head, 16 individual commit patches per parent
when the aggregate diff does not apply, 128 parent files, 128 relevant
first-parent main-history changes per parent, 64 candidates per child, 1 MiB per
blob, 2 MiB per patch/command output, 16 MiB per API response, 128 MiB total API
responses, 4,000 API calls, 30,000 Git operations, 20 minutes per source/API sweep
and a 30-minute workflow limit.
Depth-limited canonical PR fetches are checked for shallow boundaries. Main's
complete trusted history is retained (up to 64,000 commits). Missing metadata,
deleted repositories, pagination overflow, rate limits, races, unsupported source
or exceeded bounds produce `unknown` with an explicit gap and no closure.

`no-confirmed-stack` means only that these bounded checks found no proof. It is
**not** a claim that arbitrary dependencies have been ruled out. Undetected forms:

- Unmentioned, independently rebased/cherry-picked inherited work with no shared
  unmerged commit and no matching canonical parent base branch.
- Work whose parent diff and individual commit patches were partially edited,
  split, rewritten or only partly inherited so that no complete reverse patch
  applies. These source
  relationships are not established by semantic inference.
- Parents outside the bounded index, inaccessible/deleted source or histories
  beyond the bounds. These are gaps, not proved-safe results.
- Landed work rewritten sufficiently during integration that exact reverse-patch
  equivalence no longer identifies it. Exact-source checks cannot establish
  arbitrary semantic equivalence; inspect these cases manually.

## Enforcement and retries

Main-target PR opened/reopened/edited/synchronize/draft events invoke the trusted
policy directly. Other bases invoke an unprivileged wake workflow, then the
main-defined workflow_run observer. A bounded hourly/manual sweep repairs missed
or coalesced events. The workflow checks out main-defined tooling explicitly;
candidate-defined code never receives its app token. Manual dispatch defaults
to dry-run. Every run publishes JSONL in logs, a job summary and an artifact.

The required `no-stack` PR status is pending while inspecting and failure for a
confirmed stack **before** the explanation/close transaction. Observation gaps
give an error status. A bounded no-proof result gives success with that stated
limitation. Bors reads this additional PR admission status from main's bors.toml;
the existing build, bump-guard, scope, review and publication gates remain.
This status is not required on synthetic staging commits. Parent/content changes
are reconsidered on subsequent sweeps; no waiting PR builds/rebases are started.

Immediately before each explanation and close, current child head/base/body/state,
parent head/base/body/state and main identity must match the source snapshot.
Changed identities decline the action and require a fresh run. GitHub provides no
atomic compare-and-close primitive, so a residual race exists between the final
identity read and the API mutation. The audit exposes the observed identities.

Global workflow serialization and a marker authenticated by the installation's
bot identity prevent duplicate explanations on retries. Comment failure prevents
closure. A changed proof updates the same explanation for that child head rather
than posting a second one. Close failure remains observable/nonzero and can retry
using the existing comment.
No branches are deleted. A successful close emits pull_request.closed;
bors's existing handler marks the patch closed and cancels its waiting/running
batch and try work, the same withdrawal route as bors r-. Rollout must verify
an actual admitted child's removal using the bors observation endpoint, not just
infer it from a successful GitHub API response.

## Validation and rollout

Run `python3 scripts/test_stack_policy.py` for real Git and API/mutation fixtures.
`stack_policy_fixtures.json` records read-only historical PR identities, source
evidence and literal stacking prose, including declined/stale/ambiguous cases.
Run `python3 scripts/stack_policy.py --pr NUMBER --report audit.jsonl` for a
read-only source audit; omit --pr for the bounded backlog. `--apply` explicitly
enables statuses/comments/closure and requires `STACK_ACTOR` to authenticate
prior marker comments. Production uses the app installation bot login.

Before rollout, publish the historical example classifications with exact main,
child and parent identities and content hashes. Review all confirmed closures
before the first destructive dispatch. After ordinary infrastructure review and
merge, a **new main-defined workflow dispatch** must exercise actual detection,
comment, close and queued-child withdrawal. Keep #16791 open until that evidence
is linked in its rollout-verified comment; no 24-hour baseline is required.
