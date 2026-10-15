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

A confirmed stack must have a current parent identity and a complete individual
parent commit patch reverse-applicable to the child's current source tree.
It must also have an exact unmerged ancestor head or a canonical parent branch
as its base. For a body-only rebase/cherry-pick link, both the complete current
parent aggregate and its head commit patch must be present; a shared precursor
alone cannot establish direction. Content-only evidence must also be absent at
the child's main fork point; old main content is base drift, not inherited work.
Except for a current open canonical parent branch used as the child's base, every
relationship additionally requires the same head repository and the same known
PR-author account ID. An unpinned prose reference does not bypass these guards:
it can remain stale after the original prerequisite lands, while another account
force-pushes that parent to a copied prefix of the now-standalone child.
Deleted/unknown authors and an outsider opening a PR from someone else's branch
also cannot authorize closure. The canonical-base exception relies on the
child's current explicit base choice and the open parent's live branch identity,
rechecked before mutation. [GitHub requires write access to the source branch
to open a PR](https://docs.github.com/en/rest/pulls/pulls#create-a-pull-request);
the canonical exception therefore trusts repository branch writers. Account
identity does not distinguish independent agents sharing that account. If one
opens a prerequisite PR at another PR's prefix, the existing source proof can
classify the older PR as stacked and close it even when the prerequisite PR was
opened later. PR numbering does not exempt a current confirmed stack.
Repository or author identity alone never proves stacking. The source diff and
its SHA-256 are reported.
Before confirming, the detector checks actual main source history for the same
complete content, including combined bors squashes and later modifications or
reverts. GitHub PR closure/mergedAt is never proof of landing. Closed but
unlanded parents remain candidates. Common main ancestors are excluded before
graph work; identical heads alone are classified as duplicate identity.
Context-free reverse patches are used only to exclude uncertain closures: a
match after context drift is `unknown`, not proof that a parent landed. A closed
parent claiming a normal/bors landing without verifiable source equivalence is
also unknown. Closed parents are considered only for children explicitly naming
them, so unrelated body references cannot change another child's classification.
An empty or landed aggregate does not skip the individual commit search: a
child may retain prerequisite work subsequently reverted on its parent's branch.
An aggregate match cannot independently authorize closure either: its parts may
have landed separately on main without ever coexisting in one main snapshot.
Candidate descendants of the child are excluded so a standalone prerequisite is
not closed merely because another PR includes its exact current head. Rebased
shared ancestry with ambiguous direction produces a gap.

Bounds are 256 non-main commits per head, 16 individual commit patches per parent,
128 parent files, 128 relevant
first-parent main-history changes per parent, 64 candidates per child, 1 MiB per
blob, 2 MiB per patch/command output (8 MiB for the bounded main commit index),
16 MiB per API response, 128 MiB total API
responses, 4,000 API calls, 30,000 Git operations, 20 minutes per source/API sweep
and a 30-minute workflow limit.
Depth-limited canonical PR fetches are checked for shallow boundaries. Main's
complete trusted history is retained (up to 64,000 commits). Missing metadata,
deleted repositories, pagination overflow, rate limits, races, unsupported source
or exceeded bounds produce `unknown` with an explicit gap and no closure.
Each detection and subsequent validation/mutation phase has a 256-call/16-MiB
API budget, 2,500 Git operations
and 120-second budget checked before operations. A child exceeding these limits
becomes unknown while other PRs continue. Cheap direction/ownership checks
precede expensive content checks; summary records Git operations and elapsed time.

`no-confirmed-stack` means only that these bounded checks found no proof. It is
**not** a claim that arbitrary dependencies have been ruled out. Undetected forms:

- Unmentioned, independently rebased/cherry-picked inherited work with no shared
  unmerged commit and no matching canonical parent base branch.
- Cross-repository or different/unknown-author relationships without a current
  canonical parent base branch, even with an unpinned explicit parent reference.
  Such a reference cannot authenticate a later force-pushed head. Immutable head
  declarations or trusted changed-parent history are not yet supported.
- Work whose parent diff and individual commit patches were partially edited,
  split, rewritten or only partly inherited so that no complete reverse patch
  applies, and body-only links whose current parent content is incomplete.
  These relationships are not established by semantic inference.
- Parents outside the bounded index, inaccessible/deleted source or histories
  beyond the bounds. These are gaps, not proved-safe results.
- Individual merge/root commit patches. The detector skips these while looking
  for a separate supported commit within the same bound, then records a gap if
  none proves inheritance. It never guesses a merge's parent/content identity.
- Context-free possible landing matches (including ambiguous deletion-only
  patches) are unknown. Arbitrary semantic rewrites during integration cannot
  be identified by exact source matching; closed landing claims without source
  proof are unknown. The policy never declares semantic equivalence from prose.
- A repository-owned head with bors's merged-title marker is blocked when proved
  stacked but not closed automatically: the existing bors branch deleter could
  interpret that marker as permission to delete the branch. Fork heads and
  ordinary unmerged repository heads use the normal closure path.

## Enforcement and retries

Main-target PR opened/reopened/edited/synchronize/draft events invoke the trusted
policy directly. Other bases invoke an unprivileged wake workflow, then the
main-defined workflow_run observer. Every event performs a bounded backlog sweep,
so coalesced events cannot starve a pending hourly sweep. Manual dispatch can
select one PR. The triggering PR is classified first, followed by the newest
backlog PRs, so
old costly claims cannot prevent the triggering PR from being checked.
The workflow checks out main-defined tooling explicitly; candidate-defined code
never receives its app token. Every run publishes JSONL
in logs, a job summary and an artifact. `NO_STACK_APPLY=true` enables enforcement;
otherwise all triggers audit only. Manual dispatch additionally defaults to
dry-run. Clearing this repository variable pauses mutations while audits continue.
`NO_STACK_APPLY=dispatch` permits only a manual apply selecting one positive PR
number, for a production canary before enabling automatic sweeps. A dry-run also
checks current identities and live fork branches for every confirmed result.

Only a confirmed stack receives the `stacked-pr` label **before** its explanation
and close. Main's bors.toml blocks admission on that label using the existing
block-label path. The script verifies the label took effect before proceeding.
It writes no commit statuses and makes no admission mutations for ordinary or
unknown PRs. Moving main therefore does not invalidate unrelated clean heads or
consume recurring status slots. The existing build, bump-guard, scope, review and
publication gates remain. An obsolete policy label is removed only after a
complete no-proof result, complete parent index, fresh identity checks and a
latest label event owned by the policy bot. Human-applied labels and uncertainty
retain a prior block. Existing status/roadmap label reconciliation preserves it.
Retaining a block is an audit gap, not a failed mutation. A persistently incomplete
repository index can prevent automatic removal; manual label removal after review
remains available. A source/API identity mismatch is never resolved by guessing.
Parent/content changes are reconsidered on subsequent sweeps; no waiting PR
builds/rebases are started. A deleted fork is recorded per PR, not a reason to
abort all other observations. Failed individual ref fetches likewise produce gaps.

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
Unknown detections remain explicit in the audit summary; only mutation or
withdrawal failures make a completed per-PR sweep fail. Global observation
failures and global source/API budget exhaustion still fail the run. Closed-parent budget overflow affects the children
naming unavailable parents, rather than preventing unrelated classifications.
The apply audit records read-only bors membership before the blocking label and
close, then makes at most six observations (five-second gaps) after close. A
still-admitted child fails the run visibly. Missing pre-close observations are
reported as unproved withdrawal, never as a successful production verification.
Closing a member of a running batch uses bors's existing batch cancellation and
remaining-member recovery behavior.

## Running the policy

Run `python3 scripts/test_stack_policy.py` for real Git and API/mutation fixtures.
`stack_policy_fixtures.json` records read-only historical PR identities, source
evidence and literal stacking prose at its named detector/main revisions, including
declined/stale/ambiguous cases. These are observations, not a claim about later heads.
Run `python3 scripts/stack_policy.py --pr NUMBER --report audit.jsonl` for a
read-only source audit; omit --pr for the bounded backlog. `--apply` explicitly
enables labels/comments/closure and requires `STACK_ACTOR` to authenticate
prior marker comments. Production uses the app installation bot login.

To verify deployment, issue a new main-defined workflow dispatch and inspect its
audit artifact. Production verification requires actual detection, explanation,
closure, preserved branch and observed removal of a previously admitted child.
