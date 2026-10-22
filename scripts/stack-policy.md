# No stacked PRs

Tau Ceti prohibits carrying unmerged prerequisite PR work, including in drafts
and PRs with keep, hold, wip, human or do-not-close labels. Wait for prerequisites
to land on main, rebase, and open a standalone PR. No label exempts a stack. Other
housekeeping policies retain their own exemptions. Generic bors bundle support
in other repositories is unchanged.

`scripts/stack_policy.py` uses canonical GitHub API identities and Git source.
It does not read or interpret PR descriptions, rendered HTML, keywords, links or
claimed dependencies. Descriptions cannot supply a candidate, establish a
relationship, affect classification or authorize closure.

Historical event metadata uses the workflow GitHub token with Actions read
permission in the trusted main-defined job. The App token retains its existing
PR/issue/content permissions; candidate code receives neither token.

Candidate source is never checked out or executed. No Lean build, candidate
script, compiled artifact, publication credential or persistent cache is used to
identify a stack. Source is inspected in a disposable bare Git store/index. Fork
URLs are never fetched; objects come from this repository's canonical pull refs.

## Source evidence

A sweep caches at most 2,000 open PRs and the 64 most recently updated closed PRs
from this repository. Closed parents outside that bounded index are outside
coverage. Closed state, mergedAt and bors title markers do not establish landing.
Candidates share non-main commits or have a canonical repository parent head
branch matching the child's current base. An author, label, shared file, import,
branch name or non-main base alone never proves stacking.

A confirmed stack requires a complete individual parent commit patch retained in
the child's current tree, absent actual main source history. A current parent
head that is an exact unmerged ancestor, or an open canonical parent branch used
as the child's base, establishes direction. A child that is the other PR's
ancestor is not closed by reversing that relationship. Identical heads alone
are duplicate identity, not a stack proof.

A parent can advance after its child last merged it. Historical evidence starts
with a two-parent merge on the CHILD's first-parent line. The unique merge base
between its incoming history and the current parent must lie on the parent's
own first-parent line, outside the child's first-parent line. This supports
indirect imports through another branch. The audit records that merge and pinned
revision. Only parent-line commits NEWLY introduced by this merge are eligible:
all commits reachable from the child's pre-merge first parent are excluded,
including work it previously merged from its own side branches. The same
newly-introduced attribution rule applies when a CURRENT parent head arrived
through a merge, so an ordinary match cannot cite the child's own prefix either.
Straight forks still use exact current-head ancestry; older import pins require
the historical binding below.

A canonical GitHub Actions PR-event record must independently bind the exact
head repository, branch and pinned SHA while the parent PR existed (server
timestamps between creation and closure). This checks branch history without
parsing descriptions or trusting workflow artifacts. Fork run associations can
be empty; the binding uses server-recorded branch/head identity and PR lifetime.
Only pull_request/pull_request_target events qualify. The lookup is cached per
parent/pin and bounded at 100 results; incomplete results, missing timestamps or
unavailable event evidence are unknown.

The complete selected patch must also remain in BOTH current trees. Source
moved out of a parent cannot authorize closing its new owner because an old
parent commit once contained it. Shared precursors imported through merges by
both PRs do not establish a direction between them.

Except for an open canonical parent branch currently used as the child's base,
all relationships additionally require the same head repository and the same
known PR-author account ID. Deleted/unknown authors and third-party PR openers
cannot authorize closure. The canonical-base exception relies on repository
branch writers and the child's explicit current base choice. These identities
alone never prove stacking. Shared accounts do not distinguish independent
agents: a later PR opened at another PR's prefix can establish the same current
source relationship. PR numbering is not an exemption.

Actual main source history is checked for the complete patch, including normal
merges, combined bors squashes and later changes/reverts. Common main ancestors
are excluded before graph work. Context-free possible landing matches veto
closure as unknown; they do not establish landing. A closed parent claiming
landing without verifiable source equivalence is also unknown. Closed parents in the bounded recent index supply source observations, but
cannot authorize closure: unlanded source might instead belong to an absorbed or
resubmitted PR. Such a match is unknown, not landed or proved safe. This avoids
closing legitimate replacements of closed PRs, including policy-closed children
resubmitted after their prerequisite lands.

An empty or landed aggregate does not skip individually retained commits, but
every selected patch must remain in both current trees. Parent-side removals
cannot authorize closure. An aggregate match
alone cannot authorize closure; parts might have landed separately. For
canonical-base content matches without the original commit identity, equivalent
content must also be absent at the child's main fork point. Old main content is
base drift, not proof of inherited work. Every positive audit includes commit,
patch base, source SHA-256, current heads and inspected main.

## Bounds and remaining gaps

Bounds are 256 non-main commits per head, 16 individual patches per candidate,
128 parent files, 128 relevant first-parent main-history changes per patch,
64 candidates per child and 256 entries per first-parent graph. Main history is
bounded at 64,000 commits. Blobs are limited to 1 MiB; patch/command output to
2 MiB (8 MiB for the main commit index); API responses to 16 MiB each/128 MiB
total. A sweep permits 4,000 API calls, 30,000 Git operations and 20 minutes;
the workflow permits 30 minutes. Each detection and subsequent mutation phase
permits 256 API calls/16 MiB, 2,500 Git operations and 120 seconds, checked before
operations. PR, commit, patch, blob, graph and landing observations are cached
within the sweep. Depth-limited PR fetches are checked for shallow boundaries.

Missing/deleted/inaccessible source, API pagination/rate limits, source identity
mismatches, unsupported patches, exceeded bounds and races are recorded gaps
without closure. An individual merge/root commit is skipped while searching for
another supported commit; no merge patch is guessed. A failed individual fetch
does not abort unrelated PRs. Global observation and persistence errors fail the run. In checkpointed batches,
a global budget limit defers unfinished work only after successful progress;
zero-progress and mutation-time budget failures remain red. Focused invocations
without checkpoints still fail on global budget exhaustion.

`no-confirmed-stack` means only that these bounded checks found no proof. It is
not a proved-safe result. Undetected forms include:

- Independently rebased/cherry-picked work with no shared unmerged commit or
  matching canonical parent base branch. Prose does not change this result.
- Historical direct forks or merge histories without the supported first-parent
  relationship and canonical PR-event binding, and histories whose selected complete patches no longer
  apply to both current parent and child. Shared ancestry can remain ambiguous.
  Ordinary forks from an older parent revision that later merge its current head
  are only partly covered: their earlier shared prefix cannot establish ownership
  without stronger historical evidence. A canonical current parent base establishes
  direction independently, including after GitHub's Update branch merge.
- Partial, split or edited inherited content without complete patch identity.
  No semantic equivalence or Lean declaration parsing is attempted.
- Cross-repository or different/unknown-author relationships without a verified
  open canonical parent base branch.
- Closed-but-unlanded source relationships: dependency versus legitimate
  absorption/resubmission is unknown without a stronger trusted signal; no
  description is interpreted to resolve it. Older closed parents outside the
  64-entry index and inaccessible/deleted/mismatched refs remain outside coverage.
  Source/API/graph histories beyond the bounds also remain gaps.
- Possible landing after context drift, arbitrary semantic integration rewrites,
  or a closed landing claim without source equality.
- Repository-owned heads with a bors merged-title marker: confirmed stacks are
  blocked/explained but closure declines because the existing branch deleter
  could otherwise delete the branch.
- Missing source identities and incomplete metadata. Incremental batches retain
  unknown identities for retry on change, a new event, or a recovery sweep; they
  never interpret incomplete observation as proof that a PR is safe.

An unmerged module dependency without inherited source is not closure evidence.
Normal build gates and the worker rule to wait for prerequisites still apply.

## Enforcement, races and retries

The main-defined `stack-policy.yml` uses checkpointed automatic batches and
retains focused manual audits without checkpoint state.

Main-target opened/reopened/synchronize/draft events invoke trusted main policy.
Edited events invoke it only when the base changes; title/body-only edits are
filtered before taking a runner. Other bases use
an unprivileged wake followed by a main-defined observer. A focused invocation
inspects its selected current PR against the full parent index. A checkpointed
batch additionally covers changed and unfinished PRs from other notifications.
Out-of-order or stale wakes cannot substitute an old head for current metadata.
A target absent from the complete open index can be retired without mutation.
Hourly/manual full sweeps re-evaluate unchanged identities too.

The batching workflow coalesces automatic wakes globally, keeping the active run
and newest waiting wake. Explicit requests and scheduled sweeps remain distinct;
one job-level FIFO mutation lock serializes all writes. Its 100-entry limit still
applies, but automatic wakes contribute at most one waiting job instead of one per
PR event. Cancelled waiting wakes
are not coverage: the next batch must rediscover their changed PR identities.
Executed checks publish JSONL
in logs, a job summary and a retained artifact. `NO_STACK_APPLY=true` enables
automatic checks/enforcement. Otherwise automatic jobs skip and manual audits
remain available. Manual dispatch defaults to dry-run; `dispatch` allows only a
manual apply selecting one positive PR number for a canary.

Only a confirmed stack receives `stacked-pr`, before explanation and closure.
Main's bors config blocks admission on that label, which must be verified before
continuing. No commit statuses or admission mutations are written for ordinary
or unknown PRs. Existing build, bump, scope, review, axiom and publication gates
remain. No waiting PR rebuild/rebase loop is started.

A previous policy block can be removed only after a no-proof result, complete
index, current child/main identities and a latest label event owned by the bot.
The bounded closed index alone does not permanently veto unlabeling, but any
observed unresolved source/metadata gap retains a prior block. Human labels are
never removed. Reviewed manual label removal remains available. These
retained blocks are coverage gaps, not proofs of current stacking.

Immediately before every label, explanation and close, fresh child/parent
head/base/state/author/repository and main identities must match the snapshot.
Open PRs must still have their live branches. Changed identities decline the
write and require fresh observations. GitHub has no atomic compare-and-close
primitive, leaving a residual race between the final read and mutation.

Serialized mutations and an installation-authenticated marker prevent duplicate
explanations. A retry updates the same comment for that child head if evidence
changes. Comment failure prevents closing; failed mutation is observable/nonzero.
Branches are never deleted. Closing emits the existing `pull_request.closed`
webhook, which withdraws/cancels bors waiting/running/try work. The audit observes
exact-head membership before blocking and up to six times after closing, five
seconds apart. A still-admitted child fails the run. Missing before-observation
means withdrawal is unproved, never a successful verification claim. Closing a
running-batch member uses normal bors cancellation/recovery for remaining members.

For local no-stacking commands and tests, first materialize helpers using the
Tools revision pinned in `stack-policy.yml`, as described in
[shared tools](README-shared-tools.md). Run `python3 scripts/test_stack_policy.py`
for real Git/source and API/mutation fixtures, and
`python3 scripts/test_stack_checkpoint_restore.py` for unavailable checkpoint reads.
Historical source observations are recorded at their named revisions
in `stack_policy_fixtures.json`; they are not assertions about later heads.
Use `python3 scripts/stack_policy.py --pr NUMBER --report audit.jsonl` for a local
read-only audit; omit the number for backlog. `--apply` requires `STACK_ACTOR` to
authenticate policy comments. Deployments need a NEW main-defined dispatch using
the reviewed source; a changed closing path needs actual detection, explanation,
closure, preserved branch and observed admitted-child withdrawal verification.


## Batched observation and continuation

`--state-in state.json --state-out next.json` enables incremental batches.
`--prs N ...` selects multiple explicit targets without requiring separate
source preparation. Focused `--pr` invocations are uncheckpointed and inspect
only the selected PR.

Checkpoint version 1 contains a reporting `watermark`, ordered `pending` PR
numbers, `checked` and `failed` identities (head SHA, updated time and base ref),
and a mode and policy-source hash. Each batch enumerates the same complete
bounded open-PR index needed by the detector. Every new or changed identity is
selected, regardless of its timestamp, unless that exact identity is a retained
unknown awaiting a new event or sweep. This avoids dropping a PR skipped during
changing API pagination or delayed reads. Event targets are selected explicitly.
Event targets run first, followed by unfinished work in FIFO order, other changed
identities, and sweep-only rechecks. Repeated sweeps do not reorder the unfinished
tail. The comparison
index includes other open PRs and bounded recent-closed parents. Checkpoints grant
no closure authority; fresh checks before every mutation remain mandatory.

Missing, invalid or expired artifacts recover by selecting every current open PR.
A different dry-run/apply mode or policy-source hash also requests recovery.
`--sweep`, or a schedule/manual-backlog invocation with no focused targets, adds
all current PRs including unchanged unknowns. Scheduled recovery resumes retained
work rather than restarting at the first child. Closed targets are retired after
the complete open index is obtained; if one temporarily disappears during paging,
its unrecorded identity is rediscovered when it next appears.

Unvisited work, transient fetch/network/server failures and identity races remain
`pending`. Identity races and a child interrupted after successful progress stay
at the front for a fresh snapshot; zero-progress budget failures rotate to the
tail so the next batch can try unrelated work. Source/metadata gaps and child
cost limits are retained in `failed`, retried on identity change, a new explicit
event, or a sweep. No retry count drops coverage. This prevents one permanently
ambiguous or expensive child occupying every batch. Finished inspections are
saved individually. A runner loss before artifact publication can repeat work.

Restore and publish inside the job holding the shared mutation lock. The
`stack-policy-progress` artifact is retained for 14 days. Restore it only from
runs whose repository and workflow path match this workflow and whose event is
`pull_request_target`, or `workflow_run`/`schedule`/`workflow_dispatch` with main as
the head branch and TauCeti as the head repository. Missing, expired, invalid or
unreadable state triggers a full recovery sweep of current open PRs, never an
assumed empty queue. Unavailable artifact-index, producer-metadata or download
reads emit a notice and leave no input state, so enforcement can recover without
waiting for the checkpoint service. Unverified producers are never downloaded;
partial downloads are discarded. Publish only
the output checkpoint file, including on failure. Artifact publication commits
progress; a failed publication leaves the old artifact authoritative. Discover
artifacts directly because cancelled pending runs do not have useful state.
Budget exhaustion is successful deferral only after the current invocation saved
its own state and successfully completed a child. Zero-progress and mutation-time budget
failures remain red, as do unexpected execution and persistence failures.
Dry-run and focused manual invocations must not restore or publish the automatic
apply checkpoint artifact;
`--pr` rejects combination with `--state-out` to protect one-PR canaries.

The [shared batching regression tests](https://github.com/TauCetiProject/TauCetiTools/blob/980a7a0e321a7fe86981f6c9f872a2acad93af69/tests/test_stack_batch.py)
live in the pinned Tools repository. They cover collapsed notifications, current
identities, interruption and publication failure, shared source setup, fair
continuation, stale fork wakes and read-only execution.
