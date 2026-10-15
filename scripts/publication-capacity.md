# Batch publication and terminal status capacity

The audited staging build uses the existing 8-vCPU/16-GB privileged Namespace
runner. The publisher and finalizer request **new** unprivileged ephemeral
Namespace runners, priority zero, assigned to their workflow run ID:

- Publisher: `nscloud-ubuntu-24.04-amd64-4x8-with-features;job.priority=0`
- Finalizer: `nscloud-ubuntu-24.04-amd64-2x4-with-features;job.priority=0`
- Both: `namespace-features:github.run-id=${{ github.run_id }}`

Together they use 6 vCPU/12 GB, less than the freed staging allocation. Neither
requests cache volumes, cached toolchains, git mirrors or privileged containers.
The publisher refuses a mounted `/cache` or pre-existing `.lake`. Its repository
checkouts are limited to the candidate's immutable toolchain pin and workflow-pinned
planning tools. It also reads the hostile staging artifact and inherited/public
cache objects, which the key-free planner validates as data; candidate code is
never executed. `LAKE_CACHE_KEY` remains confined to the inline curl upload step. Ordinary PRs
remain ineligible to produce shared compiled caches.

The finalizer starts after the sandbox finishes, alongside the publisher. It
reads the **current attempt's** jobs API and waits for the publisher's successful
conclusion and successful exact-map confirmation step. It also verifies the
requested publisher labels and a runner name distinct from the sandbox's. Failed,
canceled, skipped or unconfirmed publication cannot produce a green `build`.
Bors authority revalidation rejects stale batch/generation identities. Immediately
before each status POST, the writer checks for a newer run attempt and suppresses
attempts already known to be superseded. This check is best effort: GitHub's GET
and POST are not atomic, so a successor can start between them. Statuses target the
exact sandbox SHA (or the immutable dispatch SHA after early sandbox failure).

The publisher has a 15-minute execution limit. Once the finalizer starts its
observer, missing/unassigned/unobservable publication fails within five minutes;
acquired publication has a twenty-minute total observation budget. HTTP requests
and status retries are separately bounded. Failure descriptions direct operators
to the run's jobs and Namespace routing/capacity. A delayed publisher may later
finish uploading the already audited immutable candidate, but cannot turn the
finalizer's failure green. No second publisher or hosted recovery job starts.

Limits: priority orders pending work under capacity pressure; it does not reserve
resources or preempt running compilers. Namespace's direct labels support these
standard shapes, and existing production has exercised this Linux platform and
priority/run-ID routing. New unprivileged assignment still needs production
verification. This account cannot read org runner groups (403) and has no
Namespace workspace configuration credential, so no reserved-capacity SLA or
workspace-limit change is claimed. If the finalizer itself cannot acquire a
runner, its execution timeout cannot fire; the existing external bors batch
timeout remains the outer recovery bound, independent of hosted Actions runners.
It is ten hours in the current `bors.toml`; the new five-minute publisher bound
applies only after a finalizer has been acquired and started observing.
An operator must inspect the queued job's empty runner name and correct provider
capacity/routing before retrying. A complete Namespace outage cannot be recovered
by another job on the same unavailable platform.

Provider references:

- [Runner label grammar and opt-in caches](https://namespace.so/docs/reference/github-actions/runner-configuration)
- [Priority and deterministic assignment](https://namespace.so/docs/solutions/github-actions/runner-controls/job-ordering)
- [Concurrency resource limits](https://namespace.so/docs/architecture/compute/resource-limits)

## Landing and production verification

Keep the finalizer-only prerequisite #16784 independent, and target this
follow-up at `main`. Both require genuine human infrastructure review and
head/base-bound bors approval. Do not use an admin merge, cancel unrelated
batches, change compiler fallback or budgets, or close #16782 before verification.

After landing, observe a **new** normal bors staging dispatch from the updated
default branch. Re-running a pre-landing workflow does not exercise its new
immutable tooling. Record the new run's workflow revision and exact candidate
from its dispatch identity/logs; use one monitor for that run:

```sh
gh run watch RUN_ID --repo TauCetiProject/TauCeti --exit-status --interval 120
gh api repos/TauCetiProject/TauCeti/actions/runs/RUN_ID/jobs \
  --jq '.jobs[] | {id,name,status,conclusion,created_at,started_at,completed_at,runner_name,labels}'
gh api repos/TauCetiProject/TauCeti/commits/CANDIDATE_SHA/status \
  --jq '.statuses[] | select(.context == "build")'
```

For both publisher and finalizer, subtract `created_at` from `started_at` for
queue wait and `started_at` from `completed_at` for execution. For a queued job,
GitHub sometimes reports `started_at` equal to creation despite no acquisition;
check `status` and `runner_name` before interpreting timestamps. Require distinct
sandbox/publisher/finalizer runner names, the exact unprivileged labels, publisher
isolation preflight, scoped token permissions, successful byte-for-byte full-map
confirmation, the required terminal status on the tested candidate, and bors
promotion of that candidate onto main. Link the publisher/finalizer logs and bors
promotion evidence on #16782. Ordinary PR CI must skip both batch jobs.

Local acceptance uses `test_finalize_batch.py` (including unavailable runner,
missing secret, cancellation and stale-generation cases), existing hostile
staging/path/symlink/digest and map tests, stock Lake integration, staging/train
identity tests and actionlint. After all gates and fresh production evidence pass,
post `rollout-verified: ...` on #16782 with merged PRs/checks/run/promotion links,
then close it. There is no 24-hour baseline wait.
