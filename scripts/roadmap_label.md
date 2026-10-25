# Roadmap label automation

`roadmap-label.yml` classifies open, reopened, pushed, and body/base-edited PRs.
Title-only edits are ignored because the title supplies no classification
evidence. A 20-second delay before token creation lets rapid events on one PR
collapse through its cancellation group. Ignored title edits use a separate
group, so they cannot cancel a meaningful run before their job is skipped. Only trusted default-branch code runs;
the PR body and changed file paths remain API data.

## Credentials and API usage

`GH_READ_TOKEN` is the job's `GITHUB_TOKEN`. PR metadata, labels, and changed files
are fetched together using a small GraphQL query, paginated when necessary. The
same snapshot supplies the advisory structure nudge. File pagination restarts on a changing head/base/body. At the 3,000-file
API boundary, or on an incomplete listing, one proven infrastructure path safely
selects `roadmap/none`; otherwise the result is `roadmap/Unknown` with a notice.
Incomplete diffs skip structure analysis and attribution nudges. Repository label probes and comment listings use REST reads.

`GH_TOKEN` remains the scoped App installation token for mutations. This matters:
App label/comment events drive downstream workflows, whereas `GITHUB_TOKEN`
label/comment mutations suppress those workflow triggers. Although
`pull_request_target` can grant write permissions on fork PRs, swapping the write
token without replacing those triggers would change behavior. Local invocations
without `GH_READ_TOKEN` use the normal authenticated `gh` credential for both.

Both credentials have finite budgets. The workflow token normally has only
1,000 REST requests and 1,000 GraphQL points per hour per repository, shared with
other workflows. Sharing reads reduces pressure on the App but can move the
bottleneck to this smaller budget. Check both resource readings during a busy
hour after rollout; a low budget or a deferred recovery is visible in the logs. Minting a
new token for the same App installation does not give it a new budget.

Every response records its credential role, HTTP status, rate-limit resource,
remaining quota, and reset time in `github-api:` log lines. The final
`github-api-summary:` and Actions step summary contain this process's request
counts, reads/writes, GraphQL query points, and latest response-header readings.
They never include tokens or PR/comment bodies. Remaining quota is shared with
other jobs: a change in that value alone cannot be attributed to this process.
The counters measure these scripts, not all workflows using the installation.

For a comparison across workflows, download a bounded sample of Actions logs
with `gh run view RUN_ID --attempt ATTEMPT --log > logs/RUN_ID.log`. Save an
array of the corresponding Actions run objects (including `id`, `name`,
`conclusion`, and `run_attempt`) in `runs.json`, then run:

```bash
python3 scripts/github_api_report.py --runs runs.json --logs logs --out api-report.json
```

The offline report groups observed reads/writes by workflow, credential role,
and API resource, and includes GraphQL costs and structured rate-limit evidence.
It reports missing logs and missing instrumentation explicitly. Sampled totals
are not installation-wide usage; quota changes include other consumers. Use
matching run attempts and unique run IDs, and compare samples collected in the
same way. New runs also count unchanged roadmap-label/structure-comment
decisions; these are not hypothetical HTTP requests saved. Queue age and
admission delay need separate queue observations.

## Writes and retries

A PR already carrying exactly the desired roadmap label causes no label mutation
or repository label probe. Relabeling adds the desired label before removing
stale roadmap labels, preserving unrelated labels. Repository labels are created
only after a definite 404; concurrent `already_exists` creation is accepted.
Existing label presentation is maintained separately through `--sync-labels`.
An unchanged structure comment also causes no mutation. Comments are capped at
60,000 UTF-8 bytes, with an omission notice. App jobs select their own bot
comments; duplicate markers from that same bot are collapsed, including a
verification read after a new POST. If the surviving older comment has stale
content, it is updated to the analysis just posted. Cleanup never deletes human comments.

Primary exhaustion waits until the response's reset time plus five seconds.
Secondary limits honor `Retry-After` (seconds or HTTP date), or wait at least a
minute with exponential backoff. At most three attempts and 180 cumulative
seconds of retry waits are allowed per process by default. `--max-wait` can
raise this budget for a deliberate long local backfill. A longer wait stops requests
using that credential and fails label reconciliation, leaving a later recovery
to finish. HTTP 200 GraphQL error responses are also handled. Permission and
validation errors fail immediately. Reads retry transport failures and transient
GraphQL errors; transport diagnostics are retained with credentials redacted. Ambiguous comment/label creation POST
failures are not repeated: the next reconciliation rereads state before writing.
Mutations are spaced by at least one second within a process.

## Recovery and maintenance

`roadmap-label-reconcile.yml` runs hourly at minute 17. It scans open PR metadata
in creation order before mutations. This keeps comment activity from moving
PRs between pages and resetting retries. The state artifact contains hashes of
the actual processed head, body, base branch name, state, canonical area set, and
classifier policy, plus the resulting label and bounded retries. It contains no
PR bodies or credentials. Unrelated comments/status-label changes and ordinary
main-tip advances do not invalidate these input hashes. A matching successful
input with the right label skips both the snapshot query and comment listing.

New, changed, or uncached inputs are inspected regardless of their update time.
This also repairs a PR missed by a concurrent close during page-numbered listing:
an unseen PR has no success record and is eligible on the next sweep. Changed,
missing, or invalid roadmap labels are repaired even on old PRs. The first run
and a cold/missing state artifact inspect every open PR.

Per-PR failures move to the artifact's retry queue while healthy work advances.
After five failed recovery attempts for the same inputs, the PR is reported in
warnings and the step summary. Transient server failures and non-capped incomplete
file listings pause for six hours, then start another bounded retry cycle without
requiring a PR edit. Non-transient failures remain exhausted until their
inputs/policy change or a manual full scan resets the state.
Rate limits, transport outages, listing errors,
and failed artifact uploads fail the workflow and retain the previous successful
window. Completed progress is saved even on a deferred run, so the next pass can
skip its successful prefix. State restoration accepts only scheduled or manually
dispatched runs from this repository's main branch, excluding fork PR runs even
when their head branch is named main. Saved retry timestamps must be finite,
nonnegative numbers. Closed PRs are pruned after a complete listing.

Without a state handoff, local recovery uses the previous successful run's start,
with two minutes of overlap, plus PRs missing a valid label. Per-PR failures then
remain nonzero, since there is no durable queue to carry them forward.

Event and recovery jobs can overlap. A concurrent edit can temporarily invalidate
a snapshot, but the next sweep checks the current input hash and roadmap labels.
Structure errors remain advisory on event runs; recovery puts them in the same
bounded retry queue. Neither workflow writes the authoritative build status.

Dispatch `full-scan: true` after unusual base-history rewrites, to force an audit
of cached inputs, or to retry exhausted PRs. Classifier/area-set changes invalidate
cached inputs automatically. Use `sync-labels: true` to create canonical labels
and repair descriptions/colours. Both run only against trusted `main` code.

Historical `--backfill` keeps bulk GraphQL reads, newest-created order, state and
tally output, and never posts attribution nudges. Only paginated diffs/labels need
individual queries. Existing associations remain protected unless
`--allow-relabel` is supplied; structure nudges, when explicitly requested, remain
independent of that label opt-in.

## Capacity planning

This mitigation does not guarantee capacity for ten times the event rate. Each
meaningful event run still needs a snapshot query; large diffs need more pages.
The debounce coalesces rapid events only on the same PR. Recovery caches avoid
repeated snapshots for unchanged PRs, but every sweep still lists all open PR
metadata. Cold state must inspect every open PR and can need multiple quota
windows to finish. The default reconciliation safety limit is 5,000 open PRs;
exceeding it fails the listing and requires explicitly raising `--limit`.

Estimate workflow GraphQL demand as meaningful event runs times measured points
per snapshot, plus recovery points and other workflows. REST demand includes
comment pages, label probes, open-PR listing pages, and artifact handoff. Keep
headroom in each credential/resource bucket, using response headers and these
scripts' counters together. Include burst traffic and cold-state recovery in
capacity tests, not just average PR creation rates. GitHub also enforces secondary
limits on concurrency and content generation; an hourly primary budget alone
does not establish safe throughput. See the official
[REST limits](https://docs.github.com/en/rest/using-the-rest-api/rate-limits-for-the-rest-api)
and [GraphQL limits](https://docs.github.com/en/graphql/overview/rate-limits-and-query-limits-for-the-graphql-api).

A smaller first scaling step is resource-specific credential routing: snapshot
reads can use the App installation's GraphQL bucket (normally at least 5,000
points/hour), which is separate from its REST bucket. The current client sends
all reads to the workflow token instead. Measure other App GraphQL consumers
before moving those reads, and retain the App credential for writes that must
trigger downstream workflows. This increases available snapshot capacity but
does not remove shared REST or secondary limits.

For sustained growth, move event processing to a durable queue keyed by repository
and PR, coalescing pending work to the newest input. A shared scheduler should pace
writes across workers, retain quota reset times, and reserve capacity for required
labels ahead of advisory comments and historical maintenance. Retry jitter and
bounded worker concurrency prevent all deferred jobs from restarting together.
Persist processed inputs and pending work so process restarts do not require a
full rescan; keep a bounded periodic audit for missed events. Batch compatible
GraphQL reads with measured query costs and node limits. These are follow-up
architecture changes, not properties of the current Actions implementation.

Monitor backlog age, classification latency, deferred/exhausted PR counts, and
remaining quota per credential/resource. Select an explicit labeling latency
target and alert before the projected workload consumes the available budget.
If measured demand still exceeds that budget after eliminating duplicate work,
evaluate a supported higher-quota deployment. Minting additional tokens for the
same installation cannot increase throughput.

For a local read-only inspection:

```bash
python3 scripts/roadmap_label.py --roadmap-dir /path/to/TauCetiRoadmap --pr 42
python3 scripts/roadmap_label.py --roadmap-dir /path/to/TauCetiRoadmap \
  --reconcile-open --since 1970-01-01T00:00:00Z
```

Add `--apply` to make changes, and `--structure-nudge` to inspect/apply the
advisory structure comment with the same PR snapshot. Historical `--backfill`
preserves existing roadmap associations unless `--allow-relabel` is supplied.

Run the hermetic regression tests with:

```bash
python3 scripts/test_roadmap_label.py
python3 scripts/test_roadmap_api.py
python3 scripts/test_structure_nudge.py
```
