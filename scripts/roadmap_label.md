# Roadmap label automation

`roadmap-label.yml` classifies open, reopened, pushed, and body/base-edited PRs.
Title-only edits are ignored because the title supplies no classification
evidence. A 20-second delay before token creation lets rapid events on one PR
collapse through its cancellation group. Only trusted default-branch code runs;
the PR body and changed file paths remain API data.

## Credentials and API usage

`GH_READ_TOKEN` is the job's `GITHUB_TOKEN`. PR metadata, labels, and changed files
are fetched together using a small GraphQL query, paginated when necessary. The
same snapshot supplies the advisory structure nudge. File pagination rejects a
changing head/base/body or an incomplete diff rather than applying a label from
mixed data. Repository label probes and comment listings use REST reads.

`GH_TOKEN` remains the scoped App installation token for mutations. This matters:
App label/comment events drive downstream workflows, whereas `GITHUB_TOKEN`
label/comment mutations suppress those workflow triggers. Although
`pull_request_target` can grant write permissions on fork PRs, swapping the write
token without replacing those triggers would change behavior. Local invocations
without `GH_READ_TOKEN` use the normal authenticated `gh` credential for both.

Both credentials have finite budgets. Sharing reads reduces pressure on the App;
it does not guarantee that either credential will always have quota. Minting a
new token for the same App installation does not give it a new budget.

Every response records its credential role, HTTP status, rate-limit resource,
remaining quota, and reset time in `github-api:` log lines. The final
`github-api-summary:` and Actions step summary contain this process's request
counts, reads/writes, GraphQL query points, and latest response-header readings.
They never include tokens or PR/comment bodies. Remaining quota is shared with
other jobs: a change in that value alone cannot be attributed to this process.
The counters measure these scripts, not all workflows using the installation.

## Writes and retries

A PR already carrying exactly the desired roadmap label causes no label mutation
or repository label probe. Relabeling adds the desired label before removing
stale roadmap labels, preserving unrelated labels. Repository labels are created
only after a definite 404; concurrent `already_exists` creation is accepted.
Existing label presentation is maintained separately through `--sync-labels`.
An unchanged structure comment also causes no mutation.

Primary exhaustion waits until the response's reset time plus five seconds.
Secondary limits honor `Retry-After` (seconds or HTTP date), or wait at least a
minute with exponential backoff. At most three attempts and 180 cumulative
seconds of retry waits are allowed per process. A longer wait stops requests
using that credential and fails label reconciliation, leaving a later recovery
to finish. HTTP 200 GraphQL error responses are also handled. Permission and
validation errors fail immediately. Ambiguous comment/label creation POST
failures are not repeated: the next reconciliation rereads state before writing.
Mutations are spaced by at least one second within a process.

## Recovery and maintenance

`roadmap-label-reconcile.yml` runs hourly at minute 17. It scans open PR metadata
and reconciles PRs updated since the previous successful recovery's **start**,
with two minutes of overlap for clock skew and concurrent listing changes. PRs without one valid roadmap label are always included.
The first recovery scans every open PR. A failed, timed-out, or rate-limited run
does not advance the window. Paging finishes before label writes can reorder
the updated-PR listing. A per-PR error is reported and makes the recovery fail;
a rate limit stops the remaining pass without probing each PR again.

The event and recovery jobs can overlap. Their additive label changes and marker
comments converge; a concurrent later edit can temporarily invalidate a snapshot,
so the overlapping recovery window is the backstop. Structure errors remain
advisory on event runs; recovery reports them as failures so its window is retried.
Neither workflow writes the authoritative build status.

After changing canonical roadmaps, dispatch recovery with `full-scan: true` to
reclassify all open PRs. Use `sync-labels: true` to create new canonical labels and
repair their descriptions/colours. Both run only against trusted `main` code.

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
