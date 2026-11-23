# CI runner routing

PR builds prefer eligible Fleet PR runners (with a small bounded waiting queue),
then Namespace (when enabled via `NAMESPACE_ENABLED` and `NAMESPACE_BUILD_CAP`),
then GitHub-hosted runners. Maintenance builds (bot Mathlib bump and lint-repair PRs
and their dispatched rebuilds) take a priority Namespace runner outside the capped
scheduler groups when `NAMESPACE_ENABLED` is unset, empty or `true` and
`NAMESPACE_BUILD_CAP` is not `0`; otherwise they use the GitHub-hosted bulk slots
(see `scripts/namespace-controls.md`). The full clean nightly build uses the Fleet PR pool and retains its twelve-hour budget;
staging-only and queue-control reservations cannot be taken by that class.

Staging runs only on tauchonki2. It prefers the exact available staging guest and
otherwise waits for the next guest with tauchonki2's permanent machine and staging
class labels. Missing or stale picker outputs cannot send staging into another pool.
The staging picker, finalizer, and isolated publisher retain their reserved queue-control
slots. Publisher and sandbox must use distinct fresh runners.

Ordinary non-staging picker jobs and the CI label dispatcher (`full-lint-label.yml`)
run on the Fleet PR pool when `FLEET_CI_ENABLED` is `true` so GitHub-hosted backlogs
cannot starve runner selection. The API docs build (`api-docs.yml`) uses the same pool, so
its hours-long re-analysis after a pin bump does not hold a GitHub-hosted runner. Setting
`PICKER_GITHUB_FALLBACK` to `true` returns all three to GitHub-hosted `ubuntu-24.04`
without a source PR. None of them receives
`APP_PRIVATE_KEY`.

Native Actions concurrency groups cap GitHub-hosted bulk builds across workflows at
`HOSTED_RUNNER_BUDGET` (default `12`, clamped to `1..19`), reserving the remaining
organization hosted slots for control work (`pr-status`, `pr-labels`, `labels-from-comments`,
and fallback pickers). The runner picker uses the existing observed hosted budget and
complete Fleet inventory; these are advisory observations rather than capacity reservations.
PR placement names the shared runner group so another enrolled host can replace a
busy guest. Staging retains its reserved machine and class.

The shared state service coalesces capacity discovery. Observations must match the
organization, remain unexpired, and be no more than 150 seconds old. Incomplete
observations do not establish spare capacity. Historical Namespace counts can remain
visible for old runs; they never authorize a new Namespace placement.

Fleet startup recovery retains the same workflow run identity. Retry placement uses
current eligible capacity and excludes failed targets; staging's workflow-level machine
restriction still applies. Existing sandbox, approval, status, and cache-publication
checks remain mandatory on every pool.

Pool membership and per-host slot limits are managed through
[Fleet enrollment](https://github.com/TauCetiProject/TauCetiFleet/blob/main/services/ci-broker/README.md).
Keep normal admissions enabled during routine live updates. Draining is reserved for
explicit host retirement or a concrete change that cannot be applied safely to live
jobs. Verify useful completions and repair stranded work after an update.
