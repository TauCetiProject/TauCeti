# CI runner routing

Namespace is retired from CI dispatch. PR builds prefer GitHub-hosted runners, then
eligible Fleet PR runners; when neither has observed spare capacity, they wait on
GitHub-hosted capacity. Maintenance builds use GitHub-hosted capacity. The shared
picker ignores retired Namespace entries in older configuration, and consumers reject
Namespace targets even when an old picker output matches the current attempt.

Staging runs only on tauchonki2. It prefers the exact available staging guest and
otherwise waits for the next guest with tauchonki2's permanent machine and staging
class labels. Missing or stale picker outputs cannot send staging into another pool.
The staging picker, finalizer, and isolated publisher retain their reserved queue-control
slots. Publisher and sandbox must use distinct fresh runners.

Ordinary picker/control jobs and fixed Linux CI workflows use GitHub-hosted Ubuntu
24.04. `PICKER_GITHUB_FALLBACK` and `STAGING_RUNS_ON` cannot re-enable Namespace.

Nineteen native Actions concurrency groups cap GitHub-hosted bulk builds across
workflows, leaving one of the organization's twenty hosted slots for control work.
The runner picker uses the existing observed hosted budget and complete Fleet
inventory; these are advisory observations rather than capacity reservations.
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
