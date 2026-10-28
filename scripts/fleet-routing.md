# CI fleet routing

The existing `pick-runner.yml` workflow calls the shared `fleet_runner.py` selector.
The policy is in `[services.fleet]` in `tauceti.toml`:

| Build class | Preference order |
| --- | --- |
| PR | GitHub → Chris → tauchonki (ineligible) → Namespace |
| Bors staging | tauchonki → Chris → Namespace → GitHub |

Chris advertises two shared jobs, each with 16 vCPU and 32 GiB RAM. Any mix of PR
and staging builds may occupy those two slots. Tauchonki advertises one staging
job with 32 vCPU and 64 GiB RAM. Each host enforces its slot count; the enrollment
service also limits the job classes and maximum slots its credential may register.
Changing a host's classes or resource shape requires draining all its guests.

The picker requires an idle online runner with the requested class, permanent
machine identity, and unique guest-instance labels. It targets that exact guest
in the `TauCetiFleet` group. Chris's enrollment name resolves to one permanent
machine identity; an absent or ambiguous identity disables that machine's choice.
Queued jobs already targeting a guest count against observed machine capacity.
A simultaneous picker can still select the same guest; startup recovery handles
jobs that fail to acquire it.

Namespace has an approximate cap of **20 queued or running build jobs**, shared
across PR and staging. Picker, recovery, publisher, and finalizer jobs are excluded.
The variable `NAMESPACE_BUILD_CAP` overrides the default in the configuration.
Concurrent picker decisions can admit jobs above this snapshot-based cap. When Namespace is
full, staging falls through to GitHub; if all eligible destinations are full or
unknown, the build waits for a GitHub-hosted slot. A failed picker uses that same
GitHub fallback. `HOSTED_RUNNER_BUDGET` defaults to 18 running GitHub-hosted jobs,
including PR and other GitHub-hosted pickers. Staging pickers run on Namespace
and do not count toward that budget. Set it below the provider's total job limit
to preserve headroom for short control jobs.

Shared capacity observations must be complete, match the organization, remain unexpired,
and be at most 150 seconds old. This retains the two-minute shared-cache allowance.

Capacity scans use the repository workflow token, preserving the reserve set by
`PICKER_REPOSITORY_API_RESERVE` (default 250 requests). Incomplete scans cannot
authorize spare cloud capacity. Ordinary PR fleet placement also requires a
complete observation of queued guest targets. Staging tries dedicated machines
first using complete online/idle fleet inventory, class labels and machine limits,
even when optional global queued-job coverage is unavailable. Any known queued
guest reservations still count against capacity. If no machine is eligible,
staging uses the existing bounded cloud discovery and fallback.
The existing shared state service coalesces cloud and queued-target discovery;
older snapshots can still answer the first GitHub preference. Staging pickers run
on the existing Namespace 2x4 priority-zero control profile, avoiding the
GitHub-hosted build queue. PR and other pickers remain on GitHub-hosted runners.

The existing `fleet-recovery.yml` watcher waits for placement and allows two
minutes for a dedicated guest to acquire the build. It cancels an unacquired
attempt, confirms it is terminal, and reruns the **same workflow run ID**. The next
picker excludes previously failed machine placements. Bors run identity stays
intact; PR retries additionally require the immutable head in the run title to
remain current. Manual PR dispatches without an immutable head and native merge
groups use cloud pools. A failed-jobs-only rerun that reuses old picker outputs
queues on GitHub instead of targeting a retired guest.

The initial Namespace limit was chosen from the archived CI database at
[the TauCetiCI db release](https://github.com/TauCetiProject/TauCetiCI/releases/tag/db),
complete through 2026-10-21 15:38:49 UTC. Over the latest complete day, 1,847
Namespace builds had peak concurrency 27, time-weighted p95 20 and p99 23.
Concurrency exceeded 20 for about 59 minutes. Over 30 days, 27,224 builds had a
peak of 32 and p99 of 19; concurrency exceeded 20 for about 2.18 hours. These are
actual execution intervals, excluding control jobs; queued builds are included
in the dispatcher's admission count as an additional precaution.

Routing policy and host configuration are managed separately. Follow the
[Fleet enrollment instructions](https://github.com/TauCetiProject/TauCetiFleet/blob/main/services/ci-broker/README.md)
to issue a machine's invitation with its allowed CI classes and shared slot limit.
Run `enroll HOST` and `prepare HOST`, then explicitly activate CI with `enable HOST`,
choosing `--ci pr`, `--ci staging`, or `--ci both`, `--max-jobs`, and the per-job
`--ci-vcpus` and `--ci-memory-gib` settings.

Before updating a host's installed Fleet release or changing its CI classes,
slot limit, or guest shape, run `drain HOST` and wait for every guest to finish.
Drain pauses new worker and CI admissions. After maintenance, explicitly
re-enable every previously enabled role.
