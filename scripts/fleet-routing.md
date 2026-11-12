# CI fleet routing

The existing `pick-runner.yml` workflow calls the shared `fleet_runner.py` selector.
The policy is in `[services.fleet]` in `tauceti.toml`:

| Build class | Preference order |
| --- | --- |
| PR | GitHub → fleet → Namespace |
| Bors staging | tauchonki2; otherwise wait for tauchonki2 |

`fleet` is a live pool of eligible runners in the configured GitHub runner group,
not a list of machines in this repository. Adding or replacing a host requires
no `tauceti.toml` machine-ID entry. Each host controls its concurrency and resource
limits; its credential controls which CI classes it may register. Registration,
resizing and retirement update the capacity seen by subsequent pickers.

The picker reads idle online runners in the trusted group, requiring the
requested class and unambiguous host and instance identities. `FLEET_CI_ENABLED`,
`FLEET_READ_TOKEN` and `FLEET_RUNNER_GROUP_ID` govern that inventory. Labels on
runners outside the approved group grant no eligibility.

When the PR fleet tier is selected, dispatch uses the `TauCetiFleet` group and
`self-hosted`, `linux`, `x64`, `tauceti-fleet-pr` labels. GitHub assigns the next
matching runner. A runner being replaced, or two pickers seeing the same idle
runner, can cause ordinary pool waiting without pinning a job to a vanished
instance. Staging-only runners cannot match PR work. No reservation service or
PR startup cancellation/rerun loop is involved. Named PR machine tiers, if
configured, retain the permanent host label but omit the disposable instance.

Staging retains exact guest selection, preferring reserved staging runners. This
project restricts staging to tauchonki2; when selection is unavailable it
waits for the permanent tauchonki2 staging label. PRs cannot consume those
staging-only runners.

Namespace has an approximate cap of **20 queued or running build jobs**, shared
across PR and staging. Picker, recovery, publisher, and finalizer jobs are excluded.
The variable `NAMESPACE_BUILD_CAP` overrides the default in the configuration.
Concurrent picker decisions can admit jobs above this snapshot-based cap. When Namespace is
full, ordinary PRs fall through to GitHub; if all eligible PR destinations are
full or unknown, the build waits for a GitHub-hosted slot. A failed picker uses that same
GitHub fallback. `HOSTED_RUNNER_BUDGET` defaults to 18 running GitHub-hosted jobs,
including other GitHub-hosted control jobs. All runner pickers run on Namespace
and do not count toward that budget. Set it below the provider's total job limit
to preserve headroom for short control jobs.

Shared capacity observations must be complete, match the organization, remain unexpired,
and be at most 150 seconds old. This retains the two-minute shared-cache allowance.

Capacity scans use the repository workflow token, preserving the reserve set by
`PICKER_REPOSITORY_API_RESERVE` (default 250 requests). Incomplete scans cannot
authorize spare cloud capacity. Fleet placement uses complete online/idle runner
inventory and class labels, retaining any observed queued guest
reservations even when global queue coverage is incomplete. Concurrent PR
selections wait in the shared pool. Staging tries its dedicated machine
first and retains the local staging fallback.
The existing shared state service coalesces cloud and queued-target discovery;
older snapshots can still answer the first GitHub preference. Every picker runs
on the existing Namespace 2x4 priority-zero control profile with a run-specific
label. Ordinary PR selection can reach ready fleet runners even when the
GitHub-hosted build queue is saturated.

During a Namespace outage, set repository variable `PICKER_GITHUB_FALLBACK=true`
to run fresh picker attempts on GitHub. Clear it to restore Namespace control
capacity. This switches the picker only; build placement and merge gates still apply.

The existing `fleet-recovery.yml` watcher applies only to Bors staging. It waits
for placement, allows two minutes for the selected guest to acquire the build,
and preserves the same workflow run ID through recovery. PR jobs wait normally
in their selected pool. A rerun that reuses stale picker outputs retains the
existing GitHub fallback; it cannot target a retired guest from an older attempt.
Manual PR dispatches and native merge groups use cloud pools.

The initial Namespace limit was chosen from the archived CI database at
[the TauCetiCI db release](https://github.com/TauCetiProject/TauCetiCI/releases/tag/db),
complete through 2026-10-21 15:38:49 UTC. Over the latest complete day, 1,847
Namespace builds had peak concurrency 27, time-weighted p95 20 and p99 23.
Concurrency exceeded 20 for about 59 minutes. Over 30 days, 27,224 builds had a
peak of 32 and p99 of 19; concurrency exceeded 20 for about 2.18 hours. These are
actual execution intervals, excluding control jobs; queued builds are included
in the dispatcher's admission count as an additional precaution.

Pool priority and live host configuration are managed separately. The repository
sets the preference between GitHub, fleet and Namespace; operator changes to fleet
membership or concurrency do not require a project commit. Follow the
[Fleet enrollment instructions](https://github.com/TauCetiProject/TauCetiFleet/blob/main/services/ci-broker/README.md)
to issue a machine's invitation with its allowed CI classes and shared slot limit.
Run `enroll HOST` and `prepare HOST`, then explicitly activate CI with `enable HOST`,
choosing `--ci pr`, `--ci staging`, or `--ci both`, `--max-jobs`, and the per-job
`--ci-vcpus` and `--ci-memory-gib` settings.

Prefer Fleet's live-update path for routine software updates, keeping normal
worker and CI admissions enabled. Use a drain when explicitly retiring a host or
when a specific change cannot be applied safely to live guests. A drain stops new
admissions while active work finishes; it is not required merely because another
host joins the fleet. CI classes and guest shape must continue to match the
credential and sandbox policy. After maintenance, explicitly re-enable the roles
that should resume.
