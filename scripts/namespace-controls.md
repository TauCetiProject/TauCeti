# Namespace runner controls

Namespace routing is controlled through the repository's
[Actions variables](https://github.com/TauCetiProject/TauCeti/settings/variables/actions).
Changing these settings requires no source PR or staging batch.

```sh
# Enable Namespace with an eight-build cap (the current operating setting).
gh variable set NAMESPACE_BUILD_CAP --repo TauCetiProject/TauCeti --body 8
gh variable set NAMESPACE_ENABLED --repo TauCetiProject/TauCeti --body true

# Stop new Namespace selections; retain running and already-admitted work.
gh variable set NAMESPACE_ENABLED --repo TauCetiProject/TauCeti --body false

# Resize; zero also disables Namespace.
gh variable set NAMESPACE_BUILD_CAP --repo TauCetiProject/TauCeti --body 4
```

`NAMESPACE_ENABLED` accepts `true` or `false`; `NAMESPACE_BUILD_CAP` accepts whole
numbers from 0 through 64. An unset or empty variable uses the `tauceti.toml`
default (enabled, cap eight). Invalid values disable Namespace while preserving
GitHub and fleet routing. Keep `NAMESPACE_ENABLED=true` when using a positive cap
to enable Namespace; a false switch always wins over a positive cap.

PR builds and nightly reference builds share the same scheduler groups, named
`tauceti-namespace-build-0` through `tauceti-namespace-build-(cap-1)`. Waiting in
these groups consumes no runner. Fixed slots can leave capacity unused when jobs
collide. The cap covers this repository's Namespace build jobs; staging retains
its dedicated tauchonki2 runner.

For a shared queue that fills every available runner, use one Namespace Runner
Profile configured with a provider concurrency limit equal to `NAMESPACE_BUILD_CAP`.
Set the limit in the profile's Advanced Settings; this uses Namespace's existing
scheduler and requires no additional service. Keep the configured pool preference
order, with Namespace last.

Switch a live fleet in two stages, without pausing admissions:

1. Configure the profile's shape and privileges to match the existing PR runner
   (8 vCPU, 16 GiB, privileged containers), and set its concurrent-runner limit to
   eight. Set `NAMESPACE_RUNNER_PROFILE` to its `namespace-profile-...` label.
   Leave `NAMESPACE_PROFILE_CAP` unset. New Namespace selections use the profile
   while retaining the existing GitHub slot groups shared with old generic jobs.
2. Reissue only unassigned generic Namespace jobs on the current workflow after
   verifying their current PR heads and absence of a running build. Let running
   generic Namespace jobs finish. Once none remain, set `NAMESPACE_PROFILE_CAP`
   to `8`, confirming the actual provider limit. New profile jobs then use the
   provider's shared queue rather than separate GitHub slot queues. Existing
   profile jobs are already covered by that same provider limit.

The confirmation must match the runtime cap. Do not set it before verifying the
provider setting and completing the generic-runner transition: the old generic
runners are outside the profile's limit. All workflows sharing this build budget
must use the same capped profile. Resizing requires updating the provider setting
and confirmation together; an inconsistent configuration rejects new Namespace
profile selection. Native fleet and GitHub choices are unaffected.

Settings govern new work, with graceful drain on a reduction: jobs already
admitted under an earlier policy, including jobs waiting in scheduler groups,
finish with that policy. The new ceiling fully applies after that work drains.
Already-created GitHub workflow runs may retain earlier variable values; this
switch does not cancel those runs. Picker logs report the effective enabled state,
cap, observed queued/running Namespace count, and capacity coverage.
