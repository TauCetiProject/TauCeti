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
collide. The cap covers this repository's picker-routed Namespace build jobs; staging retains
its dedicated tauchonki2 runner.

Maintenance builds (the review bot's Mathlib bump and lint-repair PRs, and the
rebuilds dispatched for them) take a priority Namespace runner outside these
scheduler groups, so the cap does not count them. They use Namespace only when
`NAMESPACE_ENABLED` is unset, empty or `true` and `NAMESPACE_BUILD_CAP` is not
`0`; otherwise they wait in the GitHub-hosted bulk slots. The `tauceti.toml`
defaults do not apply to them.

Settings govern new work, with graceful drain on a reduction: jobs already
admitted under an earlier policy, including jobs waiting in scheduler groups,
finish with that policy. The new ceiling fully applies after that work drains.
Already-created GitHub workflow runs may retain earlier variable values; this
switch does not cancel those runs. Picker logs report the effective enabled state,
cap, observed queued/running Namespace count, and capacity coverage.
