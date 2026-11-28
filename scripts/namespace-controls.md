# Namespace runner controls

Namespace is currently off. `NAMESPACE_ENABLED` is `false`, the `tauceti.toml`
default is disabled, and `[services.fleet].pr_order` is `["fleet"]` with
`pr_overflow_pool = "fleet"`, so the picker never considers Namespace for PR builds.
Maintenance builds and the nightly builds do not use Namespace at all.

The repository's
[Actions variables](https://github.com/TauCetiProject/TauCeti/settings/variables/actions)
only switch and size Namespace within the routing order. While `pr_order` omits
`"namespace"`, setting them has no effect. Restoring Namespace routing takes a
source PR to `tauceti.toml` that adds `"namespace"` to `pr_order` after `"fleet"`
(for example `["fleet", "namespace", "github"]`) and, if PR builds that find every
tier saturated should go to GitHub-hosted runners rather than wait for Fleet, sets
`pr_overflow_pool = "github"`. Once that routing has landed, these variables control
Namespace without a further source PR or staging batch:

```sh
# Enable Namespace with an eight-build cap.
gh variable set NAMESPACE_BUILD_CAP --repo TauCetiProject/TauCeti --body 8
gh variable set NAMESPACE_ENABLED --repo TauCetiProject/TauCeti --body true

# Stop new Namespace selections; retain running and already-admitted work.
gh variable set NAMESPACE_ENABLED --repo TauCetiProject/TauCeti --body false

# Resize; zero also disables Namespace.
gh variable set NAMESPACE_BUILD_CAP --repo TauCetiProject/TauCeti --body 4
```

`NAMESPACE_ENABLED` accepts `true` or `false`; `NAMESPACE_BUILD_CAP` accepts whole
numbers from 0 through 64. An unset or empty variable uses the `tauceti.toml`
default (disabled, cap eight). Invalid values disable Namespace while preserving
GitHub and fleet routing. Keep `NAMESPACE_ENABLED=true` when using a positive cap
to enable Namespace; a false switch always wins over a positive cap.

Picker-routed Namespace builds share scheduler groups, named
`tauceti-namespace-build-0` through `tauceti-namespace-build-(cap-1)`. Waiting in
these groups consumes no runner. Fixed slots can leave capacity unused when jobs
collide. The cap covers this repository's picker-routed Namespace build jobs; staging retains
its dedicated tauchonki2 runner.

Settings govern new work, with graceful drain on a reduction: jobs already
admitted under an earlier policy, including jobs waiting in scheduler groups,
finish with that policy. The new ceiling fully applies after that work drains.
Already-created GitHub workflow runs may retain earlier variable values; this
switch does not cancel those runs. Picker logs report the effective enabled state,
cap, observed queued/running Namespace count, and capacity coverage.
