# Shared tools

Reusable Python and shell implementations now live in TauCetiProject/TauCetiTools.
`tauceti.toml` pins their version. CI prepares the trusted project or gate checkout with the
pinned setup action before invoking scripts. Local Python callers need `tauceti-tools` installed;
shell entrypoints resolve the same immutable version through uvx. To prepare all helpers locally:

```sh
uv tool install git+https://github.com/TauCetiProject/TauCetiTools@3b5a8cf7e28f2d51fc6f5e5a13941840db612c0e
tauceti-tools materialize scripts --conf tauceti.toml --policy-dir scripts
```

Materialization is a local generated change: do not commit generated implementations over the
thin callers. Project policy files (`*.txt`, `*.json`) stay here and override supplied defaults.
Lean drivers and static data remain checked in so direct Lake commands work from a checkout.
Upgrade common tooling with a normal human-reviewed pin/workflow PR. Existing review/progress
pins, runner selection and merge policy are retained by this migration.

The complete installation inventory is in the [setup manual](https://github.com/TauCetiProject/TauCetiTools/blob/main/docs/project-setup.md).

The no-stacking workflow pins its batching implementation separately in
`.github/workflows/stack-policy.yml`. Before local no-stacking commands or tests,
materialize the helpers using that workflow's Tools revision. The project default
and other workflow pins remain independent. `infrastructure-tests.yml` selects
the same stack-policy Tools pin to run `test_stack_policy.py` and the project-owned
`test_stack_checkpoint_restore.py`. Workflow pin tests require those production
and regression-test pins to agree.

The `finalize-merge-group-build` job in `.github/workflows/pr-build.yml` pins its
Tools version separately from the project default. `.github/workflows/retry-ci-status.yml`
uses the same version to resume pending finalization and status intents.
A successful audited and published build whose requested Bors batch is explicitly
canceled finishes with `batch withdrawn; no verdict posted`, removes its pending
intent, and posts neither a red nor green `build` status. Genuine build and cache
publication failures, including an unfinished canceled build, produce `build=failure`.
Missing, malformed or unavailable Bors observations do not prove withdrawal or
authorize a green build status.

For local finalizer commands and tests, materialize the helpers using the
`tools-ref` pinned by `finalize-merge-group-build` in `.github/workflows/pr-build.yml`.
The main CI build/test job uses its own Tools pin and matching regression tests.

Local `lake test`, `lake lint` and Worker verification use the same shared local checkers.
The ordinary build/audit workflows and checkout launchers select the same Tools release.
Separately operated stack-policy and publication tooling retain their existing pins.
