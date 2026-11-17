# Shared tools

Reusable Python and shell implementations live in TauCetiProject/TauCetiTools. Every TauCeti
workflow, script and service uses TauCetiTools `main`: `tauceti.toml` says `ref = "main"`, and
workflows write `@main` and `tools-ref: main`. CI prepares the trusted project or gate checkout
with the setup action before invoking scripts. Local Python callers need `tauceti-tools`
installed; shell entrypoints run the same `main` through uvx. To prepare all helpers locally:

```sh
uv tool install git+https://github.com/TauCetiProject/TauCetiTools@main
tauceti-tools materialize scripts --conf tauceti.toml --policy-dir scripts
```

Materialization is a local generated change: do not commit generated implementations over the
thin callers. Project policy files (`*.txt`, `*.json`) stay here and override supplied defaults.
Lean drivers and static data remain checked in so direct Lake commands work from a checkout.
A change to common tooling is a TauCetiTools PR. Its CI runs this repository's infrastructure
tests against the candidate before it can reach TauCeti. Review and progress pins, runner
selection and merge policy are separate.

The complete installation inventory is in the [setup manual](https://github.com/TauCetiProject/TauCetiTools/blob/main/docs/project-setup.md).

A successful audited and published build whose requested Bors batch is explicitly
canceled finishes with `batch withdrawn; no verdict posted`, removes its pending
intent, and posts neither a red nor green `build` status. Genuine build and cache
publication failures, including an unfinished canceled build, produce `build=failure`.
Missing, malformed or unavailable Bors observations do not prove withdrawal or
authorize a green build status.

Local `lake test`, `lake lint` and Worker verification use the same shared local checkers.
