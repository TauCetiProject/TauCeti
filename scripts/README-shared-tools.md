# Shared tools

Reusable Python and shell implementations now live in TauCetiProject/TauCetiTools.
`tauceti.toml` pins their version. CI prepares the trusted project or gate checkout with the
pinned setup action before invoking scripts. Local Python callers need `tauceti-tools` installed;
shell entrypoints resolve the same immutable version through uvx. To prepare all helpers locally:

```sh
uv tool install git+https://github.com/TauCetiProject/TauCetiTools@ad4e955b398d1419b0931e3c825a925f1c6a6e9b
tauceti-tools materialize scripts --conf tauceti.toml --policy-dir scripts
```

Materialization is a local generated change: do not commit generated implementations over the
thin callers. Project policy files (`*.txt`, `*.json`) stay here and override supplied defaults.
Lean drivers and static data remain checked in so direct Lake commands work from a checkout.
Upgrade common tooling with a normal human-reviewed pin/workflow PR. Existing review/progress
pins, runner selection and merge policy are retained by this migration.

The complete installation inventory is in the [setup manual](https://github.com/TauCetiProject/TauCetiTools/blob/main/docs/project-setup.md).
