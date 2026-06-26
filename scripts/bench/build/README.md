# The `build` benchmark

This benchmark executes a complete build of TauCeti and collects global and per-module metrics.

The following metrics are collected by a wrapper around the entire build process:

- `build//instructions`
- `build//maxrss`
- `build//task-clock`
- `build//wall-clock`

The following metrics are collected from `leanc --profile` and summed across all modules:

- `build/profile/<name>//wall-clock`

The following metrics are collected from `lakeprof report`:

- `build/lakeprof/longest build path//wall-clock`
- `build/lakeprof/longest rebuild path//wall-clock`

The following metrics are collected individually for each module:

- `build/module/<name>//lines`
- `build/module/<name>//instructions`

When the benchmark runs under radar (signalled by the `IN_RADAR` environment
variable, which radar's harness sets), the lakeprof report is uploaded to
`https://speed.lean-lang.org/tauceti-out/<commit>/`. The upload is best effort:
if it fails, the benchmark still succeeds. Local runs leave `IN_RADAR` unset and
never upload.
