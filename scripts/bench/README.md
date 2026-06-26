# TauCeti benchmark suite

This directory contains the TauCeti benchmark suite. It exists so that
[radar](https://github.com/leanprover/radar), the Lean FRO performance-tracking service,
can measure TauCeti on every commit and surface regressions over time. Results are viewable
on the [Lean FRO radar instance](https://radar.lean-lang.org/).

Radar runs this suite through its generic harness
([`radar-bench-generic`](https://github.com/leanprover/radar-bench-generic)), which looks for
`scripts/bench/run` in the repo root, executes it, and collects the resulting
`measurements.jsonl`. The suite is adapted from
[cslib's](https://github.com/leanprover/cslib/tree/master/scripts/bench); the only
TauCeti-specific change is the source glob in the `size` benchmark.

To execute the entire suite, run `scripts/bench/run` in the repo root.
To execute an individual benchmark, run `scripts/bench/<benchmark>/run` in the repo root.
All scripts append their measurements to the file `measurements.jsonl`.

Radar sums any duplicated measurements with matching metrics.
To post-process the `measurements.jsonl` file this way in-place,
run `scripts/bench/combine.py` in the repo root after executing the benchmark suite.

The `*.py` symlinks exist only so the python files are a bit nicer to edit
in text editors that rely on the file ending.

## Benchmarks

- [`build`](build/README.md) — builds TauCeti from scratch and records global, per-module, and
  longest-path build metrics (instructions, wall-clock, task-clock, max RSS).
- [`size`](size/README.md) — counts `.lean` files and lines under `TauCeti/`, and `.olean`
  files and bytes under `.lake/build/`.

## Adding a benchmark

To add a benchmark to the suite, follow these steps:

1. Create a new folder containing a `run` script and a `README.md` file describing the benchmark,
   as well as any other files required for the benchmark.
2. Edit `scripts/bench/run` to call the `run` script of your new benchmark.
