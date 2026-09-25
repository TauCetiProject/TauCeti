# Bors capacity and CI-minute model

The objective is to minimize **staging CI minutes per merged PR**, subject to
the approval backlog staying bounded at the observed flow rate. PR-head CI is
required under either backend, so it is a constant in this comparison.

The model in `scripts/bors_capacity.py` replays a week of PR arrivals through
one serial bors staging lane. Arrivals during a running build accumulate in
the next batch. A batch with an integration failure is tested recursively by
halves. Each test draws a CI duration from the observed successful `pr-build`
runs. `--duration-growth` models combined builds taking longer as batch size
grows. No batching delay or utilization target is imposed. The only constraint
is that the simulated backlog remains bounded; among feasible caps, the script
selects the smallest cap within 1% of the lowest CI minutes per merge.

The 2026-09-25 snapshot contains 1,342 PR merges over seven days (192/day,
used as a proxy for review-ready arrivals) and 333 recent successful PR builds:
mean 13.79 minutes, median 13.13, p90 19.0. At 10× that weekly flow, the
model gives:

| Integration failure per approved PR | If batch duration is flat | If duration rises 5% per batch-size doubling |
| ---: | --- | --- |
| 0.1% | Feasible, cap 64 or higher | Feasible, cap 32 or higher |
| 0.3% | Feasible, cap 64 or higher | No tested cap keeps up |
| 1.0% | No tested cap keeps up | No tested cap keeps up |

At today's rate, all caps from 8 through 256 behave almost identically:
bors naturally builds groups of about 2.2 PRs because it collects approvals
while the previous CI run executes. The configured cap of 128 is a ceiling for
growth, not a request to wait until 128 approvals arrive. It costs no extra
CI minutes at the current rate in the replay. If 10× traffic arrives, a cap of
20 would bind and fall behind even with a 0.1% failure rate.

These are sensitivity results, not a claim that Tau Ceti's failure rate is
0.1% or that combined CI duration is flat. The current GitHub merge queue does
not expose an unbiased estimate of per-approved-PR integration failures for
bors. During the pilot, record for each staging attempt its batch size,
duration, terminal outcome, and whether a failure was caused by one PR or by
infrastructure. Refit both failure rate and batch-size duration growth. A
single serial lane should not be used for the 10× load if the measured values
land in an infeasible region; changing the cap or timeout cannot fix that.

The daily `bors-capacity` workflow collects the last seven days of approval
times (review App `bors r+` comments after cutover, merge times as a proxy
beforehand) and CI durations, then publishes the scenario grid as an artifact
and job summary. The bors queue itself adapts batch size continuously as
traffic changes; the report checks when a parameter or architecture change
becomes necessary. The timeout is a generous failure deadline, not a tuning
knob for throughput.

## Activation

Before the limited pilot, run `scripts/prepare_bors_bypass.py --app-id ID --app-slug
SLUG` to save the current ruleset and classic branch protection alongside a
JSON proposal. Review those files, then repeat with `--apply`. The script adds
only the bors App to both bypass lists; it retains the existing merge queue,
code-owner rule, and required checks. It does **not** switch traffic. After a
preselected pilot PR has passed staging CI and bors health is confirmed, set the repository variable
`MERGE_BACKEND=bors`. To stop new bors approvals, set it back to `queue`;
disable the bors App installation before doing so if an already-running bors
batch must be prevented from pushing to `main`.

Run locally:

```sh
python3 scripts/test_bors_capacity.py
python3 scripts/collect_bors_observations.py > observations.json
python3 scripts/bors_capacity.py \
  --observations observations.json \
  --rate-scales 1,10 --failure-rates 0.001,0.003,0.01
```
