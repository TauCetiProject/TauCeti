# Pipeline health

`scripts/pipeline_health.py` answers "where is the pull-request pipeline slow,
and why", which merge throughput on its own cannot: throughput is one number at
the end of a queue, so a fall in it says something is wrong without saying what.

It measures each lifecycle stage separately — arrival rate, departure rate,
current depth, how long the oldest occupant has waited, and median dwell — each
against a trailing baseline, and names the cause: a stage backing up, an intake
that has thinned, both, or neither.

## Reading it

```
scripts/pipeline_health.py             # fetch and report
scripts/pipeline_health.py --json      # machine-readable
```

Three things it deliberately does not do.

**Depth is not evidence.** A stage can be very deep and perfectly healthy if it
drains as fast as it fills. The bottleneck is chosen on arrivals outrunning
departures, and on occupants waiting longer than that stage normally takes.

**A thin intake is an answer, not a shrug.** Fewer merges can mean the queue is
stuck or simply that less went into it, and those want opposite responses:
adding review capacity does nothing about a week when nobody opened anything. So
arrival rates are compared against baseline too, and a fall in them is reported
as the cause. When both are true, both are said.

**A building queue is reported before throughput falls.** A stage taking in more
than it lets out is what a fall in throughput looks like before it arrives, so
`anomalies` is populated whether or not merges have dropped yet. `cause` is
separate, and answers only "why is throughput down" when it is.

**It will admit to not knowing.** If arrivals are steady and no stage is backing
up, the fall is reported as unexplained rather than pinned on whichever stage
happened to be deepest. A baseline with too few merges reports insufficient data
rather than health.

**Author-action and inactive stages are never blamed.** Those wait on the
contributor rather than on the project, and treating a backlog there as
something to fix would point effort at exactly the wrong place. They are
reported, marked with `*`, and excluded from the bottleneck.

Live depths come from the same pinned merge gate as Auto-merge. The report shows
label disagreements and unknown reads, with actual queue membership and any
Mathlib reservation separately. A reservation does not remove `ready-to-merge`
from an otherwise eligible PR, and its presence alone does not explain historical
throughput. Recorded label depths remain available as `label_depth`.

Historical flow rates still come from label transitions. An old label's waiting
time is not assigned to a newly verified different stage, and a newly introduced
stage needs a historical baseline before label migration can count as a filling
anomaly. In schema version 2, ready-stage `depth` is null when some ready labels
are unverified; that label count cannot establish a merge-capacity problem.

## Where the data comes from

Historical metrics use the same normalized snapshot as the statistics charts.
Current readiness adds GraphQL evidence reads for open PRs, diffs only for
otherwise approved PRs, and one queue scan using Auto-merge’s reservation policy. Fetching it walks every pull request's label timeline, which is
thousands of requests and takes tens of minutes, so:

- **the Pages workflow** fetches once, writes the charts, and derives
  `pipeline-health.json` from that snapshot plus a fresh readiness audit;
- **anything else** should read the published
  `https://taucetiproject.github.io/TauCeti/static/pipeline-health.json`
  rather than repeat the walk.

To work offline, dump a snapshot once and replay it:

```
scripts/pr_stats_graphs.py --dump-data snap.json --out-dir /tmp/charts
scripts/pipeline_health.py --data snap.json
# With the pinned engine at .tauceti-review/runner or TAUCETI_REVIEW_RUNNER:
scripts/pipeline_health.py --data snap.json --verify-readiness
```

A replay is measured as at the snapshot's `fetched_at`, not as at now, so an old
snapshot gives the answer it would have given when it was taken. `--as-of`
overrides that.

The baseline window is disjoint from the recent one, and both are clamped to the
date the lifecycle labels landed, so a wide baseline is not diluted by time in
which no event could have been recorded.

That is also how the tests run, so they need no network.

Offline replay uses the readiness audit saved in the snapshot, if present. Use
`--dump-data` to save a live audit. Missing policy or failed reads produce unknown
readiness, never verified eligibility. Pages can still publish an unverified
report when the policy checkout fails, and records that failure separately.
