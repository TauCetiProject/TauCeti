# Pipeline health

`scripts/pipeline_health.py` answers "where is the pull-request pipeline slow,
and why", which merge throughput on its own cannot: throughput is one number at
the end of a queue, so a fall in it says something is wrong without saying what.

It measures each lifecycle stage separately — arrival rate, departure rate,
current depth, how long its occupants have been waiting, and median dwell — each
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

**Waiting and dwell are different questions, and not a ratio.**
`median_waiting_hours` and `p90_waiting_hours` describe the pull requests
sitting in a stage right now; `median_dwell_hours` describes how long a spell
in it takes. Do not read the first against the second. A census catches long
spells more often than short ones, simply because they are there longer, so the
occupants of a perfectly healthy stage are older than its typical spell — on a
simulated stable queue whose dwell is 1h for nine spells in ten and 100h for
the tenth, the median occupant is 33 times the median dwell, and nothing is
wrong. Read the waiting figures as a description of the backlog, against
arrivals outrunning departures, and `oldest_waiting_hours` as the tail.
`waiting_count` says how many of `depth` they describe: a waiting age is read
only where the verified stage agrees with the label, because an old label's
clock says nothing about a stage the readiness audit moved a pull request to,
so under label drift these cover part of the stage rather than all of it.

**Dwell times count the spells that have not ended.** They are the whole
difficulty: a stage that is backing up is accumulating exactly the spells that
have not finished, so a median over completed ones describes the pull requests
that got served and not the stage. Taking the elapsed time of an unfinished
spell as if it were final is no better, because at any instant most occupants
are young. `median_dwell_hours` is therefore a Kaplan-Meier estimate over the
spells that *began* in the period, censoring any that had not ended by the end
of it. Selecting by where a spell ended would instead mix in spells already
under way when the period opened, which were at risk only from the age they had
then. It is `null` when the estimator never falls to half, which is what a
stage where most spells are still running honestly supports.
`dwell_completions` and `baseline_dwell_completions` count the spells in those
cohorts that actually finished, which is what a median rests on, and gate
whether it is trusted. Not `baseline_left_count`, which counts departures: a
spell can leave a period it never began in, so a handful of those would vouch
for a median resting on one observation.

**One known exception, in `anomalies` rather than the report.** Its `stalled`
test still divides `oldest_waiting_hours` by the baseline dwell, which is the
census-against-dwell comparison the paragraph above says not to make, and on a
heavy-tailed stage it will fire on a healthy queue. It predates the figures
described here and wants the anomaly detector reworked rather than patched: the
honest form compares occupant ages against a baseline survival curve, asking
what share of them have already outlasted the historical p90.

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
anomaly. From schema version 3, ready-stage `depth` is null when some ready
labels are unverified; that label count cannot establish a merge-capacity
problem.

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
