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
departures, and on a spell in the stage taking longer than it used to.

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

**Filling is asked as added drain time, not as a rate.** `anomalies` calls a stage
filling when the window's net arrivals added more than `GROWTH_DRAIN_HOURS` of
work at the pace the stage normally clears — `growth_per_hour × window_hours /
baseline_left_per_hour`, published per anomaly as `added_drain_hours` — and at
least one whole pull request accumulated. A stage with no baseline throughput to
divide by falls back to a rate margin of
`max(GROWTH_PER_HOUR, GROWTH_FRACTION × entered_per_hour)`, published as
`growth_margin_per_hour`.

A flat rate was the whole test until schema version 5, and it aged out from under
itself: 0.05/h was chosen when the busiest stage ran at a few pull requests an
hour, so at forty an hour it fired on a couple of items. The published report for
2026-09-22 named awaiting-review an anomaly for "arriving at 40.33/h and leaving
at 40.25/h" — 1.9 pull requests across a day, under five minutes of work for a
stage clearing 24.56 an hour, on a queue ten deep that was draining in about
twenty minutes.

A *fraction* of arrivals cannot replace it either, which is the trap this avoids.
Five percent is equivalent to demanding departures fall below 95% of arrivals, so
a smaller persistent loss is invisible for ever rather than merely needing more
evidence: forty in and thirty-nine out gains twenty-four pull requests a day and
stays under the margin at every window length. The dwell tests do not cover that
case — if 97.5% of spells still finish quickly, the median and the survival at
twice it both stay healthy while the queue grows all week. Drain time separates
the two: five minutes against an hour. It is an operational policy rather than a
confidence level, and it is stated in the unit the decision is about.

**A stall is asked as survival, not as a ratio.** `anomalies` calls a stage
stalled when at least half of the spells that began in it are still running at
`stall_horizon_hours`, which is `SLOWDOWN_FACTOR` times the dwell the stage used
to have. That is the same claim as "the median has at least doubled", and the
reason to phrase it this way is that it can be answered. A median needs
follow-up until half the cohort has finished; a stage slower than the window is
long never supplies that, so a ratio of medians goes null exactly as the stall
becomes serious. Survival at a horizon needs follow-up only as far as the
horizon. `slowdown_factor` is still published when both medians exist, for
reading rather than for deciding, and is `null` — never zero — when they do not.

No occupant age enters this. Two that look reasonable were tried and both fire
on a queue with nothing wrong: on a simulated stable stage whose dwell is 1h for
nine spells in ten and 100h for the tenth, the median occupant is 33 times the
median dwell, and 91% of occupants have already outlasted the baseline p90.
Length bias is why, and it is a property of censuses rather than of any
particular summary of one.

A stage is only judged on dwell once both cohorts reach `MIN_STALL_COHORT`.
Asking whether over half a cohort is still running is a coin tossed as many
times as the cohort is large, and simulated on a stage with nothing wrong, three
spells called it stalled 15.5% of the time, ten 7.7%, twenty 1.5%, fifty never.
A low-traffic stage is therefore not judged on dwell at all, which is the right
way round: it has not supplied the evidence to be judged on.

`filling` is not the fallback for an unmeasurable stall, and was never a safe
one: arrivals and departures count different cohorts, so old spells can leave
while new ones sit, balancing the flow of a stage in which nothing recent has
finished at all. `stall_horizon_surviving` is `null` only when follow-up ran out
before the horizon on a spell still running, which is reported as not knowing
rather than as health.

**What this still does not separate.** Dwell and the flow rates are per atomic
label, while the waiting clock groups `awaiting-review` with `review-in-progress`
and the three author-action labels with each other. A pull request can alternate
between two labels of one group for a long time with every atomic spell short
and the per-label flows balanced, so a stalled *episode* can hide behind healthy
*labels*. Measuring the bottleneck over grouped episodes would want the depths
and flows grouped too, which is a larger change than this.

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
