import VersoBlog
open Verso Genre Blog
open Verso.Output Verso.Output.Html

/-- Cached reports update independently of the site build; static charts remain fallbacks. -/
def liveStatus : Html := {{
  <section class="ci-live" data-ci-live="true" aria-label="Current CI activity">
    <div class="ci-live-heading">
      <h2>"Jobs right now"</h2>
      <p data-ci-status="true" role="status">"Loading live counts…"</p>
    </div>
    <dl class="ci-live-counts" data-ci-counts="true"></dl>
    <p class="ci-live-backlog" data-ci-backlog="true" hidden="hidden"></p>
    <noscript>"Enable JavaScript for live counts and automatic chart updates."</noscript>
  </section>
  <script src="static/ci-live.js" defer="defer"></script>
}}

/-- Lead with the recent fleet timeline. -/
def recentFleetGraph : Html := {{
  <figure class="loc-figure loc-figure-wide">
    <img class="loc-graph" src="static/ci-fleet-72h.svg"
         alt="CI jobs running, queued and waiting over the last 72 hours, by runner and kind"/>
    <figcaption>"The last three days in ten-minute bins."</figcaption>
  </figure>
}}

/-- The longer fleet timeline follows the explanation. -/
def monthlyFleetGraph : Html := {{
  <figure class="loc-figure loc-figure-wide">
    <img class="loc-graph" src="static/ci-fleet-30d.svg"
         alt="CI jobs running, queued and waiting over the last 30 days, by runner and kind"
         loading="lazy"/>
    <figcaption>"The last thirty days in two-hour bins."</figcaption>
  </figure>
}}

/-- One chart, full width. -/
def dailyChart (file alt caption : String) : Html := {{
  <figure class="loc-figure loc-figure-wide">
    <img class="loc-graph" src={{s!"static/{file}"}} alt={{alt}} loading="lazy"/>
    <figcaption>{{caption}}</figcaption>
  </figure>
}}

def durationGraph : Html := dailyChart "ci-build-duration.svg"
  "Median and 90th-percentile build time per day, by where the build ran"
  "Solid lines are medians, dashed lines 90th percentiles."
def waitGraph : Html := dailyChart "ci-build-wait.svg"
  "Median and 90th-percentile wait for a runner per day, by where the job ran"
  "Solid lines are medians, dashed lines 90th percentiles."
def phasesGraph : Html := dailyChart "ci-build-phases.svg"
  "Mean minutes per successful PR build, stacked by phase"
  "Mean minutes per successful PR build, by phase."
def failuresGraph : Html := dailyChart "ci-failures.svg"
  "Failed PR builds per day by cause, and the failure rate"
  "Failed PR builds by cause; the dashed line is the share of PR builds that failed."
def minutesGraph : Html := dailyChart "ci-runner-minutes.svg"
  "Build minutes per day on GitHub, Namespace, eastanglia and leanfro, and cancelled PR builds"
  "Build minutes per day."
def queueGraph : Html := dailyChart "ci-merge-queue.svg"
  "GitHub merge-queue and bors builds per day by outcome, and PRs landed"
  "GitHub merge-queue and bors staging builds by outcome; the dashed line is PR arrivals on main."
def queueSizeGraph : Html := dailyChart "ci-queue-size.svg"
  "Ready-to-merge pull-request backlog over time, with gaps where observations are missing"
  "Observed ready-to-merge PR backlog. Gaps indicate missing observations."
def stagingGraph : Html := dailyChart "ci-bors-staging.svg"
  "Bors staging runs over time, with PRs per batch on the vertical axis and green success or red failure dots"
  "Each dot is one staging run: green for success, red for failure, grey for cancelled or other outcomes."
def pickerGraph : Html := dailyChart "ci-picker.svg"
  "Share of PR builds run on GitHub-hosted runners per day"
  "Share of PR builds the runner picker sent to GitHub-hosted runners."

#doc (Page) "CI" =>

Build activity and runner queues across Tau Ceti. The charts update automatically.

:::blob recentFleetGraph
:::

:::blob liveStatus
:::

# Understanding the fleet

Where does Tau Ceti's continuous integration run, and how long does it wait? Every pull request
is built in a sandbox. The fleet uses GitHub, Namespace, and the operator-provided servers
*eastanglia* and *leanfro*. Pull-request builds prefer GitHub, then eastanglia, then leanfro when it accepts
PR jobs, then Namespace. Bors staging builds prefer leanfro, then eastanglia, then Namespace,
then GitHub. Currently leanfro accepts staging only. Each choice depends on available capacity;
a host that is busy, offline or does not accept that job class is skipped.

The eastanglia server has two job slots shared across PR and staging builds; leanfro has one staging slot.
Namespace has an approximate shared cap of twenty queued or running build jobs. Concurrent
picker decisions can briefly overshoot it. GitHub-hosted jobs are free for public repositories,
and the organisation can run twenty at once; the picker reserves headroom for control jobs by
sending new builds elsewhere once twelve GitHub jobs are busy. Namespace minutes are paid for.

The fleet timelines have three panels on one time axis. The top panel shows how many jobs were
running, averaged over each bin and stacked by runner and kind, against the twenty-job cap on
GitHub-hosted jobs. "Other GitHub jobs" are mostly the label, notification and merge-bot jobs
that run on every pull-request event; they are brief but numerous, and they compete with builds
for the same twenty slots. Ticks below the panel mark pull-request builds that the runner picker
sent to Namespace, and dotted lines mark changes to the CI configuration. The middle panel shows
the most jobs waiting for a runner at any moment in each bin. The bottom panel shows the longest
wait for a runner among jobs that started in the previous thirty minutes (or the previous bin,
when bins are longer), for builds and for other jobs separately.

GitHub merge-queue entries also run a performance-gate job, which bors staging builds do not.
That difference affects the fleet and runner-minute totals across the transition. Pilot and
unidentified bors builds remain in the other-job and cost totals.

:::blob monthlyFleetGraph
:::

# Merge queue and staging runs

How many pull requests are waiting to land, and how large are the batches bors tests?
These timelines show up to the last thirty days, including the current partial UTC day.
The backlog counts distinct PRs in the recorded ready-to-merge snapshots, including PRs
being tested. The label is a readiness hint; admission still checks the current head's CI,
reviews and scope. Missing observations leave gaps, and the line stops at the last sample.
Initial candidate scans after a bot restart are omitted when their incompleteness is recorded.
Older snapshots without that marker can briefly undercount.

:::blob queueSizeGraph
:::

Each staging dot is placed at the run's creation time, with the number of distinct PRs in its
batch on the vertical axis. The colour records the overall workflow result, including cache
publication, using the latest recorded attempt if the run was retried. Separate runs of the
same batch have separate dots. Only production main-branch staging runs with known batch
membership and a terminal result are shown; pilot and unidentified dispatches are excluded.
Shaded intervals mark incomplete run inventory: recorded dots are shown there, but missing dots
do not establish that no runs occurred.

:::blob stagingGraph
:::

# Day by day

Live reports give one point per UTC day for up to the last ninety days. Today's point is
provisional and changes as builds finish and details arrive. Each chart reports its own
source coverage. The static fallback charts include complete UTC days only.

How long does a build take, and how long does it wait before starting? A pull-request build
restores what it can from the artifact cache and compiles the rest, then runs the audits and lints.
PR build durations and waits are separated by runner; the merge-validation series combines
staging builds across providers. These timings reflect different runner sizes and workloads.

:::blob durationGraph
:::

:::blob waitGraph
:::

Where does a build's time go? The build, the audits and the two lints run in one sandboxed step.
Where a build recorded its own phases, that step is split into them, with any time the phases do
not cover shown as unattributed; otherwise it appears as one block.

:::blob phasesGraph
:::

Why do builds fail? Each failed pull-request build is classified by the step that failed and the
error lines it printed: a Lean error, one of the lints, one of the audits, a policy check (scope,
size, pins), a timeout, or an infrastructure fault such as a cache download. The classification is
by pattern, so it is a guide rather than a verdict.

:::blob failuresGraph
:::

What does it cost? Namespace bills every minute; GitHub-hosted minutes cost nothing for a public
repository. The eastanglia and leanfro servers contribute operator-provided capacity. The chart counts build-job
minutes separately for each runner provider. A cancelled PR build is usually one that a
newer push to the same pull request replaced before it finished, whose minutes bought nothing.

:::blob minutesGraph
:::

:::blob pickerGraph
:::

How is merge validation doing? The chart includes both GitHub's merge queue and bors staging builds.
Both test combined changes before they land on main. GitHub rebuilds the entries behind a failed
entry; bors splits failed batches to isolate the failing pull requests. The bars count build jobs,
including retries, so a bors batch containing several PRs is one build. Pilot batches and bors
builds whose target branch is unknown are excluded from this chart.

The dashed line counts each PR once, on the date of the earliest recorded main-push event proving
its commit reached main. The event time is an upper bound on arrival; coalesced pushes can
make that bound looser for ancestor commits. The staging commit's creation time is not used. PRs without arrival evidence are excluded from that
line. Direct merges of human-reviewed infrastructure PRs are included.

:::blob queueGraph
:::

# Where the data comes from

The data comes from [TauCetiCI](https://github.com/TauCetiProject/TauCetiCI). Its live reporting
service receives GitHub workflow and job events, records trusted summaries, and repairs missing
data within a shared GitHub request budget. New and corrected records update the affected time
buckets. Reports update independently of this website's build, and the page checks for published
updates once a minute while visible. Reading this page does not trigger GitHub API requests.
During validation or an outage, the page retains its static or last successful reports.

The [live report manifest](https://ci-data.taucetiproject.org/v1/ci/manifest.json) records
publication times, source coverage and pending details. The downloadable database remains
published as a release for anyone who wants to ask their own questions. Each chart uses its own source
coverage: fleet charts require organisation-wide job history, daily build charts require Tau Ceti
build jobs, failure and phase charts require detailed enrichment, and the merge timelines use
the latest observations and recorded runs. Explicitly unavailable records are reported as source
gaps. A backlog in one stream does not stop the others. The
[freshness report](static/ci-freshness.json) distinguishes source coverage from the coverage
used for published charts. Dated daily charts can incorporate historical corrections even while
their coverage is stale; the freshness check still reports that lag. Stale fleet and merge timelines
retain their previous assets. When source data cannot be read or rendered, the previous charts
are retained. A fallback's
published cutoff may be unknown when no earlier report recorded it.

Live workflow events record jobs individually. Older archives sampled the label, notification
and merge-bot workflows, which run thousands of times a day: one run in four was recorded
job by job, and each of those stands
for the unrecorded runs of its workflow in the same hour. Their share of the running and queued
panels is therefore an estimate, and their longest waits come from the sample. Before hourly
collection began, none of their runs were recorded job by job; there the running panel places an
estimated job at the end of each run, and the queue and wait panels leave those runs out.
