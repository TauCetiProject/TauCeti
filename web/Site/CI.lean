import VersoBlog
open Verso Genre Blog
open Verso.Output Verso.Output.Html

/-- Prepared operational snapshots update without a website build. -/
def operations : Html := {{
  <section id="operations" class="ci-operations" data-operations="true" aria-label="Queue and runner operations">
    <p class="ops-status" data-ops-health="true">"Loading queue and runner observations…"</p>
    <span class="ops-announcement" data-ops-announcement="true" role="status"></span>
    <nav class="ops-tabs" aria-label="Operations views">
      <a href="ci/#now" data-ops-tab="now">"Now"</a>
      <a href="ci/#queue" data-ops-tab="queue">"Queue"</a>
      <a href="ci/#runners" data-ops-tab="runners">"Runners"</a>
      <a href="ci/#history" data-ops-tab="history">"History"</a>
    </nav>
    <div data-ops-view="true"></div>
    <noscript>"Enable JavaScript for the live queue, PR lookup and runner views. Historical charts follow below."</noscript>
  </section>
  <script src="static/ci-operations.js" defer="defer"></script>
}}

/-- Independent chart refresh, with its source cache behind a disclosure. -/
def historicalStatus : Html := {{
  <details class="ci-chart-source ops-diagnostics" data-ci-live="true">
    <summary>"Historical chart source status"</summary>
    <p>"Chart publisher cache · all organisation workflow jobs"</p>
    <p data-ci-status="true">"Loading chart source status…"</p>
    <dl class="ci-live-counts" data-ci-counts="true"></dl>
    <p class="ci-live-backlog" data-ci-backlog="true" hidden="hidden"></p>
  </details>
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
  "Build minutes per day by cloud runner and dedicated host, and cancelled PR builds"
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

The merge queue, CI jobs and dedicated hosts share this operational view. Each source reports its own freshness.

:::blob operations
:::

:::blob historicalStatus
:::

:::blob recentFleetGraph
:::

# Understanding the fleet

Every pull request is built in a sandbox. GitHub-hosted and Namespace runners provide cloud
capacity; dedicated servers also run disposable CI guests and mathematics workers. The Runners
tab shows every published host, including hosts with CI disabled. Routing and available slots
change with the configured fleet policy. A requested cloud profile is not a measurement of
physical utilization. Unobserved resource fields stay unknown.

The queue owns admission, exact candidate versions, CI verdict bindings and landings. Its head
runs staging CI while repair and preparation work can overlap it. A failed source build supplies
repair evidence; the repaired candidate is tested again before promotion. The timelines retain
each run attempt, including superseded candidates. Observer failures preserve the last known
work and are reported separately from build silence.

:::blob monthlyFleetGraph
:::

# Merge queue and staging runs

How many pull requests are waiting to land, and how large are the batches bors tests?
These timelines show up to the last thirty days, including the current partial UTC day.
The backlog counts distinct PRs accepted by ai-merge-queue, including waiting inputs and
active batches being tested or repaired. Landed and withdrawn work is excluded.
Historical bors points count ready-labelled candidates; reconstructed queue history is
labelled on the chart. Missing observations leave gaps. The latest count and snapshot
time identify the newest complete sample; chart publication can happen later.

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
For a sample of successful builds with recorded phases, that step is split into them, with any time the phases do
not cover shown as unattributed. Days with recorded phase samples use the sampled
builds for the phase means; other days retain coarse API step timings.

:::blob phasesGraph
:::

Why do builds fail? Each failed pull-request build is classified by the step that failed and the
available error lines it printed: a Lean error, one of the lints, one of the audits, a policy check (scope,
size, pins), a timeout, or an infrastructure fault such as a cache download. The classification is
by pattern, so it is a guide rather than a verdict. Optional failure details are
limited to recent builds; unavailable causes remain unknown.

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
entry; historical bors batches used splitting, while the current queue repairs a failed combined candidate. The bars count build jobs,
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
service receives GitHub workflow and job events, repairs current missing data and samples optional details
within a shared GitHub request budget. New and corrected records update the affected time
buckets. Reports update independently of this website's build, and the page checks for published
operations updates every five seconds while visible; historical charts keep their separate cadence. Reading this page does not trigger GitHub API requests.
During validation or an outage, the page retains its static or last successful reports.

The [live report manifest](https://ci-data.taucetiproject.org/v1/ci/manifest.json) records
publication times, source coverage and pending details. The existing downloadable database remains available as a historical release;
it is refreshed only for an explicit analysis. Static fallbacks cache the published
charts rather than rebuilding them from the database. Each chart uses its own source
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
