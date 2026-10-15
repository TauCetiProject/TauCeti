"""CI charts for the CI page, from the TauCetiCI database. Called by ci_stats_graphs.py.

The daily charts have one point (or bar) per complete UTC day, up to the coverage watermark:

  ci-build-duration.svg   median and 90th-percentile build time, by where the build ran
  ci-build-wait.svg       median and 90th-percentile wait for a runner, by where the job ran
  ci-build-phases.svg     where a PR build's time goes, as mean minutes per build
  ci-failures.svg         failed PR builds by cause, and the share of PR builds that failed
  ci-runner-minutes.svg   runner-minutes per day on each kind of runner, and those spent on
                          builds cancelled before finishing
  ci-merge-queue.svg      GitHub queue and bors builds by outcome, and PR arrivals
  ci-picker.svg           the share of PR builds that ran on GitHub-hosted runners

The merge timelines use observation/run timestamps, including the current partial UTC day:

  ci-queue-size.svg       observed ready-to-merge PR backlog
  ci-bors-staging.svg     PRs bundled into each bors staging run, coloured by outcome
"""

from __future__ import annotations

import datetime as dt
import html
import json
import math
import sqlite3
from collections import defaultdict

from chart_style import MUTED, PALETTE, TEXT, base_css, card_rect, css_px, svg_unit

UTC = dt.timezone.utc
BUILD = "sandboxed-build"
PR_BUILD = ".github/workflows/pr-build.yml"
MERGE_TRIGGERS = {"merge_queue", "bors_staging"}

ASSET_NAMES = [
    "ci-build-duration.svg", "ci-build-wait.svg", "ci-build-phases.svg", "ci-failures.svg",
    "ci-runner-minutes.svg", "ci-merge-queue.svg", "ci-picker.svg",
    "ci-queue-size.svg", "ci-bors-staging.svg",
]

# Step-name patterns for the sandboxed-build job, first match wins, mapped to a phase.
STEP_PHASES = [
    ("reporting", ("Report", "Summarise CI telemetry", "Upload CI telemetry", "Post ", "Complete job")),
    ("Mathlib cache", ("Mathlib's compressed", "Fetch Mathlib", "Require a complete Mathlib")),
    ("Lake cache", ("Lake artifact cache", "TauCeti's own oleans", "Lake archive")),
    ("build, audits, lints", ("Build exact candidate",)),
    ("lint preparation", ("watchdog toolchain", "environment-lint", "Dot-notation")),
    ("setup and checks", ("",)),
]
# The telemetry's phases, folded into the three the chart shows.
TELEMETRY_PHASES = {"build": "build", "stage-cache": "build",
                    "audit-duplicates": "audits", "audit-axioms": "audits", "audit-module-system": "audits",
                    "lint-env": "lints", "lint-style": "lints"}
PHASE_ORDER = ["setup and checks", "Mathlib cache", "Lake cache", "lint preparation",
               "build", "audits", "lints", "sandbox, unattributed", "build, audits, lints", "reporting"]

FAILURE_ORDER = ["lean-error", "lint-env", "lint-style", "dot-notation", "audit-axioms",
                 "audit-duplicates", "audit-module-system", "policy", "toolchain-incompat",
                 "timeout", "infra-cache", "infra-setup", "infra-report", "build-unknown", "other"]


def ts(s: str) -> float:
    t = dt.datetime.fromisoformat(s.replace("Z", "+00:00"))
    return (t if t.tzinfo else t.replace(tzinfo=UTC)).timestamp()


def quantile(values: list[float], q: float) -> float | None:
    """Nearest-rank quantile: the smallest value with at least q of the values at or below it."""
    if not values:
        return None
    v = sorted(values)
    return v[max(0, math.ceil(q * len(v)) - 1)]


def step_phase(name: str) -> str:
    for phase, needles in STEP_PHASES:
        if any(n in name for n in needles):
            return phase
    return "setup and checks"


# --- metrics ------------------------------------------------------------------------------------


def days_between(first: str, last: str) -> list[str]:
    d0, d1 = dt.date.fromisoformat(first), dt.date.fromisoformat(last)
    return [(d0 + dt.timedelta(days=i)).isoformat() for i in range((d1 - d0).days + 1)]


def metrics(db: sqlite3.Connection, first: str, last: str, other_jobs_until=None) -> dict:
    """Per-day series for every daily chart, over complete UTC days first..last."""
    days = days_between(first, last)
    lo, hi = f"{first}T00:00:00Z", f"{last}T23:59:59Z"
    # Every attempt's build job (jobs keeps all attempts; runs only the latest):
    # PR builds and both main-branch merge engines, excluding manual dispatches.
    builds = db.execute(f"""
        SELECT substr(j.created_at, 1, 10), r.trigger, j.runner_kind, j.conclusion, j.wait_s, j.run_s,
               j.failure_class, j.job_id, r.run_id
        FROM jobs j JOIN runs r USING (repo, run_id)
        WHERE r.repo = 'TauCeti' AND r.workflow = '{PR_BUILD}' AND j.name = '{BUILD}'
          AND r.trigger IN ('pr', 'merge_queue', 'bors_staging') AND j.runner_kind IN ('github', 'namespace')
          AND j.created_at BETWEEN ? AND ?""", (lo, hi)).fetchall()

    def where(trigger, kind):
        return "merge validation" if trigger in MERGE_TRIGGERS else f"PR, {'GitHub' if kind == 'github' else 'Namespace'}"

    dur = defaultdict(list)
    wait = defaultdict(list)
    fails = defaultdict(lambda: defaultdict(int))
    pr_total = defaultdict(int)
    picker = defaultdict(lambda: [0, 0])
    job_ids = []
    for day, trigger, kind, concl, wait_s, run_s, fclass, job_id, run_id in builds:
        w = where(trigger, kind)
        if concl == "success" and run_s is not None:
            dur[(day, w)].append(run_s / 60)
        if wait_s is not None:
            wait[(day, w)].append(wait_s / 60)
        if trigger == "pr" and concl in ("success", "failure", "timed_out"):
            pr_total[day] += 1
            if concl != "success":
                fails[day][fclass or ("timeout" if concl == "timed_out" else "build-unknown")] += 1
        if trigger == "pr":
            picker[day][0 if kind == "github" else 1] += 1  # runner_kind is github or namespace here
        if trigger == "pr" and concl == "success":
            job_ids.append(job_id)

    # Waits of the other (short) GitHub jobs, from what was recorded (a sample, for most workflows).
    other_hi = hi
    if other_jobs_until is not None:
        other_last = (dt.datetime.fromtimestamp(other_jobs_until, UTC)-dt.timedelta(days=1)).date()
        other_hi = min(hi, f'{other_last}T23:59:59Z')
    for day, wait_s in db.execute("""
            SELECT substr(j.created_at, 1, 10), j.wait_s FROM jobs j JOIN runs r USING (repo, run_id)
            WHERE j.runner_kind = 'github' AND j.name NOT IN ('sandboxed-build', 'verify', 'build')
              AND j.wait_s IS NOT NULL AND j.created_at BETWEEN ? AND ?""", (lo, other_hi)):
        wait[(day, "other GitHub jobs")].append(wait_s / 60)

    # Where a successful PR build's time goes: step durations grouped into phases, with the single
    # build step split by the sandbox's telemetry where a run has it.
    phase_minutes = defaultdict(lambda: defaultdict(float))
    phase_count = defaultdict(int)
    telemetry = {}
    try:
        for run_id, phases_json in db.execute("SELECT run_id, phases_json FROM telemetry"):
            telemetry[run_id] = phases_json
    except sqlite3.OperationalError:
        pass
    run_of_job = {job_id: run_id for (_, _, _, _, _, _, _, job_id, run_id) in builds}
    day_of_job = {job_id: day for (day, _, _, _, _, _, _, job_id, _) in builds}
    chunk = 500
    for i in range(0, len(job_ids), chunk):
        ids = job_ids[i:i + chunk]
        rows = db.execute(f"SELECT job_id, name, run_s FROM steps WHERE job_id IN ({','.join('?' * len(ids))})",
                          ids).fetchall()
        per_job = defaultdict(list)
        for job_id, name, run_s in rows:
            per_job[job_id].append((name, run_s or 0))
        for job_id, steps in per_job.items():
            day = day_of_job[job_id]
            phase_count[day] += 1
            tel = telemetry.get(run_of_job[job_id])
            split = None
            if tel:
                split = defaultdict(float)
                for p in json.loads(tel):
                    if p.get("seconds") is not None and p["phase"] in TELEMETRY_PHASES:
                        split[TELEMETRY_PHASES[p["phase"]]] += p["seconds"]
            for name, secs in steps:
                phase = step_phase(name)
                if phase == "build, audits, lints" and split and sum(split.values()) > 0:
                    # The sandbox's own timings, as recorded. What they do not cover of the step's
                    # (trusted) duration stays unattributed rather than being spread over the phases;
                    # only if they exceed it (clock skew) are they scaled down to fit.
                    total = sum(split.values())
                    factor = min(1.0, secs / total)
                    for k, v in split.items():
                        phase_minutes[day][k] += v * factor / 60
                    phase_minutes[day]["sandbox, unattributed"] += max(0.0, secs - total) / 60
                else:
                    phase_minutes[day][phase] += secs / 60

    # Build minutes (the build jobs of the build workflows, all recorded in full), by the day the
    # job started.
    minutes = defaultdict(lambda: defaultdict(float))
    for day, kind, trigger, concl, run_s in db.execute("""
            SELECT substr(j.started_at, 1, 10), j.runner_kind, r.trigger, j.conclusion, j.run_s
            FROM jobs j JOIN runs r USING (repo, run_id)
            WHERE r.repo = 'TauCeti' AND j.name IN ('sandboxed-build', 'verify', 'build', 'performance-gate')
              AND j.run_s IS NOT NULL AND j.started_at BETWEEN ? AND ?""", (lo, hi)):
        if kind == "namespace":
            minutes[day]["Namespace"] += run_s / 60
        elif kind == "github":
            minutes[day]["GitHub-hosted"] += run_s / 60
        if trigger == "pr" and concl == "cancelled":
            minutes[day]["cancelled PR builds"] += run_s / 60

    # Main-branch validation builds for both engines, including every rerun.
    # Pilot and unidentified bors dispatches are excluded from production totals.
    mq = defaultdict(lambda: defaultdict(int))
    for day, trigger, kind, concl, *_ in builds:
        if trigger in MERGE_TRIGGERS:
            mq[day][concl if concl in ("success", "failure", "cancelled") else "other"] += 1
    landed = defaultdict(int)
    # A staging commit can exist hours before it is accepted onto main. Use
    # the earliest recorded main-push evidence, never its committer timestamp.
    # Repeated validation and duplicate commits for one PR still count once.
    for day, n in db.execute("""
            SELECT substr(landed_at, 1, 10), COUNT(*) FROM (
                SELECT c.pr, MIN(l.landed_at) AS landed_at
                FROM main_commits c JOIN main_landings l
                  ON l.repo = 'TauCeti' AND l.head_sha = c.sha
                WHERE c.pr IS NOT NULL GROUP BY c.pr
            ) WHERE landed_at BETWEEN ? AND ? GROUP BY 1""", (lo, hi)):
        landed[day] = n

    return {"days": days, "dur": dur, "wait": wait, "fails": fails, "pr_total": pr_total,
            "picker": picker, "phase_minutes": phase_minutes, "phase_count": phase_count,
            "minutes": minutes, "mq": mq, "landed": landed}


# --- rendering ----------------------------------------------------------------------------------

W, H = 980, 440
L, R, TOP, BOTTOM = 64, 52, 124, 380


def frame(title: str, subtitle: str) -> list[str]:
    return [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" role="img">',
            f"<style>{base_css(W)}.legend{{font-size:{css_px(W, 12)};fill:{TEXT}}}"
            f".note{{font-size:{css_px(W, 11)};fill:{MUTED}}}</style>",
            card_rect(W, H),
            f'<text class="title" x="{L}" y="36">{html.escape(title)}</text>',
            f'<text class="subtitle" x="{L}" y="58">{html.escape(subtitle)}</text>']


def nice_max(v: float) -> tuple[float, float]:
    v = max(v, 1e-9)
    for step in (0.1, 0.2, 0.25, 0.5, 1, 2, 2.5, 5, 10, 20, 25, 50, 100, 200, 250, 500, 1000, 2000, 5000):
        if v / step <= 5:
            return step, step * -(-v // step)
    return 10000, 10000 * -(-v // 10000)


def axes(out: list[str], days: list[str], vmax: float, ylabel: str, fmt=lambda v: f"{v:g}"):
    step, top = nice_max(vmax)
    y = lambda v: BOTTOM - v / top * (BOTTOM - TOP)
    v = 0.0
    while v <= top + 1e-9:
        out.append(f'<line class="grid" x1="{L}" x2="{W-R}" y1="{y(v):.1f}" y2="{y(v):.1f}"/>'
                   f'<text class="tick" x="{L-8}" y="{y(v)+4:.1f}" text-anchor="end">{fmt(v)}</text>')
        v += step
    out.append(f'<text class="tick" transform="translate(16,{(TOP+BOTTOM)/2:.0f}) rotate(-90)" '
               f'text-anchor="middle">{html.escape(ylabel)}</text>')
    n = len(days)
    bw = (W - L - R) / max(n, 1)
    x = lambda i: L + (i + 0.5) * bw
    every = max(1, n // 10)
    for i, d in enumerate(days):
        if i % every == 0:
            out.append(f'<text class="tick" x="{x(i):.1f}" y="{BOTTOM+18}" text-anchor="middle">'
                       f'{dt.date.fromisoformat(d).strftime("%d %b")}</text>')
    out.append(f'<line class="axis" x1="{L}" x2="{W-R}" y1="{BOTTOM}" y2="{BOTTOM}"/>')
    return x, y, bw


MAX_LEGEND = 12  # three rows of four fit between the subtitle and the plot


def legend(out: list[str], items: list[tuple[str, str]], dashed: set[str] = frozenset()):
    if len(items) > MAX_LEGEND:
        items = items[:MAX_LEGEND - 1] + [("… more in ci-stats.json", MUTED)]
    for idx, (label, colour) in enumerate(items):
        lx, ly = L + (idx % 4) * 225, 72 + (idx // 4) * 14
        if label in dashed:
            out.append(f'<line x1="{lx}" x2="{lx+12}" y1="{ly+6}" y2="{ly+6}" stroke="{colour}" '
                       f'stroke-width="2" stroke-dasharray="3 2"/>')
        else:
            out.append(f'<rect x="{lx}" y="{ly}" width="12" height="12" rx="2" fill="{colour}"/>')
        out.append(f'<text class="legend" x="{lx+17}" y="{ly+10}">{html.escape(label)}</text>')


def lines_chart(title, subtitle, days, series, ylabel, fmt=lambda v: f"{v:g}", dashed=frozenset()):
    """series: [(label, colour, [value or None per day])]"""
    out = frame(title, subtitle)
    vmax = max((v for _, _, vals in series for v in vals if v is not None), default=1)
    x, y, _ = axes(out, days, vmax, ylabel, fmt)
    for label, colour, vals in series:
        pts, segs = [], []
        for i, v in enumerate(vals):
            if v is None:
                if pts:
                    segs.append(pts)
                pts = []
            else:
                pts.append((x(i), y(v)))
        if pts:
            segs.append(pts)
        dash = ' stroke-dasharray="5 3"' if label in dashed else ""
        for seg in segs:
            if len(seg) == 1:
                out.append(f'<circle cx="{seg[0][0]:.1f}" cy="{seg[0][1]:.1f}" r="2.5" fill="{colour}"/>')
            else:
                out.append(f'<polyline fill="none" stroke="{colour}" stroke-width="{svg_unit(W, 2)}"{dash} '
                           f'points="' + " ".join(f"{a:.1f},{b:.1f}" for a, b in seg) + '"/>')
    legend(out, [(l, c) for l, c, _ in series], dashed)
    out.append("</svg>")
    return "\n".join(out)


def stacked_chart(title, subtitle, days, series, ylabel, line=None, line_fmt=lambda v: f"{v:g}"):
    """series: [(label, colour, [value per day])], stacked bars; `line`: (label, colour, values, max)
    drawn against a right-hand scale."""
    out = frame(title, subtitle)
    totals = [sum(vals[i] for _, _, vals in series) for i in range(len(days))]
    x, y, bw = axes(out, days, max(totals, default=1), ylabel)
    for i in range(len(days)):
        base = 0.0
        for label, colour, vals in series:
            v = vals[i]
            if v > 0:
                out.append(f'<rect x="{x(i)-bw*0.38:.1f}" y="{y(base+v):.1f}" width="{bw*0.76:.1f}" '
                           f'height="{y(base)-y(base+v):.1f}" fill="{colour}" fill-opacity="0.9"/>')
            base += v
    items = [(l, c) for l, c, _ in series]
    if line:
        label, colour, vals, vmax = line
        yr = lambda v: BOTTOM - v / vmax * (BOTTOM - TOP)
        segs, pts = [], []
        for i, v in enumerate(vals):
            if v is None:
                segs, pts = segs + ([pts] if pts else []), []
            else:
                pts.append((x(i), yr(v)))
        segs += [pts] if pts else []
        for seg in segs:
            if len(seg) == 1:
                out.append(f'<circle cx="{seg[0][0]:.1f}" cy="{seg[0][1]:.1f}" r="3" fill="{colour}"/>')
            else:
                out.append(f'<polyline fill="none" stroke="{colour}" stroke-width="{svg_unit(W, 2)}" '
                           f'stroke-dasharray="5 3" points="' + " ".join(f"{a:.1f},{b:.1f}" for a, b in seg) + '"/>')
        for frac in (0, 0.5, 1):
            out.append(f'<text class="tick" x="{W-R+6}" y="{yr(vmax*frac)+4:.1f}" '
                       f'text-anchor="start">{line_fmt(vmax*frac)}</text>')
        items.append((label, colour))
    legend(out, items, {line[0]} if line else set())
    out.append("</svg>")
    return "\n".join(out)


# Minute observations normally arrive sixty seconds apart. Do not connect across
# an outage or extrapolate the last sample to the coverage watermark.
QUEUE_SAMPLE_GAP = 3 * 60


def merge_history(db: sqlite3.Connection, since: float, until: float, *, include_queue=True, include_staging=True) -> dict:
    """Timestamped backlog samples and one result per recorded production staging run.

    runs holds each run's latest attempt; use its overall conclusion, including
    publication/finalization failures after a successful sandboxed build.
    """
    bounds = tuple(dt.datetime.fromtimestamp(t, UTC).isoformat() for t in (since, until))
    queue = []
    metadata = db.execute("SELECT 1 FROM sqlite_master WHERE name='queue_observation_metadata'").fetchone()
    query = ("""SELECT o.observed_at,
                    CASE WHEN m.eligible_count IS NULL THEN o.eligible_json END,
                    m.eligible_count, m.candidate_scan_complete, m.candidate_snapshot_at
                FROM merge_observations o LEFT JOIN queue_observation_metadata m USING(observed_at)"""
             if metadata else """SELECT o.observed_at,o.eligible_json,NULL,NULL,NULL FROM merge_observations o""")
    query += """ WHERE julianday(o.observed_at) >= julianday(?)
                  AND julianday(o.observed_at) < julianday(?) ORDER BY o.observed_at"""
    for stamp, eligible, count, complete, snapshot in (db.execute(query, bounds) if include_queue else []):
        if complete == 0 and not snapshot:
            # After a bot restart the first scan is only a partial candidate set.
            # A later in-progress scan may safely reuse its completed snapshot.
            queue.append((ts(stamp), None))
            continue
        if count is None:
            count = len({p['pr'] for p in json.loads(eligible)
                         if type(p.get('pr')) is int and p['pr'] > 0})
        queue.append((ts(stamp), count))

    runs, missing_members = [], 0
    rows = db.execute(f"""
            SELECT r.created_at, r.run_id, r.run_attempt, r.conclusion, m.batch_id, m.members_json
            FROM runs r JOIN merge_builds m USING (repo, run_id)
            WHERE r.repo = 'TauCeti' AND r.workflow = '{PR_BUILD}'
              AND r.trigger = 'bors_staging' AND m.engine = 'bors'
              AND r.conclusion IS NOT NULL
              AND julianday(r.created_at) >= julianday(?)
              AND julianday(r.created_at) < julianday(?) ORDER BY r.created_at, r.run_id""", bounds) if include_staging else []
    for stamp, run_id, attempt, conclusion, batch, members in rows:
        prs = {p["pr"] for p in json.loads(members or "[]")
               if type(p.get("pr")) is int and p["pr"] > 0}
        if not prs:
            missing_members += 1
            continue
        runs.append({"at": ts(stamp), "run_id": run_id, "attempt": attempt,
                     "conclusion": conclusion, "batch": batch, "prs": len(prs)})
    return {"queue": queue, "runs": runs, "missing_members": missing_members}


def time_axes(out: list[str], since: float, until: float, vmax: int, ylabel: str):
    """A continuous UTC time axis and a whole-PR count axis."""
    step, _ = nice_max(max(vmax, 5))
    step = math.ceil(step)
    top = step * math.ceil(max(vmax, 5) / step)
    x = lambda t: L + (t - since) / (until - since) * (W - L - R)
    y = lambda v: BOTTOM - v / top * (BOTTOM - TOP)
    v = 0
    while v <= top:
        out.append(f'<line class="grid" x1="{L}" x2="{W-R}" y1="{y(v):.1f}" y2="{y(v):.1f}"/>'
                   f'<text class="tick" x="{L-8}" y="{y(v)+4:.1f}" text-anchor="end">{v:g}</text>')
        v += step
    out.append(f'<text class="tick" transform="translate(16,{(TOP+BOTTOM)/2:.0f}) rotate(-90)" '
               f'text-anchor="middle">{html.escape(ylabel)}</text>')
    # Choose ticks from hours/days, rather than placing one dot at each day's centre.
    span = until - since
    tick = next(t for t in (3600, 3*3600, 6*3600, 12*3600, 86400, 2*86400, 4*86400)
                if span / t <= 10)
    t = math.ceil(since / tick) * tick
    while t < until:
        stamp = dt.datetime.fromtimestamp(t, UTC)
        label = stamp.strftime("%d %b %H:%M" if tick < 86400 else "%d %b")
        out.append(f'<text class="tick" x="{x(t):.1f}" y="{BOTTOM+18}" text-anchor="middle">{label}</text>')
        t += tick
    out.append(f'<line class="axis" x1="{L}" x2="{W-R}" y1="{BOTTOM}" y2="{BOTTOM}"/>'
               f'<text class="tick" x="{(L+W-R)/2}" y="{BOTTOM+40}" text-anchor="middle">Time (UTC)</text>')
    return x, y


def inventory_gaps(db, since, until):
    """Intervals lacking proven TauCeti run inventory; recorded dots remain useful there."""
    if db.execute("SELECT 1 FROM sqlite_master WHERE name='stream_coverage'").fetchone():
        rows = db.execute("""SELECT since,complete_to FROM stream_coverage
            WHERE repo='TauCeti' AND stream='inventory' ORDER BY since""").fetchall()
    elif db.execute("SELECT 1 FROM sqlite_master WHERE name='coverage'").fetchone():
        rows = [(dt.datetime.fromtimestamp(since, UTC).isoformat(), end)
                for (end,) in db.execute("SELECT complete_to FROM coverage WHERE repo='TauCeti'")]
    else:
        rows = []
    cursor, gaps = since, []
    for lo, hi in sorted((ts(lo), ts(hi)) for lo, hi in rows):
        lo, hi = max(since, lo), min(until, hi)
        if hi <= lo or hi <= cursor:
            continue
        if lo > cursor:
            gaps.append((cursor, lo))
        cursor = hi
    if cursor < until:
        gaps.append((cursor, until))
    return gaps


def merge_charts(db: sqlite3.Connection, until: float, *, queue_until=None, staging_until=None,
                 include_queue=True, include_staging=True) -> dict[str, str]:
    """Merge timelines use independent observation and recorded-run timestamps.

    Incomplete run inventory is shaded, so partial staging data is never
    presented as proof that no runs occurred. Queue samples never fill gaps.
    """
    queue_until = until if queue_until is None else queue_until
    staging_until = until if staging_until is None else staging_until
    since = until - 30 * 86400
    m = merge_history(db, since, until, include_queue=include_queue, include_staging=include_staging)
    starts = [t for t, _ in m["queue"]] + [r["at"] for r in m["runs"]]
    if starts:
        since = max(since, math.floor(min(starts) / 86400) * 86400)
    def through(t):
        return dt.datetime.fromtimestamp(t, UTC).strftime("%d %b %Y %H:%M UTC")

    out = frame("Merge queue size", f"Observed ready-to-merge PR backlog; data through {through(queue_until)}")
    samples = [(t, n) for t, n in m['queue'] if t < queue_until]
    x, y = time_axes(out, since, until, max((n for _, n in samples if n is not None), default=0), "PRs")
    segments = []
    segment = None
    for t, n in samples:
        if n is None:
            segment = None
            continue
        if segment is None or t - segment[-1][0] > QUEUE_SAMPLE_GAP:
            segment = []
            segments.append(segment)
        segment.append((t, n))
    for segment in segments:
        # Keep both sides of a change, but omit redundant interior samples.
        points = [segment[0]]
        for previous, current in zip(segment, segment[1:]):
            if previous[1] != current[1]:
                points.extend([(current[0], previous[1]), current])
        points.append(segment[-1])
        out.append(f'<polyline fill="none" stroke="{PALETTE[2]}" stroke-width="{svg_unit(W, 2)}" '
                   f'points="' + " ".join(f"{x(t):.1f},{y(n):.1f}" for t, n in points) + '"/>')
        if len(segment) == 1:
            t, n = segment[0]
            out.append(f'<circle cx="{x(t):.1f}" cy="{y(n):.1f}" r="2.5" fill="{PALETTE[2]}"/>')
    legend(out, [("ready-to-merge PRs", PALETTE[2])])
    if not any(n is not None for _, n in samples):
        out.append(f'<text class="note" x="{L+16}" y="{TOP+24}">No queue observations in this window</text>')
    out.append("</svg>")
    queue_svg = "\n".join(out)

    if not include_staging:
        return {'ci-queue-size.svg': queue_svg} if include_queue else {}

    out = frame("Bors staging runs", f"Recorded runs at creation time; data through {through(staging_until)}")
    runs = [r for r in m['runs'] if r['at'] < staging_until]
    x, y = time_axes(out, since, until, max((r["prs"] for r in runs), default=0), "PRs in batch")
    gaps = inventory_gaps(db, since, until)
    for lo, hi in gaps:
        out.append(f'<rect class="coverage-gap" x="{x(lo):.1f}" y="{TOP}" '
                   f'width="{x(hi)-x(lo):.1f}" height="{BOTTOM-TOP}" fill="{MUTED}" fill-opacity="0.12">'
                   '<title>Run inventory incomplete; recorded runs are shown</title></rect>')
    for r in runs:
        conclusion = r["conclusion"]
        colour = (PALETTE[5] if conclusion == "success" else PALETTE[3]
                  if conclusion in {"failure", "timed_out", "startup_failure"}
                  else MUTED)
        stamp = dt.datetime.fromtimestamp(r["at"], UTC).strftime("%d %b %Y %H:%M:%S UTC")
        label = (f'Run {r["run_id"]}, attempt {r["attempt"]}, batch {r["batch"]}: '
                 f'{r["prs"]} PRs, {conclusion}; created {stamp}')
        out.append(f'<circle cx="{x(r["at"]):.1f}" cy="{y(r["prs"]):.1f}" r="3.5" '
                   f'fill="{colour}" fill-opacity="0.85"><title>{html.escape(label)}</title></circle>')
    items = [("success", PALETTE[5]), ("failure", PALETTE[3]), ("cancelled / other", MUTED)]
    if gaps:
        items.append(('shaded: inventory gaps', MUTED))
    legend(out, items)
    if not runs:
        out.append(f'<text class="note" x="{L+16}" y="{TOP+24}">No staging runs with known batch sizes</text>')
    if m["missing_members"]:
        out.append(f'<text class="note" x="{L}" y="{TOP-10}">'
                   f'{m["missing_members"]} runs omitted: batch membership unavailable</text>')
    out.append("</svg>")
    result = {}
    if include_queue:
        result['ci-queue-size.svg'] = queue_svg
    if include_staging:
        result['ci-bors-staging.svg'] = '\n'.join(out)
    return result


def charts(db: sqlite3.Connection, until: float, other_jobs_until=None, assets=None, covered_since=None) -> dict[str, str]:
    """All daily charts, through the last complete UTC day before `until`."""
    last = (dt.datetime.fromtimestamp(until, UTC) - dt.timedelta(days=1)).date()
    first_row = db.execute(f"SELECT MIN(created_at) FROM runs WHERE workflow = '{PR_BUILD}'").fetchone()[0]
    if not first_row:
        return {}
    first = max(dt.date.fromisoformat(first_row[:10]), last - dt.timedelta(days=89))
    if covered_since is not None:
        start=dt.datetime.fromtimestamp(covered_since,UTC)
        first_covered=start.date() if start.time()==dt.time() else start.date()+dt.timedelta(days=1)
        first=max(first,first_covered)
    if first > last:
        return {}
    m = metrics(db, first.isoformat(), last.isoformat(), other_jobs_until)
    days = m["days"]
    span = f"UTC days {dt.date.fromisoformat(days[0]):%d %b} to {dt.date.fromisoformat(days[-1]):%d %b}"
    places = [("PR, GitHub", PALETTE[2]), ("PR, Namespace", PALETTE[1]), ("merge validation", PALETTE[3])]
    out = {}

    series = []
    for place, colour in places:
        series.append((f"{place}, median", colour, [quantile(m["dur"][(d, place)], 0.5) for d in days]))
        series.append((f"{place}, 90th pct", colour, [quantile(m["dur"][(d, place)], 0.9) for d in days]))
    out["ci-build-duration.svg"] = lines_chart(
        "How long a build takes", f"Successful sandboxed builds, from start to finish; {span}",
        days, series, "minutes", dashed={s[0] for s in series if s[0].endswith("pct")})

    series = []
    for place, colour in places + [("other GitHub jobs", PALETTE[0])]:
        series.append((f"{place}, median", colour, [quantile(m["wait"][(d, place)], 0.5) for d in days]))
        series.append((f"{place}, 90th pct", colour, [quantile(m["wait"][(d, place)], 0.9) for d in days]))
    out["ci-build-wait.svg"] = lines_chart(
        "How long a job waits for a runner", f"From the job being queued to it starting; {span}",
        days, series, "minutes", dashed={s[0] for s in series if s[0].endswith("pct")})
    if other_jobs_until is not None and other_jobs_until < until:
        stamp = dt.datetime.fromtimestamp(other_jobs_until, UTC).strftime('%d %b %H:%M UTC')
        note = f'Other GitHub jobs: coverage through {stamp}' if other_jobs_until > 0 else 'Other GitHub jobs: coverage unavailable'
        out['ci-build-wait.svg'] = out['ci-build-wait.svg'].replace('</svg>',
            f'<text class="note" x="{L}" y="112">{note}</text>\n</svg>')

    phases = [p for p in PHASE_ORDER if any(m["phase_minutes"][d].get(p) for d in days)]
    series = [(p, PALETTE[i % len(PALETTE)],
               [m["phase_minutes"][d].get(p, 0) / m["phase_count"][d] if m["phase_count"][d] else 0 for d in days])
              for i, p in enumerate(phases)]
    out["ci-build-phases.svg"] = stacked_chart(
        "Where a PR build's time goes", f"Mean minutes per successful PR build, by phase; {span}",
        days, series, "minutes per build")

    classes = [c for c in FAILURE_ORDER if any(m["fails"][d].get(c) for d in days)]
    # (A day's bars and the rate share one denominator: finished PR builds, timeouts counted as failures.)
    classes += sorted({c for d in days for c in m["fails"][d]} - set(classes))
    series = [(c, PALETTE[i % len(PALETTE)], [m["fails"][d].get(c, 0) for d in days]) for i, c in enumerate(classes)]
    rate = [sum(m["fails"][d].values()) / m["pr_total"][d] if m["pr_total"][d] else None for d in days]
    out["ci-failures.svg"] = stacked_chart(
        "Why PR builds fail", f"Failed PR builds by cause (bars) and the share that failed (dashed, right "
        f"scale); {span}", days, series, "failed builds",
        line=("failure rate", TEXT, rate, max([r for r in rate if r is not None] + [0.1])),
        line_fmt=lambda v: f"{v:.0%}")

    kinds = [("Namespace", PALETTE[1]), ("GitHub-hosted", PALETTE[2]), ("cancelled PR builds", PALETTE[3])]
    series = [(k, c, [m["minutes"][d].get(k, 0) for d in days]) for k, c in kinds]
    out["ci-runner-minutes.svg"] = lines_chart(
        "Build minutes per day", f"Build jobs by runner (Namespace is billed; GitHub-hosted is free), and "
        f"cancelled PR builds; {span}", days, series, "minutes")

    outcomes = [("success", PALETTE[5]), ("failure", PALETTE[3]), ("cancelled", MUTED), ("other", PALETTE[4])]
    series = [(o, c, [m["mq"][d].get(o, 0) for d in days]) for o, c in outcomes]
    landed = [m["landed"].get(d, 0) for d in days]
    out["ci-merge-queue.svg"] = stacked_chart(
        "Merge validation", f"GitHub queue + bors builds (bars); PR arrivals on main (dashed, right scale); "
        f"{span}", days, series, "merge validation builds",
        line=("PR arrivals on main", TEXT, landed, max(landed + [1])))

    share = [m["picker"][d][0] / sum(m["picker"][d]) if sum(m["picker"][d]) else None for d in days]
    out["ci-picker.svg"] = lines_chart(
        "PR builds on GitHub-hosted runners", f"Share of PR builds the runner picker sent to GitHub rather "
        f"than Namespace; {span}", days, [("share on GitHub", PALETTE[2], share)], "share",
        fmt=lambda v: f"{v:.0%}")
    return {name: svg for name, svg in out.items() if assets is None or name in assets}
