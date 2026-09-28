#!/usr/bin/env python3
"""CI fleet charts for the Tau Ceti CI page, drawn from the TauCetiCI database.

    python3 scripts/ci_stats_graphs.py --db ci.sqlite --out-dir web/static_files/

The database is the `ci.sqlite.gz` asset of https://github.com/TauCetiProject/TauCetiCI/releases/tag/db
(`--download` fetches it). Writes:

  ci-fleet-72h.svg   the fleet timeline for the last 72 hours in 10-minute bins
  ci-fleet-30d.svg   the same for the last 30 days in 2-hour bins
  ci-stats.json      the binned series behind both, for anyone who wants the numbers

and the daily charts of ci_daily_graphs.py (build duration, waits, phases, failures, runner-minutes,
merge queue, runner picker).

The fleet timeline has three panels on one time axis, after Marcelo Lynch's mathlib4 fleet graph:

  1. Jobs running (time-averaged over each bin), stacked by runner and kind, against the 20-job cap
     on concurrent GitHub-hosted jobs. Ticks under the axis mark PR builds the runner picker sent to
     Namespace.
  2. The peak number of jobs waiting for a runner in each bin, GitHub-hosted and Namespace.
  3. The longest wait for a runner over the trailing 30 minutes, for build jobs and for the short
     label, notification and merge jobs, against a 5-minute reference line.
"""

from __future__ import annotations

import argparse
import bisect
import datetime as dt
import gzip
import html
import json
import shutil
import sqlite3
import subprocess
import sys
import tempfile
import xml.etree.ElementTree as ET
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import ci_daily_graphs  # noqa: E402
from chart_style import AXIS, BG, MUTED, PANEL, PALETTE, TEXT, base_css, card_rect, css_px, svg_unit  # noqa: E402

UTC = dt.timezone.utc
HOSTED_CAP = 20
# Jobs of these names in the build workflows are the builds; everything else is "other".
BUILD_JOBS = {"sandboxed-build", "verify", "build", "performance-gate"}
# Queue waits cannot exceed GitHub's 24-hour queue limit, nor runs its 6-hour job limit, so a job
# overlapping the window was created no more than this long before it.
LOOKBACK = 30 * 3600
# Refuse to redraw from data older than this: the freshness report should say so instead.
MAX_STALENESS = 36 * 3600

# (key, label, colour); stacking order bottom to top.
SERIES = [
    ("gh-build-pr", "PR builds on GitHub", PALETTE[2]),
    ("gh-build-other", "main and scheduled builds on GitHub", PALETTE[10]),
    ("gh-other", "other GitHub jobs", PALETTE[0]),
    ("ns-pr", "PR builds on Namespace", PALETTE[1]),
    ("ns-mq", "merge queue on Namespace", PALETTE[3]),
    ("ns-other", "other Namespace jobs", PALETTE[4]),
]
WAIT_SERIES = [("build", "builds", PALETTE[1]), ("other", "other jobs", PALETTE[0])]


def ts(s: str) -> float:
    t = dt.datetime.fromisoformat(s.replace("Z", "+00:00"))
    return (t if t.tzinfo else t.replace(tzinfo=UTC)).timestamp()


def iso(t: float) -> str:
    return dt.datetime.fromtimestamp(t, UTC).strftime("%Y-%m-%dT%H:%M:%SZ")


def classify(name: str, kind: str, trigger: str) -> tuple[str, str]:
    build = name in BUILD_JOBS
    if kind == "namespace":
        key = {"merge_queue": "ns-mq", "pr": "ns-pr"}.get(trigger, "ns-other")
    elif build:
        key = "gh-build-pr" if trigger in ("pr", "workflow_dispatch") else "gh-build-other"
    else:
        key = "gh-other"
    return key, "build" if build else "other"


def load_jobs(db: sqlite3.Connection, since: float, until: float) -> list[dict]:
    """Every job whose queue or run overlaps [since, until], classified and weighted.

    TauCetiCI fetches the jobs of only a sample of the high-volume workflows' runs. A fetched job
    of such a workflow stands for the unfetched runs of the same workflow in the same UTC hour: its
    weight is the hour's runs over the hour's fetched runs. The hour, not the day, because how much
    was sampled changes between collections. A workflow-hour with no fetched run at all (long
    backfills) is represented by one estimated job per run, placed at the end of the run and lasting
    the workflow's median job time; those count toward jobs running only, because the time before
    them mixes waiting for a runner with waiting on a concurrency group."""
    lo, hi = iso(since - LOOKBACK), iso(until)
    counts = {}
    for workflow, day, total, fetched in db.execute("""
            SELECT workflow, substr(created_at, 1, 13), COUNT(*), SUM(jobs_fetched)
            FROM runs WHERE created_at BETWEEN ? AND ? AND conclusion != 'skipped'
            GROUP BY 1, 2""", (lo, hi)):
        counts[(workflow, day)] = (total, fetched or 0)

    out = []
    for name, created, started, completed, kind, trigger, workflow, run_created in db.execute("""
            SELECT j.name, j.created_at, j.started_at, j.completed_at, j.runner_kind, r.trigger, r.workflow,
                   r.created_at
            FROM jobs j JOIN runs r USING (repo, run_id)
            WHERE j.created_at BETWEEN ? AND ? AND j.runner_kind IN ('github', 'namespace')
              AND (j.completed_at IS NULL OR j.completed_at >= ?)""", (lo, hi, iso(since))):
        if not created:
            continue
        key, wait_series = classify(name, kind, trigger)
        total, fetched = counts.get((workflow, run_created[:13]), (1, 1))
        out.append({
            "key": key, "kind": kind, "wait_series": wait_series,
            "weight": total / fetched if fetched else 1.0,
            "created": ts(created), "started": ts(started) if started else None,
            "completed": ts(completed) if completed else None,
            "picked_ns": kind == "namespace" and trigger == "pr" and name == "sandboxed-build",
        })

    typical = {}
    for workflow, run_s in db.execute("""
            SELECT r.workflow, j.run_s FROM jobs j JOIN runs r USING (repo, run_id)
            WHERE j.run_s IS NOT NULL AND j.runner_kind = 'github' ORDER BY r.workflow, j.run_s"""):
        typical.setdefault(workflow, []).append(run_s)
    median = {w: v[len(v) // 2] for w, v in typical.items()}
    for workflow, created, updated in db.execute("""
            SELECT workflow, created_at, updated_at FROM runs
            WHERE jobs_fetched = 0 AND conclusion != 'skipped' AND created_at BETWEEN ? AND ?
              AND updated_at >= ?""", (lo, hi, iso(since))):
        if counts.get((workflow, created[:13]), (0, 0))[1]:
            continue  # represented by the weighted sample
        c, u = ts(created), ts(updated)
        out.append({"key": "gh-other", "kind": "github", "wait_series": None, "weight": 1.0,
                    "created": c, "started": max(c, u - median.get(workflow, 15.0)), "completed": u,
                    "picked_ns": False})
    return out


def bin_series(jobs: list[dict], since: float, until: float, step: float) -> dict:
    n = int(round((until - since) / step))
    edges = [since + i * step for i in range(n + 1)]
    running = {k: [0.0] * n for k, _, _ in SERIES}
    for j in jobs:
        s, e = j["started"], j["completed"]
        if s is None or e is None or e <= since or s >= until:
            continue
        i0 = max(0, int((s - since) // step))
        i1 = min(n - 1, int((min(e, until) - since) // step))
        for i in range(i0, i1 + 1):
            overlap = min(e, edges[i + 1]) - max(s, edges[i])
            if overlap > 0:
                running[j["key"]][i] += j["weight"] * overlap / step

    # Peak (weighted) number waiting for a runner in each bin. A job waits over [created, started);
    # at equal times the start is applied before a creation, so a job starting exactly on a bin edge
    # is not counted in the bin it has already left.
    queued = {"github": [0.0] * n, "namespace": [0.0] * n}
    for kind in queued:
        events = []
        for j in jobs:
            if (j["kind"] == kind and j["wait_series"] and j["started"]
                    and j["started"] > j["created"]):
                events += [(j["created"], j["weight"]), (j["started"], -j["weight"])]
        events.sort()
        depth, k = 0.0, 0
        for i in range(n):
            while k < len(events) and (events[k][0] < edges[i] or (events[k][0] == edges[i] and events[k][1] < 0)):
                depth += events[k][1]
                k += 1
            peak = depth
            while k < len(events) and events[k][0] < edges[i + 1]:
                depth += events[k][1]
                peak = max(peak, depth)
                k += 1
            queued[kind][i] = max(peak, 0.0)

    # Longest wait among jobs that started in the trailing window: thirty minutes, or the bin if
    # that is longer, so that no job falls between samples.
    window = max(30 * 60, step)
    waits = {}
    for key, _, _ in WAIT_SERIES:
        started = sorted((j["started"], j["started"] - j["created"]) for j in jobs
                         if j["wait_series"] == key and j["started"])
        times = [t for t, _ in started]
        series = []
        for i in range(n):
            t = edges[i + 1]
            a, b = bisect.bisect_right(times, t - window), bisect.bisect_right(times, t)
            series.append(max((w for _, w in started[a:b]), default=0) / 60)
        waits[key] = series

    ticks = sorted(j["created"] for j in jobs if j["picked_ns"] and since <= j["created"] < until)
    return {"since": since, "until": until, "step": step, "window": window, "running": running,
            "queued": queued, "wait_min": waits, "picked_namespace": ticks}


# --- drawing ------------------------------------------------------------------------------------


def fmt_time(t: float, with_day: bool) -> str:
    d = dt.datetime.fromtimestamp(t, UTC)
    return d.strftime("%a %d %H:%MZ") if with_day else d.strftime("%H:%MZ")


def render(data: dict, title: str, subtitle: str, annotations: list[tuple[float, str]]) -> str:
    W, H = 980, 760
    L, R = 64, 20
    panels = [(120, 370), (430, 540), (590, 700)]   # (top, bottom) for running, queued, wait
    since, until, step = data["since"], data["until"], data["step"]
    n = len(data["running"][SERIES[0][0]])
    x = lambda t: L + (t - since) / (until - since) * (W - L - R)
    out = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" role="img">',
           f"<style>{base_css(W)}.legend{{font-size:{css_px(W, 12)};fill:{TEXT}}}"
           f".note{{font-size:{css_px(W, 11)};fill:{MUTED}}}</style>",
           card_rect(W, H),
           f'<text class="title" x="{L}" y="36">{title}</text>',
           f'<text class="subtitle" x="{L}" y="58">{html.escape(subtitle)}</text>']

    def yscale(top, bottom, vmax):
        return lambda v: bottom - (v / vmax) * (bottom - top)

    def grid(top, bottom, vmax, stepv, label):
        y = yscale(top, bottom, vmax)
        v = 0
        while v <= vmax + 1e-9:
            out.append(f'<line class="grid" x1="{L}" x2="{W-R}" y1="{y(v):.1f}" y2="{y(v):.1f}"/>')
            out.append(f'<text class="tick" x="{L-8}" y="{y(v)+4:.1f}" text-anchor="end">{v:g}</text>')
            v += stepv
        out.append(f'<text class="tick" transform="translate(16,{(top+bottom)/2:.0f}) rotate(-90)" '
                   f'text-anchor="middle">{label}</text>')
        return y

    def nice(vmax, target=5):
        for s in (1, 2, 4, 5, 10, 20, 25, 50, 100):
            if vmax / s <= target:
                return s, s * max(1, -(-vmax // s))
        return 100, 100 * (-(-vmax // 100))

    # Panel 1: stacked running jobs.
    top, bottom = panels[0]
    stacks = [0.0] * n
    layers = []
    for key, label, colour in SERIES:
        lower = stacks[:]
        stacks = [a + b for a, b in zip(stacks, data["running"][key])]
        layers.append((key, label, colour, lower, stacks[:]))
    s1, vmax1 = nice(max(max(stacks, default=0), HOSTED_CAP) * 1.1)
    y1 = grid(top, bottom, vmax1, s1, "jobs running")
    for key, label, colour, lower, upper in layers:
        if not any(u - l > 0 for u, l in zip(upper, lower)):
            continue
        pts = []
        for i in range(n):
            t0, t1 = since + i * step, since + (i + 1) * step
            pts += [(x(t0), y1(upper[i])), (x(t1), y1(upper[i]))]
        for i in reversed(range(n)):
            t0, t1 = since + i * step, since + (i + 1) * step
            pts += [(x(t1), y1(lower[i])), (x(t0), y1(lower[i]))]
        out.append(f'<polygon fill="{colour}" fill-opacity="0.85" points="'
                   + " ".join(f"{a:.1f},{b:.1f}" for a, b in pts) + '"/>')
    ycap = y1(HOSTED_CAP)
    out.append(f'<line x1="{L}" x2="{W-R}" y1="{ycap:.1f}" y2="{ycap:.1f}" stroke="{TEXT}" '
               f'stroke-dasharray="6 4" stroke-width="{svg_unit(W, 1.2)}"/>')
    out.append(f'<text class="note" x="{W-R-4}" y="{ycap-5:.1f}" text-anchor="end">'
               f'{HOSTED_CAP} concurrent GitHub-hosted jobs (free plan)</text>')
    for t in data["picked_namespace"]:
        out.append(f'<line x1="{x(t):.1f}" x2="{x(t):.1f}" y1="{bottom+4}" y2="{bottom+12}" '
                   f'stroke="{PALETTE[1]}" stroke-width="{svg_unit(W, 1.5)}"/>')
    for t, text in annotations:
        if since <= t < until:
            out.append(f'<line x1="{x(t):.1f}" x2="{x(t):.1f}" y1="{top}" y2="{bottom}" stroke="{MUTED}" '
                       f'stroke-dasharray="2 3" stroke-width="{svg_unit(W, 1)}"/>')
            right = x(t) > (L + W - R) / 2
            out.append(f'<text class="note" x="{x(t) + (-4 if right else 4):.1f}" y="{top+12}" '
                       f'text-anchor="{"end" if right else "start"}">{html.escape(text)}</text>')
    for idx, (key, label, colour) in enumerate(SERIES):
        lx, ly = L + (idx % 3) * 290, 72 + (idx // 3) * 18
        out.append(f'<rect x="{lx}" y="{ly}" width="12" height="12" rx="2" fill="{colour}"/>')
        out.append(f'<text class="legend" x="{lx+17}" y="{ly+10}">{label}</text>')
    out.append(f'<text class="note" x="{W-R}" y="{bottom+26}" text-anchor="end">'
               f'ticks: PR builds the picker sent to Namespace</text>')

    # Panel 2: peak queued.
    top, bottom = panels[1]
    qmax = max(max(data["queued"]["github"], default=0), max(data["queued"]["namespace"], default=0), 1)
    s2, vmax2 = nice(qmax * 1.1, 3)
    y2 = grid(top, bottom, vmax2, s2, "peak queued")
    bw = (W - L - R) / n
    for i in range(n):
        g, ns = data["queued"]["github"][i], data["queued"]["namespace"][i]
        t0 = x(since + i * step)
        if g:
            out.append(f'<rect x="{t0:.1f}" y="{y2(g):.1f}" width="{max(bw*0.45, 0.8):.1f}" '
                       f'height="{bottom-y2(g):.1f}" fill="{PALETTE[0]}"/>')
        if ns:
            out.append(f'<rect x="{t0+bw*0.5:.1f}" y="{y2(ns):.1f}" width="{max(bw*0.45, 0.8):.1f}" '
                       f'height="{bottom-y2(ns):.1f}" fill="{PALETTE[3]}"/>')
    out.append(f'<rect x="{L}" y="{top-18}" width="12" height="12" rx="2" fill="{PALETTE[0]}"/>'
               f'<text class="legend" x="{L+17}" y="{top-8}">waiting for GitHub</text>'
               f'<rect x="{L+180}" y="{top-18}" width="12" height="12" rx="2" fill="{PALETTE[3]}"/>'
               f'<text class="legend" x="{L+197}" y="{top-8}">waiting for Namespace</text>')

    # Panel 3: trailing max wait.
    top, bottom = panels[2]
    wmax = max(max(max(v, default=0) for v in data["wait_min"].values()), 6)
    s3, vmax3 = nice(wmax * 1.1, 3)
    y3 = grid(top, bottom, vmax3, s3, "max wait, min")
    y5 = y3(5)
    out.append(f'<line x1="{L}" x2="{W-R}" y1="{y5:.1f}" y2="{y5:.1f}" stroke="{MUTED}" '
               f'stroke-dasharray="4 4" stroke-width="{svg_unit(W, 1)}"/>'
               f'<text class="note" x="{W-R-4}" y="{y5-4:.1f}" text-anchor="end">5 min</text>')
    lx = L
    for key, label, colour in WAIT_SERIES:
        pts = []
        for i, v in enumerate(data["wait_min"][key]):
            pts += [(x(since + i * step), y3(v)), (x(since + (i + 1) * step), y3(v))]
        out.append(f'<polyline fill="none" stroke="{colour}" stroke-width="{svg_unit(W, 1.6)}" points="'
                   + " ".join(f"{a:.1f},{b:.1f}" for a, b in pts) + '"/>')
        out.append(f'<rect x="{lx}" y="{top-18}" width="12" height="12" rx="2" fill="{colour}"/>'
                   f'<text class="legend" x="{lx+17}" y="{top-8}">{label}</text>')
        lx += 130

    # Shared time axis.
    span = until - since
    tick_step = 6 * 3600 if span <= 4 * 86400 else 3 * 86400
    t = (since // tick_step + 1) * tick_step
    while t < until:
        out.append(f'<line class="grid" x1="{x(t):.1f}" x2="{x(t):.1f}" y1="{panels[0][0]}" y2="{panels[2][1]}"/>')
        midnight = dt.datetime.fromtimestamp(t, UTC).hour == 0
        out.append(f'<text class="tick" x="{x(t):.1f}" y="{panels[2][1]+18}" text-anchor="middle">'
                   f'{fmt_time(t, midnight or span > 4 * 86400)}</text>')
        t += tick_step
    for top, bottom in panels:
        out.append(f'<line class="axis" x1="{L}" x2="{W-R}" y1="{bottom}" y2="{bottom}"/>')
    out.append("</svg>")
    return "\n".join(out)


def download(dest: Path):
    with tempfile.TemporaryDirectory() as d:
        subprocess.run(["gh", "release", "download", "db", "-R", "TauCetiProject/TauCetiCI",
                        "-p", "ci.sqlite.gz", "-D", d], check=True)
        with gzip.open(Path(d) / "ci.sqlite.gz") as src, dest.open("wb") as dst:
            shutil.copyfileobj(src, dst)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--db", default="ci.sqlite")
    ap.add_argument("--download", action="store_true", help="fetch the database from TauCetiCI first")
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--until", default=None,
                    help="ISO end time, UTC (default: where the data is complete)")
    args = ap.parse_args(argv)
    dbp = Path(args.db)
    if args.download:
        download(dbp)
    db = sqlite3.connect(dbp)
    # End where every repository's runs are recorded, not at the wall clock: past that point an
    # empty bin would mean "not collected yet", and would draw as an idle fleet.
    now = dt.datetime.now(UTC).timestamp()
    covered = [ts(c) for (c,) in db.execute("SELECT complete_to FROM coverage")]
    if not covered and not args.until:
        sys.exit("the CI database records no coverage; not drawing charts that could not say where it ends")
    watermark = min(covered) if covered else now
    until = ts(args.until) if args.until else min(now, watermark)
    if not args.until and now - until > MAX_STALENESS:
        sys.exit(f"CI data is complete only to {iso(until)}, more than "
                 f"{MAX_STALENESS // 3600} hours ago; not redrawing the charts from it")
    annotations = []
    try:
        annotations = [(ts(a), text) for a, text in db.execute("SELECT at, text FROM annotations")]
    except sqlite3.OperationalError:
        pass
    out = Path(args.out_dir)
    out.mkdir(parents=True, exist_ok=True)
    stats, svgs = {}, {}
    for name, hours, step_min, title in [("72h", 72, 10, "CI fleet, last 72 hours"),
                                         ("30d", 30 * 24, 120, "CI fleet, last 30 days")]:
        until_b = until // (step_min * 60) * (step_min * 60)
        since = until_b - hours * 3600
        data = bin_series(load_jobs(db, since, until_b), since, until_b, step_min * 60)
        stats[name] = data
        subtitle = (f"{step_min}-minute bins, data through {fmt_time(until_b, True)}; "
                    "all TauCetiProject repositories")
        svgs[name] = render(data, title, subtitle, annotations)
        ET.fromstring(svgs[name])  # refuse to publish a malformed SVG
    files = {f"ci-fleet-{name}.svg": svg for name, svg in svgs.items()}
    files.update(ci_daily_graphs.charts(db, until))
    for svg in files.values():
        ET.fromstring(svg)  # refuse to publish a malformed SVG
    # Written only once every chart has rendered and parsed, so a failure leaves the fallbacks.
    for name, svg in files.items():
        (out / name).write_text(svg)
    (out / "ci-stats.json").write_text(json.dumps(stats, separators=(",", ":")))


if __name__ == "__main__":
    main()
