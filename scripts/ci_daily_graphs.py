"""Daily CI charts for the CI page, from the TauCetiCI database. Called by ci_stats_graphs.py.

Every chart is one point (or bar) per complete UTC day, up to the database's coverage watermark:

  ci-build-duration.svg   median and 90th-percentile build time, by where the build ran
  ci-build-wait.svg       median and 90th-percentile wait for a runner, by where the job ran
  ci-build-phases.svg     where a PR build's time goes, as mean minutes per build
  ci-failures.svg         failed PR builds by cause, and the share of PR builds that failed
  ci-runner-minutes.svg   runner-minutes per day on each kind of runner, and those spent on
                          builds cancelled before finishing
  ci-merge-queue.svg      merge-queue builds by outcome, and PRs landed
  ci-picker.svg           the share of PR builds that ran on GitHub-hosted runners
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

ASSET_NAMES = [
    "ci-build-duration.svg", "ci-build-wait.svg", "ci-build-phases.svg", "ci-failures.svg",
    "ci-runner-minutes.svg", "ci-merge-queue.svg", "ci-picker.svg",
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


def metrics(db: sqlite3.Connection, first: str, last: str) -> dict:
    """Per-day series for every daily chart, over complete UTC days first..last."""
    days = days_between(first, last)
    lo, hi = f"{first}T00:00:00Z", f"{last}T23:59:59Z"
    # Every attempt's build job (jobs keeps all attempts; runs only the latest), PR and merge-queue
    # builds only: manual dispatches are neither.
    builds = db.execute(f"""
        SELECT substr(j.created_at, 1, 10), r.trigger, j.runner_kind, j.conclusion, j.wait_s, j.run_s,
               j.failure_class, j.job_id, r.run_id
        FROM jobs j JOIN runs r USING (repo, run_id)
        WHERE r.repo = 'TauCeti' AND r.workflow = '{PR_BUILD}' AND j.name = '{BUILD}'
          AND r.trigger IN ('pr', 'merge_queue') AND j.runner_kind IN ('github', 'namespace')
          AND j.created_at BETWEEN ? AND ?""", (lo, hi)).fetchall()

    def where(trigger, kind):
        return "merge queue" if trigger == "merge_queue" else f"PR, {'GitHub' if kind == 'github' else 'Namespace'}"

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
    for day, wait_s in db.execute("""
            SELECT substr(j.created_at, 1, 10), j.wait_s FROM jobs j JOIN runs r USING (repo, run_id)
            WHERE j.runner_kind = 'github' AND j.name NOT IN ('sandboxed-build', 'verify', 'build')
              AND j.wait_s IS NOT NULL AND j.created_at BETWEEN ? AND ?""", (lo, hi)):
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

    # Merge-queue build jobs, every attempt.
    mq = defaultdict(lambda: defaultdict(int))
    for day, trigger, kind, concl, *_ in builds:
        if trigger == "merge_queue":
            mq[day][concl if concl in ("success", "failure", "cancelled") else "other"] += 1
    landed = defaultdict(int)
    for day, n in db.execute("""SELECT substr(committed_at, 1, 10), COUNT(*) FROM main_commits
                                WHERE pr IS NOT NULL AND committed_at BETWEEN ? AND ? GROUP BY 1""", (lo, hi)):
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


def charts(db: sqlite3.Connection, until: float) -> dict[str, str]:
    """All daily charts, through the last complete UTC day before `until`."""
    last = (dt.datetime.fromtimestamp(until, UTC) - dt.timedelta(days=1)).date()
    first_row = db.execute(f"SELECT MIN(created_at) FROM runs WHERE workflow = '{PR_BUILD}'").fetchone()[0]
    if not first_row:
        return {}
    first = max(dt.date.fromisoformat(first_row[:10]), last - dt.timedelta(days=89))
    if first > last:
        return {}
    m = metrics(db, first.isoformat(), last.isoformat())
    days = m["days"]
    span = f"UTC days {dt.date.fromisoformat(days[0]):%d %b} to {dt.date.fromisoformat(days[-1]):%d %b}"
    places = [("PR, GitHub", PALETTE[2]), ("PR, Namespace", PALETTE[1]), ("merge queue", PALETTE[3])]
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
        "The merge queue", f"Merge-queue builds by outcome (bars) and PRs landed (dashed, right scale); "
        f"{span}", days, series, "merge-queue builds",
        line=("PRs landed", TEXT, landed, max(landed + [1])))

    share = [m["picker"][d][0] / sum(m["picker"][d]) if sum(m["picker"][d]) else None for d in days]
    out["ci-picker.svg"] = lines_chart(
        "PR builds on GitHub-hosted runners", f"Share of PR builds the runner picker sent to GitHub rather "
        f"than Namespace; {span}", days, [("share on GitHub", PALETTE[2], share)], "share",
        fmt=lambda v: f"{v:.0%}")
    return out
