#!/usr/bin/env python3
"""Generate a self-contained "lines of code by date" SVG from git history.

Pure stdlib: no third-party dependencies, so CI needs no `pip install`.

For each day on which a matching commit landed, counts the total lines present
in the files matching the given pathspecs at that day's latest commit — exactly
what `wc -l` would report on a checkout. The whole series is reconstructed from
git each run, so there is no state file to keep up to date. Counting the lines
that exist (rather than summing diffs) needs no special handling for merges,
renames, or binary files.

Styled to sit on the dark navy Tau Ceti site (see web/static_files/style.css).
"""

import subprocess, sys, argparse, datetime as dt, html, math

from chart_style import base_css, card_rect


def git(repo, *args):
    return subprocess.run(["git", "-C", repo, *args],
                          capture_output=True, text=True).stdout


def count_lines(repo, commit, pathspecs):
    """Total lines in the matching files at `commit` (binary files excluded)."""
    out = git(repo, "grep", "-I", "-c", "^", commit, "--", *pathspecs)
    return sum(int(line.rsplit(":", 1)[1]) for line in out.splitlines())


def completed_days(dated, today=None):
    """Drop any day that is not over yet, in UTC.

    Takes any sequence of `(iso date, ...)` pairs and filters on the date, so it works on the
    `(day, commit)` pairs read out of git as well as on finished `(day, count)` points.

    The chart is regenerated every three hours, so the newest point was usually a few hours old
    -- a day with only part of its commits in it. On a cumulative count that does not read as
    "incomplete", it reads as "growth slowed down": the final segment rises by whatever landed
    before lunchtime and then flattens, and the same point is redrawn steeper each time the
    workflow runs. Plotting only finished days costs at most one day of latency and makes every
    segment mean the same thing.

    `today` is a parameter so tests do not depend on the clock. Days at or after it are dropped
    rather than just the last one, because a commit can carry a future committer timestamp.
    """
    if today is None:
        today = dt.datetime.now(dt.timezone.utc).date()
    return [row for row in dated if dt.date.fromisoformat(row[0]) < today]


def carry_to(points, last_day):
    """Extend the series forward to `last_day`, carrying the final count.

    The same argument as carry_quiet_days, applied to the end rather than the middle: after
    the last commit on this ref nothing about the ref changed, so the count on every later day
    is still the count at that commit. Without this the right edge sits wherever activity last
    happened, and since dropping the unfinished current day moves that edge, a chart could
    appear to stop three days earlier than it did on the previous run.

    True for any `--ref`, not only HEAD. The series describes the tree at that ref, and the
    tree at a historical ref does not change either.
    """
    if not points or dt.date.fromisoformat(points[-1][0]) >= last_day:
        return points
    return carry_quiet_days(points + [(last_day.isoformat(), points[-1][1])])


def series(repo, pathspecs, ref, today=None):
    # The last commit to land on each day that touched the files, keyed by
    # committer timestamp: that records when the code actually entered the repo,
    # whereas author dates can predate their parents. Convert the timestamp to a
    # UTC day explicitly; Git's short date otherwise uses each commit's recorded
    # timezone, which can make consecutive calendar dates decrease across timezone
    # offsets. Keying on committer time also keeps the newest point at HEAD, so the
    # "as of" label reflects the current repo. The sort is insurance against
    # history rewrites that leave committer timestamps out of order.
    #
    # --first-parent walks the mainline only, so the chart tracks the size of
    # the branch itself. Without it, a commit on a feature branch is sampled on
    # its own (earlier) date, and count_lines there sees the whole branch tree,
    # so a large branch shows up as a spike on the day it was written that
    # vanishes the next day and only truly lands when the branch merges.
    day_commit = {}
    # --reverse walks oldest-first, so the last write for a UTC day wins.
    for line in git(repo, "log", "--first-parent", "--reverse",
                    "--format=%ct %H", ref, "--", *pathspecs).splitlines():
        timestamp, commit = line.split()
        day = dt.datetime.fromtimestamp(int(timestamp), dt.timezone.utc).date().isoformat()
        day_commit[day] = commit
    if today is None:
        today = dt.datetime.now(dt.timezone.utc).date()
    # Trimmed before counting, not after: count_lines shells out to `git grep` over the whole
    # tree for each day kept, so there is no reason to price a day that will be discarded.
    kept = completed_days(sorted(day_commit.items()), today)
    points = carry_quiet_days([(date, count_lines(repo, commit, pathspecs))
                               for date, commit in kept])
    return carry_to(points, today - dt.timedelta(days=1))


def carry_quiet_days(points):
    """Fill in the days on which nothing landed, carrying the last count forward.

    A day with no matching commit is not missing data: the files were all still
    there, unchanged, and `wc -l` on that day would have returned the previous
    day's number. Sampling only commit days left those stretches as a single
    long segment with no points on it -- the line was right, but the chart said
    "no data here" where it should have said "nothing changed here", and the
    two look quite different when one of them is a three-day pause. Tau Ceti has
    two such stretches so far (2026-06-05..08 and 2026-07-12..14).

    Every date between the first and the last therefore gets a point. The ends
    are left alone: there is nothing to carry forward from before the first
    commit, and extending past the last one would invent a measurement.
    """
    filled = []
    for date, value in points:
        if filled:
            day = dt.date.fromisoformat(filled[-1][0]) + dt.timedelta(days=1)
            end = dt.date.fromisoformat(date)
            carried = filled[-1][1]
            while day < end:
                filled.append((day.isoformat(), carried))
                day += dt.timedelta(days=1)
        filled.append((date, value))
    return filled


def nice_ceil(x):
    """Round up to a 1/2/2.5/5 * 10^k value for a tidy axis top."""
    if x <= 0:
        return 1
    mag = 10 ** math.floor(math.log10(x))
    for m in (1, 2, 2.5, 5, 10):
        if x <= m * mag:
            return int(m * mag)
    return int(10 * mag)


def render(data, title, accent, out):
    W, H = 900, 460
    L, R, T, B = 72, 28, 60, 52      # margins
    pw, ph = W - L - R, H - T - B

    d0 = dt.date.fromisoformat(data[0][0])
    d1 = dt.date.fromisoformat(data[-1][0])
    span = max((d1 - d0).days, 1)
    ymax = nice_ceil(max(v for _, v in data))

    def X(d): return L + (dt.date.fromisoformat(d) - d0).days / span * pw
    def Y(v): return T + ph - v / ymax * ph

    pts = [(X(d), Y(v)) for d, v in data]
    line = " ".join(f"{x:.1f},{y:.1f}" for x, y in pts)
    area = f"{L},{T+ph} " + line + f" {L+pw},{T+ph}"

    yticks = []
    for i in range(6):
        v = ymax * i // 5
        y = Y(v)
        yticks.append(f'<line class="grid" x1="{L}" y1="{y:.1f}" x2="{L+pw}" y2="{y:.1f}"/>')
        yticks.append(f'<text class="tick ytick" x="{L-12}" y="{y+4:.1f}">{v:,}</text>')

    # x ticks: walk left to right, label only when >= 78px past the last label
    # (so runs of consecutive days don't collide); always keep first and last.
    xticks, last_x = [], -1e9
    for i, (d, _) in enumerate(data):
        x = X(d)
        forced = i == 0 or i == len(data) - 1
        if forced or x - last_x >= 78:
            if i == len(data) - 1 and xticks and x - last_x < 78:
                xticks.pop()        # drop a label that would crowd the final one
            dd = dt.date.fromisoformat(d)
            lab = f"{dd:%b} {dd.day}"   # avoid the GNU-only %-d
            xticks.append(f'<text class="tick xtick" x="{x:.1f}" y="{T+ph+24}">{lab}</text>')
            last_x = x

    dots = "".join(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="3"/>' for x, y in pts)
    latest = data[-1][1]
    grad = "g" + accent.lstrip("#")

    svg = f'''<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" role="img"
     aria-label="{html.escape(title)}: {latest:,} lines as of {data[-1][0]}">
  <defs>
    <linearGradient id="{grad}" x1="0" y1="0" x2="0" y2="1">
      <stop offset="0" stop-color="{accent}" stop-opacity="0.28"/>
      <stop offset="1" stop-color="{accent}" stop-opacity="0"/>
    </linearGradient>
  </defs>
  <style>
    {base_css(W)}
    .ytick{{text-anchor:end}}
    .xtick{{text-anchor:middle}}
    .line{{fill:none;stroke:{accent};stroke-width:2.5;stroke-linejoin:round;stroke-linecap:round}}
    circle{{fill:{accent}}}
  </style>
  {card_rect(W, H)}
  <text class="title" x="{L}" y="30">{html.escape(title)}</text>
  <text class="subtitle" x="{L}" y="48">{latest:,} lines as of {data[-1][0]}</text>
  {''.join(yticks)}
  <line class="axis" x1="{L}" y1="{T}" x2="{L}" y2="{T+ph}"/>
  <line class="axis" x1="{L}" y1="{T+ph}" x2="{L+pw}" y2="{T+ph}"/>
  <polygon points="{area}" fill="url(#{grad})"/>
  <polyline class="line" points="{line}"/>
  {dots}
  {''.join(xticks)}
</svg>
'''
    with open(out, "w") as f:
        f.write(svg)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=".")
    ap.add_argument("--ref", default="HEAD")
    ap.add_argument("--title", required=True)
    ap.add_argument("--accent", default="#ff9d4d")
    ap.add_argument("--out", required=True)
    ap.add_argument("pathspecs", nargs="+")
    a = ap.parse_args()
    data = series(a.repo, a.pathspecs, a.ref)
    if not data:
        sys.exit("no commits matched pathspecs on a day that has finished")
    render(data, a.title, a.accent, a.out)
    print(f"wrote {a.out}: {len(data)} points, latest {data[-1][1]:,}")
