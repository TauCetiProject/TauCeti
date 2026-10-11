#!/usr/bin/env python3
"""Roadmap size, layer completion history, and rough work-calibrated exhaustion forecasts.

Read daily first-parent snapshots of TauCetiRoadmap, without checking them out or querying
GitHub. Specification size counts Markdown and Lean inside actual roadmap directories,
excluding generated STATUS.md / PROGRESS.md. Completed/ remains in the denominator.
Layer recognition and machine coverage validation use the Progress page's existing rules.

Completion is first observed in an archived roadmap or a coverage report. Those observation
dates are approximate; do not backdate a new report's verdicts into older snapshots. Completion
credit is measured at each observation against the library's then-current LOC, not elapsed
time. The observed units-per-added-LOC ratio is converted to units/day using the last seven
complete UTC days of library growth. New specification lines/layers over those same seven
days supply the continued-authoring scenario. These are rough extrapolations, not deadlines.
"""

from __future__ import annotations

import argparse
import bisect
import datetime as dt
import html
import json
import pathlib
import subprocess
import tempfile

import loc_graph
import roadmap_progress as progress
from chart_style import MUTED, PALETTE, base_css, card_rect, css_px

ASSET_NAMES = ("loc-roadmap.svg", "roadmap-layers.svg", "roadmap-exhaustion.svg",
               "roadmap-completion.json")


def git(repo, *args):
    return subprocess.check_output(["git", "-C", str(repo), *args], text=True)


class Trees:
    """Read each distinct blob once; repeated daily README/report versions share the cache."""

    def __init__(self, repo):
        self.repo = repo
        self.blobs = {}

    def read(self, commit):
        tree = {}
        raw = git(self.repo, "ls-tree", "-rz", commit, "--", "TauCetiRoadmap", "Completed")
        for entry in raw.split("\0"):
            if not entry:
                continue
            meta, path = entry.split("\t", 1)
            mode, kind, oid = meta.split()
            if (kind == "blob" and mode in {"100644", "100755"}
                    and pathlib.PurePosixPath(path).suffix in {".md", ".lean"}
                    and not path.endswith("/PROGRESS.md")):
                tree[path] = oid
        needed = sorted(set(tree.values()) - self.blobs.keys())
        if needed:
            proc = subprocess.run(["git", "-C", str(self.repo), "cat-file", "--batch"],
                                  input=("\n".join(needed) + "\n").encode(),
                                  stdout=subprocess.PIPE, check=True)
            offset = 0
            for oid in needed:
                end = proc.stdout.index(b"\n", offset)
                found, kind, size = proc.stdout[offset:end].decode().split()
                if found != oid or kind != "blob":
                    raise ValueError(f"could not read roadmap blob {oid}")
                offset = end + 1
                data = proc.stdout[offset:offset + int(size)]
                self.blobs[oid] = "" if b"\0" in data else data.decode("utf-8", "replace")
                offset += int(size) + 1
        return {path: self.blobs[oid] for path, oid in tree.items()}


def assessment(readme, report, name):
    """States for the current layer IDs, retaining the Progress board's stale-README flag."""
    titles = progress.layer_headings(readme)
    ids = [progress.layer_id(title) for title in titles]
    states, changed = ["unassessed"] * len(ids), False
    if report:
        marker = (report["sub_coverage"].get(name) if "/" in name else report["coverage"])
        if marker is not None:
            found, why = progress.states_from_marker(
                marker, name, titles, report["to_sha"], progress.sha256(readme))
            if why == progress.DIFFERENT_README:
                found, _ = progress.states_from_marker(
                    marker, name, titles, report["to_sha"], marker["readme_sha"])
                changed = found is not None
            if found is not None:
                states = found
    return dict(zip(ids, states)), changed


def snapshot(tree):
    """Specification units in one immutable tree; umbrella layers and child layers count once."""
    roadmaps, layers = {}, {}
    stale = 0
    for path, readme in sorted(tree.items()):
        parts = path.split("/")
        if len(parts) != 3 or parts[-1] != "README.md":
            continue
        base, area, _ = parts
        prefix = f"{base}/{area}/"
        completed = base == "Completed"
        size = sum(len(text.splitlines()) for file, text in tree.items()
                   if file.startswith(prefix)
                   and pathlib.PurePosixPath(file).name not in {"STATUS.md", "PROGRESS.md"})
        # An active successor and an archived roadmap may share a name (IntegralLattices).
        # Keep both specifications; net layer credit stays constant on an ordinary move.
        roadmaps[f"{base}/{area}"] = {"size": size, "done": completed}
        report = progress.parse_status(tree.get(prefix + "STATUS.md", ""))
        units = [(area, readme, report)]
        for child_path, child_text in sorted(tree.items()):
            child_parts = child_path.split("/")
            if (child_path.startswith(prefix) and len(child_parts) == 4
                    and child_parts[-1] == "README.md"
                    and prefix + child_parts[2] + "/Suggested.lean" in tree):
                own = progress.parse_status(tree.get(prefix + child_parts[2] + "/STATUS.md", ""))
                units.append((area + "/" + child_parts[2], child_text, own or report))
        for name, text, status in units:
            marker_name = name.rsplit("/", 1)[-1] if status and status is not report else name
            states, changed = assessment(text, status, marker_name)
            stale += int(changed and not completed)
            for layer, state in states.items():
                # Archival is the human completion decision even if an older report had gaps.
                layers[f"{base}/{name}/{layer}"] = "done" if completed else state
    return {"roadmaps": roadmaps, "layers": layers, "stale_assessments": stale}


def summarize(state):
    roadmaps, layers = state["roadmaps"], state["layers"]
    return {
        "roadmaps": len(roadmaps),
        "completed_roadmaps": sum(r["done"] for r in roadmaps.values()),
        "spec_lines": sum(r["size"] for r in roadmaps.values()),
        "completed_spec_lines": sum(r["size"] for r in roadmaps.values() if r["done"]),
        "layers": len(layers),
        "completed_layers": sum(s == "done" for s in layers.values()),
        "unassessed_layers": sum(s == "unassessed" for s in layers.values()),
        "stale_assessments": state["stale_assessments"],
    }


def history(repo, ref, today):
    day_commit = {}
    for line in git(repo, "log", "--first-parent", "--reverse", "--format=%ct %H", ref,
                    "--", "TauCetiRoadmap", "Completed").splitlines():
        timestamp, commit = line.split()
        day = dt.datetime.fromtimestamp(int(timestamp), dt.timezone.utc).date()
        if day < today:
            day_commit[day] = commit
    if not day_commit:
        raise ValueError("no roadmap history on a finished UTC day")
    trees = Trees(repo)
    rows, events = [], []
    previous = {"roadmaps": {}, "layers": {}}
    credit = {"spec_lines": 0, "layers": 0}
    # Completion credit is frozen at the size at which an area was archived: edits to an
    # archived README are authoring, not new completions. Reopening withdraws that credit.
    weights = {}
    day, last = min(day_commit), today - dt.timedelta(days=1)
    state = None
    while day <= last:
        if day in day_commit:
            state = snapshot(trees.read(day_commit[day]))
            for area, weight in list(weights.items()):
                if not state["roadmaps"].get(area, {}).get("done"):
                    credit["spec_lines"] -= weight
                    del weights[area]
                    events.append({"date": day.isoformat(), "basis": "spec_lines", "units": -weight,
                                   "id": area})
            for area, item in state["roadmaps"].items():
                if item["done"] and area not in weights:
                    weights[area] = item["size"]
                    credit["spec_lines"] += item["size"]
                    events.append({"date": day.isoformat(), "basis": "spec_lines", "units": item["size"],
                                   "id": area})
            before = {key for key, value in previous["layers"].items() if value == "done"}
            after = {key for key, value in state["layers"].items() if value == "done"}
            for key in sorted(before ^ after):
                change = 1 if key in after else -1
                credit["layers"] += change
                events.append({"date": day.isoformat(), "basis": "layers", "units": change, "id": key})
            previous = state
        rows.append({"date": day.isoformat(), **summarize(state), "completion_credit": dict(credit)})
        day += dt.timedelta(days=1)
    return rows, events


def value_at(points, day):
    """A daily cumulative measurement, carried forward, with zero before the first observation."""
    index = bisect.bisect_right([row[0] for row in points], day) - 1
    return points[index][1] if index >= 0 else 0


def scenario(backlog, capacity, authoring):
    if backlog == 0:
        return {"days": 0, "state": "exhausted"}
    if capacity is None:
        return {"days": None, "state": "insufficient-history"}
    net = capacity - authoring
    if net <= 0:
        return {"days": None, "state": "not-catching-up"}
    return {"days": backlog / net, "state": "finite"}


def forecasts(rows, events, code):
    latest = rows[-1]
    end = dt.date.fromisoformat(latest["date"])
    start = end - dt.timedelta(days=7)
    end_loc = value_at(code, end.isoformat())
    recent_loc = end_loc - value_at(code, start.isoformat())
    elapsed_loc = end_loc - value_at(code, (dt.date.fromisoformat(rows[0]["date"])
                                           - dt.timedelta(days=1)).isoformat())
    previous = next((row for row in reversed(rows) if row["date"] <= start.isoformat()), None)
    result = {"window_days": 7, "last_full_day": latest["date"],
              "library_lines": end_loc, "library_growth_lines_per_day": recent_loc / 7,
              "calibration_added_library_lines": elapsed_loc, "estimates": {}}
    for basis, total, done in (("spec_lines", "spec_lines", "completed_spec_lines"),
                               ("layers", "layers", "completed_layers")):
        completed = latest["completion_credit"][basis]
        rate = completed / elapsed_loc if completed > 0 and elapsed_loc > 0 else None
        complete_window = previous is not None and code[0][0] <= start.isoformat()
        capacity = (rate * recent_loc / 7
                    if rate is not None and recent_loc > 0 and complete_window else None)
        # Net changes to the full specification, including Completed/, ensure that archiving
        # a roadmap is not mistaken for negative authoring. Removals do not imply future shrinkage.
        authoring = max(0, latest[total] - (previous[total] if previous else 0)) / 7
        backlog = latest[total] - latest[done]
        result["estimates"][basis] = {
            "backlog": backlog, "observed_completion_units": completed,
            "completion_units_per_library_line": rate,
            "completion_units_per_day": capacity, "authoring_units_per_day": authoring,
            "stop_authoring": scenario(backlog, capacity, 0),
            "continue_authoring": scenario(backlog, capacity, authoring),
        }
    # The work coordinate at each completion is exported for alternative fits by consumers.
    for event in events:
        event["library_lines"] = value_at(code, event["date"])
    return result


def render_history(rows, total_key, done_key, unknown_key, title, unit, out):
    width, height = 980, 460
    left, top, plot_w, plot_h = 80, 100, 870, 305
    start, end = (dt.date.fromisoformat(rows[i]["date"]) for i in (0, -1))
    span = max((end - start).days, 1)
    maximum = loc_graph.nice_ceil(max(row[total_key] for row in rows))
    x = lambda day: left + (dt.date.fromisoformat(day) - start).days / span * plot_w
    y = lambda count: top + plot_h - count / maximum * plot_h
    # Step paths: completion and authoring land on an observation day, not continuously.
    def curve(key):
        points = [f"M {x(rows[0]['date']):.1f},{y(rows[0][key]):.1f}"]
        for row in rows[1:]:
            points.append(f"H {x(row['date']):.1f} V {y(row[key]):.1f}")
        return " ".join(points)
    bottom = top + plot_h
    latest = rows[-1]
    fraction = 100 * latest[done_key] / latest[total_key] if latest[total_key] else 0
    subtitle = (f"{latest[done_key]:,} / {latest[total_key]:,} {unit} completed ({fraction:.1f}%)"
                f" · through {latest['date']}")
    labels = [(PALETTE[2], "All roadmaps" if unit == "specification lines" else "All layers / lanes"),
              (PALETTE[0], "Archived in Completed/" if unit == "specification lines" else "Completed")]
    if unknown_key:
        labels.append((MUTED, f"{latest[unknown_key]:,} currently unassessed"))
    legend = "".join(f'<rect x="{left + i * 265}" y="74" width="12" height="12" rx="2" fill="{color}"/>'
                     f'<text class="tick" x="{left + i * 265 + 20}" y="85">{html.escape(label)}</text>'
                     for i, (color, label) in enumerate(labels))
    ticks = ""
    for i in range(6):
        value = maximum * i / 5
        ticks += (f'<line class="grid" x1="{left}" y1="{y(value):.1f}" x2="{left+plot_w}" y2="{y(value):.1f}"/>'
                  f'<text class="tick" text-anchor="end" x="{left-12}" y="{y(value)+4:.1f}">{value:,.0f}</text>')
    for i in range(7):
        day = start + dt.timedelta(days=round(span * i / 6))
        ticks += f'<text class="tick" text-anchor="middle" x="{x(day.isoformat()):.1f}" y="435">{day:%b %d}</text>'
    shapes = ""
    for key, color, opacity in ((total_key, PALETTE[2], 0.22), (done_key, PALETTE[0], 0.6)):
        path = curve(key)
        shapes += (f'<path d="{path} L {x(latest["date"]):.1f},{bottom} L {left},{bottom} Z" '
                   f'fill="{color}" fill-opacity="{opacity}"/>'
                   f'<path d="{path}" fill="none" stroke="{color}" stroke-width="2"/>')
    if unknown_key:
        # Shade the unknown portion at the top; it stays in the denominator and earns no credit.
        known = [{**row, "known": row[total_key] - row[unknown_key]} for row in rows]
        edge = [(x(row["date"]), y(row[total_key])) for row in rows]
        edge += [(x(row["date"]), y(row["known"])) for row in reversed(known)]
        shapes += ('<polygon points="' + " ".join(f"{a:.1f},{b:.1f}" for a, b in edge)
                   + f'" fill="{MUTED}" fill-opacity="0.25"/>')
    svg = (f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {width} {height}" role="img" '
           f'aria-label="{html.escape(title + ": " + subtitle)}"><style>{base_css(width)}</style>'
           f'{card_rect(width,height)}<text class="title" x="{left}" y="32">{html.escape(title)}</text>'
           f'<text class="subtitle" x="{left}" y="55">{html.escape(subtitle)}</text>{legend}{ticks}{shapes}</svg>\n')
    pathlib.Path(out).write_text(svg)


def duration(estimate):
    if estimate["state"] == "not-catching-up":
        return "No exhaustion at this pace"
    if estimate["state"] == "insufficient-history":
        return "Not enough growth / history"
    days = estimate["days"]
    if days == 0:
        return "No recorded backlog"
    if days < 1:
        return "Less than a day"
    if days < 60:
        return f"About {days:.0f} days"
    if days < 730:
        return f"About {days / 30.44:.0f} months"
    return f"About {days / 365.25:.1f} years"


def render_forecasts(data, out):
    width, height = 980, 350
    svg = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {width} {height}" role="img" '
           'aria-label="Rough time to roadmap exhaustion, with and without continued authoring">',
           f'<style>{base_css(width)}.estimate{{font-size:{css_px(width,18)};font-weight:600}}'
           f'.forecast{{fill:{PALETTE[0]}}}</style>',
           card_rect(width, height),
           '<text class="title" x="35" y="35">Rough time to exhaustion</text>',
           f'<text class="subtitle" x="35" y="60">Recent pace: {data["library_growth_lines_per_day"]:,.0f} added Lean lines/day · seven days through {data["last_full_day"]}</text>',
           '<text class="subtitle" x="325" y="100">Stop roadmap authoring</text>',
           '<text class="subtitle" x="625" y="100">Continue seven-day authoring pace</text>']
    for i, (basis, label, unit) in enumerate((("spec_lines", "Roadmap size", "specification lines"),
                                             ("layers", "Layers / lanes", "layers"))):
        estimate = data["estimates"][basis]
        top = 142 + 90 * i
        svg += [f'<text class="estimate" x="35" y="{top}">{label}</text>',
                f'<text class="subtitle" x="35" y="{top+24}">{estimate["backlog"]:,} {unit} remaining</text>']
        for scenario_name, pos in (("stop_authoring", 325), ("continue_authoring", 625)):
            svg.append(f'<text class="estimate forecast" x="{pos}" y="{top}">{duration(estimate[scenario_name])}</text>')
        capacity = estimate["completion_units_per_day"]
        rate = f"{capacity:,.1f}" if capacity is not None else "unknown"
        svg.append(f'<text class="subtitle" x="325" y="{top+24}">Inferred completion: {rate}/day · authoring: {estimate["authoring_units_per_day"]:,.1f}/day</text>')
    svg.append('<text class="subtitle" x="35" y="315">Completions per added Lean line over recorded history × recent Lean growth. Unequal goals; approximate dates.</text></svg>\n')
    pathlib.Path(out).write_text("".join(svg))


def generate(roadmap_repo, roadmap_ref, code_repo, code_ref, out_dir, today=None, code_data=None):
    # A cached LOC series fixes the common cutoff, including if generation crosses midnight.
    if today is None:
        today = (dt.date.fromisoformat(code_data[-1][0]) + dt.timedelta(days=1)
                 if code_data else dt.datetime.now(dt.timezone.utc).date())
    for repo in (roadmap_repo, code_repo):
        if git(repo, "rev-parse", "--is-shallow-repository").strip() == "true":
            raise ValueError(f"full git history is required for completion forecasts: {repo}")
    roadmap_ref = git(roadmap_repo, "rev-parse", roadmap_ref).strip()
    code_ref = git(code_repo, "rev-parse", code_ref).strip()
    rows, events = history(roadmap_repo, roadmap_ref, today)
    code = code_data if code_data is not None else loc_graph.series(
        str(code_repo), ["TauCeti", "TauCeti.lean"], code_ref, today)
    if not code or code[-1][0] != rows[-1]["date"]:
        raise ValueError("library LOC data must extend through the last complete UTC day")
    forecast = forecasts(rows, events, code)
    payload = {"schema_version": 1, "roadmap_commit": roadmap_ref, "library_commit": code_ref,
               "last_full_day": rows[-1]["date"], "history": rows, "completion_events": events,
               "forecast": forecast,
               "definitions": {
                   "spec_lines": "Markdown and Lean within roadmap directories, including reference notes and Completed/, excluding generated STATUS.md and PROGRESS.md.",
                   "completed_roadmap": "A roadmap under Completed/, the maintainers' archival decision.",
                   "completed_layer": "A current layer recorded done by a machine coverage marker, or belonging to an archived roadmap. Partial/unassessed earn zero credit; transitional hand-read assessments are not replayed.",
                   "observation_date": "First observed in the last first-parent commit of a complete UTC day; reporting and archival may lag implementation.",
                   "completion_events": "Signed changes in recorded completion credit; archival can emit offsetting negative active-layer and positive archived-layer entries, with no net new completion.",
                   "calibration": "Net observed completions (roadmap size frozen at archival) divided by added library LOC over the recorded roadmap history.",
                   "authoring": "Nonnegative net increase in all specification lines or layers over seven complete UTC days, divided by seven.",
               }}
    out_dir = pathlib.Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    # Write a coherent set only after every calculation/render succeeds, preserving fallbacks
    # on git, data or rendering errors. Each individual replacement is atomic.
    with tempfile.TemporaryDirectory(dir=out_dir) as temp:
        staging = pathlib.Path(temp)
        render_history(rows, "spec_lines", "completed_spec_lines", None,
                       "Tau Ceti Roadmap — specification size", "specification lines", staging / "loc-roadmap.svg")
        render_history(rows, "layers", "completed_layers", "unassessed_layers",
                       "Roadmap layers / lanes — completion", "layers / lanes", staging / "roadmap-layers.svg")
        render_forecasts(forecast, staging / "roadmap-exhaustion.svg")
        (staging / "roadmap-completion.json").write_text(json.dumps(payload, indent=2, allow_nan=False) + "\n")
        for name in ASSET_NAMES:
            (staging / name).replace(out_dir / name)
    return payload


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--roadmap-repo", required=True, type=pathlib.Path)
    parser.add_argument("--roadmap-ref", default="HEAD")
    parser.add_argument("--code-repo", default=".", type=pathlib.Path)
    parser.add_argument("--code-ref", default="HEAD")
    parser.add_argument("--code-data", type=pathlib.Path, help="daily LOC pairs from loc_graph.py --dump-data")
    parser.add_argument("--today", type=dt.date.fromisoformat, help="UTC cutoff for reproducible offline rendering")
    parser.add_argument("--out-dir", required=True, type=pathlib.Path)
    args = parser.parse_args()
    code = json.loads(args.code_data.read_text()) if args.code_data else None
    data = generate(args.roadmap_repo, args.roadmap_ref, args.code_repo, args.code_ref,
                    args.out_dir, args.today, code)
    latest = data["history"][-1]
    print(f"wrote roadmap completion: {latest['completed_roadmaps']}/{latest['roadmaps']} archived roadmaps, "
          f"{latest['completed_layers']}/{latest['layers']} completed layers, through {latest['date']}")


if __name__ == "__main__":
    main()
