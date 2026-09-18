#!/usr/bin/env python3
"""Generate the data behind the site's Progress page: where every roadmap stands.

The Statistics page measures volume (lines of Lean per roadmap, pull-request throughput). This
answers the other question, how far each roadmap is from its own specification, one row per
roadmap and one segment per layer, beside the pull requests merged under that roadmap's label.

Three classes of evidence go into the output, and the page keeps them visibly apart:

* **Layers** come from the roadmap's own `README.md`: every heading (or bold bullet) that opens
  with `Layer`, `Lane`, `Part`, `Stage`, or an `L0A`-style label. Humans wrote these and they do
  not move when code lands, so they are the unit of progress. No percentages are computed from
  them: layers are not equal in size.

* **Per-layer state** (done / partial / untouched) is a judgment about the library, and the only
  place that judgment is made is the generated `STATUS.md` that TauCetiProgress writes for a
  roadmap. Its prose cannot be aggregated, so this script reads a machine-readable companion,
  a `tauceti-coverage:v1` marker beside the `tauceti-status:v1` header, when one is present.
  Until TauCetiProgress emits that marker, `scripts/roadmap_coverage.json` carries the same
  verdicts read by hand from the prose; an entry there is keyed to the exact `to_sha` of the
  snapshot it was read from, so a newer snapshot silently retires it and the layer shows as
  unassessed rather than stale. Either way the states have the standing of the prose: a model's
  account, not security-validated, and never a kernel-checked claim.

* **Activity** is mechanical: merged pull requests carrying exactly one `roadmap/<Area>` label,
  the attribution the Statistics page already relies on. It reads the snapshot the Pages workflow
  caches for the statistics charts (`--data`), so no second walk of GitHub is needed; without one
  it pages the merged pull requests itself through `gh`.

Roadmaps under `Completed/` are done by declaration: the maintainers judged them complete against
their README, and their targets are discharged in place, so that is the one kernel-checked state
on the page.

Topics are a hand assignment (`scripts/roadmap_topics.json`) and are labelled as such.

Pure stdlib, like the other chart generators, so CI needs no pip install.
"""

from __future__ import annotations

import argparse
import collections
import datetime as dt
import json
import pathlib
import re
import subprocess
import sys

AREAS_DIR = "TauCetiRoadmap"
COMPLETED_DIR = "Completed"
AREA_PREFIX = "roadmap/"
EXCLUDE = {"roadmap/none", "roadmap/Unknown"}
WEEKS = 16
# TauCetiProgress opens a new reporting window once this many labelled PRs have merged since the
# last one, so this is the threshold at which a snapshot is genuinely behind rather than merely old.
UPDATE_DUE_PRS = 10

STATUS_MARKER = "tauceti-status:v1"
COVERAGE_MARKER = "tauceti-coverage:v1"
_MARKER_RE = re.compile(r"<!--\s*(tauceti-[a-z-]+:v\d+)\s*(\{.*?\})\s*-->", re.S)

STATES = ("done", "partial", "untouched", "unassessed")
_STATE_CHAR = {"d": "done", "p": "partial", "u": "untouched", "?": "unassessed"}

# A layer heading: `### Layer 3: ...`, `## Lane G: grid homology`, `### Part A — ...`,
# `### Stage 2: ...`, or a short label such as `### L0A — sheaves of modules` or `### S1: the
# twenty-six sporadic presentations` (a capital, digits, an optional letter, then a separator).
# The id is the label before the first separator, which is what a coverage marker refers to.
_WORD_LEAD = r"(?:Layer|Lane|Part|Stage|Milestone)\b"
_SHORT_LEAD = r"[A-Z]\d+[A-Za-z]?(?=\s*[:—–,])"
_LAYER_LEAD = rf"(?:{_WORD_LEAD}|{_SHORT_LEAD})"
_WORD_HEADING_RE = re.compile(rf"^#{{2,4}}\s+({_WORD_LEAD}.*?)\s*$", re.M)
_SHORT_HEADING_RE = re.compile(rf"^#{{2,4}}\s+({_SHORT_LEAD}.*?)\s*$", re.M)
_BULLET_RE = re.compile(rf"^- \*\*({_LAYER_LEAD}[^*]*?)\*\*", re.M)
_ID_RE = re.compile(rf"^({_LAYER_LEAD}[^:—–,(]*?)\s*(?:[:—–,(]|$)")


def layer_headings(readme: str) -> list[str]:
    """The layer titles of a roadmap, in README order, with trailing parentheticals dropped.

    Worded headings win outright: a roadmap that has `## Part A` also tends to have `### A1`
    sub-headings beneath it, and those are its milestones, not further layers. Short labels
    count only in a roadmap that names its layers that way throughout, and bold bullets only
    when there are no layer headings at all.
    """
    found = _WORD_HEADING_RE.findall(readme) or _SHORT_HEADING_RE.findall(readme) or _BULLET_RE.findall(readme)
    out = []
    for h in found:
        h = re.sub(r"\s*\([^()]*\)\s*$", "", h).strip().rstrip(".")
        if h and h not in out:
            out.append(h)
    return out


def layer_id(title: str) -> str:
    m = _ID_RE.match(title)
    return (m.group(1) if m else title).strip()


def markers(text: str) -> dict[str, dict]:
    """Every `<!--tauceti-*:vN {json}-->` marker in a generated file, by name (first wins)."""
    out = {}
    for name, body in _MARKER_RE.findall(text):
        if name not in out:
            try:
                out[name] = json.loads(body)
            except json.JSONDecodeError:
                continue
    return out


def parse_status(text: str) -> dict | None:
    """The header, at-a-glance sentence, frontier bullets and coverage marker of a STATUS.md."""
    m = markers(text)
    head = m.get(STATUS_MARKER)
    if not head or not head.get("to_sha"):
        return None
    glance = re.search(r"\*\*At a glance\.\*\*\s*(.+)", text)
    frontier_start = text.find("## The frontier")
    frontier = re.findall(r"^- \*\*(.+?)\*\*", text[frontier_start:], re.M) if frontier_start >= 0 else []
    return {
        "to_sha": head["to_sha"],
        "ts": head.get("ts"),
        "glance": glance.group(1).strip() if glance else "",
        "frontier": frontier[:5],
        "coverage": m.get(COVERAGE_MARKER),
    }


def states_from_marker(marker: dict, layers: list[str], to_sha: str) -> list[str] | None:
    """Per-layer states from a `tauceti-coverage:v1` marker, or None if it does not fit.

    It fits when it describes the same snapshot and names every layer id exactly once with a
    legal state; anything else is ignored whole rather than half-applied.
    """
    if not marker or marker.get("to_sha") != to_sha:
        return None
    by_id = {}
    for entry in marker.get("layers") or []:
        lid, state = entry.get("id"), entry.get("state")
        if lid in by_id or state not in STATES:
            return None
        by_id[lid] = state
    ids = [layer_id(t) for t in layers]
    if sorted(by_id) != sorted(ids) or len(set(ids)) != len(ids):
        return None
    return [by_id[i] for i in ids]


def states_from_transitional(entry: dict | None, layers: list[str], to_sha: str) -> list[str] | None:
    """Per-layer states from the hand-read file, valid only for the snapshot they were read from."""
    want = entry.get("to_sha") if entry else None
    if not want or len(want) < 7 or not to_sha.startswith(want):
        return None
    chars = entry.get("states", "")
    if len(chars) != len(layers) or any(c not in _STATE_CHAR for c in chars):
        return None
    return [_STATE_CHAR[c] for c in chars]


def read_roadmap(dirpath: pathlib.Path, completed: bool, transitional: dict,
                 inherit: dict | None = None) -> dict | None:
    """One roadmap row. `inherit` is a parent's parsed STATUS.md for a sub-roadmap without its
    own: TauCetiProgress reports an umbrella roadmap as one unit, so its snapshot is the only
    account of the sub-roadmaps, and hand-read states for them are keyed to its commit."""
    readme = dirpath / "README.md"
    if not readme.is_file():
        return None
    text = readme.read_text(encoding="utf-8")
    title = next((l[2:].strip() for l in text.splitlines() if l.startswith("# ")), dirpath.name)
    title = re.sub(r"^Roadmap:\s*", "", title)
    hand = transitional.get(dirpath.name) or {}
    layers = layer_headings(text) or list(hand.get("layers") or [])
    row = {
        "name": dirpath.name,
        "title": title,
        "completed": completed,
        "layers": layers,
        "layer_ids": [layer_id(t) for t in layers],
        "states": ["unassessed"] * len(layers),
        "states_source": None,
        "status": None,
        "status_inherited": False,
    }
    status_file = dirpath / "STATUS.md"
    st = parse_status(status_file.read_text(encoding="utf-8")) if status_file.is_file() else None
    if st is None and inherit:
        st = dict(inherit, coverage=None)
        row["status_inherited"] = True
    if st:
        row["status"] = {k: st[k] for k in ("to_sha", "ts", "glance", "frontier")}
        states = states_from_marker(st["coverage"], layers, st["to_sha"])
        if states:
            row["states"], row["states_source"] = states, "marker"
        else:
            states = states_from_transitional(hand, layers, st["to_sha"])
            if states:
                row["states"], row["states_source"] = states, "hand-read"
    if completed and row["states_source"] is None:
        row["states"], row["states_source"] = ["done"] * len(layers), "completed"
    return row


def read_roadmaps(roadmap_dir: pathlib.Path, transitional: dict) -> list[dict]:
    """Every roadmap, active then completed, each followed by its sub-roadmaps if it has any."""
    rows = []
    for base, completed in ((AREAS_DIR, False), (COMPLETED_DIR, True)):
        root = roadmap_dir / base
        if not root.is_dir():
            continue
        for d in sorted(p for p in root.iterdir() if p.is_dir()):
            row = read_roadmap(d, completed, transitional)
            if row is None:
                continue
            row["parent"] = None
            rows.append(row)
            # A sub-roadmap is a directory that is itself a roadmap: README plus targets. That
            # keeps a `references/` folder with a README of its own out of the board.
            for sub in sorted(p for p in d.iterdir() if p.is_dir() and (p / "Suggested.lean").is_file()):
                child = read_roadmap(sub, completed, transitional, inherit=row["status"])
                if child is None:
                    continue
                child["parent"] = d.name
                rows.append(child)
    return rows


# ---- activity -------------------------------------------------------------------------------

def load_prs(path: pathlib.Path) -> list[dict]:
    """Merged pull requests as `{number, merged_at, labels}` from any of the shapes we meet.

    Accepts the statistics snapshot (`{"prs": [{"merged_at", "labels": [name, ...]}]}`), the
    output of `gh pr list --json number,mergedAt,labels`, or the raw GraphQL nodes.
    """
    raw = json.loads(path.read_text(encoding="utf-8"))
    items = raw["prs"] if isinstance(raw, dict) else raw
    out = []
    for pr in items:
        merged = pr.get("merged_at", pr.get("mergedAt"))
        if not merged:
            continue
        labels = pr.get("labels") or []
        if isinstance(labels, dict):
            labels = labels.get("nodes") or []
        names = [l["name"] if isinstance(l, dict) else l for l in labels]
        out.append({"number": pr["number"], "merged_at": merged, "labels": names})
    return out


_PAGE_QUERY = """
query($owner:String!,$name:String!,$cursor:String){
  repository(owner:$owner,name:$name){
    pullRequests(states:MERGED,first:100,after:$cursor,orderBy:{field:UPDATED_AT,direction:DESC}){
      pageInfo{hasNextPage endCursor}
      nodes{number mergedAt labels(first:20){nodes{name}}}}}}
"""


def fetch_merged(repo: str) -> list[dict]:
    owner, name = repo.split("/", 1)
    cursor, out = None, []
    while True:
        args = ["gh", "api", "graphql", "-f", f"query={_PAGE_QUERY}", "-f", f"owner={owner}",
                "-f", f"name={name}"]
        if cursor:
            args += ["-f", f"cursor={cursor}"]
        data = json.loads(subprocess.run(args, check=True, text=True, stdout=subprocess.PIPE).stdout)
        conn = data["data"]["repository"]["pullRequests"]
        for pr in conn["nodes"]:
            out.append({"number": pr["number"], "merged_at": pr["mergedAt"],
                        "labels": [l["name"] for l in pr["labels"]["nodes"]]})
        if not conn["pageInfo"]["hasNextPage"]:
            break
        cursor = conn["pageInfo"]["endCursor"]
    return out


def area_of(pr: dict) -> str | None:
    labs = [l for l in pr["labels"] if l.startswith(AREA_PREFIX) and l not in EXCLUDE]
    return labs[0][len(AREA_PREFIX):] if len(labs) == 1 else None


def week_start(d: dt.date) -> dt.date:
    return d - dt.timedelta(days=d.weekday())


def activity(prs: list[dict], today: dt.date, weeks: int = WEEKS) -> tuple[list[str], list[int], dict]:
    """Per-area merge activity: weekly counts over the trailing window, totals, last merge."""
    week0 = week_start(today) - dt.timedelta(weeks=weeks - 1)
    labels = [(week0 + dt.timedelta(weeks=i)).isoformat() for i in range(weeks)]
    allweekly = [0] * weeks
    per = collections.defaultdict(lambda: {"weekly": [0] * weeks, "total": 0, "last30": 0, "last": None,
                                           "merged": []})
    for pr in prs:
        day = dt.date.fromisoformat(pr["merged_at"][:10])
        wi = (week_start(day) - week0).days // 7
        if 0 <= wi < weeks:
            allweekly[wi] += 1
        area = area_of(pr)
        if area is None:
            continue
        a = per[area]
        a["total"] += 1
        a["merged"].append(pr["merged_at"])
        if 0 <= wi < weeks:
            a["weekly"][wi] += 1
        if (today - day).days < 30:
            a["last30"] += 1
        if a["last"] is None or day.isoformat() > a["last"]:
            a["last"] = day.isoformat()
    return labels, allweekly, per


# ---- assembly -------------------------------------------------------------------------------

def git_head(repo_dir: pathlib.Path) -> str | None:
    try:
        return subprocess.run(["git", "-C", str(repo_dir), "rev-parse", "--short", "HEAD"],
                              check=True, text=True, stdout=subprocess.PIPE).stdout.strip()
    except (subprocess.CalledProcessError, FileNotFoundError):
        return None


def build(rows: list[dict], prs: list[dict], topics: dict, today: dt.date,
          roadmap_head: str | None, prs_source: str) -> dict:
    labels, allweekly, per = activity(prs, today)
    topic_of = topics.get("map", {})
    for row in rows:
        row["topic"] = topic_of.get(row["parent"] or row["name"], "Unsorted")
        a = per.get(row["name"]) if row["parent"] is None else None
        if a:
            since = None
            if row["status"] and row["status"]["ts"]:
                since = sum(1 for m in a["merged"] if m > row["status"]["ts"])
            row["activity"] = {"weekly": a["weekly"], "total": a["total"], "last30": a["last30"],
                               "last": a["last"], "since_snapshot": since}
        else:
            row["activity"] = None
    return {
        "schema_version": 1,
        "generated_at": today.isoformat(),
        "roadmap_head": roadmap_head,
        "prs_source": prs_source,
        "merged_total": len(prs),
        "first_merge": min((p["merged_at"][:10] for p in prs), default=None),
        "update_due_prs": UPDATE_DUE_PRS,
        "weeks": labels,
        "all_weekly": allweekly,
        "topics": topics.get("order", []),
        "rows": rows,
    }


def main(argv=None) -> int:
    here = pathlib.Path(__file__).resolve().parent
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--roadmap-dir", type=pathlib.Path, required=True,
                   help="a checkout of TauCetiRoadmap")
    p.add_argument("--repo", default="TauCetiProject/TauCeti",
                   help="repository whose merged PRs carry the roadmap labels")
    p.add_argument("--data", type=pathlib.Path,
                   help="pull-request snapshot to read instead of querying gh")
    p.add_argument("--topics", type=pathlib.Path, default=here / "roadmap_topics.json")
    p.add_argument("--coverage", type=pathlib.Path, default=here / "roadmap_coverage.json",
                   help="hand-read per-layer states, used only when no coverage marker fits")
    p.add_argument("--today", type=dt.date.fromisoformat, default=dt.date.today())
    p.add_argument("--out", type=pathlib.Path, required=True)
    args = p.parse_args(argv)

    topics = json.loads(args.topics.read_text(encoding="utf-8"))
    transitional = json.loads(args.coverage.read_text(encoding="utf-8")) if args.coverage.is_file() else {}
    rows = read_roadmaps(args.roadmap_dir, transitional)
    if not rows:
        print(f"no roadmaps found under {args.roadmap_dir}", file=sys.stderr)
        return 1
    if args.data and args.data.is_file():
        prs, source = load_prs(args.data), f"snapshot {args.data.name}"
    else:
        prs, source = fetch_merged(args.repo), "gh"
    data = build(rows, prs, topics, args.today, git_head(args.roadmap_dir), source)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(data, ensure_ascii=False, separators=(",", ":")) + "\n",
                        encoding="utf-8")
    assessed = sum(1 for r in rows if r["states_source"])
    print(f"{len(rows)} rows, {assessed} with per-layer states, {len(prs)} merged PRs ({source})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
