#!/usr/bin/env python3
"""Generate the data behind the site's Progress page: where every roadmap stands.

The Statistics page measures volume (lines of Lean per roadmap, pull-request throughput). This
answers the other question, how far each roadmap has got against its own specification: one row
per roadmap, one segment per layer, beside the pull requests merged under that roadmap's label.
The board describes coverage of the roadmaps that exist, not how much of mathematics is
formalized; there is no inventory of mathematics here to measure against.

Three kinds of evidence go into the output, and the page keeps them apart:

* **Layers** come from the roadmap's own `README.md`: every heading (or bold bullet) that opens
  with `Layer`, `Lane`, `Part`, `Stage`, or a short label such as `L0A` or `S1`. Humans wrote
  these and they do not move when code lands, so they are the unit of progress. Nothing here turns
  them into a percentage: layers are not equal in size, and a partial layer is not half done.

* **Per-layer state** (done / partial / untouched / unassessed) is an assessment of the library at
  a particular revision, and the only place that assessment is made is the generated `STATUS.md`
  that TauCetiProgress writes for a roadmap. Its prose cannot be aggregated, so this script reads
  a machine-readable companion, a `tauceti-coverage:v1` marker beside the `tauceti-status:v1`
  header, when one is present and fits; each layer entry may also carry a one-line `remaining`
  note, what the next contributor would pick up. Until TauCetiProgress emits that marker,
  `scripts/roadmap_coverage.json` carries the same verdicts transcribed by hand from the prose.
  A transcription is bound to the exact report it was read from (its library commit and a hash of
  the report's text), to the exact specification it was read against (a hash of the README), and
  to the exact layer ids it names; a rewritten report, an edited README or a re-layered one
  retires it, each with its own reason, rather than letting old states attach to new
  requirements. The states have the standing of the prose: a model's account of the library, not
  a certificate that a layer's whole specification is met, and not something Lean checks.

* **Activity** is mechanical: merged (and, separately, open) pull requests carrying exactly one
  `roadmap/<Area>` label,
  the attribution the Statistics page already relies on. Pull requests with no roadmap label, or
  more than one, are counted in the global figures and reported as unattributed rather than
  assigned to a row. It reads the snapshot the Pages workflow caches for the statistics charts
  (`--data`), so no second walk of GitHub is needed; without one it pages the merged pull
  requests itself through `gh`. Three times are kept apart: when the pull requests were fetched
  (`collected_at`, unknown for a snapshot that does not say), the cutoff up to which they count
  (`cutoff`, which is what "in the last 30 days" is measured from), and when this file was
  written (`exported_at`).

A roadmap under `Completed/` is one the maintainers declared complete against its README. That is
a human decision, recorded separately from any layer assessment; the two are shown side by side
and neither is inferred from the other.

Topics are a hand assignment (`scripts/roadmap_topics.json`) and are labelled as such, and
`scripts/roadmap_links.json` lists per-roadmap pages elsewhere (a contributor's route map, say)
that a row should point at.

Pure stdlib, like the other chart generators, so CI needs no pip install.
"""

from __future__ import annotations

import argparse
import collections
import datetime as dt
import hashlib
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
RECENT_DAYS = 30
# TauCetiProgress opens a new reporting window once this many labelled PRs have merged since the
# last one, so this is the threshold at which a report is behind by its own rule. It is a
# heuristic about when a new report is due, not a claim that nothing changed below it.
UPDATE_DUE_PRS = 10

STATUS_MARKER = "tauceti-status:v1"
COVERAGE_MARKER = "tauceti-coverage:v1"
_MARKER_RE = re.compile(r"<!--\s*(tauceti-[a-z-]+:v\d+)\s*(\{.*?\})\s*-->", re.S)
MALFORMED = "malformed"  # a marker that is present but whose JSON does not parse

STATES = ("done", "partial", "untouched", "unassessed")
_STATE_CHAR = {"d": "done", "p": "partial", "u": "untouched", "?": "unassessed"}

# Why a row's layers carry the states they do. `ok` means an assessment applied; every other
# reason leaves the layers unassessed and says which kind of gap that is.
REASONS = ("ok", "no-layers", "no-report", "not-transcribed", "transcription-retired",
           "specification-changed", "invalid-marker")

# A layer heading: `### Layer 3: ...`, `## Lane G: grid homology`, `### Part A — ...`,
# `### Stage 2: ...`, or a short label such as `### L0A — sheaves of modules` or `### S1: the
# twenty-six sporadic presentations` (a capital, digits, an optional letter, then a separator).
# The id is the label before the first separator, which is what an assessment refers to.
_WORD_LEAD = r"(?:Layer|Lane|Part|Stage|Milestone)\b"
_SHORT_LEAD = r"[A-Z]\d+[A-Za-z]?(?=\s*[:—–,])"
_LAYER_LEAD = rf"(?:{_WORD_LEAD}|{_SHORT_LEAD})"
_WORD_HEADING_RE = re.compile(rf"^#{{2,4}}\s+({_WORD_LEAD}.*?)\s*$", re.M)
_SHORT_HEADING_RE = re.compile(rf"^#{{2,4}}\s+({_SHORT_LEAD}.*?)\s*$", re.M)
_BULLET_RE = re.compile(rf"^- \*\*({_LAYER_LEAD}[^*]*?)\*\*", re.M)
_ID_RE = re.compile(rf"^({_LAYER_LEAD}[^:—–,(]*?)\s*(?:[:—–,(]|$)")


def sha256(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def layer_headings_with_lines(readme: str) -> list[tuple[str, int]]:
    """The layer titles of a roadmap with their 1-based line numbers, in README order, trailing
    parentheticals dropped.

    Worded headings win outright: a roadmap that has `## Part A` also tends to have `### A1`
    sub-headings beneath it, and those are its milestones, not further layers. Short labels
    count only in a roadmap that names its layers that way throughout, and bold bullets only
    when there are no layer headings at all.
    """
    def scan(rx):
        return [(m.group(1), readme.count("\n", 0, m.start()) + 1) for m in rx.finditer(readme)]
    found = scan(_WORD_HEADING_RE) or scan(_SHORT_HEADING_RE) or scan(_BULLET_RE)
    out, seen = [], set()
    for h, line in found:
        h = re.sub(r"\s*\([^()]*\)\s*$", "", h).strip().rstrip(".")
        if h and h not in seen:
            seen.add(h)
            out.append((h, line))
    return out


def layer_headings(readme: str) -> list[str]:
    """The layer titles alone; see `layer_headings_with_lines`."""
    return [h for h, _ in layer_headings_with_lines(readme)]


def layer_id(title: str) -> str:
    m = _ID_RE.match(title)
    return (m.group(1) if m else title).strip()


def markers(text: str) -> dict:
    """Every `<!--tauceti-*:vN {json}-->` marker in a generated file, by name (first wins).

    A marker whose JSON does not parse is recorded as `MALFORMED` rather than dropped, so a
    present-but-broken marker is reported as such instead of looking absent.
    """
    out = {}
    for name, body in _MARKER_RE.findall(text):
        if name in out:
            continue
        try:
            out[name] = json.loads(body)
        except json.JSONDecodeError:
            out[name] = MALFORMED
    return out


def _paragraph_after(text: str, label: str) -> str:
    """The Markdown paragraph that follows `label`, soft-wrapped lines joined with spaces.

    Stops at a blank line, a heading, a list item or a marker, so a wrapped "At a glance"
    paragraph comes back whole and the frontier that follows it is never swallowed.
    """
    i = text.find(label)
    if i < 0:
        return ""
    rest = text[i + len(label):]
    lines = []
    for line in rest.splitlines():
        s = line.strip()
        if not lines and not s:
            continue  # the label may sit on a line of its own
        if not s or s.startswith("#") or s.startswith("- ") or s.startswith("<!--"):
            break
        lines.append(s)
    return " ".join(lines).strip()


def _frontier(text: str) -> list[dict]:
    """The frontier bullets, each as its bold target name and the rest of the bullet's text."""
    i = text.find("## The frontier")
    if i < 0:
        return []
    items, current = [], None
    for line in text[i:].splitlines()[1:]:
        s = line.rstrip()
        if s.startswith("## "):
            break
        m = re.match(r"^- \*\*(.+?)\*\*\s*(.*)$", s)
        if m:
            current = {"name": m.group(1).strip(), "text": m.group(2).strip()}
            items.append(current)
        elif current is not None and s.strip() and not s.startswith("- "):
            current["text"] = (current["text"] + " " + s.strip()).strip()
        elif not s.strip():
            current = None
    return items[:5]


_TS_RE = re.compile(r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:Z|[+-]\d{2}:\d{2})$")


def parse_ts(value) -> dt.datetime | None:
    """An ISO-8601 timestamp with an explicit zone, as an aware UTC datetime, or None."""
    if not isinstance(value, str) or not _TS_RE.match(value):
        return None
    try:
        return dt.datetime.fromisoformat(value.replace("Z", "+00:00")).astimezone(dt.timezone.utc)
    except ValueError:
        return None


def iso_z(when: dt.datetime) -> str:
    return when.astimezone(dt.timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def parse_status(text: str) -> dict | None:
    """The header, at-a-glance paragraph, frontier and coverage marker of a STATUS.md."""
    m = markers(text)
    head = m.get(STATUS_MARKER)
    if not isinstance(head, dict) or not isinstance(head.get("to_sha"), str) or not head["to_sha"]:
        return None
    ts = head.get("ts")
    return {
        "to_sha": head["to_sha"],
        "ts": iso_z(parse_ts(ts)) if parse_ts(ts) else None,
        "roadmap": head.get("roadmap") if isinstance(head.get("roadmap"), str) else None,
        "glance": _paragraph_after(text, "**At a glance.**"),
        "frontier": _frontier(text),
        "report_sha": sha256(text),
        "coverage": m.get(COVERAGE_MARKER),
    }


def _check_ids(by_id: dict, ids: list[str]) -> str | None:
    """Why a mapping of layer id to state does not fit the layer ids, or None if it does."""
    if len(set(ids)) != len(ids):
        return "the README's layer ids are not unique"
    missing = [i for i in ids if i not in by_id]
    extra = [i for i in by_id if i not in ids]
    if missing or extra:
        return ("layer ids differ from the README" + (f"; missing {missing}" if missing else "")
                + (f"; unknown {extra}" if extra else ""))
    bad = [i for i, s in by_id.items() if s not in STATES]
    if bad:
        return f"illegal state for {bad}"
    return None


def states_from_marker(marker, name: str, layers: list[str], to_sha: str) -> tuple[list[str] | None, str | None]:
    """Per-layer states from a `tauceti-coverage:v1` marker, or (None, reason).

    It fits when it names this roadmap and this snapshot and lists every layer id exactly once
    with a legal state; anything else is refused whole, with a reason, rather than half-applied.
    The marker's shape is TauCetiProgress's contract and is read as it is; specification identity
    is recorded beside it (`readme_sha` on the row), not written into it. An entry's optional
    string `remaining` is read by `remaining_from_marker`.
    """
    if marker == MALFORMED:
        return None, "marker JSON does not parse"
    if not isinstance(marker, dict):
        return None, "marker is not an object"
    if marker.get("roadmap") != name:
        return None, f"marker names roadmap {marker.get('roadmap')!r}, not {name!r}"
    if marker.get("to_sha") != to_sha:
        return None, "marker describes a different library commit than the status header"
    entries = marker.get("layers")
    if not isinstance(entries, list):
        return None, "marker has no layer list"
    by_id = {}
    for entry in entries:
        if not isinstance(entry, dict) or not isinstance(entry.get("id"), str) or not isinstance(entry.get("state"), str):
            return None, "marker layer entries must be objects with string id and state"
        if entry["id"] in by_id:
            return None, f"duplicate layer id {entry['id']!r}"
        by_id[entry["id"]] = entry["state"]
    ids = [layer_id(t) for t in layers]
    problem = _check_ids(by_id, ids)
    if problem:
        return None, problem
    return [by_id[i] for i in ids], None


def remaining_notes(entries, ids: list[str]) -> dict:
    """`{layer id: note}` from a marker's layer list or a transcription's `remaining` map: only
    string notes for known ids, everything else ignored."""
    if isinstance(entries, list):
        entries = {e.get("id"): e.get("remaining") for e in entries if isinstance(e, dict)}
    if not isinstance(entries, dict):
        return {}
    return {k: v.strip() for k, v in entries.items() if k in ids and isinstance(v, str) and v.strip()}


def _prefix_ok(want, full: str, minimum: int) -> bool:
    return isinstance(want, str) and len(want) >= minimum and full.startswith(want)


def _layer_map(raw, ids: list[str]) -> dict | None:
    """A validated `{layer id: state}` from a transcription's `layers`, or None."""
    if not isinstance(raw, dict) or not all(isinstance(k, str) and isinstance(v, str) for k, v in raw.items()):
        return None
    by_id = {k: _STATE_CHAR.get(v, v) for k, v in raw.items()}
    return None if _check_ids(by_id, ids) else by_id


def states_from_transitional(entry, layers: list[str], to_sha: str, report_sha: str,
                             readme_sha: str) -> tuple[list[str] | None, str | None]:
    """Per-layer states from the hand-transcribed file, or (None, reason).

    An entry is `{"to_sha", "report_sha", "readme_sha", "layers": {id: char}}` and applies only
    to the exact report it was transcribed from (library commit and report hash), the exact
    README it was read against, and the exact layer ids it names. Prefixes are accepted: seven
    characters of a commit, twelve of a content hash.
    """
    if not isinstance(entry, dict):
        return None, "not-transcribed"
    if not _prefix_ok(entry.get("to_sha"), to_sha, 7) or not _prefix_ok(entry.get("report_sha"), report_sha, 12):
        return None, "transcription-retired"
    if not _prefix_ok(entry.get("readme_sha"), readme_sha, 12):
        return None, "specification-changed"
    ids = [layer_id(t) for t in layers]
    by_id = _layer_map(entry.get("layers"), ids)
    if by_id is None:
        return None, "specification-changed"
    return [by_id[i] for i in ids], None


def read_roadmap(dirpath: pathlib.Path, base: str, transitional: dict, parent: str | None = None,
                 inherit: dict | None = None, links: dict | None = None) -> dict | None:
    """One roadmap row. `inherit` is a parent's parsed STATUS.md for a sub-roadmap without its
    own: TauCetiProgress reports an umbrella roadmap as one unit, so its report is the only
    account of the sub-roadmaps, and hand transcriptions for them are bound to that report."""
    readme = dirpath / "README.md"
    if not readme.is_file():
        return None
    text = readme.read_text(encoding="utf-8")
    title = next((l[2:].strip() for l in text.splitlines() if l.startswith("# ")), dirpath.name)
    title = re.sub(r"^Roadmap:\s*", "", title)
    name = dirpath.name
    parent_id = f"{base}/{parent}" if parent else None
    rel = f"{parent_id}/{name}" if parent else f"{base}/{name}"
    hand = transitional.get(rel)
    with_lines = layer_headings_with_lines(text)
    layers = [h for h, _ in with_lines]
    row = {
        "id": rel,
        "name": name,
        "title": title,
        "parent": parent,
        "parent_id": parent_id,
        "completed": base == COMPLETED_DIR,
        "readme": f"{rel}/README.md",
        "readme_sha": sha256(text),
        "layers": layers,
        "layer_ids": [layer_id(t) for t in layers],
        "layer_lines": [line for _, line in with_lines],
        "states": ["unassessed"] * len(layers),
        "assessment": {"source": None, "reason": "no-layers" if not layers else "no-report", "detail": None,
                       "notes": {}, "remaining": {}},
        "links": [l for l in ((links or {}).get(rel) or []) if isinstance(l, dict)
                  and isinstance(l.get("label"), str) and isinstance(l.get("url"), str)
                  and l["url"].startswith("https://")],
        "status": None,
        "retired": None,
    }
    status_file = dirpath / "STATUS.md"
    st = parse_status(status_file.read_text(encoding="utf-8")) if status_file.is_file() else None
    inherited = False
    if st is None and inherit:
        st, inherited = inherit, True
    if st:
        row["status"] = {
            "to_sha": st["to_sha"], "ts": st["ts"], "glance": st["glance"], "frontier": st["frontier"],
            "report_sha": st["report_sha"], "inherited": inherited,
            "path": f"{parent_id}/STATUS.md" if inherited else f"{rel}/STATUS.md",
            "progress_path": f"{parent_id}/PROGRESS.md" if inherited else f"{rel}/PROGRESS.md",
        }
    if not layers or not st:
        return row
    a = row["assessment"]
    if st["coverage"] is not None and not inherited:
        states, why = states_from_marker(st["coverage"], name, layers, st["to_sha"])
        if states:
            row["states"], a["source"], a["reason"] = states, "marker", "ok"
            a["remaining"] = remaining_notes(st["coverage"].get("layers"), row["layer_ids"])
        else:
            a["reason"], a["detail"] = "invalid-marker", why
        return row
    states, why = states_from_transitional(hand, layers, st["to_sha"], st["report_sha"], row["readme_sha"])
    if states:
        row["states"], a["source"], a["reason"] = states, "hand-read", "ok"
        notes = hand.get("notes")
        a["notes"] = {k: v for k, v in notes.items() if k in row["layer_ids"] and isinstance(v, str)} if isinstance(notes, dict) else {}
        a["remaining"] = remaining_notes(hand.get("remaining"), row["layer_ids"])
        return row
    a["reason"] = why
    if why == "transcription-retired":
        a["detail"] = "the report changed after the transcription was made"
    elif why == "specification-changed":
        a["detail"] = "the README changed after the transcription was made"
    if why in ("transcription-retired", "specification-changed"):
        # Keep the retired reading, dated, for the detail panel, but only if its shape is sound;
        # a malformed old entry is left out with a diagnostic rather than aborting the build.
        old = _layer_map(hand.get("layers"), row["layer_ids"])
        if old is not None:
            row["retired"] = {"to_sha": hand.get("to_sha") if isinstance(hand.get("to_sha"), str) else None,
                              "states": [old[i] for i in row["layer_ids"]]}
        else:
            a["detail"] += "; the old transcription is malformed and was not kept"
    return row


def read_roadmaps(roadmap_dir: pathlib.Path, transitional: dict, links: dict | None = None) -> list[dict]:
    """Every roadmap, active then completed, each followed by its sub-roadmaps if it has any."""
    rows = []
    for base in (AREAS_DIR, COMPLETED_DIR):
        root = roadmap_dir / base
        if not root.is_dir():
            continue
        for d in sorted(p for p in root.iterdir() if p.is_dir()):
            row = read_roadmap(d, base, transitional, links=links)
            if row is None:
                continue
            rows.append(row)
            parent_status = None
            if row["status"]:
                parent_status = parse_status((d / "STATUS.md").read_text(encoding="utf-8"))
            # A sub-roadmap is a directory that is itself a roadmap: README plus targets. That
            # keeps a `references/` folder with a README of its own out of the board.
            for sub in sorted(p for p in d.iterdir() if p.is_dir() and (p / "Suggested.lean").is_file()):
                child = read_roadmap(sub, base, transitional, parent=d.name, inherit=parent_status, links=links)
                if child is not None:
                    rows.append(child)
    return rows


# ---- activity -------------------------------------------------------------------------------

def _normalize(items) -> list[dict]:
    """`{number, merged_at, open, labels}` records, one per pull request, from any shape we meet.

    A pull request is merged when it has a merge time and open when its state says so (or it has
    neither a merge nor a close time); closed-unmerged ones are kept out, since nothing here
    counts them.
    """
    out, seen = [], set()
    for pr in items:
        number = pr.get("number")
        if not isinstance(number, int) or number in seen:
            continue
        merged = parse_ts(pr.get("merged_at", pr.get("mergedAt")))
        state = str(pr.get("state") or "").upper()
        is_open = merged is None and (state == "OPEN" or (not state and not pr.get("closed_at", pr.get("closedAt"))))
        if merged is None and not is_open:
            continue
        seen.add(number)
        labels = pr.get("labels") or []
        if isinstance(labels, dict):
            labels = labels.get("nodes") or []
        names = [l["name"] if isinstance(l, dict) else l for l in labels]
        out.append({"number": number, "merged_at": iso_z(merged) if merged else None, "open": is_open,
                    "labels": [n for n in names if isinstance(n, str)]})
    return out


def load_prs(path: pathlib.Path) -> tuple[list[dict], str | None]:
    """Merged pull requests and, when the snapshot records it, when they were fetched.

    Accepts the statistics snapshot (`{"fetched_at", "prs": [{"merged_at", "labels": [...]}]}`),
    the output of `gh pr list --json number,mergedAt,labels`, or the raw GraphQL nodes. A bare
    list carries no collection time, and none is invented for it.
    """
    raw = json.loads(path.read_text(encoding="utf-8"))
    if isinstance(raw, dict):
        fetched = parse_ts(raw.get("fetched_at"))
        return _normalize(raw.get("prs") or []), iso_z(fetched) if fetched else None
    return _normalize(raw), None


_PAGE_QUERY = """
query($owner:String!,$name:String!,$states:[PullRequestState!],$cursor:String){
  repository(owner:$owner,name:$name){
    pullRequests(states:$states,first:100,after:$cursor,orderBy:{field:UPDATED_AT,direction:DESC}){
      pageInfo{hasNextPage endCursor}
      nodes{number state mergedAt closedAt labels(first:20){nodes{name}}}}}}
"""


def fetch_prs(repo: str) -> list[dict]:
    """Every merged and every open pull request, with labels, through `gh`."""
    owner, name = repo.split("/", 1)
    raw = []
    for states in ("MERGED", "OPEN"):
        cursor = None
        while True:
            args = ["gh", "api", "graphql", "-f", f"query={_PAGE_QUERY}", "-f", f"owner={owner}",
                    "-f", f"name={name}", "-f", f"states={states}"]
            if cursor:
                args += ["-f", f"cursor={cursor}"]
            data = json.loads(subprocess.run(args, check=True, text=True, stdout=subprocess.PIPE).stdout)
            conn = data["data"]["repository"]["pullRequests"]
            raw.extend(conn["nodes"])
            if not conn["pageInfo"]["hasNextPage"]:
                break
            cursor = conn["pageInfo"]["endCursor"]
    return _normalize(raw)


def area_of(pr: dict) -> str | None:
    """The one roadmap a pull request advances, or None when it has no label or several."""
    labs = [l for l in pr["labels"] if l.startswith(AREA_PREFIX) and l not in EXCLUDE]
    return labs[0][len(AREA_PREFIX):] if len(labs) == 1 else None


def week_start(d: dt.date) -> dt.date:
    return d - dt.timedelta(days=d.weekday())


def activity(prs: list[dict], cutoff: dt.datetime, weeks: int = WEEKS, known: set[str] | None = None):
    """Per-area merge activity plus the global series and the attribution accounting.

    Only pull requests merged at or before `cutoff` count; "recent" means within `RECENT_DAYS`
    before the cutoff; weekly bins are UTC weeks starting Monday, the last containing the cutoff.
    Open pull requests are counted as they stand in the snapshot, per area and in total.
    Returns `(week_labels, global, per_area)`. `global` holds the weekly counts, the recent count
    and the total over the same population, and how many pull requests were left unattributed
    and why; a pull request is never assigned to a row by guesswork.
    """
    cutoff = cutoff.astimezone(dt.timezone.utc)
    today = cutoff.date()
    recent_from = cutoff - dt.timedelta(days=RECENT_DAYS)
    week0 = week_start(today) - dt.timedelta(weeks=weeks - 1)
    labels = [(week0 + dt.timedelta(weeks=i)).isoformat() for i in range(weeks)]
    glob = {"weekly": [0] * weeks, "recent": 0, "total": 0, "open": 0,
            "unattributed": {"no_label": 0, "several_labels": 0, "unknown_area": 0}}
    per = collections.defaultdict(lambda: {"weekly": [0] * weeks, "total": 0, "recent": 0, "last": None,
                                           "open": 0, "merged": []})
    for pr in prs:
        if pr.get("open"):
            glob["open"] += 1
            area = area_of(pr)
            if area is not None and (known is None or area in known):
                per[area]["open"] += 1
            continue
        when = parse_ts(pr["merged_at"])
        if when is None or when > cutoff:
            continue
        wi = (week_start(when.date()) - week0).days // 7
        recent = when > recent_from
        glob["total"] += 1
        if 0 <= wi < weeks:
            glob["weekly"][wi] += 1
        if recent:
            glob["recent"] += 1
        area = area_of(pr)
        if area is None:
            n = len([l for l in pr["labels"] if l.startswith(AREA_PREFIX) and l not in EXCLUDE])
            glob["unattributed"]["several_labels" if n > 1 else "no_label"] += 1
            continue
        if known is not None and area not in known:
            glob["unattributed"]["unknown_area"] += 1
            continue
        a = per[area]
        a["total"] += 1
        a["merged"].append(pr["merged_at"])
        if 0 <= wi < weeks:
            a["weekly"][wi] += 1
        if recent:
            a["recent"] += 1
        if a["last"] is None or pr["merged_at"] > a["last"]:
            a["last"] = pr["merged_at"]
    return labels, glob, per


# ---- assembly -------------------------------------------------------------------------------

def git_head(repo_dir: pathlib.Path) -> str | None:
    try:
        return subprocess.run(["git", "-C", str(repo_dir), "rev-parse", "HEAD"],
                              check=True, text=True, stdout=subprocess.PIPE).stdout.strip()
    except (subprocess.CalledProcessError, FileNotFoundError):
        return None


def build(rows: list[dict], prs: list[dict], topics: dict, exported_at: dt.datetime,
          cutoff: dt.datetime, collected_at: str | None, roadmap_head: str | None, prs_source: str) -> dict:
    labels, glob, per = activity(prs, cutoff, known={r["name"] for r in rows if r["parent"] is None})
    topic_of = topics.get("map", {})
    for row in rows:
        row["topic"] = topic_of.get(row["parent"] or row["name"], "Unsorted")
        a = per.get(row["name"]) if row["parent"] is None else None
        if a and (a["total"] or a["open"]):
            since = None
            if row["status"] and row["status"]["ts"]:
                since = sum(1 for m in a["merged"] if m > row["status"]["ts"])
            row["activity"] = {"weekly": a["weekly"], "total": a["total"], "recent": a["recent"],
                               "last": a["last"], "since_report": since, "open": a["open"]}
        else:
            row["activity"] = None
    return {
        "schema_version": 3,
        "exported_at": iso_z(exported_at),
        "collected_at": collected_at,
        "cutoff": iso_z(cutoff),
        "recent_days": RECENT_DAYS,
        "roadmap_head": roadmap_head,
        "prs_source": prs_source,
        "update_due_prs": UPDATE_DUE_PRS,
        "weeks": labels,
        "global": {**glob, "first_merge": min((p["merged_at"] for p in prs if p["merged_at"] and parse_ts(p["merged_at"]) <= cutoff), default=None)},
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
                   help="hand-transcribed per-layer states, used only when no coverage marker fits")
    p.add_argument("--links", type=pathlib.Path, default=here / "roadmap_links.json",
                   help="per-roadmap pages elsewhere to link from a row")
    p.add_argument("--cutoff", type=parse_ts, default=None,
                   help="count pull requests merged up to this ISO-8601 UTC time (default: the "
                        "snapshot's collection time when it records one, else now)")
    p.add_argument("--out", type=pathlib.Path, required=True)
    args = p.parse_args(argv)
    now = dt.datetime.now(dt.timezone.utc)

    topics = json.loads(args.topics.read_text(encoding="utf-8"))
    transitional = json.loads(args.coverage.read_text(encoding="utf-8")) if args.coverage.is_file() else {}
    links = json.loads(args.links.read_text(encoding="utf-8")) if args.links.is_file() else {}
    rows = read_roadmaps(args.roadmap_dir, transitional, links)
    if not rows:
        print(f"no roadmaps found under {args.roadmap_dir}", file=sys.stderr)
        return 1
    if args.data and args.data.is_file():
        (prs, collected_at), source = load_prs(args.data), f"snapshot {args.data.name}"
    else:
        prs, collected_at, source = fetch_prs(args.repo), iso_z(now), "gh"
    cutoff = args.cutoff or parse_ts(collected_at) or now
    data = build(rows, prs, topics, now, cutoff, collected_at, git_head(args.roadmap_dir), source)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(data, ensure_ascii=False, separators=(",", ":")) + "\n",
                        encoding="utf-8")
    for r in rows:
        why = r["assessment"]["reason"]
        if why in ("transcription-retired", "specification-changed", "invalid-marker"):
            print(f"{r['id']}: layers unassessed ({why}): {r['assessment']['detail']}", file=sys.stderr)
    assessed = sum(1 for r in rows if r["assessment"]["source"])
    merged_n = sum(1 for p in prs if not p["open"])
    print(f"{len(rows)} rows, {assessed} with per-layer states, {merged_n} merged and "
          f"{len(prs) - merged_n} open PRs ({source}), "
          f"cutoff {iso_z(cutoff)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
