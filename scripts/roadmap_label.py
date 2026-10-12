#!/usr/bin/env python3
"""Assign each PR's declared roadmap association as a `roadmap/<Area>` label.

Every PR should carry one standalone ``Roadmap: <Area>`` or ``Roadmap: none``
line. This is attribution, not scope authorization: new mathematics must still
cite the exact roadmap target that it advances, while a refactor may associate
itself with the roadmap that chiefly motivates the cleanup.

## The classifier (see `classify`)

A PR gets exactly one label, decided in this order:

1. `roadmap/none` -- the diff touches an infrastructure path (anything outside
   `TauCeti/`, the root `TauCeti.lean`, and the two ordinary Lake pins).
2. `roadmap/none` -- the diff is a pin-only dependency bump.
3. The one valid explicit ``Roadmap:`` declaration.
4. One validated canonical ``focus`` in a ``tauceti-target:v1`` marker.
5. One canonical roadmap-file citation, for compatibility with older PR bodies.
6. `roadmap/Unknown` -- attribution is absent, invalid, or conflicting.

Evidence from steps 3--5 must agree. Area names are read at runtime from active
and completed roadmaps, and labels are created only when missing (`ensure_label`).
File paths and conventional-commit titles are deliberately not used as roadmap
evidence.

## Usage

    # classify one PR and print the label (no writes):
    roadmap_label.py --pr 781 --repo TauCetiProject/TauCeti --roadmap-dir roadmap
    # ... and apply it (create the label if missing, drop any stale roadmap/* label),
    # leaving a nudge if it lands in roadmap/Unknown:
    roadmap_label.py --pr 781 --repo ... --roadmap-dir roadmap --apply --nudge
    # inspect every PR (never nudges):
    roadmap_label.py --backfill --repo ... --roadmap-dir roadmap
    # changing an existing roadmap label is deliberately opt-in:
    roadmap_label.py --backfill --repo ... --roadmap-dir roadmap \
        --apply --allow-relabel

API calls shell out to authenticated `gh`. GH_READ_TOKEN can separate reads
from App writes (GH_TOKEN). --reconcile-open repairs missed event runs;
--sync-labels maintains label presentation separately from per-PR writes.
`classify` and the parsing helpers are pure and are what the tests exercise.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys
from urllib.parse import quote

from github_api import APIError, Deferred, GitHub, pr_snapshot

# --- label namespace -------------------------------------------------------

NONE_LABEL = "roadmap/none"
UNKNOWN_LABEL = "roadmap/Unknown"


def area_label(area: str) -> str:
    return f"roadmap/{area}"


# Colours are cosmetic; kept uniform so the namespace reads as one group.
AREA_COLOR = "1d76db"      # blue: a resolved roadmap
NONE_COLOR = "ededed"      # grey: not roadmap work
UNKNOWN_COLOR = "fbca04"   # yellow: needs a citation

# --- the CI-allowed path set ----------------------------------------------

# A PR whose files all match this is one an AI author may land without a human
# override: `TauCeti/`, the root aggregator, and the two bump-guarded Lake pins.
_ALLOWED_PATH = re.compile(r"^(?:TauCeti/|TauCeti\.lean$|lake-manifest\.json$|lean-toolchain$)")

_PINS = {"lake-manifest.json", "lean-toolchain"}
_TARGET_MARKER = re.compile(r"<!--tauceti-target:v1 (\{[^}]*\})-->")


def is_infra(files: list[str]) -> bool:
    """True if any changed path is one CI would not let an AI PR touch alone.

    An empty file list is treated as infra (fail closed, as the scope guard does):
    we could not see a diff, so we do not claim a roadmap for it.
    """
    if not files:
        return True
    return any(not _ALLOWED_PATH.match(f) for f in files)


def is_pin_only(files: list[str]) -> bool:
    """True exactly when a nonempty diff changes only the two validated pins."""
    return bool(files) and set(files) <= _PINS


def _body_lines_outside_quotes_and_fences(body: str):
    """Yield body lines that are not inside Markdown fences or blockquotes."""
    fence = None
    for line in (body or "").splitlines():
        stripped = line.lstrip()
        marker = stripped[:3]
        if marker in {"```", "~~~"}:
            if fence is None:
                fence = marker
            elif fence == marker:
                fence = None
            continue
        if fence is None and not stripped.startswith(">"):
            yield line


def parse_declared_area(body: str, areas: set[str]) -> tuple[bool, str | None]:
    """Return ``(present, value)`` for standalone ``Roadmap:`` lines.

    ``value`` is an area name or ``none`` when every declaration is valid and
    identical. It is ``None`` for invalid or conflicting declarations. Examples
    in fenced code and blockquotes are ignored.
    """
    present = False
    values = set()
    invalid = False
    for line in _body_lines_outside_quotes_and_fences(body):
        if not re.match(r"^Roadmap\s*:", line):
            continue
        present = True
        match = re.fullmatch(r"Roadmap:\s*(\S+)\s*", line)
        if match is None:
            invalid = True
            continue
        value = match.group(1)
        if value != "none" and value not in areas:
            invalid = True
        else:
            values.add(value)
    if invalid or len(values) != 1:
        return present, None
    return present, next(iter(values))


def parse_target_areas(body: str, areas: set[str]) -> set[str]:
    """Canonical roadmap focuses from valid ``tauceti-target:v1`` markers."""
    found = set()
    for match in _TARGET_MARKER.finditer(body or ""):
        try:
            focus = json.loads(match.group(1)).get("focus")
        except (json.JSONDecodeError, AttributeError):
            continue
        if focus in areas:
            found.add(focus)
    return found


def parse_cited_areas(body: str, areas: set[str]) -> set[str]:
    """Roadmap areas cited in the PR body, restricted to canonical ones.

    Recognizes the forms authors actually use: a `TauCetiRoadmap/<Area>` path, and
    a bare `<Area>/README.md` or `<Area>/Suggested.lean`. `<Area>` must be an
    existing roadmap directory, so a typo or an unrelated path is ignored rather
    than minting a bogus label.
    """
    if not body:
        return set()
    found: set[str] = set()
    for m in re.finditer(r"TauCetiRoadmap/([A-Za-z0-9]+)", body):
        if m.group(1) in areas:
            found.add(m.group(1))
    for m in re.finditer(r"\b([A-Za-z0-9]+)/(?:README\.md|Suggested\.lean)", body):
        if m.group(1) in areas:
            found.add(m.group(1))
    return found


def classify(title: str, body: str, files: list[str], areas: set[str]) -> str:
    """Return the single roadmap label for a PR. Pure; see module docstring."""
    if is_infra(files):
        return NONE_LABEL
    if is_pin_only(files):
        return NONE_LABEL

    declared_present, declared = parse_declared_area(body, areas)
    if declared_present and declared is None:
        return UNKNOWN_LABEL

    targets = parse_target_areas(body, areas)
    cited = parse_cited_areas(body, areas)
    indirect = targets | cited

    if declared is not None:
        if declared == "none":
            return NONE_LABEL if not indirect else UNKNOWN_LABEL
        return area_label(declared) if indirect <= {declared} else UNKNOWN_LABEL

    return area_label(next(iter(indirect))) if len(indirect) == 1 else UNKNOWN_LABEL


# --- roadmap area discovery ------------------------------------------------


def canonical_areas(roadmap_dir: pathlib.Path) -> set[str]:
    """Active and completed roadmap directory names under a checkout.

    At the repository root, active areas live under the inner
    `TauCetiRoadmap/` package and archived areas live under the sibling
    `Completed/` directory. Accepting the package directory itself remains
    useful for local one-area tests and older callers.
    """
    inner = roadmap_dir / "TauCetiRoadmap"
    if not inner.is_dir():
        return {
            p.name for p in roadmap_dir.iterdir()
            if p.is_dir() and (p / "README.md").is_file()
        }

    bases = [inner]
    completed = roadmap_dir / "Completed"
    if completed.is_dir():
        bases.append(completed)
    return {
        p.name for base in bases for p in base.iterdir()
        if p.is_dir() and (p / "README.md").is_file()
    }


# --- gh plumbing (only reached in --apply/--nudge/--pr/--backfill IO paths) --


def ensure_label(api: GitHub, repo: str, name: str, color: str, desc: str) -> None:
    """Create only on a definite 404, and cache the result for a reconciliation pass."""
    key = (repo, name)
    if key in api.known_labels:
        return
    try:
        api.request("GET", f"repos/{repo}/labels/{quote(name, safe='')}")
    except APIError as error:
        if error.status != 404:
            raise
        try:
            api.request("POST", f"repos/{repo}/labels",
                        {"name": name, "color": color, "description": desc})
        except APIError as create_error:
            # Another run may have created it between our probe and POST.
            errors = create_error.data.get("errors", []) if isinstance(create_error.data, dict) else []
            if create_error.status != 422 or not any(
                isinstance(item, dict) and item.get("code") == "already_exists" for item in errors
            ):
                raise
    api.known_labels.add(key)


def sync_labels(api: GitHub, repo: str, areas: set[str]) -> None:
    """Maintain presentation separately from the per-PR event path (manual opt-in)."""
    existing = {row["name"]: row for row in api.items(f"repos/{repo}/labels")}
    for name in sorted({NONE_LABEL, UNKNOWN_LABEL} | {area_label(a) for a in areas}):
        color, desc = _label_meta(name, areas)
        row = existing.get(name)
        if row is None:
            ensure_label(api, repo, name, color, desc)
        elif row["color"].lower() != color or (row.get("description") or "") != desc:
            api.request("PATCH", f"repos/{repo}/labels/{quote(name, safe='')}",
                        {"color": color, "description": desc})


def _label_meta(name: str, areas: set[str]) -> tuple[str, str]:
    if name == NONE_LABEL:
        return NONE_COLOR, "No roadmap association (declared, infrastructure, or pin-only bump)"
    if name == UNKNOWN_LABEL:
        return UNKNOWN_COLOR, "Missing, invalid, or conflicting roadmap association"
    return AREA_COLOR, "PR declares the {} roadmap as its primary association".format(
        name[len("roadmap/"):])


NUDGE_MARKER = "<!--roadmap-label:nudge-->"
NUDGE_BODY = (
    NUDGE_MARKER + "\n"
    "I could not determine this PR's roadmap association, so I labelled it "
    "`roadmap/Unknown`. Please add one standalone line to the description:\n\n"
    "```text\nRoadmap: CanonicalAreaName\n```\n\n"
    "Use `Roadmap: none` for genuinely general, cross-cutting, infrastructure, "
    "or dependency work. Refactors need no fresh roadmap authorization, but should "
    "name the one roadmap chiefly motivating them. For new mathematics, this "
    "attribution line does not replace the [scope rubric's]"
    "(https://github.com/TauCetiProject/TauCetiReview/blob/main/rubrics/scope.md) "
    "requirement to cite the exact roadmap file and target."
)


def apply_label(api: GitHub, repo: str, pr: int, target: str, areas: set[str], current) -> None:
    """Change only roadmap labels; preserve every unrelated label."""
    have = {item["name"] for item in current}
    stale = sorted(n for n in have if n.startswith("roadmap/") and n != target)
    if target in have and not stale:
        return  # No label creation, presentation update, or mutation for an unchanged PR.
    if target not in have:
        color, desc = _label_meta(target, areas)
        ensure_label(api, repo, target, color, desc)
        api.request("POST", f"repos/{repo}/issues/{pr}/labels", {"labels": [target]})
    for name in stale:
        try:
            api.request("DELETE", f"repos/{repo}/issues/{pr}/labels/{quote(name, safe='')}")
        except APIError as error:
            if error.status != 404:  # A concurrent reconciliation already removed it.
                raise


def nudge(api: GitHub, repo: str, pr: int) -> None:
    """Post the attribution nudge once; never retry an ambiguous comment POST."""
    comments = api.items(f"repos/{repo}/issues/{pr}/comments")
    if any(NUDGE_MARKER in (c.get("body") or "") for c in comments):
        return
    api.request("POST", f"repos/{repo}/issues/{pr}/comments", {"body": NUDGE_BODY})


# --- CLI -------------------------------------------------------------------


def run_pr(api, args, areas, pr):
    snapshot = pr_snapshot(api, args.repo, pr)
    info = snapshot["info"]
    title, body = info.get("title") or "", info.get("body") or ""
    files = [row["filename"] for row in snapshot["files"]]
    label = classify(title, body, files, areas)
    print(f"#{pr}\t{label}\t{title}")
    declared_present, declared = parse_declared_area(body, areas)
    if (is_infra(files) or is_pin_only(files)) and declared_present and declared not in {None, "none"}:
        reason = "infrastructure/empty diff" if is_infra(files) else "pin-only bump"
        print(f"::notice::Roadmap: {declared} is overridden by the {reason} classification")
    if args.apply:
        apply_label(api, args.repo, pr, label, areas, info["labels"])
        if args.nudge and label == UNKNOWN_LABEL:
            nudge(api, args.repo, pr)
    if args.structure_nudge and info["state"] == "open":
        import structure_nudge
        try:
            structure_nudge.run_pr(args.repo, pr, args.apply, api=api, snapshot=snapshot)
        except Deferred:
            # A recovery pass must not advance its watermark past an unapplied comment.
            if args.reconcile_open:
                raise
            print(f"::warning::Structure nudge for #{pr} deferred; hourly reconciliation will retry")
        except Exception as error:
            if args.reconcile_open:
                raise  # Preserve the recovery window for a transient advisory failure too.
            print(f"::warning::Structure nudge for #{pr} failed: {error}")
    return label


def recovery_since(api, repo):
    """Only successful recovery runs advance the window; overlap their start time."""
    runs = api.request("GET", f"repos/{repo}/actions/workflows/roadmap-label-reconcile.yml/runs"
                       "?status=success&branch=main&per_page=1")["workflow_runs"]
    if not runs:
        return "1970-01-01T00:00:00Z"
    import datetime as dt
    start = dt.datetime.fromisoformat(runs[0]["run_started_at"].replace("Z", "+00:00"))
    # Match the status reconciler's overlap for clock skew and concurrent listing changes.
    return (start - dt.timedelta(minutes=2)).strftime("%Y-%m-%dT%H:%M:%SZ")


def candidates(api, args, areas):
    since = args.since
    if args.reconcile_open and since == "auto":
        since = recovery_since(api, args.repo)
    state = "open" if args.reconcile_open else "all"
    count = 0
    valid = {NONE_LABEL, UNKNOWN_LABEL} | {area_label(a) for a in areas}
    for page in api.pages(f"repos/{args.repo}/pulls?state={state}&sort=updated&direction=desc"):
        for info in page:
            if count >= args.limit:
                if args.reconcile_open:
                    raise RuntimeError("PR listing reached --limit; increase it to complete reconciliation")
                return  # Historical backfills intentionally inspect only the requested count.
            count += 1
            current = {item["name"] for item in info["labels"] if item["name"].startswith("roadmap/")}
            # Old PRs with missing/invalid labels also self-heal, regardless of the window.
            if args.reconcile_open and since and info["updated_at"] < since and len(current) == 1 and current <= valid:
                continue
            if args.apply and args.backfill and current and not args.allow_relabel:
                continue
            yield info["number"]


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="Assign roadmap labels and reconcile missed events.")
    ap.add_argument("--repo", default="TauCetiProject/TauCeti")
    ap.add_argument("--roadmap-dir", required=True)
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument("--pr", type=int)
    mode.add_argument("--backfill", action="store_true", help="inspect historical PRs")
    mode.add_argument("--reconcile-open", action="store_true", help="repair open PRs since a successful recovery")
    ap.add_argument("--since", default="auto", help="recovery window start (ISO UTC); auto uses the previous success")
    ap.add_argument("--limit", type=int, default=5000)
    ap.add_argument("--apply", action="store_true")
    ap.add_argument("--allow-relabel", action="store_true")
    ap.add_argument("--nudge", action="store_true")
    ap.add_argument("--structure-nudge", action="store_true", help="reuse the diff for the advisory structure nudge")
    ap.add_argument("--sync-labels", action="store_true", help="also maintain repository label colours/descriptions")
    args = ap.parse_args(argv)
    if args.limit < 1:
        ap.error("--limit must be positive")
    if args.since != "auto":
        import datetime as dt
        try:
            moment = dt.datetime.fromisoformat(args.since.replace("Z", "+00:00"))
            if moment.utcoffset() != dt.timedelta(0):
                raise ValueError("UTC required")
            args.since = moment.strftime("%Y-%m-%dT%H:%M:%SZ")
        except ValueError:
            ap.error("--since must be an ISO timestamp in UTC")
    areas = canonical_areas(pathlib.Path(args.roadmap_dir))
    if not areas:
        print("no roadmap areas found", file=sys.stderr)
        return 2
    api = GitHub()
    failed = False
    try:
        if args.sync_labels and args.apply:
            sync_labels(api, args.repo, areas)
        if args.pr is not None:
            run_pr(api, args, areas, args.pr)
        else:
            # Finish paging before mutations move PRs to the front of the updated list.
            pending = list(candidates(api, args, areas))
            for pr in pending:
                try:
                    run_pr(api, args, areas, pr)
                except Deferred:
                    raise  # Do not hammer a blocked credential for each remaining PR.
                except Exception as error:
                    print(f"PR #{pr} unapplied: {error}", file=sys.stderr)
                    failed = True
        return 1 if failed else 0
    except Deferred as error:
        print(f"::warning::{error}; hourly reconciliation will retry", file=sys.stderr)
        return 1  # A deferred recovery must not become the successful watermark.
    except Exception as error:
        print(f"Roadmap reconciliation failed: {error}", file=sys.stderr)
        return 1
    finally:
        api.report()


if __name__ == "__main__":
    raise SystemExit(main())
