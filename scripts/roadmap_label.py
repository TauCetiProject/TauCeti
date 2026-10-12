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
import functools
import hashlib
import os
import json
import pathlib
import re
import sys
import time
from urllib.parse import quote

from github_api import APIError, Deferred, GitHub, history_snapshots, pr_snapshot

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
        return UNKNOWN_COLOR, "Missing, invalid, conflicting, or unverifiable roadmap association"
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


MAX_RETRIES = 5


@functools.lru_cache(maxsize=1)
def policy_key():
    root = pathlib.Path(__file__).parent
    return hashlib.sha256(b"".join((root / name).read_bytes() for name in
                          ("roadmap_label.py", "github_api.py", "structure_nudge.py"))).hexdigest()


def input_key(info, areas):
    # Comments/status labels and a moving main tip do not change a PR's attribution inputs.
    values = {"head": info["head"]["sha"], "base": info["base"]["ref"],
              "body": info.get("body") or "", "state": info["state"], "areas": sorted(areas), "policy": policy_key()}
    return hashlib.sha256(json.dumps(values, sort_keys=True).encode()).hexdigest()


class RecoveryState:
    """Persist successful input hashes and bounded retries without storing PR bodies."""

    def __init__(self, path=None, *, reset=False):
        self.records, self.inputs, self.seen = {}, {}, set()
        self.listed = False
        if path and not reset and pathlib.Path(path).is_file():
            value = json.loads(pathlib.Path(path).read_text())
            if value.get("version") != 1 or not isinstance(value.get("prs"), dict):
                raise RuntimeError("invalid recovery state")
            for number, record in value["prs"].items():
                if not number.isdigit() or not isinstance(record, dict):
                    raise RuntimeError("invalid recovery record")
                if not re.fullmatch(r"[0-9a-f]{64}", record.get("key", "")) or type(record.get("attempts")) is not int or not 0 <= record["attempts"] <= MAX_RETRIES:
                    raise RuntimeError("invalid recovery retry/input hash")
                if record["attempts"] == 0 and not isinstance(record.get("label"), str):
                    raise RuntimeError("invalid recovery success label")
                self.records[int(number)] = record
        if reset:
            self.records.clear()

    def select(self, info, areas):
        number = info["number"]
        key = input_key(info, areas)
        self.inputs[number] = key
        self.seen.add(number)
        record = self.records.get(number)
        if not record or record["key"] != key:
            self.records.pop(number, None)
            return True  # Unknown/changed inputs self-heal even outside the time window.
        if record["attempts"] >= MAX_RETRIES:
            retry_at = record.get("retry_at")
            if retry_at is not None and time.time() >= retry_at:
                self.records.pop(number)
                return True
            print(f"::warning::PR #{number}: recovery retries exhausted; " +
                  (f"automatic retry after epoch {retry_at}" if retry_at else "change its inputs or run a full scan"))
            return False
        if record["attempts"]:
            return True  # Retry even when a previous successful window has passed it.
        current = {item["name"] for item in info["labels"] if item["name"].startswith("roadmap/")}
        return current != {record["label"]}  # A changed roadmap label must self-heal too.

    def success(self, number, label, key):
        self.records[number] = {"key": key, "label": label, "attempts": 0}

    def failure(self, number, error, key=None, *, transient=False):
        key = key or self.inputs[number]
        previous = self.records.get(number, {})
        attempts = previous.get("attempts", 0) if previous.get("key") == key else 0
        self.records[number] = {"key": key, "attempts": min(MAX_RETRIES, attempts + 1),
                                "error": str(error)[:300]}
        if attempts + 1 >= MAX_RETRIES and (transient or isinstance(error, APIError) and error.status >= 500):
            # Persistent server/input-listing failures can recover without a PR edit.
            # Pause six hours between bounded retry cycles instead of quarantining forever.
            self.records[number]["retry_at"] = time.time() + 6 * 3600

    def save(self, path):
        records = {str(number): record for number, record in self.records.items()
                   if not self.listed or number in self.seen}
        target = pathlib.Path(path)
        target.parent.mkdir(parents=True, exist_ok=True)
        temporary = target.with_suffix(".tmp")
        temporary.write_text(json.dumps({"version": 1, "prs": records}, sort_keys=True))
        temporary.replace(target)

    def report(self):
        pending = [number for number, record in self.records.items() if 0 < record["attempts"] < MAX_RETRIES]
        exhausted = [number for number, record in self.records.items() if record["attempts"] == MAX_RETRIES]
        summary = f"Recovery: {len(pending)} PRs queued for retry; {len(exhausted)} exhausted."
        print(summary, file=sys.stderr)
        if os.environ.get("GITHUB_STEP_SUMMARY"):
            with open(os.environ["GITHUB_STEP_SUMMARY"], "a") as stream:
                stream.write("\n" + summary + "\n")
                for number in pending + exhausted:
                    stream.write(f"- #{number}: attempt {self.records[number]['attempts']}/{MAX_RETRIES}\n")


def run_pr(api, args, areas, pr, snapshot=None, preserve_labels=False):
    snapshot = snapshot if snapshot is not None else pr_snapshot(api, args.repo, pr)
    info = snapshot["info"]
    title, body = info.get("title") or "", info.get("body") or ""
    files = [row["filename"] for row in snapshot["files"]]
    incomplete = info.get("incomplete_files", False)
    if incomplete:
        label = NONE_LABEL if files and is_infra(files) else UNKNOWN_LABEL
        print(f"::notice::PR #{pr}: incomplete diff; using {label} and skipping structure analysis")
    else:
        label = classify(title, body, files, areas)
    args._processed_key = input_key(info, areas)
    args._processed_incomplete = incomplete and not info.get("files_capped", False)
    state_column = info["state"].upper() + "\t" if args.backfill else ""
    print(f"#{pr}\t{state_column}{label}\t{title}")
    declared_present, declared = parse_declared_area(body, areas)
    if label == NONE_LABEL and (is_infra(files) or is_pin_only(files)) and declared_present and declared not in {None, "none"}:
        reason = "infrastructure/empty diff" if is_infra(files) else "pin-only bump"
        print(f"::notice::Roadmap: {declared} is overridden by the {reason} classification")
    if args.apply and not preserve_labels:
        apply_label(api, args.repo, pr, label, areas, info["labels"])
        if args.nudge and args.pr is not None and not incomplete and label == UNKNOWN_LABEL:
            nudge(api, args.repo, pr)
    if args.structure_nudge and info["state"] == "open" and not incomplete:
        try:
            import structure_nudge
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
    if args.reconcile_open and since == "auto" and not getattr(args, "_state", None):
        since = recovery_since(api, args.repo)
    state = "open" if args.reconcile_open else "all"
    recovery = getattr(args, "_state", None)
    order = "created" if recovery else "updated" if args.reconcile_open else "created"
    count = 0
    valid = {NONE_LABEL, UNKNOWN_LABEL} | {area_label(a) for a in areas}
    for page in api.pages(f"repos/{args.repo}/pulls?state={state}&sort={order}&direction=desc"):
        for info in page:
            if count >= args.limit:
                if args.reconcile_open:
                    raise RuntimeError("PR listing reached --limit; increase it to complete reconciliation")
                return  # Historical backfills intentionally inspect only the requested count.
            count += 1
            if recovery:
                decision = recovery.select(info, areas)
                if decision is False:
                    continue
                if decision is True:
                    yield info["number"]
                    continue
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
    ap.add_argument("--max-wait", type=int, default=180, help="cumulative quota/transient retry wait budget in seconds")
    ap.add_argument("--state-in", help="previous recovery input hashes and retry queue")
    ap.add_argument("--state-out", help="recovery input hashes and retries for the next run")
    ap.add_argument("--retry-exhausted", action="store_true", help="reset cached successes and exhausted retries")
    ap.add_argument("--allow-relabel", action="store_true")
    ap.add_argument("--nudge", action="store_true")
    ap.add_argument("--structure-nudge", action="store_true", help="reuse the diff for the advisory structure nudge")
    ap.add_argument("--sync-labels", action="store_true", help="also maintain repository label colours/descriptions")
    args = ap.parse_args(argv)
    if args.max_wait < 0:
        ap.error("--max-wait must be nonnegative")
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
    api = GitHub(max_wait=args.max_wait)
    failed = False
    args._state = None
    try:
        if args.reconcile_open and args.apply and args.state_out:
            args._state = RecoveryState(args.state_in, reset=args.retry_exhausted)
        if args.sync_labels and args.apply:
            sync_labels(api, args.repo, areas)
        if args.pr is not None:
            run_pr(api, args, areas, args.pr)
        elif args.backfill:
            from collections import Counter
            tally = Counter()
            for pr, snapshot in history_snapshots(api, args.repo, args.limit):
                if isinstance(snapshot, Exception):
                    print(f"PR #{pr} unapplied: {snapshot}", file=sys.stderr)
                    failed = True
                    continue
                current = {item["name"] for item in snapshot["info"]["labels"] if item["name"].startswith("roadmap/")}
                # Keep the historical classification report even when existing labels are preserved.
                try:
                    label = run_pr(api, args, areas, pr, snapshot=snapshot,
                                   preserve_labels=bool(current and not args.allow_relabel))
                    tally[label] += 1
                    if args.apply and current != {label} and current and not args.allow_relabel:
                        print(f"PR #{pr}: preserving {sorted(current)}; pass --allow-relabel to change it", file=sys.stderr)
                except Deferred:
                    raise
                except Exception as error:
                    print(f"PR #{pr} unapplied: {error}", file=sys.stderr)
                    failed = True
            print("\n=== summary ===", file=sys.stderr)
            for label, count in tally.most_common():
                print(f"  {label}: {count}", file=sys.stderr)
        else:
            # Finish paging before mutations move PRs to the front of the updated list.
            pending = list(candidates(api, args, areas))
            if args._state:
                args._state.listed = True
            for pr in pending:
                args._processed_key = None
                args._processed_incomplete = False
                try:
                    label = run_pr(api, args, areas, pr)
                    if args._state:
                        if args._processed_incomplete:
                            args._state.failure(pr, RuntimeError("temporary incomplete diff; queued for retry"),
                                                args._processed_key, transient=True)
                        else:
                            args._state.success(pr, label, args._processed_key)
                except Deferred:
                    raise  # Do not hammer a blocked credential for each remaining PR.
                except Exception as error:
                    print(f"::warning::PR #{pr} unapplied: {error}", file=sys.stderr)
                    if isinstance(error, APIError) and error.status == 0:
                        raise  # A transport outage is global; stop instead of probing every PR.
                    if args._state:
                        args._state.failure(pr, error, args._processed_key)
                    else:
                        failed = True
                finally:
                    if args._state:
                        args._state.save(args.state_out)
        return 1 if failed else 0
    except Deferred as error:
        print(f"::warning::{error}; hourly reconciliation will retry", file=sys.stderr)
        return 1  # A deferred recovery must not become the successful watermark.
    except Exception as error:
        print(f"Roadmap reconciliation failed: {error}", file=sys.stderr)
        return 1
    finally:
        if args._state:
            args._state.save(args.state_out)
            args._state.report()
        api.report()


if __name__ == "__main__":
    raise SystemExit(main())
