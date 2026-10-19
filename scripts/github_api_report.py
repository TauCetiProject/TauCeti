#!/usr/bin/env python3
"""Summarize downloaded Actions logs without making GitHub requests.

Usage: github_api_report.py --runs runs.json --logs logs --out report.json
The manifest is an array of Actions run objects; logs are RUN_ID.log from
``gh run view RUN_ID --attempt N --log``. Each ID must appear only once, with
logs for its recorded attempt. Missing logs and uninstrumented runs remain
visible as coverage gaps, never as zero request usage.
"""

import argparse
from collections import Counter, defaultdict
import json
from pathlib import Path
import re


PREFIX = re.compile(r"^(?:[^\t]+\t[^\t]+\t)?\d{4}-\d\d-\d\dT[\d:.]+Z ")
ROLE = re.compile(r"[a-z][a-z0-9-]{0,40}\Z")


def payload(line):
    """Remove gh's optional job/step/timestamp prefix, preserving shell echo text."""
    return PREFIX.sub("", line).strip()


def number(value):
    """Parse a nonnegative integer counter/header; absent or invalid is unknown."""
    if type(value) is int and value >= 0:
        return value
    if isinstance(value, str) and value.isascii() and value.isdigit():
        return int(value)
    return None


def inspect_log(text):
    """Return requests, query-point totals, rate-limit evidence and skipped decisions.

    Response rows count actual attempts, including retries. Summary lines supply
    GraphQL costs only, so requests are never counted twice. Merge-engine errors
    establish a rate-limit failure, but their invocation numbers are not HTTP
    request counts. Plain error text and arbitrary response bodies are ignored.
    """
    requests, points, limited, skipped = [], Counter(), False, Counter()
    for raw in text.splitlines():
        line = payload(raw)
        try:
            if line.startswith("github-api: "):
                row = json.loads(line.removeprefix("github-api: "))
                role, method, resource = row["credential"], row["method"], row["resource"]
                if not (isinstance(role, str) and ROLE.fullmatch(role)
                        and method in {"GET", "POST", "PATCH", "PUT", "DELETE"}
                        and resource in {"core", "graphql", "search"}
                        and type(row["status"]) is int):
                    continue
                read = method == "GET" or row.get("path") == "graphql"
                requests.append((role, resource, read, number(row.get("remaining"))))
                limited |= row["status"] == 429 or (
                    row["status"] == 403 and number(row.get("remaining")) == 0)
            elif line.startswith("github-api-summary: "):
                summary = json.loads(line.removeprefix("github-api-summary: "))
                for role, stat in summary.items():
                    if isinstance(role, str) and ROLE.fullmatch(role):
                        cost = number(stat.get("graphql_points"))
                        if cost is not None:
                            points[role] += cost
            elif line.startswith("github-api-skip: "):
                row = json.loads(line.removeprefix("github-api-skip: "))
                if row.get("kind") in {"roadmap-label", "structure-comment"}:
                    skipped[row["kind"]] += 1
            elif line.startswith("github-api-limited: "):
                row = json.loads(line.removeprefix("github-api-limited: "))
                if row.get("status") in (403, 429):
                    limited = True
            elif line.startswith("{"):
                row = json.loads(line)
                if row.get("schema") == "tauceti-merge.api-error/v1" and row.get("rate_limit_kind"):
                    limited = True
        except (ValueError, KeyError, TypeError, AttributeError):
            continue
    return requests, points, limited, skipped


def summarize(runs, logs):
    """Aggregate a manifest and matching log directory with explicit coverage.

    Shared remaining-quota readings are reported as observations, never used to
    infer this workflow's consumption. Duplicate run IDs are rejected so merged
    manifest pages cannot silently double-count a run.
    """
    workflows = defaultdict(lambda: {"runs": 0, "conclusions": Counter(),
        "logs_available": 0, "runs_with_request_telemetry": 0,
        "rate_limited_runs_observed": 0, "usage": {}})
    seen = set()
    for run in runs:
        ident = run["id"]
        if type(ident) is not int or ident <= 0 or ident in seen:
            raise ValueError("Manifest requires unique positive run IDs")
        seen.add(ident)
        entry = workflows[run["name"]]
        entry["runs"] += 1
        entry["conclusions"][run.get("conclusion") or "unfinished"] += 1
        path = logs / f"{ident}.log"
        if not path.is_file() or not path.stat().st_size:
            continue
        entry["logs_available"] += 1
        requests, points, limited, skipped = inspect_log(path.read_text(errors="replace"))
        entry["runs_with_request_telemetry"] += bool(requests)
        entry["rate_limited_runs_observed"] += limited
        for role, resource, read, remaining in requests:
            key = f"{role}/{resource}"
            bucket = entry["usage"].setdefault(key, {
                "requests": 0, "reads": 0, "writes": 0,
                "minimum_remaining_observed": None})
            bucket["requests"] += 1
            bucket["reads" if read else "writes"] += 1
            if remaining is not None:
                previous = bucket["minimum_remaining_observed"]
                bucket["minimum_remaining_observed"] = remaining if previous is None else min(previous, remaining)
        entry.setdefault("graphql_points_observed", Counter()).update(points)
        entry.setdefault("unchanged_write_decisions", Counter()).update(skipped)
    return {"schema": "tauceti-github-api-report/v1", "workflows": dict(workflows),
        "limitations": [
            "Request totals cover instrumented downloaded logs only; missing telemetry is unknown.",
            "Credential roles do not identify globally shared installations or quotas.",
            "Remaining-quota changes cannot be attributed to one workflow.",
            "Unchanged-write decisions cover roadmap labels/structure comments only; not hypothetical requests saved.",
            "Pending-work age and staging-admission delay require separate queue observations.",
            "Logs are observations and must never authorize merges or workflow execution."]}


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--runs", required=True, type=Path)
    ap.add_argument("--logs", required=True, type=Path)
    ap.add_argument("--out", required=True, type=Path)
    args = ap.parse_args(argv)
    report = summarize(json.loads(args.runs.read_text()), args.logs)
    args.out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
