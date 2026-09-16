"""Read-only adapter to the exact TauCetiReview gate used by Auto-merge.

Labels and pipeline health call the deployed gate, rather than implementing a
second interpretation of scoreboards. Set TAUCETI_REVIEW_RUNNER to its pinned
checkout's runner directory (the workflows provision it without credentials).
"""

import functools
from datetime import datetime, timezone
import importlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

import core

@functools.lru_cache(maxsize=1)
def engine():
    runner = Path(os.environ.get("TAUCETI_REVIEW_RUNNER", ".tauceti-review/runner")).resolve()
    if not (runner / "merge_from_scoreboard.py").is_file():
        raise RuntimeError("Pinned review engine missing; set TAUCETI_REVIEW_RUNNER")
    sys.path.insert(0, str(runner))
    return importlib.import_module("merge_from_scoreboard")


def sweep_engine():
    engine()
    return importlib.import_module("sweep")


def routing_state(pr):
    labels = {label["name"].lower() for label in pr.get("labels", [])}
    return (pr["head"]["sha"], pr["base"]["ref"], pr["state"], pr.get("draft"),
            labels & sweep_engine().KEEP_LABELS)


def classify(pr, comments, statuses, diff, now=None):
    """Pure evaluation of a fetched PR. Reservations and queue capacity are separate."""
    gate = engine()
    head = pr["head"]["sha"]
    result = {"head": head, "number": pr["number"], "eligible": False,
              "category": None, "reason": "PR is closed", "gate": None}
    if pr["state"] != "open":
        return result
    verdict = gate.decide_from_comments(
        comments, head, set(gate.DEFAULT_RUBRICS), diff,
        statuses.get("build", ""), statuses.get("bump-guard", ""),
        scope=statuses.get("scope", ""), now=now)
    result["gate"] = verdict
    result["reason"] = verdict["reason"]
    labels = {label["name"].lower() for label in pr.get("labels", [])}
    if pr.get("draft") or labels & sweep_engine().KEEP_LABELS:
        result.update(category="on-hold", reason="PR is a draft or intentionally held")
    elif pr["base"]["ref"] != "main":
        result.update(category="awaiting-dependency", reason="PR targets another branch, not main")
    elif pr.get("mergeable") is False:
        result.update(category="awaiting-author", reason="GitHub reports a merge conflict with the base")
    elif verdict["merge"]:
        result.update(category="ready-to-merge", eligible=True)
    elif statuses.get("build", "").lower() != "success":
        result["category"] = ("ci-failed" if statuses.get("build", "").lower()
                              in {"failure", "error"} else "awaiting-CI")
    else:
        latest = gate.latest_current_scoreboard(comments, head)
        if latest is None or latest[1].get("mode") == "init":
            result["category"] = ("review-in-progress" if gate.has_live_review(comments, head, now)
                                  else "awaiting-review")
        elif not verdict["review_safe"]:
            board, meta = latest
            states = meta.get("states")
            if not isinstance(states, dict) or not states:
                states = gate.states_from_table(board.get("body"))
            blocking = any(states.get(r) in {"blocking_request", "blocking_block"}
                           for r in gate.DEFAULT_RUBRICS)
            result["category"] = ("awaiting-author" if blocking else
                                  "review-in-progress" if gate.has_live_review(comments, head, now)
                                  else "awaiting-review")
        elif gate.has_live_review(comments, head, now):
            result["category"] = "review-in-progress"
        else:
            paths = gate.changed_paths(diff)
            human = not paths or any(not (p.startswith("TauCeti/") or p in gate.DEFAULT_ALLOW)
                                     for p in paths)
            if human:
                result["category"] = "needs-human-review"
            else:
                guards = [statuses.get("scope", "")]
                if paths & {"lake-manifest.json", "lean-toolchain"}:
                    guards.append(statuses.get("bump-guard", ""))
                result["category"] = ("merge-check-failed" if any(g.lower() in {"failure", "error"}
                                                        for g in guards) else "awaiting-CI")
    return result


# Use GraphQL for evidence so the all-open audit does not spend one REST request
# per metadata/comments/status read. Status.contexts contains the latest value of
# each commit-status context; check runs are intentionally not interchangeable.
_FIELDS = """number state isDraft baseRefName headRefOid mergeable
  labels(first:100) { nodes { name } pageInfo { hasNextPage } }
  commits(last:1) { nodes { commit { oid status { contexts { context state } } } } }
"""


def graphql(query, **variables):
    if time.time() < core._BLOCKED_UNTIL:
        raise core.RateLimited("GitHub reads paused after a rate limit")
    cmd = ["gh", "api", "graphql", "-f", "query=" + query]
    for key, value in variables.items():
        cmd += ["-F" if isinstance(value, int) else "-f", f"{key}={value}"]
    out = subprocess.run(cmd, text=True, capture_output=True)
    # GraphQL can report RATE_LIMITED in an HTTP-200 error response.
    try:
        payload = json.loads(out.stdout or "{}")
    except ValueError:
        payload = {}
    errors = payload.get("errors", [])
    if core._rate_limited(out.stderr) or any(e.get("type") == "RATE_LIMITED" for e in errors):
        core._block_for(core.RATE_LIMIT_MAX_WAIT_SECONDS)
        raise core.RateLimited("GitHub rate limited the readiness audit; retry on the next run")
    if out.returncode or errors or not payload.get("data"):
        raise RuntimeError(f"Readiness GraphQL read failed: {out.stderr.strip() or errors}")
    return payload["data"]["repository"]["pullRequest"]


def evidence(number, repo, comments=True):
    owner, name = repo.split("/", 1)
    comment_fields = ("comments(first:100, after:$cursor) { nodes { body updatedAt createdAt } "
                      "pageInfo { hasNextPage endCursor } }" if comments else "")
    declaration = ", $cursor:String" if comments else ""
    query = ("query($owner:String!, $name:String!, $number:Int!" + declaration + ") { "
             "repository(owner:$owner,name:$name) { pullRequest(number:$number) { " +
             _FIELDS + comment_fields + " } } }")
    variables = dict(owner=owner, name=name, number=number)
    rows = []
    first = None
    while True:
        node = graphql(query, **variables)
        if not node or node["labels"]["pageInfo"]["hasNextPage"]:
            raise RuntimeError("Missing PR or truncated labels; refusing readiness")
        if first is None:
            first = node
        elif node["headRefOid"] != first["headRefOid"]:
            raise RuntimeError("PR head moved during comment pagination")
        if not comments:
            break
        rows.extend({"body": c["body"], "updated_at": c["updatedAt"],
                     "created_at": c["createdAt"]} for c in node["comments"]["nodes"])
        page = node["comments"]["pageInfo"]
        if not page["hasNextPage"]:
            break
        variables["cursor"] = page["endCursor"]
    commit = first["commits"]["nodes"][-1]["commit"]
    if commit["oid"] != first["headRefOid"]:
        raise RuntimeError("Commit statuses do not belong to the current PR head")
    pr = {"number": number, "state": first["state"].lower(), "draft": first["isDraft"],
          "head": {"sha": first["headRefOid"]}, "base": {"ref": first["baseRefName"]},
          "labels": first["labels"]["nodes"],
          "mergeable": {"MERGEABLE": True, "CONFLICTING": False}.get(first["mergeable"])}
    statuses = {c["context"]: c["state"].lower()
                for c in (commit["status"] or {}).get("contexts", [])}
    return pr, rows, statuses


def assess(pr, repo=None, now=None):
    """Fetch fresh evidence and bind the reported decision to the current head."""
    repo = repo or core.REPO
    number = int(pr)
    current, comments, statuses = evidence(number, repo)
    result = classify(current, comments, statuses, "", now=now)
    # The gate rejects missing/build/review evidence before inspecting paths.
    # Only otherwise approved PRs need the expensive diff read.
    if result["category"] in {"needs-human-review", "merge-check-failed"}:
        diff = subprocess.check_output(["gh", "pr", "diff", str(number), "--repo", repo], text=True)
        result = classify(current, comments, statuses, diff, now=now)
    after, _, _ = evidence(number, repo, comments=False)
    if routing_state(after) != routing_state(current):
        result.update(eligible=False, category="awaiting-CI" if after["state"] == "open" else None,
                      reason="PR changed while collecting merge evidence; awaiting reconciliation",
                      head=after["head"]["sha"])
    elif after.get("mergeable") is False and result["eligible"]:
        result.update(eligible=False, category="awaiting-author",
                      reason="GitHub reports a merge conflict with the base")
    result["checked_at"] = int(time.time()) if now is None else now
    return result


def queue_snapshot(repo):
    """Read the queue once per report, using Auto-merge's reservation policy."""
    if time.time() < core._BLOCKED_UNTIL:
        raise core.RateLimited("Queue read skipped after a rate limit")
    sweep = sweep_engine()
    sweep.REPO = repo
    entries = sweep.queue_entries()
    return {"known": True, "numbers": [e["number"] for e in entries],
            "reservation_holder": sweep.reservation_holder(entries, datetime.now(timezone.utc))}


def audit(snapshot):
    """Validate current stages without trusting labels; retain failures as unknown."""
    try:
        engine()
    except RuntimeError as exc:
        # Publish an explicitly unverified report if the policy checkout failed.
        return {"checked_at": int(time.time()), "prs": {},
                "queue": {"known": False, "reason": str(exc)}, "error": str(exc)}
    repo = snapshot["repo"]
    results = {}
    for pr in snapshot["prs"]:
        if pr["state"] != "OPEN" or pr["is_draft"]:
            continue
        number = pr["number"]
        try:
            results[str(number)] = assess(number, repo=repo)
        except (RuntimeError, subprocess.CalledProcessError, KeyError, ValueError) as exc:
            results[str(number)] = {"number": number, "eligible": None,
                                    "category": None, "reason": str(exc)}
    try:
        queue = queue_snapshot(repo)
    except (RuntimeError, subprocess.CalledProcessError, KeyError, ValueError) as exc:
        queue = {"known": False, "reason": str(exc)}
    return {"checked_at": int(time.time()), "prs": results, "queue": queue}
