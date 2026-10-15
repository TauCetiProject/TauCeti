#!/usr/bin/env python3
"""Bound queued fleet startup using the SAME workflow run's second attempt.

Using rerun instead of repository_dispatch preserves bors's unique staging-run
identity. Attempt two is forced to Namespace by the trusted picker, and existing
run-attempt fencing prevents old finalizers from publishing over the replacement.
"""

import datetime as dt
import json
import os
import re
import sys
import time
import urllib.request

TITLE = re.compile(
    r"^bors branch=[^ ]+ batch=[1-9][0-9]* head=[0-9a-f]{40} base=[0-9a-f]{40}$"
)
ROOT = "https://api.github.com/repos/TauCetiProject/TauCeti"


def api(path, data=None):
    request = urllib.request.Request(
        ROOT + path,
        data=None if data is None else json.dumps(data).encode(),
        headers={
            "Authorization": "Bearer " + os.environ["GH_TOKEN"],
            "Accept": "application/vnd.github+json",
            "User-Agent": "TauCetiFleetRecovery/1.0",
        },
    )
    with urllib.request.urlopen(request, timeout=15) as response:
        raw = response.read(2 * 1024 * 1024 + 1)
    if len(raw) > 2 * 1024 * 1024:
        raise ValueError("API response exceeds bound")
    return json.loads(raw) if raw else {}


def eligible(run):
    return (
        run.get("event") == "repository_dispatch"
        and run.get("run_attempt") == 1
        and bool(TITLE.fullmatch(run.get("display_title", "")))
        and run.get("path") == ".github/workflows/pr-build.yml"
        and run.get("repository", {}).get("full_name") == "TauCetiProject/TauCeti"
    )


def build_job(data):
    jobs = data["jobs"]
    if data["total_count"] != len(jobs) or len(jobs) > 100:
        raise ValueError("incomplete job observation")
    found = [j for j in jobs if j["name"] == "sandboxed-build"]
    if len(found) > 1:
        raise ValueError("ambiguous sandbox job")
    return found[0] if found else None


def recover(
    run_id, *, fetch=api, clock=time.monotonic, sleep=time.sleep, wall=time.time
):
    run = fetch(f"/actions/runs/{run_id}")
    if not eligible(run):
        return "not-an-initial-bors-attempt"
    deadline = clock() + 420
    while clock() < deadline:
        latest = fetch(f"/actions/runs/{run_id}")
        if latest.get("run_attempt") != 1 or latest.get("status") == "completed":
            return "already-terminal-or-retried"
        job = build_job(fetch(f"/actions/runs/{run_id}/attempts/1/jobs?per_page=100"))
        if job:
            if "tauceti-fleet" not in job.get("labels", []):
                return "namespace-selected"
            if job.get("runner_name") or job["status"] in ("in_progress", "completed"):
                return "runner-acquired"
            created = dt.datetime.fromisoformat(
                job["created_at"].replace("Z", "+00:00")
            ).timestamp()
            if wall() - created >= 120:
                break
        sleep(10)
    else:
        return "picker-not-observable-within-bound"
    # Mutations are not automatically retried after an ambiguous HTTP failure.
    fetch(f"/actions/runs/{run_id}/cancel", {})
    deadline = clock() + 90
    while clock() < deadline:
        latest = fetch(f"/actions/runs/{run_id}")
        if latest.get("run_attempt") != 1:
            return "another-recovery-already-advanced-attempt"
        if latest["status"] == "completed":
            if latest.get("conclusion") != "cancelled":
                return "completed-during-cancellation"
            final_job = build_job(
                fetch(f"/actions/runs/{run_id}/attempts/1/jobs?per_page=100")
            )
            if not final_job or final_job.get("runner_name"):
                # A real build raced acquisition; normal bors recovery owns it.
                return "runner-acquired-during-cancellation"
            fetch(f"/actions/runs/{run_id}/rerun", {})
            return "rerun-on-namespace-requested"
        sleep(5)
    raise TimeoutError("Cancellation not confirmed; refusing an overlapping retry")


def main():
    try:
        run_id = int(os.environ["FLEET_RUN_ID"])
        if run_id <= 0:
            raise ValueError("run id")
        print(recover(run_id))
        return 0
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print(
            "::error::Fleet startup recovery incomplete: "
            + type(exc).__name__
            + "; inspect the original workflow run",
            file=sys.stderr,
        )
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
