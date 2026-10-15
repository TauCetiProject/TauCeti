#!/usr/bin/env python3
"""Bound queued fleet startup using the SAME workflow run's second attempt.

Using rerun instead of repository_dispatch preserves bors's unique staging-run
identity. Attempt two is forced to Namespace by the trusted picker. Force-cancel
bypasses always() finalizers; failed recovery publishes an infrastructure verdict.
"""

import datetime as dt
import json
import os
import re
import sys
import time
import urllib.request

TITLE = re.compile(
    r"^bors branch=[^ ]+ batch=[1-9][0-9]* head=(?P<head>[0-9a-f]{40}) base=[0-9a-f]{40}$"
)
ROOT = "https://api.github.com/repos/TauCetiProject/TauCeti"


def api(path, data=None):
    """Read or mutate the fixed repository API with bounded response size.

    Supplying data sends a JSON POST. HTTP/transport/decoding failures propagate;
    callers must not automatically repeat an ambiguous cancellation or rerun.
    """
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
    """Accept only initial bors dispatches with the expected repository, path and title."""
    return (
        run.get("event") == "repository_dispatch"
        and run.get("run_attempt") == 1
        and bool(TITLE.fullmatch(run.get("display_title", "")))
        and run.get("path") == ".github/workflows/pr-build.yml"
        and run.get("repository", {}).get("full_name") == "TauCetiProject/TauCeti"
    )


def build_job(data):
    """Return the unique sandbox job, or None before it appears.

    Truncated or ambiguous observations raise ValueError and cannot authorize
    cancellation. At most one complete page of jobs is accepted.
    """
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
    """Bound first-attempt fleet acquisition and request a same-run Namespace retry.

    Read observations until a fleet job acquires a runner or waits two minutes.
    Only a never-acquired job is force-canceled. Once terminal, request exactly
    one rerun; re-read after an ambiguous response instead of repeating mutation.
    A failed handoff posts a failure on the verified staging head so bors can
    recover. Acquired jobs retain normal reporting. Incomplete evidence before
    cancellation cannot authorize mutation; unconfirmed handoff raises an error.
    """
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
            labels = job.get("labels", [])
            if labels and "tauceti-fleet" not in labels:
                return "namespace-selected"
            if job.get("runner_name") or job.get("runner_id") or job["status"] in ("in_progress", "completed"):
                return "runner-acquired"
            if not labels:
                sleep(10)
                continue
            created = dt.datetime.fromisoformat(
                job["created_at"].replace("Z", "+00:00")
            ).timestamp()
            if wall() - created >= 120:
                break
        sleep(10)
    else:
        raise TimeoutError("Picker placement was not observable within seven minutes")
    try:
        return handoff(run_id, run, fetch=fetch, clock=clock, sleep=sleep)
    except (OSError, ValueError, KeyError, TypeError, RuntimeError):
        failure_status(run_id, run, fetch=fetch)
        raise


def handoff(run_id, run, *, fetch, clock, sleep):
    """Force-stop one verified attempt and reconcile its single rerun request.

    The caller owns terminal failure reporting if any observation or mutation
    fails. No mutation is repeated after an ambiguous HTTP result.
    """
    # Mutations are not automatically retried after an ambiguous HTTP failure.
    try:
        fetch(f"/actions/runs/{run_id}/force-cancel", {})
    except OSError:
        pass  # The server may have accepted it: reconcile before any further action.
    deadline = clock() + 120
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
            if not final_job or final_job.get("runner_name") or final_job.get("runner_id"):
                # A real build raced acquisition; normal bors recovery owns it.
                failure_status(run_id, run, fetch=fetch)
                return "runner-acquired-during-cancellation"
            try:
                fetch(f"/actions/runs/{run_id}/rerun", {})
                return "rerun-on-namespace-requested"
            except OSError:
                # POST may have succeeded despite a lost response. Observe the
                # successor before deciding to hand recovery back to bors.
                deadline = clock() + 60
                while clock() < deadline:
                    if fetch(f"/actions/runs/{run_id}").get("run_attempt", 0) > 1:
                        return "rerun-on-namespace-observed"
                    sleep(5)
                raise RuntimeError("Namespace retry not confirmed; bors infrastructure recovery requested") from None
        sleep(5)
    raise TimeoutError("Force cancellation not confirmed; bors infrastructure recovery requested")


def failure_status(run_id, original, *, fetch=api):
    """Report failed handoff only for the verified original attempt.

    A successor attempt must retain ownership of its statuses. This is a
    best-effort GET/POST fence, matching the finalizer's run-attempt check.
    """
    latest = fetch(f"/actions/runs/{run_id}")
    if not eligible(latest) or latest["display_title"] != original["display_title"]:
        return
    head = TITLE.fullmatch(original["display_title"]).group("head")
    fetch(f"/statuses/{head}", dict(
        context="build", state="failure", description="fleet startup recovery failed; retry staging on Namespace",
        target_url=f"https://github.com/TauCetiProject/TauCeti/actions/runs/{run_id}",
    ))


def main():
    try:
        run_id = int(os.environ["FLEET_RUN_ID"])
        if run_id <= 0:
            raise ValueError("run id")
        print(recover(run_id))
        return 0
    except (OSError, ValueError, KeyError, TypeError, RuntimeError) as exc:
        print(
            "::error::Fleet startup recovery incomplete: "
            + type(exc).__name__
            + "; inspect the original workflow run",
            file=sys.stderr,
        )
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
