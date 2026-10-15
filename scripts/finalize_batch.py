#!/usr/bin/env python3
"""Post one terminal batch status, with bounded isolated-publisher acquisition.

Executed only from the immutable workflow checkout. The finalizer starts beside
the publisher after the full sandbox audit; it never consumes candidate files.
"""
import json
import os
import sys
import time
import urllib.request
from email.utils import parsedate_to_datetime

from bors_observation import MAX_BYTES, REPO, observation, sha
from bors_train_identity import candidate_ref

PUBLISHER = "publish-merge-group-cache / publish"
CONFIRM = "Confirm the exact revision map on the public endpoint"
ACQUISITION_SECONDS = 300
PUBLICATION_SECONDS = 1200
POST_RETRY_SECONDS = 180
MACHINE_LABEL = "nscloud-ubuntu-24.04-amd64-4x8-with-features;job.priority=0"
API_ROOT = "https://api.github.com/repos/" + REPO


def api(path, payload=None):
    """Bound API I/O and keep the status token on the fixed repository authority."""
    request = urllib.request.Request(API_ROOT + path, headers={
        "Authorization": "Bearer " + os.environ["GH_TOKEN"],
        "Accept": "application/vnd.github+json",
        "X-GitHub-Api-Version": "2022-11-28",
        "User-Agent": "TauCetiBatchFinalizer/1.0",
        "Content-Type": "application/json",
    }, data=None if payload is None else json.dumps(payload).encode())
    with urllib.request.urlopen(request, timeout=15) as response:
        raw = response.read(MAX_BYTES + 1)
    if len(raw) > MAX_BYTES:
        raise ValueError("GitHub response exceeds bound")
    return json.loads(raw)


def publication_job(data):
    """Use only this attempt's unique trusted publisher, never an older attempt."""
    jobs = data["jobs"]
    if data["total_count"] != len(jobs) or len(jobs) > 100:
        raise ValueError("incomplete jobs response")
    matches = [job for job in jobs if job["name"] == PUBLISHER]
    if len(matches) > 1:
        raise ValueError("ambiguous publisher")
    return matches[0] if matches else None


def isolated_runner(data, job, run_id):
    """Require the selected nonprivileged labels and a different sandbox runner."""
    labels = {MACHINE_LABEL, f"namespace-features:github.run-id={run_id}"}
    sandbox = [item for item in data["jobs"] if item["name"] == "sandboxed-build"]
    return (set(job.get("labels", [])) == labels and bool(job.get("runner_name"))
            and len(sandbox) == 1 and bool(sandbox[0].get("runner_name"))
            and job["runner_name"] != sandbox[0]["runner_name"])


def wait_publication(run_id, attempt, *, fetch=api, clock=time.monotonic, sleep=time.sleep):
    """Return success only after the publisher and its exact-map check complete."""
    start = clock()
    previous = None
    acquired = False
    while True:
        elapsed = clock() - start
        try:
            data = fetch(f"/actions/runs/{run_id}/attempts/{attempt}/jobs?per_page=100")
            job = publication_job(data)
        except (OSError, ValueError, KeyError, TypeError) as error:
            # A transient API failure gets a bounded retry, never a green result.
            print(f"::warning::publisher observation unavailable: {type(error).__name__}", flush=True)
            job = None
        if job is not None:
            current = (job["status"], job.get("conclusion"), job.get("runner_name"))
            if current != previous:
                print("Publisher evidence: " + json.dumps({key: job.get(key) for key in (
                    "id", "status", "conclusion", "created_at", "started_at",
                    "completed_at", "runner_name", "labels")}), flush=True)
                previous = current
            if job["status"] == "completed" and not job.get("runner_name"):
                return "failure", "publisher completed without acquiring a runner; inspect run jobs and Namespace routing"
            if job["status"] in {"in_progress", "completed"} and job.get("conclusion") != "skipped":
                if not isolated_runner(data, job, run_id):
                    return "failure", "publisher runner/labels are not isolated; inspect Namespace routing"
            if job["status"] == "completed":
                confirmed = any(step.get("name") == CONFIRM and step.get("conclusion") == "success"
                                for step in job.get("steps", []))
                if job.get("conclusion") == "success" and confirmed:
                    return "success", "sandboxed build passed; exact revision cache is public"
                return "failure", "build passed, but isolated publication/confirmation failed"
        if job is not None and job["status"] == "in_progress" and job.get("runner_name"):
            acquired = True
        if not acquired and elapsed >= ACQUISITION_SECONDS:
            return "failure", "publisher not acquired/observable in 5m; inspect run jobs and Namespace routing"
        if elapsed >= PUBLICATION_SECONDS:
            return "failure", "isolated publication exceeded 20m; inspect run jobs and Namespace capacity"
        sleep(30)


def terminal_state(env, *, wait=wait_publication, observe=observation):
    """Keep failed/canceled audits red and revalidate bors before a green status."""
    if env.get("BUILD_JOB_RESULT") != "success" or env.get("BUILD_STATE") != "success":
        return "failure", env.get("BUILD_DESCRIPTION") or "sandboxed merge-group build did not complete"
    if env.get("PUBLICATION_REQUIRED") == "true":
        state, description = wait(int(env["GITHUB_RUN_ID"]), int(env["GITHUB_RUN_ATTEMPT"]))
    else:
        state, description = "success", "sandboxed build passed (cache upload is not configured)"
    if state == "success" and env.get("BORS_STAGING") == "true":
        try:
            batch_id = int(env["BORS_BATCH_ID"])
            branch = env["BORS_BASE_REF"]
            candidate_ref(observe(batch_id, branch), env["STATUS_SHA"], env["BORS_BASE_SHA"],
                          batch_id=batch_id, branch=branch)
        except (OSError, ValueError, KeyError, TypeError):
            return "failure", "bors generation is stale or its authority is unavailable; redispatch current batch"
    return state, description


def main():
    env = os.environ
    revision = env.get("STATUS_SHA")
    if not sha(revision):
        print("::error::cannot post a batch status without an exact commit SHA", file=sys.stderr)
        return 1
    try:
        state, description = terminal_state(env)
    except (OSError, ValueError, KeyError, TypeError) as error:
        state, description = "failure", "batch finalization failed: " + type(error).__name__
    payload = dict(state=state, context="build", description=description[:140],
                   target_url=f"https://github.com/{REPO}/actions/runs/{env['GITHUB_RUN_ID']}")
    deadline = time.monotonic() + POST_RETRY_SECONDS
    delay = 5
    while time.monotonic() < deadline:
        try:
            # Defense in depth for completed/canceled/rerun API states. This is a
            # best-effort check; GitHub does not make the GET and POST atomic.
            latest = api(f"/actions/runs/{env['GITHUB_RUN_ID']}")
            if latest["run_attempt"] != int(env["GITHUB_RUN_ATTEMPT"]):
                print("::notice::superseded run attempt will not overwrite its successor's status", flush=True)
                return 1
            if latest.get("conclusion") == "cancelled":
                payload.update(state="failure", description="batch workflow was canceled; redispatch current batch")
                state = "failure"
            api(f"/statuses/{revision}", payload)
            print(f"Posted build={state} on {revision}: {description}", flush=True)
            return 0 if state == "success" else 1
        except (OSError, ValueError, KeyError) as error:
            print(f"::warning::terminal status POST failed: {type(error).__name__}", flush=True)
            headers = getattr(error, "headers", None)
            retry_after = headers.get("Retry-After") if headers else None
            requested_delay = delay
            if retry_after:
                try:
                    requested_delay = max(0, int(retry_after))
                except ValueError:
                    try:
                        requested_delay = max(0, parsedate_to_datetime(retry_after).timestamp() - time.time())
                    except (ValueError, TypeError, OverflowError):
                        pass
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                break
            time.sleep(min(max(1, requested_delay), remaining))
            delay = min(delay * 2, 30)
    print("::error::terminal status could not be posted; inspect GitHub API availability", file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
