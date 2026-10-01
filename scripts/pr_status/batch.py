"""Reconcile the status label and the Zulip post of every PR with activity since a point in time.

Usage: batch.py --since <ISO time> [--pr <number>]...

pr-status.yml runs this once per burst of PR events instead of once per event. Its concurrency
group admits one run at a time and keeps only the newest waiting one, so a burst of events costs at
most two runs; each run reconciles every PR touched since the previous successful run started,
which covers the events whose own runs were collapsed away.

A PR has had activity since T if any of these holds:

  - the PR (or its issue: comments, labels, edits) was updated at or after T;
  - a pr-build or Review run for its head was created or updated at or after T (a commit status
    does not move the PR's updated_at, so build results are found through the runs);
  - it was named with --pr (the event that started this run).

For each such PR it applies exactly the per-PR reconciliation the per-event workflows used:
labels.reconcile, then zulip.reconcile. Two things the events used to supply are derived from
current state instead:

  - a PR whose pr-build run for its head is still queued or running shows CI as running (what
    zulip-pr-status.yml painted on pr-build's `requested` event);
  - the Zulip post is created if missing only while the PR is open (`create_if_open`), which is
    what the opened/reopened events did, without letting later churn on a closed PR resurrect it.

A rate limit or a configuration error (missing Zulip credentials, a listing past GitHub's cap) fails
the run, so it is not counted as the watermark and the next run covers its window again. A single
PR's failure does not: that PR is handed to the next run through --retry-out/--retry-in and retried
up to MAX_RETRIES times, so one broken PR cannot hold every later run back.

Requires authenticated gh, TAUCETI_REVIEW_RUNNER (for labels), and ZULIP_EMAIL/ZULIP_API_KEY.
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import sys
from concurrent.futures import ThreadPoolExecutor

import core
import labels
import zulip

REPO = core.REPO
# Runs finish within GitHub's six-hour job limit, so a run that completed after `since` was created
# no earlier than this before it.
RUN_LOOKBACK = dt.timedelta(hours=7)
# PRs reconciled at once. Each takes a few seconds, nearly all of it waiting on GitHub and Zulip; at
# busy times some fifty PRs are touched in ten minutes, which one at a time would barely keep up with.
# A PR's own label and Zulip steps stay in order; only different PRs overlap.
PARALLEL = 4
MAX_RETRIES = 5


def log(msg):
    print(msg, flush=True)


def iso(t: dt.datetime) -> str:
    return t.astimezone(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def lines(path: str, jq: str, paginate: bool = False) -> list[str]:
    return [l for l in core.gh_api(path, jq=jq, paginate=paginate).splitlines() if l]


def updated_prs(since: str) -> tuple[list[int], set[int]]:
    """PRs whose updated_at is at or after `since`, newest first, and those of them created at or
    after `since`. The list is sorted by update time, so paging stops at the first page that reaches
    back past `since`."""
    out, opened = [], set()
    page = 1
    while True:
        rows = lines(f"/repos/{REPO}/pulls?state=all&sort=updated&direction=desc&per_page=100&page={page}",
                     jq='.[] | "\\(.number) \\(.updated_at) \\(.created_at)"')
        done = False
        for row in rows:
            number, updated, created = row.split()
            if updated < since:
                done = True
                break
            out.append(int(number))
            if created >= since:
                opened.add(int(number))
        if done or len(rows) < 100:
            return out, opened
        page += 1


def open_heads() -> dict[str, list[int]]:
    """Head sha -> the open PRs with that head (usually one; stacked or duplicate PRs can share)."""
    heads: dict[str, list[int]] = {}
    for row in lines(f"/repos/{REPO}/pulls?state=open&per_page=100", jq='.[] | "\\(.head.sha) \\(.number)"',
                     paginate=True):
        sha, number = row.split()
        heads.setdefault(sha, []).append(int(number))
    return heads


def workflow_runs(workflow: str, query: str) -> list[dict]:
    # A filtered listing stops at 1,000 results however far it is paged; beyond that runs would go
    # missing silently, so refuse instead (the run fails and the next covers the window again).
    total = int(core.gh_api(f"/repos/{REPO}/actions/workflows/{workflow}/runs?{query}&per_page=1",
                            jq=".total_count").strip() or 0)
    if total >= 1000:
        raise core.RateLimited(f"{workflow} {query}: {total} runs, past the listing's 1,000-result cap")
    rows = lines(f"/repos/{REPO}/actions/workflows/{workflow}/runs?{query}&per_page=100",
                 jq='.workflow_runs[] | {head_sha, status, created_at, updated_at} | tojson', paginate=True)
    return [json.loads(r) for r in rows]


ACTIVE = ("requested", "queued", "pending", "waiting", "in_progress")


def touched_by_runs(since: str, heads: dict[str, list[int]]) -> tuple[set[int], set[str]]:
    """PRs whose pr-build or Review runs moved since `since`, and the heads with a pr-build run
    still queued or in progress (whose CI therefore reads as running)."""
    prs, running = set(), set()
    lookback = iso(dt.datetime.fromisoformat(since.replace("Z", "+00:00")) - RUN_LOOKBACK)
    # pr-build runs for PRs are pull_request_target runs; Review is started by workflow_run and
    # issue_comment events, so its runs are listed whatever their event.
    for workflow, event in (("pr-build.yml", "&event=pull_request_target"), ("review.yml", "")):
        for status in ACTIVE + ("completed",):
            # Completed runs by completion (updated_at), not creation: a long build created before
            # `since` may finish after it.
            query = f"status={status}{event}" + (f"&created=>={lookback}" if status == "completed" else "")
            runs = workflow_runs(workflow, query)
            for r in runs:
                if status == "completed" and r["updated_at"] < since:
                    continue
                if r["head_sha"] in heads:
                    prs.update(heads[r["head_sha"]])
                    if workflow == "pr-build.yml" and status != "completed":
                        running.add(r["head_sha"])
    return prs, running


def running_prs(heads: dict[str, list[int]], running: set[str], number: int) -> bool:
    return any(number in ns and s in running for s, ns in heads.items())


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--since", required=True, help="ISO-8601 UTC time")
    ap.add_argument("--pr", type=int, action="append", default=[], help="a PR to reconcile regardless")
    ap.add_argument("--dry-run", action="store_true", help="list the PRs that would be reconciled; write nothing")
    ap.add_argument("--retry-in", help="JSON {pr: failed attempts} from the previous run, to retry")
    ap.add_argument("--retry-out", help="where to write this run's {pr: failed attempts}")
    args = ap.parse_args(argv)

    heads = open_heads()
    by_update, opened = updated_prs(args.since)
    by_runs, running = touched_by_runs(args.since, heads)
    retry = {}
    if args.retry_in and os.path.exists(args.retry_in):
        try:
            retry = {int(k): int(v) for k, v in json.load(open(args.retry_in)).items()}
        except (ValueError, OSError):
            retry = {}
    ordered = list(dict.fromkeys(args.pr + by_update + sorted(by_runs) + sorted(retry)))
    log(f"since {args.since}: {len(ordered)} PRs to reconcile "
        f"({len(by_update)} updated, {len(by_runs)} with build or review runs, {len(args.pr)} named)")

    if args.dry_run:
        log(f"opened in the window: {sorted(opened)}")
        for number in ordered:
            log(f"would reconcile #{number}" + (" (CI running)" if running_prs(heads, running, number) else ""))
        return 0

    email = (os.environ.get("ZULIP_EMAIL") or "").strip()
    api_key = (os.environ.get("ZULIP_API_KEY") or "").strip()
    if not (email and api_key):
        return zulip.fail_config("ZULIP_EMAIL / ZULIP_API_KEY not set (no bot configured)")
    z = zulip.Zulip(email, api_key, (os.environ.get("ZULIP_SITE") or "https://leanprover.zulipchat.com").strip())
    try:
        bot_id = z.my_user_id()
    except zulip.ConfigError as exc:
        return zulip.fail_config(str(exc))

    label_failures, zulip_failures, stop = [], [], []

    def one(number: int):
        if stop:
            return
        try:
            labels.reconcile(str(number))
        except core.RateLimited as exc:
            stop.append(f"rate limited: {exc}")
            return
        except Exception as exc:  # one PR's failure must not starve the rest
            label_failures.append(number)
            log(f"PR #{number}: label reconciliation failed: {exc}")
        ci = "running" if running_prs(heads, running, number) else None
        try:
            # A PR opened in this window gets its post unconditionally, as the `opened` event did;
            # any other gets one only while open, so churn on a closed PR never creates a late post.
            zulip.reconcile(z, str(number), number in opened, ci, bot_id=bot_id, create_if_open=True)
        except zulip.ConfigError as exc:
            stop.append(f"Zulip configuration: {exc}")
        except core.RateLimited as exc:
            stop.append(f"rate limited: {exc}")
        except Exception as exc:
            zulip_failures.append(number)
            log(f"PR #{number}: Zulip reconciliation failed: {exc}")

    with ThreadPoolExecutor(max_workers=PARALLEL) as pool:
        list(pool.map(one, ordered))
    if stop:
        if stop[0].startswith("Zulip"):
            return zulip.fail_config(stop[0])
        log(f"stopping: {stop[0]}")
        return 1
    log(f"done: {len(ordered)} PRs; label failures {label_failures}; Zulip failures {zulip_failures}")
    # A PR that failed is retried by the next run (up to MAX_RETRIES times) rather than failing this
    # one: a failed run would hold the watermark back, and one PR that keeps failing would then make
    # every later run redo an ever-growing window. Rate limits and configuration errors, which are
    # not about one PR, do fail the run (above).
    failed = set(label_failures) | set(zulip_failures)
    carry = {n: retry.get(n, 0) + 1 for n in failed if retry.get(n, 0) + 1 <= MAX_RETRIES}
    dropped = sorted(n for n in failed if n not in carry)
    if dropped:
        log(f"::warning::giving up on PRs after {MAX_RETRIES} failed attempts: {dropped} "
            "(the hourly sweep in pr-labels.yml still reconciles their labels)")
    if args.retry_out:
        with open(args.retry_out, "w") as fh:
            json.dump({str(k): v for k, v in carry.items()}, fh)
    return 0


if __name__ == "__main__":
    sys.exit(main())
