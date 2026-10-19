"""Reconcile the status label and the Zulip post of every PR with activity since a point in time.

Usage: batch.py --since <ISO time> [--pr <number>]... [--state-in FILE] [--state-out FILE] [--dry-run]

--since supplies the fallback boundary when no checkpoint is available.

pr-status.yml runs this once per burst of PR events instead of once per event. Its concurrency
group admits one run at a time and keeps only the newest waiting one, so a burst of events costs at
most two runs. A checkpoint preserves pending PRs and the discovery boundary,
covering collapsed events without repeating a completed prefix after an interruption.

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
the run. The next run resumes its pending work; only finishing the scan advances its watermark. A single
PR's failure does not: that PR is handed to the next run through --state-out/--state-in and retried
up to MAX_RETRIES times, so one broken PR cannot hold every later run back.

Checkpoints contain PR numbers, retry counts, UTC window boundaries and a finite quota
deadline; no PR bodies or credentials. A forced runner loss before artifact upload can
repeat work from the last uploaded checkpoint. Missing state uses the workflow fallback.

Requires authenticated gh, TAUCETI_REVIEW_RUNNER (for labels), and ZULIP_EMAIL/ZULIP_API_KEY.
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import math
from pathlib import Path
import threading
import time
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


def updated_prs(since: str, completed=None) -> tuple[list[int], set[int]]:
    """PRs whose updated_at is at or after `since`, newest first, and those of them created at or
    after `since`. Paging stops after reaching older activity. ``completed`` maps
    PR numbers to the start times of finished checks; older updates are skipped.
    Same-second updates remain eligible to avoid losing concurrent changes.
    """
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
            # Skip only updates older than a finished check's start. Writes
            # during the check may cause one extra reconciliation on resume.
            # Same-second updates remain eligible because ordering is unknown.
            if completed and updated < completed.get(number, ''):
                continue
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


def touched_by_runs(since: str, heads: dict[str, list[int]], completed=None) -> tuple[set[int], set[str]]:
    """PRs whose pr-build or Review runs moved since `since`, and the heads with a pr-build run
    still queued or in progress (whose CI therefore reads as running).

    ``completed`` filters activity older than the start of a finished PR check;
    running flags remain current even when no new reconciliation is needed.
    """
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
                    prs.update(n for n in heads[r["head_sha"]]
                               if not completed or r['updated_at'] >= completed.get(str(n), ''))
                    if workflow == "pr-build.yml" and status != "completed":
                        running.add(r["head_sha"])
    return prs, running


def running_prs(heads: dict[str, list[int]], running: set[str], number: int) -> bool:
    return any(number in ns and s in running for s, ns in heads.items())


def load_progress(path, since):
    """Load a validated checkpoint, or start at the fallback window boundary.

    Record pending PRs, a completed discovery boundary, and the start times of
    finished PR checks. A drained batch advances its watermark to that boundary.
    Resumed batches discover newer activity but skip updates older than the
    start of a finished check, so changes during its reads remain eligible.
    """
    state = {"version": 1, "watermark": since, "active": None, "retry": {}, "blocked_until": 0}
    if path and Path(path).is_file():
        loaded = json.loads(Path(path).read_text())
        # Migrate the former retry-only artifact on the first deployment.
        if isinstance(loaded, dict) and all(k.isdigit() for k in loaded):
            state['retry'] = loaded
        else:
            state = loaded
    if not isinstance(state, dict) or state.get('version') != 1:
        raise ValueError('Invalid progress version')
    def timestamp(value):
        if not isinstance(value, str):
            raise ValueError('Invalid progress timestamp')
        parsed = dt.datetime.fromisoformat(value.replace('Z', '+00:00'))
        if parsed.utcoffset() != dt.timedelta(0):
            raise ValueError('Progress timestamps must be UTC')
    timestamp(state['watermark'])
    blocked = state['blocked_until']
    if type(blocked) not in (int, float) or not 0 <= blocked < math.inf:
        raise ValueError('Invalid quota deadline')
    retry = state['retry']
    if not isinstance(retry, dict) or any(not k.isdigit() or int(k) <= 0 or
            type(v) is not int or not 1 <= v <= MAX_RETRIES for k, v in retry.items()):
        raise ValueError('Invalid retry queue')
    active = state['active']
    if active is not None:
        timestamp(active['started_at'])
        completed = active['completed']
        if not isinstance(completed, dict):
            raise ValueError('Invalid completion records')
        for number, finished in completed.items():
            if not number.isdigit() or int(number) <= 0:
                raise ValueError('Invalid completed PR')
            timestamp(finished)
        for field in ('pending', 'opened'):
            numbers = active[field]
            if not isinstance(numbers, list) or any(type(n) is not int or n <= 0 for n in numbers) or len(set(numbers)) != len(numbers):
                raise ValueError('Invalid pending PRs')
        if not set(active['opened']) <= set(active['pending']):
            raise ValueError('Opened PRs must still be pending')
    return state


def save_progress(path, state):
    """Atomically checkpoint pending work, retries and this process's quota hold.

    Merge core's quota deadline into state and atomically replace ``path``.
    A missing path suppresses the file write. Callers must hold the worker lock
    while workers are active. The workflow uploads the file even on failure.
    """
    state['blocked_until'] = max(state['blocked_until'], core._BLOCKED_UNTIL)
    if path:
        target = Path(path)
        target.parent.mkdir(parents=True, exist_ok=True)
        temporary = target.with_suffix('.tmp')
        temporary.write_text(json.dumps(state, sort_keys=True))
        temporary.replace(target)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--since", required=True, help="fallback window start, ISO-8601 UTC")
    ap.add_argument("--pr", type=int, action="append", default=[], help="a PR to reconcile regardless")
    ap.add_argument("--dry-run", action="store_true", help="list work; write nothing")
    ap.add_argument("--state-in", help="previous progress/retries JSON checkpoint")
    ap.add_argument("--state-out", help="where to checkpoint progress, including on failure")
    args = ap.parse_args(argv)
    if any(number <= 0 for number in args.pr):
        ap.error('--pr must be a positive PR number')
    try:
        state = load_progress(args.state_in, args.since)
    except (OSError, ValueError, KeyError, TypeError):
        log('::warning::Invalid PR-status checkpoint; rebuilding from the fallback window')
        state = load_progress(None, args.since)
    output = None if args.dry_run else args.state_out
    lock = threading.Lock()
    try:
        if state['blocked_until'] > time.time():
            log(f"deferred until epoch {state['blocked_until']}; pending work retained")
            return 0 if args.dry_run else 1
        if state['active'] is None:
            started = iso(dt.datetime.now(dt.timezone.utc))
            since = iso(dt.datetime.fromisoformat(state['watermark'].replace('Z', '+00:00')) - dt.timedelta(minutes=2))
            heads = open_heads()
            by_update, opened = updated_prs(since)
            by_runs, running = touched_by_runs(since, heads)
            ordered = list(dict.fromkeys(args.pr + by_update + sorted(by_runs) + sorted(int(n) for n in state['retry'])))
            state['active'] = {"started_at": started, "pending": ordered,
                               "opened": sorted(set(ordered) & opened), "completed": {}}
        else:
            active = state['active']
            discovered = iso(dt.datetime.now(dt.timezone.utc))
            heads = open_heads()
            # Include collapsed events since discovery, but omit activity known
            # to precede the start of an already completed reconciliation.
            since = iso(dt.datetime.fromisoformat(active['started_at'].replace('Z', '+00:00')) - dt.timedelta(minutes=2))
            by_update, newly_opened = updated_prs(since, active['completed'])
            by_runs, running = touched_by_runs(since, heads, active['completed'])
            active['pending'] = list(dict.fromkeys(args.pr + active['pending'] + by_update + sorted(by_runs)))
            active['opened'] = sorted(set(active['opened']) | (newly_opened & set(active['pending'])))
            # Only advance after both discovery streams were read completely.
            active['started_at'] = discovered
        active = state['active']
        ordered, opened = list(active['pending']), set(active['opened'])
        log(f"scan {active['started_at']}: {len(ordered)} pending PRs; {len(state['retry'])} queued retries")
        if args.dry_run:
            for number in ordered:
                log(f"would reconcile #{number}")
            return 0
        save_progress(output, state)
        email, api_key = (os.environ.get('ZULIP_EMAIL') or '').strip(), (os.environ.get('ZULIP_API_KEY') or '').strip()
        if not (email and api_key):
            return zulip.fail_config('ZULIP_EMAIL / ZULIP_API_KEY not set (no bot configured)')
        z = zulip.Zulip(email, api_key, (os.environ.get('ZULIP_SITE') or 'https://leanprover.zulipchat.com').strip())
        try:
            bot_id = z.my_user_id()
        except zulip.ConfigError as exc:
            return zulip.fail_config(str(exc))
        stop, failures = [], []

        def one(number):
            if stop:
                return
            failed = False
            checked_from = iso(dt.datetime.now(dt.timezone.utc))
            try:
                labels.reconcile(str(number))
            except core.RateLimited as exc:
                stop.append(('quota', str(exc)))
                return
            except Exception as exc:
                failed = True
                log(f"PR #{number}: label reconciliation failed: {exc}")
            try:
                ci = 'running' if running_prs(heads, running, number) else None
                zulip.reconcile(z, str(number), number in opened, ci, bot_id=bot_id, create_if_open=True)
            except zulip.ConfigError as exc:
                stop.append(('config', str(exc)))
                return
            except core.RateLimited as exc:
                stop.append(('quota', str(exc)))
                return
            except Exception as exc:
                failed = True
                log(f"PR #{number}: Zulip reconciliation failed: {exc}")
            with lock:
                key = str(number)
                if failed:
                    failures.append(number)
                    attempt = state['retry'].get(key, 0) + 1
                    if attempt <= MAX_RETRIES:
                        state['retry'][key] = attempt
                    else:
                        state['retry'].pop(key, None)
                        log(f"::warning::giving up on PR #{number} after {MAX_RETRIES} retries")
                else:
                    state['retry'].pop(key, None)
                active['completed'][key] = checked_from
                active['pending'].remove(number)
                if number in active['opened']:
                    active['opened'].remove(number)
                save_progress(output, state)

        with ThreadPoolExecutor(max_workers=PARALLEL) as pool:
            list(pool.map(one, ordered))
        if stop:
            log(f"stopping: {stop[0][1]}; {len(active['pending'])} PRs retained")
            config = next((reason for kind, reason in stop if kind == 'config'), None)
            return zulip.fail_config(config) if config is not None else 1
        # Advance to a completely read discovery boundary, never merely to
        # this workflow run's creation time.
        state['watermark'] = active['started_at']
        state['active'] = None
        log(f"done: {len(ordered)} PRs; failures queued for retry: {failures}")
        return 0
    finally:
        if not args.dry_run:
            save_progress(output, state)


if __name__ == "__main__":
    sys.exit(main())
