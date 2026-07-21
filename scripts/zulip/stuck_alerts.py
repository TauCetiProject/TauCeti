#!/usr/bin/env python3
"""Post *stuck-automation* alerts to a dedicated Zulip topic (Tau Ceti > Stuck PRs).

This is an EMERGENCY channel, not a "ask the humans for help" queue. Every alert
here means a piece of Tau Ceti's own automation was supposed to make progress and
could not unstick itself: a bump that will not cross a breaking change, a green PR
the merge machinery never merged, a scheduled job that stopped firing, main gone
red. The expected response to any alert is to FIX THE INFRASTRUCTURE (a script, a
workflow, a pin, a guard) so the situation cannot recur -- not to hand-hold one PR
and move on. If an alert can only ever be resolved by a human doing a one-off
favour, it does not belong here; see the "deliberately NOT alerted" list below.

Detectors (each names the infra failure it implies):

  1. stuck-bump      The last-known-good bump PR (branch hopscotch/lkg-bump) has a
                     RED `build` check and has been open >=24h. The daily bump
                     cannot cross a mathlib breaking change on its own; something
                     (a proof, scripts/lint-env.sh, a guard) needs a human fix.
  2. stale-pin       main's mathlib pin is >=4 days old. The bump has stopped
                     advancing (a wedged PR, an unresolved first-known-bad freeze,
                     or update.yml silently broken).
  3. stranded-pr     A PR that is in-scope (TauCeti/ + allowed roots, bump-guard
                     green for any pin change), `build` green, every blocking
                     rubric green at HEAD, not draft/hold, yet unmerged >=6h
                     (~6 merge-sweep cycles). auto-merge / the queue / merge-sweep
                     is broken.
  4. review-stuck    An open issue titled "Review stuck: PR #...": the review
                     engine self-flagged a PR it cannot resolve.
  5. dead-scheduler  A scheduled workflow is `disabled`, or its last run is older
                     than its cadence + slack. GitHub disabled the cron (60-day
                     inactivity), or it errors at dispatch.
  6. main-red        main's latest CI run concluded `failure`. The "main is always
                     green" invariant is broken.
  7. stale-fkb       A first-known-bad / mathlib-incompatibility tracking issue
                     (bot-authored) has been open >=3 days. A regression against
                     TauCeti nobody has landed the fix for.

Deliberately NOT alerted (normal backlog, not stuck automation -- alerting on
these would cheapen the topic and train people to ignore it):
  * a PR awaiting its first review verdict -- CI review generation is off by
    default (CI_REVIEW_ENABLED); reviews are run by humans / the worker on their
    own cadence, so "no verdict yet" is expected, not stuck;
  * a PR with changes-requested that nobody addressed -- housekeeping.py retires
    these after STALE_DAYS;
  * open roadmap / help-wanted issues -- that IS the ask-the-humans queue.

Idempotent, like zulip_pr_status.py: exactly one bot-owned message per active
alert key, tagged with a hidden `<!--stuck:v1 <key>-->` marker. Each run
reconciles the topic against the live GitHub state -- a new alert posts a message,
an alert that has cleared has its message edited to a resolved (checkmark) form,
and an unchanged alert is left exactly as-is (so a persisting emergency is not
re-posted every hour). Editing never notifies; only a genuinely NEW alert makes a
new message appear. There are no @-mentions (the topic is watched, not pinged).

Run status mirrors the healthcheck philosophy: the ALERTS are the signal, not the
run's red/green, so a run that successfully checks and posts exits 0 even when it
raised ten alerts. Only a persistent Zulip CONFIG break (bad key, forbidden bot,
not subscribed) fails the run loudly -- if we cannot post, the emergency channel
itself is down, and that must not be silent.

Usage:
    stuck_alerts.py            # reconcile all detectors against the topic
    stuck_alerts.py --dry-run  # print the alerts it would post; touch no Zulip

Environment:
    ZULIP_API_KEY, ZULIP_EMAIL, ZULIP_SITE   bot credentials (required)
    ZULIP_CHANNEL                            default "Tau Ceti"
    ZULIP_TOPIC                              default "Stuck PRs"
    GH_REPO                                  default "TauCetiProject/TauCeti"
    GH_TOKEN / GITHUB_TOKEN                  used by `gh` for the GitHub API

Only python3's standard library and an authenticated `gh` CLI are required.
The Zulip client, credential handling, and sanitizer are reused verbatim from
zulip_pr_status.py (same package dir); this file adds only the detectors and the
alert-reconciliation loop. Pointing that shared client at a different topic is the
module's own documented mechanism: ZULIP_TOPIC (set to "Stuck PRs" by the
stuck-alerts workflow) is read at import, so send/find target this topic.
"""

import base64
import datetime
import json
import os
import re
import sys

# Reuse the proven Zulip client + helpers. Because ZULIP_TOPIC is read at import
# time, the workflow sets it to "Stuck PRs" and every send/narrow below targets
# this topic without any change to zulip_pr_status.py.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import zulip_pr_status as zp  # noqa: E402

REPO = zp.REPO
MARKER_RE = re.compile(r"<!--stuck:v1 ([^>]+)-->")
LKG_BRANCH = "hopscotch/lkg-bump"  # keep in sync with update.yml's LKG_BRANCH

# --- thresholds (hours unless noted) -----------------------------------------
# Each scheduler threshold is ~2-3x the workflow's cadence, generous enough to
# ride out GitHub's routine scheduled-run delays without false-firing.
BUMP_STUCK_HOURS = 24
PIN_STALE_DAYS = 4
STRANDED_HOURS = 6
FKB_STALE_DAYS = 3
SCHEDULERS = {
    # workflow file            (human name,               max age hours)
    "update.yml":            ("daily mathlib bump",       30),
    "pages.yml":             ("pages / doc-gen publish",  30),
    "housekeeping.yml":      ("queue housekeeping",        7),
    "zulip-healthcheck.yml": ("zulip healthcheck",        15),
    "merge-sweep.yml":       ("merge sweep",               4),
}
# A PR carrying any of these labels is intentionally parked; never "stranded".
HOLD_LABELS = {"keep", "hold", "wip", "human", "do-not-close", "blocked"}
# First-known-bad / incompatibility tracking issue, bot-authored. Heuristic:
# confirm against the first real occurrence and tighten if it over/under-matches.
FKB_AUTHOR_PREFIX = "tauceti-review-bot"
FKB_TITLE_RE = re.compile(r"incompat|first[- ]known[- ]bad|known[- ]bad", re.I)


def now_utc():
    # new Date() / Date.now() are fine in plain python; the workflow runs live.
    return datetime.datetime.now(datetime.timezone.utc)


def parse_ts(s):
    """Parse a GitHub ISO-8601 UTC timestamp (e.g. 2026-07-20T19:06:08Z)."""
    return datetime.datetime.fromisoformat(s.replace("Z", "+00:00"))


def hours_since(s):
    return (now_utc() - parse_ts(s)).total_seconds() / 3600.0


def gh_json(path, jq=None, paginate=False):
    """gh_api for a jq that yields a JSON object or array (parsed and returned).

    `gh --jq` prints an object/array as JSON, so json.loads applies. Do NOT use
    this for a scalar/string jq result -- gh prints those RAW (unquoted), which is
    not JSON; use gh_scalar for those. Returns None on empty output.
    """
    out = zp.gh_api(path, jq=jq, paginate=paginate).strip()
    if not out:
        return None
    return json.loads(out)


def gh_scalar(path, jq, paginate=False):
    """gh_api for a jq that yields a scalar/string, returned as a stripped str.

    Mirrors how zulip_pr_status reads statuses: `gh --jq '.foo // ""'` prints the
    raw string value, so we take it as text (never json.loads it)."""
    return zp.gh_api(path, jq=jq, paginate=paginate).strip()


def build_status(head):
    """(state, updated_at) of the newest `build` commit status, or (None, None).

    state is the raw GitHub status state: pending|success|failure|error.
    """
    rows = gh_json(
        f"/repos/{REPO}/commits/{head}/statuses",
        jq='[.[] | select(.context == "build")] | sort_by(.updated_at)'
           ' | last | {state: (.state // ""), updated_at: (.updated_at // "")}',
    )
    if not rows or not rows.get("state"):
        return None, None
    return rows["state"], rows["updated_at"] or None


def status_state(head, context):
    """Newest commit-status state for `context` on `head` ("" if none)."""
    return gh_scalar(
        f"/repos/{REPO}/commits/{head}/statuses",
        jq=f'[.[] | select(.context == "{context}")] | sort_by(.updated_at)'
           ' | last | .state // ""',
    )


# ----- detectors --------------------------------------------------------------
# Each returns a list of alert dicts {key, title, body}. `key` is stable across
# runs so the same ongoing situation reconciles to the same Zulip message.

def detect_stuck_bump():
    prs = gh_json(
        f"/repos/{REPO}/pulls?state=open&head=TauCetiProject:{LKG_BRANCH}&per_page=5",
        jq='[.[] | {number, head: .head.sha, created_at}]',
    ) or []
    out = []
    for pr in prs:
        state, _ = build_status(pr["head"])
        if state in ("failure", "error") and hours_since(pr["created_at"]) >= BUMP_STUCK_HOURS:
            age = int(hours_since(pr["created_at"]) // 24)
            out.append({
                "key": f"stuck-bump/{pr['number']}",
                "title": f"Mathlib bump wedged — PR #{pr['number']} build red",
                "body": (
                    f"The last-known-good bump PR "
                    f"https://github.com/{REPO}/pull/{pr['number']} has a red `build` "
                    f"check and has been open ~{age}d. The daily bump cannot cross a "
                    f"mathlib breaking change on its own.\n\n"
                    f"**Fix:** open the failing build, land the fix it needs (a proof, "
                    f"`scripts/lint-env.sh`, a guard) together with the pin move in one "
                    f"human-owned PR, so the bump can resume."),
            })
    return out


def detect_stale_pin():
    # Staleness is "how long since the pin last MOVED", not the age of the pinned
    # commit: right after a bump to an LKG commit that itself lags master, the
    # pinned commit can be days old while the bump is perfectly healthy. The daily
    # bump rewrites lake-manifest.json whenever mathlib advances, so the manifest's
    # last-change date on main is a direct proxy for the bump cadence.
    date = gh_scalar(f"/repos/{REPO}/commits?path=lake-manifest.json&sha=main&per_page=1",
                     jq='.[0].commit.committer.date // ""')
    if not date:
        return []
    days = hours_since(date) / 24.0
    if days < PIN_STALE_DAYS:
        return []
    rev = ""
    content = gh_scalar(f"/repos/{REPO}/contents/lake-manifest.json?ref=main", jq='.content')
    if content:
        try:  # contents is base64 with embedded newlines; b64decode discards them
            data = json.loads(base64.b64decode(content).decode())
            rev = next((p["rev"] for p in data.get("packages", [])
                        if p["name"] == "mathlib"), "")
        except Exception:
            rev = ""
    pin = f" (mathlib `{rev[:10]}`)" if rev else ""
    return [{
        "key": "stale-pin",
        "title": f"Mathlib pin has not moved in {int(days)}d",
        "body": (
            f"`lake-manifest.json` on main{pin} last changed ~{int(days)}d ago; the "
            f"daily bump has stopped advancing.\n\n"
            f"**Fix:** find why — a wedged bump PR (see any stuck-bump alert), an "
            f"unresolved first-known-bad freeze, or `update.yml` failing — and clear "
            f"it so `hopscotch/lkg-bump` can move forward again."),
    }]


def detect_stranded_prs():
    prs = gh_json(
        f"/repos/{REPO}/pulls?state=open&base=main&per_page=100",
        jq='[.[] | {number, head: .head.sha, draft, '
           'labels: [.labels[].name], title}]',
        paginate=True,
    ) or []
    out = []
    for pr in prs:
        if pr.get("draft"):
            continue
        if HOLD_LABELS.intersection(n.lower() for n in pr.get("labels", [])):
            continue
        head = pr["head"]
        state, updated = build_status(head)
        if state != "success" or not updated or hours_since(updated) < STRANDED_HOURS:
            continue
        # Every blocking rubric green AT HEAD (mirrors auto-merge's ledger read).
        if zp.review_emoji(zp.scoreboard_meta(pr["number"]), head) != "check":
            continue
        # In-scope: TauCeti/ + allowed roots only; a human-owned path legitimately
        # does not auto-merge, so it is NOT stranded. Fail closed on any doubt.
        files = gh_json(f"/repos/{REPO}/pulls/{pr['number']}/files?per_page=300",
                        jq='[.[].filename]', paginate=True) or []
        if not files:
            continue
        allowed_roots = {"TauCeti.lean", "lake-manifest.json", "lean-toolchain"}
        touches_pin = any(f in ("lake-manifest.json", "lean-toolchain") for f in files)
        if not all(f.startswith("TauCeti/") or f in allowed_roots for f in files):
            continue
        # A pin change must have bump-guard green, exactly as the merge gate requires.
        if touches_pin and status_state(head, "bump-guard") != "success":
            continue
        age = int(hours_since(updated))
        out.append({
            "key": f"stranded-pr/{pr['number']}",
            "title": f"Green PR not merging — #{pr['number']}",
            "body": (
                f"https://github.com/{REPO}/pull/{pr['number']} is in-scope, `build` "
                f"green, and every blocking rubric green at HEAD, yet has sat unmerged "
                f"~{age}h while merge-sweep runs hourly.\n\n"
                f"**Fix:** the merge path is broken — check `auto-merge.yml`, the merge "
                f"queue, and `merge-sweep.yml` (and the pinned TauCetiReview merge-only "
                f"/ merge-sweep workflow) for why a ready PR is not being taken."),
        })
    return out


def detect_review_stuck():
    issues = gh_json(
        f"/repos/{REPO}/issues?state=open&per_page=100",
        jq='[.[] | select(.pull_request == null) '
           '| select(.title | test("^Review stuck")) | {number, title}]',
        paginate=True,
    ) or []
    return [{
        "key": f"review-stuck/{i['number']}",
        "title": zp.zulip_sanitize(i["title"]),
        "body": (
            f"The review engine self-flagged a PR it cannot resolve: "
            f"https://github.com/{REPO}/issues/{i['number']}\n\n"
            f"**Fix:** this is not a one-off review to nudge — the engine hit a state "
            f"it has no rule for (a rubric contradiction, an error loop). Fix the "
            f"review logic / rubric in TauCetiReview so it cannot re-wedge."),
    } for i in issues]


def detect_dead_schedulers():
    out = []
    for wf, (name, max_hours) in SCHEDULERS.items():
        meta = gh_json(f"/repos/{REPO}/actions/workflows/{wf}",
                       jq='{state: (.state // ""), id: .id}')
        if not meta or not meta.get("state"):
            continue
        if meta["state"] != "active":
            out.append({
                "key": f"dead-scheduler/{wf}",
                "title": f"Scheduler disabled — {name}",
                "body": (
                    f"`{wf}` is `{meta['state']}` (GitHub disables a cron after 60 days "
                    f"of repo inactivity, or on repeated failure).\n\n"
                    f"**Fix:** re-enable it (`gh workflow enable {wf}`) and address the "
                    f"underlying cause so it stays scheduled."),
            })
            continue
        last = gh_scalar(
            f"/repos/{REPO}/actions/workflows/{wf}/runs?per_page=1",
            jq='.workflow_runs[0].created_at // ""')
        if not last:
            continue
        age = hours_since(last)
        if age >= max_hours:
            out.append({
                "key": f"dead-scheduler/{wf}",
                "title": f"Scheduler stalled — {name}",
                "body": (
                    f"`{wf}` last ran ~{int(age)}h ago (cadence + slack is {max_hours}h). "
                    f"Its schedule has stopped firing.\n\n"
                    f"**Fix:** check the Actions tab for a dispatch error or an org-level "
                    f"disable; restore the cron so `{name}` runs on cadence again."),
            })
    return out


def detect_main_red():
    run = gh_json(
        f"/repos/{REPO}/actions/workflows/ci.yml/runs?branch=main&status=completed&per_page=1",
        jq='.workflow_runs[0] | {conclusion: (.conclusion // ""), sha: (.head_sha // "")}')
    if not run or run.get("conclusion") != "failure":
        return []
    sha = run.get("sha") or ""
    return [{
        "key": "main-red",
        "title": "main is RED",
        "body": (
            f"The latest CI run on `main` (`{sha[:10]}`) concluded `failure`. The "
            f"\"main is always green\" invariant is broken.\n\n"
            f"**Fix:** identify the merge or environment change that broke it and land a "
            f"revert or forward-fix immediately — a red main blocks every bump and merge."),
    }]


def detect_stale_fkb():
    issues = gh_json(
        f"/repos/{REPO}/issues?state=open&per_page=100",
        jq='[.[] | select(.pull_request == null) '
           '| {number, title, created_at, author: (.user.login // "")}]',
        paginate=True,
    ) or []
    out = []
    for i in issues:
        if not i["author"].startswith(FKB_AUTHOR_PREFIX):
            continue
        if not FKB_TITLE_RE.search(i["title"]):
            continue
        if hours_since(i["created_at"]) / 24.0 < FKB_STALE_DAYS:
            continue
        days = int(hours_since(i["created_at"]) / 24.0)
        out.append({
            "key": f"stale-fkb/{i['number']}",
            "title": f"Mathlib incompatibility unresolved {days}d — #{i['number']}",
            "body": (
                f"A first-known-bad tracking issue has been open ~{days}d: "
                f"https://github.com/{REPO}/issues/{i['number']}. The pin is frozen at "
                f"the last-known-good commit until this is fixed.\n\n"
                f"**Fix:** land the fix PR pinned at the first-known-bad commit so the "
                f"freeze lifts and the daily bump resumes toward master."),
        })
    return out


DETECTORS = [
    detect_stuck_bump, detect_stale_pin, detect_stranded_prs, detect_review_stuck,
    detect_dead_schedulers, detect_main_red, detect_stale_fkb,
]


def collect_alerts():
    """Run every detector; a detector that errors is logged and skipped so one
    flaky GitHub call cannot suppress every other alert."""
    alerts = []
    for det in DETECTORS:
        try:
            alerts.extend(det() or [])
        except Exception as exc:  # transient API/parse hiccup in one detector
            zp.log(f"detector {det.__name__} failed (non-fatal): {exc}")
    return alerts


# ----- reconcile against the topic -------------------------------------------

def alert_content(a):
    return f"\U0001f534 **{a['title']}**\n\n{a['body']}\n\n<!--stuck:v1 {a['key']}-->"


def resolved_content(message):
    """Rewrite an existing alert message to its cleared form, keeping the marker
    so future runs recognise it as already-resolved and leave it alone."""
    body = message["content"]
    m = MARKER_RE.search(body)
    key = m.group(1) if m else "?"
    # Keep the original title line for context; swap the red circle for a check.
    title = "(cleared)"
    for line in body.splitlines():
        if line.startswith("\U0001f534 **") or line.startswith("**"):
            title = line.split("**")[1] if "**" in line else title
            break
    return (f"✅ **{title}** — cleared\n\n_No longer active as of the latest "
            f"check._\n\n<!--stuck:v1 {key}-->")


def reconcile(z, alerts, dry_run):
    bot_id = z.my_user_id()
    msgs = z.get_messages([
        {"operator": "channel", "operand": zp.CHANNEL},
        {"operator": "topic", "operand": zp.TOPIC},
    ])
    existing = {}
    for m in msgs:
        if m["sender_id"] != bot_id:
            continue
        mk = MARKER_RE.search(m["content"])
        if mk:
            existing[mk.group(1)] = m

    active = {a["key"]: a for a in alerts}

    for key, a in active.items():
        content = alert_content(a)
        msg = existing.get(key)
        if msg is None:
            zp.log(f"NEW alert {key}: {a['title']}")
            if not dry_run:
                z.send_message(content)
        elif msg["content"] != content:
            # Content drifted (title/body wording changed, or it was resolved and
            # has re-fired); refresh in place so it reads correctly, no re-ping.
            zp.log(f"refresh alert {key}")
            if not dry_run:
                z.update_message(msg["id"], content)
        else:
            zp.log(f"ongoing alert {key} (unchanged)")

    for key, msg in existing.items():
        if key in active:
            continue
        if msg["content"].startswith("✅"):
            continue  # already marked resolved
        zp.log(f"RESOLVED alert {key}")
        if not dry_run:
            z.update_message(msg["id"], resolved_content(msg))


def main(argv):
    dry_run = "--dry-run" in argv[1:]

    alerts = collect_alerts()
    zp.log(f"{len(alerts)} active alert(s): {sorted(a['key'] for a in alerts)}")

    email = (os.environ.get("ZULIP_EMAIL") or "").strip()
    api_key = (os.environ.get("ZULIP_API_KEY") or "").strip()
    site = (os.environ.get("ZULIP_SITE") or "https://leanprover.zulipchat.com").strip()
    if dry_run and not (email and api_key):
        for a in alerts:
            print("\n" + alert_content(a))
        return 0
    if not (email and api_key):
        return zp.fail_config("ZULIP_EMAIL / ZULIP_API_KEY not set (no bot configured)")

    z = zp.Zulip(email, api_key, site)
    try:
        reconcile(z, alerts, dry_run)
    except zp.ConfigError as exc:  # emergency channel itself is down: fail loud
        return zp.fail_config(str(exc))
    except Exception as exc:  # a transient Zulip hiccup is cosmetic; self-heals
        zp.log(f"reconcile failed (non-fatal): {exc}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
