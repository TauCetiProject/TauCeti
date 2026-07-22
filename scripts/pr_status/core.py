#!/usr/bin/env python3
"""Shared derivation of a TauCeti PR's status from GitHub truth.

This is the single place that reads what a PR's status *is* -- its lifecycle
(open / merged / closed), its `build` CI state, and its review state (from the
canonical `<!--tauceti-scoreboard-->` comment's meta JSON). Every status *sink*
imports it and renders that one truth its own way:

  * zulip.py   -> two independent groups of emoji reactions on the PR's message
  * labels.py  -> exactly one of the five status labels on the PR itself

Keeping the derivation here means the two sinks can never disagree about what a
PR's state is: they read the same `derive()` and only differ in how they show it.

The module is a pure library -- importing it has no side effects, writes nothing,
and needs only python3's standard library plus an authenticated `gh` CLI (via
GH_TOKEN / GITHUB_TOKEN). It reads GitHub; it never touches Zulip or labels.
"""

import json
import os
import re
import subprocess

REPO = os.environ.get("GH_REPO", "TauCetiProject/TauCeti")


# ----- GitHub truth (via the gh CLI, authenticated by GH_TOKEN) ---------------

def gh_api(path, jq=None, paginate=False):
    cmd = ["gh", "api", path]
    if paginate:
        cmd.append("--paginate")
    if jq is not None:
        cmd += ["--jq", jq]
    out = subprocess.run(cmd, capture_output=True, text=True)
    if out.returncode != 0:
        raise RuntimeError(f"gh api {path} failed: {out.stderr.strip()}")
    return out.stdout


def pr_state(pr):
    """{'state','merged','head','title'} for the PR.

    Prefer the triggering event's payload, passed in via PR_STATE/PR_HEAD/
    PR_MERGED/PR_TITLE (a workflow that has the pull_request object can set these
    from github.event.pull_request, so a close/merge needs no GitHub API call at
    all). Fall back to the REST API when they aren't set (the workflow_run and
    issue_comment triggers, and the backfill), where the payload is absent or
    isn't the PR we're reconciling.
    """
    env_state = os.environ.get("PR_STATE")
    env_head = os.environ.get("PR_HEAD")
    if env_state and env_head:
        return {
            "state": env_state,
            "merged": os.environ.get("PR_MERGED") == "true",
            "head": env_head,
            "title": os.environ.get("PR_TITLE") or f"PR #{pr}",
        }
    d = json.loads(gh_api(f"/repos/{REPO}/pulls/{pr}"))
    return {
        "state": d["state"],                 # "open" | "closed"
        "merged": bool(d.get("merged")),
        "head": d["head"]["sha"],
        "title": d.get("title") or f"PR #{pr}",
    }


def scoreboard_meta(pr):
    """The newest trusted scoreboard comment's meta JSON ({} if none).

    Trust mirrors round.sh: the <!--tauceti-scoreboard--> marker AND an author
    with repo association (OWNER/MEMBER/COLLABORATOR), so a random external
    comment cannot forge review state. Paginates so the canonical comment is
    found even on long PRs.
    """
    body = gh_api(
        f"/repos/{REPO}/issues/{pr}/comments?per_page=100",
        jq='[.[] | select(.body|contains("<!--tauceti-scoreboard-->"))'
           ' | select(.author_association|IN("OWNER","MEMBER","COLLABORATOR"))]'
           ' | sort_by(.updated_at) | last | .body // ""',
        paginate=True,
    )
    # With --paginate the jq runs per page, so take the last non-empty body.
    body = next((ln for ln in reversed(body.splitlines()) if ln.strip()), "")
    m = re.search(r"<!--tauceti-meta:v1 (.*)-->", body)
    if not m:
        return {}
    try:
        return json.loads(m.group(1))
    except json.JSONDecodeError:
        return {}


def ci_status(head):
    """'running' | 'success' | 'failure' | None from the `build` commit status."""
    state = gh_api(
        f"/repos/{REPO}/commits/{head}/statuses",
        jq='[.[] | select(.context == "build")] | sort_by(.updated_at) | last | .state // ""',
    ).strip()
    if state == "pending":
        return "running"
    if state == "success":
        return "success"
    if state in ("failure", "error"):
        return "failure"
    return None


def review_state(meta, head):
    """Map the scoreboard meta at the current head to a sink-agnostic review state.

    Mirrors round.sh's review_all_green / ledger_blocking: a verdict is blocking
    if it is neither "approve" nor "error"; a round is all-green iff it ran and
    every rubric approved. State not at the current head (a fix landed since the
    last review) reads as "running, green so far".

        "none"     nothing posted yet          (Zulip 👀 / label awaiting-review)
        "running"  mid-round, or behind HEAD    (Zulip ▶️ / label awaiting-review)
        "changes"  at HEAD, a blocking verdict  (Zulip ✍️ / label awaiting-author)
        "approved" at HEAD, every rubric green  (Zulip ✔️ / label ready-to-merge)
    """
    if not meta:
        return "none"
    runs = meta.get("runs") or []
    at_head = meta.get("head_sha") == head
    if at_head and runs:
        if any(r.get("verdict") not in ("approve", "error") for r in runs):
            return "changes"
        if all(r.get("verdict") == "approve" for r in runs):
            return "approved"
    return "running"


def derive(pr, ci_override=None):
    """The canonical status of a PR, as a dict:

        {"lifecycle": "open"|"merged"|"closed",
         "ci":        "running"|"success"|"failure"|None,   # None => not reported
         "review":    "none"|"running"|"changes"|"approved"|None,
         "head":      "<sha>", "title": "<title>"}

    `ci` and `review` are only meaningful while the PR is open; on a merged/closed
    PR they are None (a sink shows a terminal state and clears the rest).

    `ci_override` (one of running|success|failure|none|None) forces the CI state
    instead of reading the `build` commit status, for the pr-build "requested"
    event, which fires before that status is posted and passes "running".
    """
    st = pr_state(pr)
    if st["merged"]:
        lifecycle = "merged"
    elif st["state"] == "closed":
        lifecycle = "closed"
    else:
        lifecycle = "open"

    if lifecycle != "open":
        ci = None
        review = None
    else:
        if ci_override is not None:
            ci = None if ci_override == "none" else ci_override
        else:
            ci = ci_status(st["head"])
        review = review_state(scoreboard_meta(pr), st["head"])

    return {
        "lifecycle": lifecycle,
        "ci": ci,
        "review": review,
        "head": st["head"],
        "title": st["title"],
    }
