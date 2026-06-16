#!/usr/bin/env python3
"""Mirror a TauCeti PR's lifecycle onto Zulip emoji reactions.

We keep exactly one bot-owned message per PR in a dedicated channel/topic
(default: "Tau Ceti" > "PRs") and reconcile two independent, mutually-exclusive
groups of emoji reactions on it from GitHub truth:

  CI (build) group        review / lifecycle group
    running   -> yellow      review has begun        -> eyes
    passed    -> green_circle running, green so far   -> arrow_forward
    failed    -> red_circle  changes_requested/block -> writing
                             all review done, green  -> white_check_mark
                             merged                  -> merge        (realm emoji)
                             closed, not merged      -> closed-pr    (realm emoji)

The script reads *everything* it needs from GitHub (PR state, the canonical
`<!--tauceti-scoreboard-->` comment's meta JSON, and the `build` commit status),
so it is fully idempotent: the same `reconcile` powers both the event-driven
GitHub Actions and a one-shot backfill over historical PRs. Run it as often as
you like; it converges the reactions to match GitHub and changes nothing else.

Usage:
    zulip_pr_status.py reconcile <pr_number> [--create]

`--create` posts the per-PR message if it does not exist yet (used by the PR
"opened" workflow and by backfill). Without it, a PR with no message yet is
left alone (other events only react to an existing message, never create one,
so two near-simultaneous events can't post duplicate messages).

Environment:
    ZULIP_API_KEY, ZULIP_EMAIL, ZULIP_SITE   bot credentials (required)
    ZULIP_CHANNEL                            default "Tau Ceti"
    ZULIP_TOPIC                              default "PRs"
    GH_REPO                                  default "FormalFrontier/TauCeti"
    GH_TOKEN / GITHUB_TOKEN                  used by `gh` for the GitHub API

Emoji updates are cosmetic; on any non-fatal hiccup we log and exit 0 so a
caller can wrap us in `continue-on-error` and never fail CI over a reaction.
"""

import json
import os
import re
import subprocess
import sys

import zulip

REPO = os.environ.get("GH_REPO", "FormalFrontier/TauCeti")
CHANNEL = os.environ.get("ZULIP_CHANNEL", "Tau Ceti")
TOPIC = os.environ.get("ZULIP_TOPIC", "PRs")

# name -> (reaction_type, emoji_code). Unicode emoji resolve by name on the
# server, so emoji_code is None; realm (custom) emoji must carry their id.
EMOJI = {
    # CI (build) group
    "yellow":           ("unicode_emoji", None),
    "green_circle":     ("unicode_emoji", None),
    "red_circle":       ("unicode_emoji", None),
    # review / lifecycle group
    "eyes":             ("unicode_emoji", None),
    "arrow_forward":    ("unicode_emoji", None),
    "writing":          ("unicode_emoji", None),
    "white_check_mark": ("unicode_emoji", None),
    "merge":            ("realm_emoji", "18527"),
    "closed-pr":        ("realm_emoji", "61293"),
}
CI_GROUP = ["yellow", "green_circle", "red_circle"]
REVIEW_GROUP = ["eyes", "arrow_forward", "writing", "white_check_mark", "merge", "closed-pr"]


def log(msg):
    print(msg, flush=True)


def pr_url(pr):
    return f"https://github.com/{REPO}/pull/{pr}"


# ----- GitHub truth (via the gh CLI, authenticated by GH_TOKEN) ---------------

def gh_api(path, jq=None):
    cmd = ["gh", "api", path]
    if jq is not None:
        cmd += ["--jq", jq]
    out = subprocess.run(cmd, capture_output=True, text=True)
    if out.returncode != 0:
        raise RuntimeError(f"gh api {path} failed: {out.stderr.strip()}")
    return out.stdout


def pr_state(pr):
    """{'state','merged','head','title','author'} for the PR, from GitHub."""
    raw = gh_api(f"/repos/{REPO}/pulls/{pr}")
    d = json.loads(raw)
    return {
        "state": d["state"],                 # "open" | "closed"
        "merged": bool(d.get("merged")),
        "head": d["head"]["sha"],
        "title": d.get("title") or f"PR #{pr}",
        "author": (d.get("user") or {}).get("login", ""),
    }


def scoreboard_meta(pr):
    """The newest trusted scoreboard comment's meta JSON ({} if none).

    Trust mirrors round.sh: the <!--tauceti-scoreboard--> marker AND an author
    with repo association (OWNER/MEMBER/COLLABORATOR), so a random external
    comment cannot forge review state.
    """
    body = gh_api(
        f"/repos/{REPO}/issues/{pr}/comments?per_page=100",
        jq='[.[] | select(.body|contains("<!--tauceti-scoreboard-->"))'
           ' | select(.author_association|IN("OWNER","MEMBER","COLLABORATOR"))]'
           ' | sort_by(.updated_at) | last | .body // ""',
    )
    m = re.search(r"<!--tauceti-meta:v1 (.*)-->", body)
    if not m:
        return {}
    try:
        return json.loads(m.group(1))
    except json.JSONDecodeError:
        return {}


def ci_status(head):
    """'running' | 'success' | 'failure' | None from the `build` commit status."""
    raw = gh_api(
        f"/repos/{REPO}/commits/{head}/statuses",
        jq='[.[] | select(.context == "build")] | sort_by(.updated_at) | last | .state // ""',
    )
    state = raw.strip()
    if state == "pending":
        return "running"
    if state == "success":
        return "success"
    if state in ("failure", "error"):
        return "failure"
    return None


def review_emoji(meta, head):
    """Map the scoreboard meta at the current head to a review-group emoji.

    Mirrors round.sh's review_all_green / ledger_blocking: a verdict is blocking
    if it is neither "approve" nor "error"; a round is all-green iff it ran and
    every rubric approved. State that is not at the current head (a fix landed
    since the last review) reads as "running, green so far".
    """
    if not meta:
        return "eyes"  # review has begun / queued, nothing posted yet
    runs = meta.get("runs") or []
    at_head = meta.get("head_sha") == head
    if at_head and runs:
        if any(r.get("verdict") not in ("approve", "error") for r in runs):
            return "writing"  # at least one changes_requested / block
        if all(r.get("verdict") == "approve" for r in runs):
            return "white_check_mark"  # all review done, all green
    return "arrow_forward"  # running, green so far


# ----- Zulip side ------------------------------------------------------------

def find_message(client, pr):
    """The oldest bot-topic message that links to this PR, or None."""
    url = pr_url(pr)
    resp = client.get_messages({
        "anchor": "newest",
        "num_before": 5000,
        "num_after": 0,
        "narrow": [
            {"operator": "channel", "operand": CHANNEL},
            {"operator": "topic", "operand": TOPIC},
            {"operator": "search", "operand": url},
        ],
    })
    if resp.get("result") != "success":
        raise RuntimeError(f"get_messages failed: {resp}")
    # Match the exact PR URL with a word boundary so #17 never matches #171.
    pat = re.compile(re.escape(url) + r"(?![0-9])")
    hits = [m for m in resp["messages"] if pat.search(m["content"])]
    if not hits:
        return None
    return min(hits, key=lambda m: m["id"])


def create_message(client, st, pr):
    content = f"**{st['title']}** · {pr_url(pr)}"
    resp = client.send_message({
        "type": "stream",
        "to": CHANNEL,
        "topic": TOPIC,
        "content": content,
    })
    if resp.get("result") != "success":
        raise RuntimeError(f"send_message failed: {resp}")
    log(f"created message {resp['id']} for PR #{pr}")
    return {"id": resp["id"], "reactions": []}


def set_group(client, message, group, desired):
    """Ensure `desired` (or nothing) is the only reaction from `group` present."""
    present = {r["emoji_name"] for r in message.get("reactions", [])
              if r["emoji_name"] in group}
    for name in group:
        if name in present and name != desired:
            rtype, code = EMOJI[name]
            args = {"message_id": message["id"], "emoji_name": name}
            if rtype == "realm_emoji":
                args.update(emoji_code=code, reaction_type="realm_emoji")
            log(f"removing {name}")
            client.remove_reaction(args)
    if desired and desired not in present:
        rtype, code = EMOJI[desired]
        args = {"message_id": message["id"], "emoji_name": desired}
        if rtype == "realm_emoji":
            args.update(emoji_code=code, reaction_type="realm_emoji")
        log(f"adding {desired}")
        client.add_reaction(args)


def reconcile(client, pr, create):
    st = pr_state(pr)
    message = find_message(client, pr)
    if message is None:
        if not create:
            log(f"no message for PR #{pr} yet and --create not set; nothing to do")
            return
        message = create_message(client, st, pr)

    if st["merged"]:
        rev = "merge"
    elif st["state"] == "closed":
        rev = "closed-pr"
    else:
        rev = review_emoji(scoreboard_meta(pr), st["head"])
    set_group(client, message, REVIEW_GROUP, rev)

    # CI status is only meaningful while the PR is open; clear it on a terminal PR.
    if st["state"] == "open":
        ci = ci_status(st["head"])
        ci_emoji = {"running": "yellow", "success": "green_circle",
                    "failure": "red_circle", None: None}[ci]
    else:
        ci_emoji = None
    set_group(client, message, CI_GROUP, ci_emoji)
    log(f"PR #{pr}: review={rev} ci={ci_emoji}")


def main(argv):
    if len(argv) < 3 or argv[1] != "reconcile":
        print(__doc__)
        return 2
    pr = argv[2].lstrip("#")
    if not pr.isdigit():
        log(f"not a PR number: {argv[2]!r}")
        return 0
    create = "--create" in argv[3:]
    email = os.environ.get("ZULIP_EMAIL")
    api_key = os.environ.get("ZULIP_API_KEY")
    site = os.environ.get("ZULIP_SITE", "https://leanprover.zulipchat.com")
    if not (email and api_key):
        log("ZULIP_EMAIL / ZULIP_API_KEY not set; skipping (no bot configured yet)")
        return 0
    client = zulip.Client(email=email, api_key=api_key, site=site)
    try:
        reconcile(client, pr, create)
    except Exception as exc:  # cosmetic: never fail the caller over a reaction
        log(f"reconcile failed (non-fatal): {exc}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
