#!/usr/bin/env python3
"""Queue housekeeping: retire PRs that are spent or stuck, and close duplicate roadmap PRs.

Green PRs merge on their own (when CI review is enabled, via review.yml `enable_automerge`). This
covers the janitorial jobs, in CI so the autonomous worker can stay focused on producing work:

  abandon  Close any open PR the review engine has labelled `review-budget-spent`: it used its full
           review budget without reaching an all-green review. The engine clears the label if a later
           round fixes the PR. The branch is kept, and the closing comment says it is fine to open a
           fresh PR after another look at the approach.
  dedup    Close a newer PR that authors the same roadmap target (the `<!--tauceti-target:v1 ...-->`
           body marker) as an older open one. Keep the lowest PR number.
  stale    Close a PR whose latest review scoreboard is `changes requested` or `blocked` and which has
           had no activity for STALE_DAYS (default 7): a request for changes nobody acted on. The
           branch is kept; the comment invites a fresh PR.

The one override is a `keep` label (also `hold`/`wip`/`human`/`do-not-close`): a PR with one of those
is never auto-closed. By design these jobs do NOT spare human-touched PRs — anyone who wants a PR held
adds `keep`. abandon is a server-side label query, so it costs one request no matter how many PRs are
open (the engine does the per-PR budget bookkeeping as it reviews); it then leaves alone any labelled
PR whose head commit landed after the label was applied, since a fix is in flight and the re-review
has not cleared the label yet. A failed close makes the job exit nonzero.

Env: GH_TOKEN (a token that can close PRs), REPO (owner/name), optional DRY_RUN=1, BUDGET_LABEL,
STALE_DAYS.
"""
import datetime
import json
import os
import re
import subprocess
import sys

REPO = os.environ["REPO"]
DRY_RUN = os.environ.get("DRY_RUN") == "1"
# The label the TauCetiReview engine applies when a PR has spent its review budget without going green.
BUDGET_LABEL = os.environ.get("BUDGET_LABEL", "review-budget-spent")
# How long a changes-requested/blocked PR may sit untouched before the stale job retires it.
STALE_DAYS = int(os.environ.get("STALE_DAYS", "7"))

TARGET_MARKER_RE = re.compile(r"<!--tauceti-target:v1 \{[^}]*\}-->")
TARGET_ID_RE = re.compile(r'"id"\s*:\s*"([^"]+)"')
# The reviewer posts one scoreboard comment per PR carrying a machine-readable meta block; its
# `overall` is the PR's current review verdict (see the coordination contract, Section 2).
SCOREBOARD_META_RE = re.compile(r"<!--tauceti-meta:v1\s+(\{.*?\})-->", re.S)
STALE_STATES = {"changes requested", "blocked"}
KEEP_LABELS = {"keep", "hold", "wip", "human", "do-not-close"}
ABANDON_COMMENT = (
    "Closing automatically: this PR used its review budget without reaching an all-green review, so the "
    "queue housekeeping is retiring it to keep things moving. The branch is kept, so nothing is lost. It "
    "is completely fine to open a fresh PR once you have had another think about the approach. Add the "
    "`keep` label if you would rather it stay open.")
DEDUP_COMMENT = (
    "Closing automatically: this PR authors the same roadmap target (`{tid}`) as the older open #{kept}. "
    "The queue housekeeping keeps the earlier PR and closes this duplicate to avoid redundant review. "
    "The branch is kept; add the `keep` label if it is intentionally distinct.")
STALE_COMMENT = (
    "Closing automatically: this PR's last review asked for changes ({overall}) and it has sat untouched "
    "for over {days} days, so the queue housekeeping is retiring it to keep things moving. The branch is "
    "kept, so nothing is lost. It is completely fine to open a fresh PR once the findings are addressed. "
    "Add the `keep` label if you would rather it stay open.")


def gh_json(args):
    r = subprocess.run(["gh", *args], capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError(f"gh {' '.join(args)} failed: {r.stderr.strip()}")
    return json.loads(r.stdout or "null")


def has_keep_label(pr: dict) -> bool:
    return bool({(l.get("name") or "").lower() for l in (pr.get("labels") or [])} & KEEP_LABELS)


def parse_ts(s: str) -> datetime.datetime:
    """Parse a GitHub ISO-8601 timestamp (trailing 'Z') into an aware datetime."""
    return datetime.datetime.fromisoformat((s or "").replace("Z", "+00:00"))


def latest_scoreboard_overall(pr: int, pr_author: str = ""):
    """The `overall` verdict from the newest review scoreboard comment, or None if the PR has no
    parseable scoreboard yet. Fails safe (returns None) on any API/parse error, so a hiccup never
    causes a wrong close. Scoreboards authored by the PR author are ignored: a review is meant to be
    independent, and trusting a self-posted marker would let an author spoof their own verdict."""
    try:
        comments = gh_json(["api", "--paginate", f"/repos/{REPO}/issues/{pr}/comments?per_page=100"])
    except RuntimeError as e:
        print(f"stale: #{pr} scoreboard fetch failed ({e}); leaving it", file=sys.stderr)
        return None
    best_ts, overall = "", None
    for c in comments or []:
        if pr_author and (c.get("user") or {}).get("login") == pr_author:
            continue                                   # ignore the author's own (self-review) markers
        body = c.get("body") or ""
        if "tauceti-meta:v1" not in body:
            continue
        m = SCOREBOARD_META_RE.search(body)
        if not m:
            continue
        try:
            meta = json.loads(m.group(1))
        except ValueError:
            continue
        ts = c.get("updated_at") or ""
        if ts >= best_ts:
            best_ts, overall = ts, (meta.get("overall") or "").strip().lower()
    return overall


def pushed_after_label(pr: int, head: str) -> bool:
    """True if the PR's head commit landed after the budget label was last applied — a fix is in
    flight and the re-review has not cleared the label yet, so we must not close. Fails safe (returns
    True) on any uncertainty, so a transient API error never causes a wrong close. O(labelled PRs)."""
    try:
        timeline = gh_json(["api", "--paginate", f"/repos/{REPO}/issues/{pr}/timeline?per_page=100"])
        added = [e.get("created_at") for e in (timeline or [])
                 if e.get("event") == "labeled" and (e.get("label") or {}).get("name") == BUDGET_LABEL]
        if not added:
            return True                                  # labelled but no event found: don't risk it
        commit = gh_json(["api", f"/repos/{REPO}/commits/{head}"])
        head_time = ((commit or {}).get("commit") or {}).get("committer", {}).get("date", "")
        if not head_time:
            return True
        return head_time > max(added)
    except RuntimeError as e:
        print(f"abandon: #{pr} freshness check failed ({e}); leaving it", file=sys.stderr)
        return True


def close(pr: int, comment: str) -> bool:
    """Close the PR with a comment. Returns True on success (or in dry-run), False on failure."""
    if DRY_RUN:
        print(f"[dry-run] would close #{pr}: {comment[:60]}...")
        return True
    r = subprocess.run(["gh", "pr", "close", str(pr), "--repo", REPO, "--comment", comment],
                       capture_output=True, text=True)
    if r.returncode == 0:
        print(f"closed #{pr}")
        return True
    print(f"close of #{pr} failed: {r.stderr.strip()}", file=sys.stderr)
    return False


def main() -> int:
    failures = 0
    suffix = " [dry-run]" if DRY_RUN else ""

    # abandon: the engine has already decided these are spent and labelled them. Just close them
    # (unless a human asked to keep one). One query, independent of total open-PR count.
    spent = gh_json(["pr", "list", "--repo", REPO, "--state", "open", "--label", BUDGET_LABEL,
                     "--limit", "1000", "--json", "number,headRefOid,labels"]) or []
    print(f"abandon: {len(spent)} PR(s) labelled {BUDGET_LABEL}{suffix}")
    for p in spent:
        if has_keep_label(p):
            print(f"abandon: #{p['number']} is {BUDGET_LABEL} but has a keep label; leaving it")
            continue
        if pushed_after_label(p["number"], p.get("headRefOid", "")):
            print(f"abandon: #{p['number']} has a newer commit than its {BUDGET_LABEL} label "
                  "(a fix is in flight); leaving it")
            continue
        print(f"abandon: #{p['number']} ({BUDGET_LABEL})")
        failures += not close(p["number"], ABANDON_COMMENT)

    # dedup: a newer PR sharing a tauceti-target id with an older open one (keep the lowest number).
    # List-only (the marker is in the body), so this pages cheaply; the marker is on roadmap PRs only.
    limit = 2000
    prs = gh_json(["pr", "list", "--repo", REPO, "--state", "open", "--limit", str(limit),
                   "--json", "number,isDraft,body,labels"]) or []
    if len(prs) >= limit:
        print(f"warning: hit the {limit}-PR list limit; some open PRs may not be de-duplicated",
              file=sys.stderr)
    prs = [p for p in prs if not p.get("isDraft")]
    print(f"dedup: scanning {len(prs)} open PR(s){suffix}")
    seen: dict = {}
    for p in sorted(prs, key=lambda x: x["number"]):
        body = (p.get("body") or "").replace("\n", " ")
        mk = TARGET_MARKER_RE.search(body)
        if not mk:
            continue
        mid = TARGET_ID_RE.search(mk.group(0))
        if not mid:
            continue
        tid = mid.group(1)
        if tid not in seen:
            seen[tid] = p["number"]
            continue
        if has_keep_label(p):
            print(f"dedup: #{p['number']} duplicates #{seen[tid]} (target '{tid}') but has a keep "
                  "label; leaving it")
            continue
        print(f"dedup: #{p['number']} duplicates #{seen[tid]} (target '{tid}')")
        failures += not close(p["number"], DEDUP_COMMENT.format(tid=tid, kept=seen[tid]))

    # stale: a PR whose latest scoreboard is changes-requested/blocked and that has had no activity
    # for STALE_DAYS. updatedAt bumps on any push/comment/label, so a still-worked PR is never stale.
    cutoff = datetime.datetime.now(datetime.timezone.utc) - datetime.timedelta(days=STALE_DAYS)
    open_prs = gh_json(["pr", "list", "--repo", REPO, "--state", "open", "--limit", "1000",
                        "--json", "number,isDraft,labels,updatedAt,author"]) or []
    # isDraft must be explicitly False (fail closed: an unknown draft state is never stale-closed).
    fresh = [p for p in open_prs if p.get("isDraft") is False and not has_keep_label(p)
             and parse_ts(p.get("updatedAt", "")) < cutoff]
    print(f"stale: {len(fresh)} open PR(s) untouched for >{STALE_DAYS}d to check{suffix}")
    for p in fresh:
        overall = latest_scoreboard_overall(p["number"], (p.get("author") or {}).get("login", ""))
        if overall not in STALE_STATES:
            continue
        # Re-check the keep label right before closing: a human may have added it since the list.
        live = gh_json(["pr", "view", str(p["number"]), "--repo", REPO, "--json", "labels"]) or {}
        if has_keep_label(live):
            print(f"stale: #{p['number']} gained a keep label since listing; leaving it")
            continue
        print(f"stale: #{p['number']} ({overall}, untouched >{STALE_DAYS}d)")
        failures += not close(p["number"], STALE_COMMENT.format(overall=overall, days=STALE_DAYS))

    if failures:
        print(f"housekeeping: {failures} close(s) failed", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except RuntimeError as e:
        print(f"housekeeping: {e}", file=sys.stderr)
        sys.exit(1)
