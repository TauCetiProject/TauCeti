#!/usr/bin/env python3
"""Keep exactly one status label on every open TauCeti PR.

The five labels are mutually exclusive; together they say, at a glance in the PR
list, where a PR is in the pipeline:

    awaiting-CI         CI has not yet reported on the latest commit
    awaiting-review     CI is green; waiting for review verdicts
    review-in-progress  a review agent is actively reviewing (best-effort)
    awaiting-author     the build failed or a review requested changes
    ready-to-merge      CI green and every rubric approved

This sink derives four of them from the PR's status (core.derive) and sets that
one, removing any other status label so the "exactly one" invariant holds. It is
idempotent and convergent: every reconcile reads GitHub truth afresh and drives
the label set to the single correct value, so a transient race between two events
self-heals on the next reconcile.

`review-in-progress` is the one label this sink never *derives*. The worker
(kim-em/TauCetiWorker) sets it best-effort while it is actively reviewing, as a
transient overlay on the `awaiting-review` slot. This sink treats it accordingly:

  * it is preserved while the derived state is `awaiting-review` (CI still owns
    the slot conceptually, but we don't clobber the worker's finer signal); and
  * any *real* transition clears it -- a new commit moves the PR to `awaiting-CI`,
    a posted scoreboard moves it to `awaiting-author`/`ready-to-merge`, a merge
    strips all labels. So even if the worker crashes mid-review and never clears
    its own label, the next status event converges the PR back to one label.

A terminal PR (merged or closed) carries no status label: reconcile removes all
five.

Usage:
    labels.py reconcile <pr_number> [--ci STATE]

`--ci STATE` (running|success|failure|none) forces the CI state instead of
reading the `build` commit status, for the pr-build "requested" event (which
fires before that status is posted and passes "running").

Environment:
    GH_REPO                   default "TauCetiProject/TauCeti"
    GH_TOKEN / GITHUB_TOKEN   used by `gh` for the GitHub API (needs issues:write)

Only python3's standard library and an authenticated `gh` CLI are required.
"""

import subprocess
import sys

import core

REPO = core.REPO

# label -> (hex color, description). Created on first use, like the roadmap
# labels, so setting this up needs no manual label creation.
LABELS = {
    "awaiting-CI":        ("fbca04", "CI has not yet reported on the latest commit"),
    "awaiting-review":    ("1d76db", "CI is green; waiting for review verdicts"),
    "review-in-progress": ("a371f7", "A review agent is actively reviewing (best-effort, set by the worker)"),
    "awaiting-author":    ("d93f0b", "The build failed or a review requested changes; author action needed"),
    "ready-to-merge":     ("0e8a16", "CI green and every rubric approved; ready to merge"),
}
STATUS_LABELS = list(LABELS)
# The label the worker owns; this sink preserves but never derives it.
WORKER_LABEL = "review-in-progress"


def log(msg):
    print(msg, flush=True)


def derived_label(status):
    """The one CI-owned status label for `status`, or None if the PR is terminal.

    `review-in-progress` is never returned here -- it is the worker's overlay,
    applied in reconcile(). Precedence:

        PR merged/closed                 -> None (no status label)
        CI not reported yet / running    -> awaiting-CI
        CI failed                        -> awaiting-author
        CI green, review requested chgs  -> awaiting-author
        CI green, every rubric approved  -> ready-to-merge
        CI green, review pending/stale   -> awaiting-review
    """
    if status["lifecycle"] != "open":
        return None
    ci = status["ci"]
    if ci in (None, "running"):
        return "awaiting-CI"
    if ci == "failure":
        return "awaiting-author"
    # ci == "success"
    review = status["review"]
    if review == "changes":
        return "awaiting-author"
    if review == "approved":
        return "ready-to-merge"
    return "awaiting-review"  # "none" or "running": CI green, no verdict yet


# ----- GitHub label writes (via gh; core.gh_api handles reads) ----------------

def _gh(args, tolerate_codes=()):
    """Run `gh api ARGS`; tolerate expected idempotent failures (a 404 removing
    an absent label, a 422 creating an existing one) so reconcile stays green on
    the normal no-op paths, and raise on anything genuinely wrong."""
    out = subprocess.run(["gh", "api", *args], capture_output=True, text=True)
    if out.returncode != 0:
        stderr = out.stderr.strip()
        if any(str(c) in stderr for c in tolerate_codes):
            return out
        raise RuntimeError(f"gh api {' '.join(args)} failed: {stderr}")
    return out


def current_status_labels(pr):
    """The status labels currently on the PR (a subset of STATUS_LABELS)."""
    names = core.gh_api(
        f"/repos/{REPO}/issues/{pr}/labels",
        jq=".[].name", paginate=True,
    ).splitlines()
    return [n for n in names if n in STATUS_LABELS]


def ensure_label(name):
    """Create the label if it does not exist yet (idempotent)."""
    probe = subprocess.run(
        ["gh", "api", f"/repos/{REPO}/labels/{name}"],
        capture_output=True, text=True,
    )
    if probe.returncode == 0:
        return
    color, description = LABELS[name]
    _gh([
        "--method", "POST", f"/repos/{REPO}/labels",
        "-f", f"name={name}", "-f", f"color={color}",
        "-f", f"description={description}",
    ], tolerate_codes=(422,))  # 422 == already exists (a concurrent create won)


def add_label(pr, name):
    ensure_label(name)
    _gh([
        "--method", "POST", f"/repos/{REPO}/issues/{pr}/labels",
        "-f", f"labels[]={name}",
    ])
    log(f"added {name}")


def remove_label(pr, name):
    _gh([
        "--method", "DELETE", f"/repos/{REPO}/issues/{pr}/labels/{name}",
    ], tolerate_codes=(404,))  # already gone == the end state we want
    log(f"removed {name}")


def reconcile(pr, ci_override):
    status = core.derive(pr, ci_override)
    target = derived_label(status)          # a CI-owned label, or None (terminal)
    current = set(current_status_labels(pr))

    # Overlay: don't clobber the worker's `review-in-progress` while the derived
    # slot is still `awaiting-review`; in every other state it must clear.
    desired = target
    if target == "awaiting-review" and WORKER_LABEL in current:
        desired = WORKER_LABEL

    for name in current:
        if name != desired:
            remove_label(pr, name)
    if desired is not None and desired not in current:
        add_label(pr, desired)

    log(f"PR #{pr}: lifecycle={status['lifecycle']} ci={status['ci']} "
        f"review={status['review']} -> label={desired or '(none)'}")


def main(argv):
    if len(argv) < 3 or argv[1] != "reconcile":
        print(__doc__)
        return 2
    pr = argv[2].lstrip("#")
    if not pr.isdigit():
        log(f"not a PR number: {argv[2]!r}")
        return 0
    rest = argv[3:]
    ci_override = None
    if "--ci" in rest:
        ci_override = rest[rest.index("--ci") + 1]
    reconcile(pr, ci_override)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
