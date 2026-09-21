#!/usr/bin/env python3
"""Keep one lifecycle label per PR using the pinned Auto-merge decision.

readiness.py calls the same gate as Auto-merge. A ready PR passes all per-PR
prerequisites; queue reservations and membership are reported separately.

Usage: labels.py reconcile <pr_number> | reconcile-all
Requires authenticated gh and TAUCETI_REVIEW_RUNNER pointing to the pinned engine.
"""

import json
import subprocess
import sys

import core
import readiness

REPO = core.REPO

# label -> (hex color, description). Created on first use, like the roadmap labels, so setting this
# up needs no manual label creation.
LABELS = {
    "awaiting-CI":        ("fbca04", "CI has not yet reported on the latest commit"),
    "awaiting-review":    ("1d76db", "CI is green; waiting for review verdicts"),
    "review-in-progress": ("a371f7", "A review is running on this exact commit right now"),
    # Distinct colours on purpose: telling a red build apart from a changes request AT A GLANCE in
    # the PR list is the whole reason these are two labels rather than one.
    "ci-failed":          ("d93f0b", "The build failed on the latest commit; author action needed"),
    "awaiting-author":    ("e99695", "A review requested changes; author action needed"),
    "merge-check-failed": ("d93f0b", "A scope or pin-validation check failed; the build itself may be green"),
    "needs-human-review": ("8b5cf6", "Approved PR changes human-owned files; human review and merge needed"),
    "awaiting-dependency": ("c5def5", "PR targets a stacked branch rather than main"),
    "on-hold":            ("eeeeee", "Draft PR or explicitly held by a keep/hold/wip/human/do-not-close label"),
    "ready-to-merge":     ("0e8a16", "Current head passes all automated merge prerequisites; queue reservations may delay entry"),
}
STATUS_LABELS = list(LABELS)


def log(msg):
    print(msg, flush=True)


# ----- GitHub label writes (via gh; core.gh_api handles reads) ----------------

def _run(args):
    return subprocess.run(["gh", "api", *args], capture_output=True, text=True)


def current_status_labels(pr):
    """The status labels currently on the PR (a subset of STATUS_LABELS)."""
    names = core.gh_api(
        f"/repos/{REPO}/issues/{pr}/labels",
        jq=".[].name", paginate=True,
    ).splitlines()
    return [n for n in names if n in STATUS_LABELS]


def ensure_label(name):
    """Create the label if absent, and keep its colour and description matching LABELS (idempotent).

    Only a clear 404 on the probe means 'absent, create it'; any other probe failure is left alone
    (the add may still succeed, and we do not want to mask a token/permission error as a missing
    label). When the label already exists we reconcile its presentation rather than returning
    straight away: a label is created once and then lives forever, so editing a description in
    LABELS would otherwise never reach GitHub and the live label would keep describing behaviour
    this file no longer has. The probe already fetched it, so the comparison is free and only a
    genuine mismatch costs a PATCH."""
    probe = _run([f"/repos/{REPO}/labels/{name}"])
    if probe.returncode == 0:
        _reconcile_label_presentation(name, probe.stdout)
        return
    if "404" not in probe.stderr:
        return
    color, description = LABELS[name]
    create = _run([
        "--method", "POST", f"/repos/{REPO}/labels",
        "-f", f"name={name}", "-f", f"color={color}", "-f", f"description={description}",
    ])
    # A concurrent create (422 already_exists) is fine; anything else is a real error.
    if create.returncode != 0 and "already_exists" not in create.stderr:
        raise RuntimeError(f"gh api create label {name} failed: {create.stderr.strip()}")


def _reconcile_label_presentation(name, probe_stdout):
    """PATCH an existing label whose colour or description has drifted from LABELS.

    Presentation is cosmetic, so this never raises: an unparseable probe body or a failed PATCH
    leaves the label as it is and lets the caller get on with the actual add, which is what keeps
    the PR list correct."""
    color, description = LABELS[name]
    try:
        live = json.loads(probe_stdout)
    except (ValueError, TypeError):
        return
    if live.get("color") == color and (live.get("description") or "") == description:
        return
    patch = _run([
        "--method", "PATCH", f"/repos/{REPO}/labels/{name}",
        "-f", f"color={color}", "-f", f"description={description}",
    ])
    if patch.returncode != 0:
        log(f"note: could not update the {name} label's colour/description: {patch.stderr.strip()}")


def add_label(pr, name):
    ensure_label(name)
    r = _run(["--method", "POST", f"/repos/{REPO}/issues/{pr}/labels", "-f", f"labels[]={name}"])
    if r.returncode != 0:
        raise RuntimeError(f"gh api add label {name} failed: {r.stderr.strip()}")
    log(f"added {name}")


def remove_label(pr, name):
    r = _run(["--method", "DELETE", f"/repos/{REPO}/issues/{pr}/labels/{name}"])
    # A label already gone (the label is not on the issue) is the end state we want. GitHub answers a
    # DELETE of an unattached label with 404 "Label does not exist"; tolerate exactly that.
    if r.returncode != 0 and not ("404" in r.stderr and "does not exist" in r.stderr):
        raise RuntimeError(f"gh api remove label {name} failed: {r.stderr.strip()}")
    log(f"removed {name}")


def reconcile(pr):
    status = readiness.assess(pr)
    desired = status["category"]          # one of STATUS_LABELS, or None (terminal)
    current = set(current_status_labels(pr))

    for name in current:
        if name != desired:
            remove_label(pr, name)
    if desired is not None and desired not in current:
        add_label(pr, desired)

    log(f"PR #{pr}@{status['head']}: {status['reason']} -> label={desired or '(none)'}")



def reconcile_all():
    readiness.engine()  # Fail once, before any writes, if policy is unavailable.
    numbers = core.gh_api(f"/repos/{REPO}/pulls?state=open&per_page=100",
                          jq=".[].number", paginate=True).splitlines()
    for name in LABELS:
        ensure_label(name)  # Migrate descriptions once per pass, including unchanged labels.
    failures = []
    for index, number in enumerate(numbers):
        try:
            reconcile(number)
        except core.RateLimited as exc:
            log(f"Backfill stopped: {exc}; {len(numbers) - index} PRs remain unchecked")
            return 1
        except (RuntimeError, subprocess.CalledProcessError, ValueError, KeyError) as exc:
            failures.append(number)
            log(f"PR #{number}: reconciliation failed: {exc}")
    log(f"Backfill: {len(numbers) - len(failures)}/{len(numbers)} reconciled; failures={failures}")
    return 1 if failures else 0


def main(argv):
    if argv[1:] == ["reconcile-all"]:
        return reconcile_all()
    if len(argv) != 3 or argv[1] != "reconcile":
        print(__doc__)
        return 2
    pr = argv[2].lstrip("#")
    if not pr.isdigit():
        log(f"not a PR number: {argv[2]!r}")
        return 0
    reconcile(pr)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
