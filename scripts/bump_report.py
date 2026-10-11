#!/usr/bin/env python3
"""Reconcile downstream-reports with the pin already validated on main.

The snapshot export time is not the validation time. A successful main CI run
with the current pin, on a descendant of a source revision with an older pin, can
supersede an incompatibility report without claiming compatibility with newer
Mathlib. In that case the manifest watcher must revalidate before another bump.
"""

import argparse
import datetime as dt
import json
import os
from pathlib import Path
import re
import subprocess
import urllib.request


SNAPSHOTS = "https://downstreamreports.z13.web.core.windows.net"
SHA = re.compile(r"[0-9a-f]{40}")


def sha(value):
    if not isinstance(value, str) or not SHA.fullmatch(value):
        raise ValueError("Expected a full commit SHA")
    return value


def pin(manifest):
    return sha(next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib"))


def entry(snapshot, repo, *, required=True):
    result = next((v for v in snapshot["downstreams"].values() if v["repo"] == repo), None)
    if result is None and required:
        raise ValueError(f"Downstream {repo} is absent from the snapshot")
    return result or {}


def timestamp(value):
    result = dt.datetime.fromisoformat(value)
    if result.tzinfo is None:
        raise ValueError("Validation timestamp must include a timezone")
    return result


def decision(fkb, current_pin, report, ci_runs, *, compare, ancestor, pin_at):
    """Return whether to wait, and the evidence for that decision."""
    if not fkb:
        return False, "No active incompatibility reported."
    sha(fkb)
    sha(current_pin)
    relation = "identical" if fkb == current_pin else compare(fkb, current_pin)
    if relation not in {"identical", "ahead", "behind", "diverged"}:
        raise ValueError("Could not establish the pin's relation to the reported boundary")
    if relation in {"behind", "diverged"}:
        return False, f"Active incompatibility: {fkb}; current pin is {relation} of the boundary."
    if report.get("first_known_bad_commit") != fkb:
        return True, "The boundary and validation snapshots disagree; awaiting revalidation."
    reported_at = report.get("reported_at")
    tested = report.get("downstream_commit")
    if not reported_at or not tested:
        return True, "The report has no validation timestamp or source revision; awaiting revalidation."
    tested = sha(tested)
    timestamp(reported_at)
    # A report that already tested this pin is fresh evidence of a real
    # disagreement, even if unrelated later source revisions pass main CI.
    tested_pin = pin_at(tested)
    if tested_pin is None or tested_pin == current_pin:
        return False, f"Active incompatibility: {fkb}, tested on {tested} at {reported_at}."
    if relation in {"identical", "ahead"}:
        for run in ci_runs():
            green = sha(run["head_sha"])
            if run.get("status") != "completed" or run.get("conclusion") in {
                    "cancelled", "skipped", "neutral"}:
                continue
            if not ancestor(green, "HEAD") or pin_at(green) != current_pin:
                continue
            # The newest conclusive run for this pin owns the signal. Looking
            # only at successes would hide a later main failure.
            if (run.get("conclusion") == "success" and green != tested
                    and ancestor(tested, green)):
                return True, (
                    f"Report tested {tested} at {reported_at}. Main CI succeeded on "
                    f"{green} with pin {current_pin}; awaiting downstream revalidation."
                )
            break
    return False, f"Active incompatibility: {fkb}, tested on {tested} at {reported_at}."


def gh_api(path):
    return json.loads(subprocess.check_output(["gh", "api", path], text=True, timeout=60))


def git_ancestor(base, head):
    for commit in (base, head):
        if not git_has_commit(commit):
            return False
    result = subprocess.run(["git", "merge-base", "--is-ancestor", base, head],
                            capture_output=True, text=True, timeout=30)
    if result.returncode not in {0, 1}:
        raise RuntimeError(result.stderr.strip())
    return result.returncode == 0


def git_has_commit(commit):
    return subprocess.run(["git", "cat-file", "-e", f"{commit}^{{commit}}"],
                          capture_output=True, timeout=30).returncode == 0


def git_pin(commit):
    sha(commit)
    if not git_has_commit(commit):
        return None
    payload = subprocess.check_output(["git", "show", f"{sha(commit)}:lake-manifest.json"],
                                      text=True, timeout=30)
    return pin(json.loads(payload))


def fetch_snapshot(kind):
    with urllib.request.urlopen(f"{SNAPSHOTS}/{kind}/latest.json", timeout=30) as response:
        return json.load(response)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", default=os.environ.get("GITHUB_REPOSITORY", "TauCetiProject/TauCeti"))
    args = parser.parse_args()
    boundary = entry(fetch_snapshot("lkg"), args.repo)
    fkb = boundary.get("first_known_bad_commit") or ""
    current_pin = pin(json.loads(Path("lake-manifest.json").read_text()))
    relation = None
    if fkb:
        sha(fkb)
        relation = "identical" if fkb == current_pin else gh_api(
            f"repos/leanprover-community/mathlib4/compare/{fkb}...{current_pin}")["status"]
    report = {}
    if relation in {"identical", "ahead"}:
        report = entry(fetch_snapshot("runs"), args.repo, required=False)
    waiting, message = decision(
        fkb, current_pin, report,
        lambda: gh_api(f"repos/{args.repo}/actions/workflows/ci.yml/runs"
                       "?branch=main&event=push&per_page=20")["workflow_runs"],
        compare=lambda base, head: relation,
        ancestor=git_ancestor, pin_at=git_pin,
    )
    print(message)
    if report.get("reported_at"):
        age = dt.datetime.now(dt.timezone.utc) - timestamp(report["reported_at"])
        print(f"Actual validation age: {age.total_seconds() / 3600:.1f} hours")
    if os.environ.get("GITHUB_OUTPUT"):
        with open(os.environ["GITHUB_OUTPUT"], "a") as output:
            output.write(f"commit={fkb}\nawaiting_revalidation={str(waiting).lower()}\n")
    if os.environ.get("GITHUB_STEP_SUMMARY"):
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a") as summary:
            summary.write(f"{message}\n\n")
            if waiting:
                summary.write("The downstream manifest watcher requests a targeted validation "
                              "after a merged pin change. Hourly reconciliation will consume "
                              "its result; this run creates no incompatibility issue or fix PR.\n\n")


if __name__ == "__main__":
    main()
