#!/usr/bin/env python3
"""Reconcile after successful main CI changes a pin, including coalesced pushes."""

import json
import os
from pathlib import Path
import subprocess

from bump_report import git_ancestor, git_pin, sha


def reconcile(run, previous, *, repo, current, pin_at, ancestor):
    if (run.get("event") != "push" or run.get("head_branch") != "main"
            or run.get("head_repository", {}).get("full_name") != repo
            or run.get("status") != "completed" or run.get("conclusion") != "success"):
        return False
    head = sha(run["head_sha"])
    # A newer pin must finish its own CI; this event proves only its own pin.
    if not ancestor(head, current) or pin_at(head) != pin_at(current):
        return False
    for old in sorted(previous, key=lambda old: old["id"], reverse=True):
        if (old.get("id", 0) >= run["id"] or old.get("event") != "push"
                or old.get("head_branch") != "main" or old.get("status") != "completed"
                or old.get("conclusion") != "success"):
            continue
        base = sha(old["head_sha"])
        if ancestor(base, head):
            # This is the last successful run on this history, not HEAD's parent:
            # CI can coalesce several intervening main pushes.
            return pin_at(base) != pin_at(head)
    # Initial run or truncated API history: one idempotent reconciliation is safe.
    return True


def revision_pins(commit):
    return (git_pin(commit), subprocess.check_output(
        ["git", "show", f"{sha(commit)}:lean-toolchain"], text=True, timeout=30).strip())


def main():
    event = json.loads(Path(os.environ["GITHUB_EVENT_PATH"]).read_text())
    result = True
    if os.environ["GITHUB_EVENT_NAME"] == "workflow_run":
        repo = os.environ["GITHUB_REPOSITORY"]
        run = event["workflow_run"]
        previous = json.loads(subprocess.check_output([
            "gh", "api", f"repos/{repo}/actions/workflows/ci.yml/runs?branch=main&event=push&per_page=20"
        ], text=True, timeout=60))["workflow_runs"]
        current = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
        result = reconcile(run, previous, repo=repo, current=current,
                           pin_at=revision_pins, ancestor=git_ancestor)
    print(f"Dependency reconciliation required: {result}")
    with open(os.environ["GITHUB_OUTPUT"], "a") as output:
        output.write(f"reconcile={str(result).lower()}\n")


if __name__ == "__main__":
    main()
