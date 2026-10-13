#!/usr/bin/env python3
"""Reconcile after successful main CI changes a pin, including coalesced pushes."""

import base64
import json
import os
from pathlib import Path
import subprocess

from bump_report import sha


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


def github(path):
    return json.loads(subprocess.check_output(["gh", "api", path], text=True, timeout=60))


class Evidence:
    """Small immutable file reads; no clone of historical repository contents."""
    def __init__(self, repo, api=github):
        self.repo, self.api, self.pins = repo, api, {}

    def pin_at(self, commit):
        commit = sha(commit)
        if commit not in self.pins:
            values = []
            for file in ["lake-manifest.json", "lean-toolchain"]:
                result = self.api(f"repos/{self.repo}/contents/{file}?ref={commit}")
                if result["encoding"] != "base64":
                    raise ValueError("Pin file encoding unavailable")
                values.append(base64.b64decode(result["content"]).decode())
            manifest = json.loads(values[0])
            mathlib = sha(next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib"))
            self.pins[commit] = (mathlib, values[1].strip())
        return self.pins[commit]

    def ancestor(self, base, head):
        if base == head:
            return True
        result = self.api(f"repos/{self.repo}/compare/{sha(base)}...{sha(head)}?per_page=1")
        return result["status"] in {"identical", "ahead"}


def main():
    event = json.loads(Path(os.environ["GITHUB_EVENT_PATH"]).read_text())
    result = True
    if os.environ["GITHUB_EVENT_NAME"] == "workflow_run":
        repo = os.environ["GITHUB_REPOSITORY"]
        run = event["workflow_run"]
        previous = github(
            f"repos/{repo}/actions/workflows/ci.yml/runs?branch=main&event=push&per_page=20"
        )["workflow_runs"]
        current = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
        evidence = Evidence(repo)
        # The sparse checkout already supplies current pin files; seed their
        # immutable snapshot without two redundant API reads.
        manifest = json.loads(Path("lake-manifest.json").read_text())
        evidence.pins[sha(current)] = (
            sha(next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")),
            Path("lean-toolchain").read_text().strip())
        result = reconcile(run, previous, repo=repo, current=current,
                           pin_at=evidence.pin_at, ancestor=evidence.ancestor)
    print(f"Dependency reconciliation required: {result}")
    with open(os.environ["GITHUB_OUTPUT"], "a") as output:
        output.write(f"reconcile={str(result).lower()}\n")


if __name__ == "__main__":
    main()
