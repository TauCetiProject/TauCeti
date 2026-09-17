#!/usr/bin/env python3
"""Detect a Lake-pin reservation release; the existing sweep owns recovery policy."""

import json
import os
import subprocess


# Same pin paths as TauCetiReview runner/sweep.py; no candidate or merge policy here.
PIN_PATHS = {"lake-manifest.json", "lean-toolchain"}


def gh_json(*args):
    return json.loads(subprocess.check_output(["gh", *args], text=True))


def should_sweep(repo, released_pr, action):
    if action not in {"closed", "dequeued", "manual"}:
        raise ValueError(f"Unexpected release action: {action}")
    pages = gh_json("api", "--paginate", "--slurp",
                    f"repos/{repo}/pulls/{released_pr}/files?per_page=100")
    if not any(f["filename"] in PIN_PATHS for page in pages for f in page):
        return False
    # A delayed release event may arrive after the same bump has been re-enqueued.
    owner, name = repo.split("/")
    response = gh_json("api", "graphql", "-f", "query=" + """
        query($owner: String!, $name: String!, $pr: Int!) {
          repository(owner: $owner, name: $name) {
            pullRequest(number: $pr) { baseRefName isInMergeQueue state }
          }
        }
        """, "-f", f"owner={owner}", "-f", f"name={name}", "-F", f"pr={released_pr}")
    if response.get("errors"):
        raise RuntimeError(f"Cannot read reservation state: {response['errors']}")
    current = response["data"]["repository"]["pullRequest"]
    if current["baseRefName"] != "main" or current["isInMergeQueue"]:
        return False
    # Closing an arbitrary unmerged pin PR must not trigger a repository-wide sweep.
    # If it was queued, its dequeued event handles that release. A merged bump's
    # closed event owns recovery; ignore a duplicate dequeued event arriving later.
    if action == "closed":
        return current["state"] == "MERGED"
    if action == "dequeued":
        return current["state"] != "MERGED"
    return True


def main():
    released_pr = int(os.environ["RELEASED_PR"])
    eligible = should_sweep(os.environ["REPO"], released_pr, os.environ["RELEASE_ACTION"])
    print(f"Queue release for #{released_pr}: dispatch sweep = {eligible}")
    with open(os.environ["GITHUB_OUTPUT"], "a") as output:
        output.write(f"sweep={str(eligible).lower()}\n")


if __name__ == "__main__":
    main()
