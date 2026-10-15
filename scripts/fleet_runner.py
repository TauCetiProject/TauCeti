#!/usr/bin/env python3
"""Select an idle dedicated runner, or retain Namespace. No new coordinator."""

import json
import os
import urllib.request

LABELS = {"self-hosted", "linux", "x64", "tauceti-fleet"}


def choose(pages, *, enabled, attempt):
    if not enabled or attempt != 1:
        return False
    found = []
    total = None
    for page in pages:
        if type(page.get("total_count")) is not int or not isinstance(
            page.get("runners"), list
        ):
            return False
        if total is not None and total != page["total_count"]:
            return False
        total = page["total_count"]
        found.extend(page["runners"])
    if total is None or len(found) != total:
        return False
    return any(
        r.get("status") == "online"
        and r.get("busy") is False
        and LABELS
        <= {str(label.get("name", "")).lower() for label in r.get("labels", [])}
        for r in found
    )


def main():
    selected = False
    try:
        attempt = int(os.environ["GITHUB_RUN_ATTEMPT"])
        enabled = os.environ.get("FLEET_CI_ENABLED") == "true"
        token = os.environ.get("FLEET_READ_TOKEN", "")
        group = int(os.environ.get("FLEET_RUNNER_GROUP_ID") or "0")
        pages = []
        if enabled and attempt == 1 and token and group > 0:
            for page in range(1, 21):
                request = urllib.request.Request(
                    f"https://api.github.com/orgs/TauCetiProject/actions/runner-groups/{group}/runners?per_page=100&page={page}",
                    headers={
                        "Authorization": "Bearer " + token,
                        "Accept": "application/vnd.github+json",
                        "User-Agent": "TauCetiFleetPicker/1.0",
                    },
                )
                with urllib.request.urlopen(request, timeout=10) as response:
                    raw = response.read(2 * 1024 * 1024 + 1)
                if len(raw) > 2 * 1024 * 1024:
                    raise ValueError("runner inventory exceeds bound")
                data = json.loads(raw)
                pages.append(data)
                if sum(len(p["runners"]) for p in pages) >= data["total_count"]:
                    break
            selected = choose(pages, enabled=enabled, attempt=attempt)
    except (OSError, ValueError, KeyError, TypeError):
        print("::notice::Fleet inventory unavailable/incomplete; retaining Namespace")
    with open(os.environ["GITHUB_OUTPUT"], "a") as out:
        out.write("fleet=" + ("true" if selected else "false") + "\n")
    print("Dedicated fleet selected" if selected else "Namespace selected")


if __name__ == "__main__":
    main()
