#!/usr/bin/env python3
"""Collect a rolling 7-day bors capacity input from GitHub's API via gh.

After cutover, review App r+ commands are the actual admission stream. Before
cutover, merged PR timestamps are a proxy. The output contains no credentials.
"""
import datetime as dt
import json
import subprocess
import sys

REPO = "TauCetiProject/TauCeti"


def gh(*args):
    return json.loads(subprocess.check_output(["gh", *args], text=True))


def timestamp(value):
    return dt.datetime.fromisoformat(value.replace("Z", "+00:00"))


def main():
    end = dt.datetime.now(dt.timezone.utc)
    start = end - dt.timedelta(days=7)
    since = start.strftime("%Y-%m-%dT%H:%M:%SZ")
    runs = gh("run", "list", "--repo", REPO, "--workflow", "pr-build.yml",
              "--limit", "500", "--json", "startedAt,updatedAt,conclusion,event")
    durations = [(timestamp(r["updatedAt"]) - timestamp(r["startedAt"])).total_seconds() / 60
                 for r in runs if r.get("event") in ("pull_request_target", "repository_dispatch")
                 and r.get("conclusion") == "success" and r.get("startedAt") and r.get("updatedAt")]
    durations = [round(x, 3) for x in durations if 0 < x < 300]
    if len(durations) < 30:
        raise SystemExit("fewer than 30 successful CI duration samples")

    # gh --paginate with --jq emits one JSON object per line across pages.
    raw = subprocess.check_output([
        "gh", "api", "--paginate",
        f"repos/{REPO}/issues/comments?since={since}&per_page=100",
        "--jq", '.[] | {created_at, body, app_id: .performed_via_github_app.id}'
    ], text=True)
    comments = [json.loads(line) for line in raw.splitlines() if line]
    approvals = [timestamp(c["created_at"]) for c in comments
                 if c.get("app_id") == 3_947_238
                 and (c.get("body") or "").startswith("bors r+ sha=")
                 and start <= timestamp(c["created_at"]) < end]

    if len(approvals) >= 30:
        arrivals = approvals
        source = "review App bors r+ comments"
    else:
        prs = gh("pr", "list", "--repo", REPO, "--state", "merged",
                "--limit", "3000", "--json", "mergedAt")
        arrivals = [timestamp(p["mergedAt"]) for p in prs
                    if p.get("mergedAt") and start <= timestamp(p["mergedAt"]) < end]
        source = "merged PR timestamps (pre-cutover proxy)"
    if len(arrivals) < 30:
        raise SystemExit("fewer than 30 arrival samples")

    out = {
        "admissions_per_day": len(arrivals) / 7,
        "arrival_minutes_in_week": sorted(round((t - start).total_seconds() / 60, 3)
                                          for t in arrivals),
        "ci_minutes": durations,
        "source": {"arrival": source, "start": start.isoformat(), "end": end.isoformat(),
                   "ci": "last 500 successful pr-build runs"},
    }
    json.dump(out, sys.stdout, indent=2)
    print()


if __name__ == "__main__":
    main()
