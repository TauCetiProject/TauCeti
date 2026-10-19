#!/usr/bin/env python3
"""Publish bounded, data-only summaries from a fresh trusted workflow runner.

The service reserves all six possible GitHub requests before this script reads
GitHub. No candidate code runs here. Artifacts are parsed as bounded JSON, never
extracted to disk or executed. Phase telemetry remains sandbox statistics.
"""

import argparse
import io
import json
import os
import re
import urllib.error
import urllib.parse
import urllib.request
import zipfile

ORIGIN = "https://ci-data.taucetiproject.org"
MAX_BYTES = 24 * 1024 * 1024


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args, **kwargs):
        return None


class HTTPFailure(RuntimeError):
    def __init__(self, error, url):
        super().__init__(
            f"HTTP {error.code} from {urllib.parse.urlparse(url).hostname}"
        )
        self.status = error.code
        self.retry_after = error.headers.get("Retry-After")
        self.remaining = error.headers.get("X-RateLimit-Remaining")
        self.reset = error.headers.get("X-RateLimit-Reset")


def request(url, token, data=None):
    headers = {
        "Authorization": "Bearer " + token,
        "User-Agent": "TauCetiCI-live/1.0",
        "Accept": "application/vnd.github+json",
        "Content-Type": "application/json",
    }
    req = urllib.request.Request(
        url,
        headers=headers,
        data=json.dumps(data).encode() if data is not None else None,
    )
    try:
        with urllib.request.build_opener(NoRedirect).open(req, timeout=30) as response:
            value = response.read(MAX_BYTES + 1)
    except urllib.error.HTTPError as error:
        if error.code not in (301, 302, 303, 307, 308):
            raise HTTPFailure(error, url) from None
        location = error.headers["Location"]
        if urllib.parse.urlparse(location).scheme != "https":
            raise RuntimeError("Unsafe artifact redirect")
        # Signed blob URLs never receive the GitHub credential.
        with urllib.request.urlopen(location, timeout=30) as response:
            value = response.read(MAX_BYTES + 1)
    if len(value) > MAX_BYTES:
        raise RuntimeError("Response exceeds summary size limit")
    return value


def excerpt(log, failed):
    out = []
    lo, hi = failed.get("started_at"), failed.get("completed_at")
    for raw in log.splitlines():
        if "\x1b[36;1m" in raw:
            continue
        raw = raw.lstrip("\ufeff")
        if (
            lo
            and hi
            and re.match(r"^\d{4}-\d\d-\d\dT", raw)
            and not lo[:19] <= raw[:19] <= hi[:19]
        ):
            continue
        line = re.sub(
            r"\x1b\[[0-9;]*m", "", re.sub(r"^\d{4}-\d\d-\d\dT[\d:.]+Z ", "", raw)
        ).strip()
        if (
            re.search(r"error|FAIL|✖|timed out|Killed", line, re.I)
            and not re.match(r"^(?:✔(?:\s|$)|\+\+?\s)", line)
            and "Process completed with exit code" not in line
        ):
            out.append(line[:300])
            if len(out) == 30:
                break
    return out


def telemetry(archive):
    with zipfile.ZipFile(io.BytesIO(archive)) as z:
        info = z.getinfo("telemetry.json")
        if info.file_size > 1024 * 1024:
            raise ValueError("Telemetry exceeds limit")
        value = json.loads(z.read(info))
    if value.get("schema") != "tauceti-ci.telemetry/v1":
        raise ValueError("Unknown telemetry schema")
    # Candidate-produced fields cannot establish run identity or producer trust.
    return {"phases": value.get("phases", [])}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--run-id", required=True, type=int)
    ap.add_argument("--attempt", required=True, type=int)
    args = ap.parse_args()
    oidc_url = os.environ["ACTIONS_ID_TOKEN_REQUEST_URL"] + "&audience=tauceti-live-ci"
    oidc = json.loads(request(oidc_url, os.environ["ACTIONS_ID_TOKEN_REQUEST_TOKEN"]))[
        "value"
    ]
    lease = json.loads(
        request(
            ORIGIN + "/telemetry/lease",
            oidc,
            {"run_id": str(args.run_id), "attempt": args.attempt},
        )
    )
    if not lease.get("granted"):
        print("Summary deferred: shared GitHub budget unavailable")
        return
    calls = 0

    def github(path, binary=False):
        nonlocal calls
        if calls >= lease["max_requests"]:
            raise RuntimeError("Summary request allowance exhausted")
        calls += 1
        try:
            value = request(
                "https://api.github.com/repos/TauCetiProject/TauCeti/" + path,
                os.environ["GH_TOKEN"],
            )
        except HTTPFailure as error:
            if error.status in (403, 429):
                request(
                    ORIGIN + "/telemetry/quota",
                    oidc,
                    {
                        "status": error.status,
                        "retry_after": error.retry_after,
                        "remaining": error.remaining,
                        "reset": error.reset,
                    },
                )
            raise
        return value if binary else json.loads(value)

    run = github(f"actions/runs/{args.run_id}/attempts/{args.attempt}")
    if (
        run.get("repository", {}).get("full_name") != "TauCetiProject/TauCeti"
        or run.get("run_attempt") != args.attempt
        or run.get("path")
        not in (".github/workflows/pr-build.yml", ".github/workflows/ci.yml")
    ):
        raise RuntimeError("Run identity mismatch")
    listing = github(
        f"actions/runs/{args.run_id}/attempts/{args.attempt}/jobs?per_page=100"
    )
    jobs = listing["jobs"]
    summary = {
        "run": run,
        "jobs": jobs,
        "verified_jobs": listing["total_count"] <= len(jobs),
    }
    try:
        artifacts = github(
            f"actions/runs/{args.run_id}/artifacts?name=ci-telemetry&per_page=100"
        )["artifacts"]
        for artifact in artifacts:
            created = artifact.get("created_at", "")
            if (
                not artifact.get("expired")
                and run.get("run_started_at", "")
                <= created
                <= run.get("updated_at", "")
                and artifact.get("size_in_bytes", MAX_BYTES + 1) <= MAX_BYTES
            ):
                summary["telemetry"] = telemetry(
                    github(f"actions/artifacts/{artifact['id']}/zip", binary=True)
                )
                break
    except (RuntimeError, ValueError, KeyError, zipfile.BadZipFile):
        print("Phase telemetry unavailable; retaining step timing")
    for job in jobs:
        if job.get("conclusion") == "failure" and calls < lease["max_requests"]:
            failed = next(
                (s for s in job.get("steps", []) if s.get("conclusion") == "failure"),
                {},
            )
            try:
                job["failure_excerpt"] = excerpt(
                    github(f"actions/jobs/{job['id']}/logs", binary=True).decode(
                        "utf-8", errors="replace"
                    ),
                    failed,
                )
            except RuntimeError:
                job["failure_excerpt"] = None
    request(ORIGIN + "/telemetry", oidc, summary)
    print(
        f"Published attempt {args.attempt} summary using {calls}/{lease['max_requests']} reserved requests"
    )


if __name__ == "__main__":
    main()
