"""Small GitHub client for roadmap labels and advisory comments.

GH_READ_TOKEN selects the workflow token for reads; GH_TOKEN remains the App
token for writes whose events must reach downstream workflows. Local invocations
without GH_READ_TOKEN use the normal gh credential for both.
"""

from __future__ import annotations

import datetime as dt
import email.utils
import json
import math
import os
import re
import subprocess
import sys
import time


class APIError(RuntimeError):
    """A failed API request, retaining its HTTP status and parsed response data.

    ``status`` is zero when no HTTP response was received; ``data`` then holds
    a bounded diagnostic with the request's credentials redacted. The exception
    message identifies the method/path and the server's message, if present.
    """

    def __init__(self, method, path, status, data):
        self.status, self.data = status, data
        message = data.get("message", "request failed") if isinstance(data, dict) else "request failed"
        super().__init__(f"GitHub {method} {path}: HTTP {status}: {message}")


class Deferred(RuntimeError):
    """Stop this credential's requests; a later reconciliation must retry."""

    def __init__(self, credential, until):
        self.until = until
        reset = dt.datetime.fromtimestamp(until, dt.timezone.utc).isoformat()
        super().__init__(f"GitHub {credential} rate limited; deferred until {reset}")


def response(raw):
    """Split gh api --include's status/headers from its JSON body."""
    raw = raw.replace("\r\n", "\n")
    head, separator, body = raw.partition("\n\n")
    match = re.match(r"HTTP/\S+ (\d+)", head)
    if not separator or not match:
        raise RuntimeError("gh api returned no HTTP response headers")
    headers = {}
    for line in head.splitlines()[1:]:
        name, colon, value = line.partition(":")
        if colon:
            headers[name.lower()] = value.strip()
    try:
        data = json.loads(body) if body.strip() else None
    except json.JSONDecodeError:
        data = {"message": "non-JSON API response"}
    return int(match.group(1)), headers, data


def retry_after(value, now):
    if not value:
        return 0
    try:
        return max(0, float(value))
    except ValueError:
        try:
            return max(0, email.utils.parsedate_to_datetime(value).timestamp() - now)
        except (TypeError, ValueError, OverflowError):
            return 0


class GitHub:
    """A gh-backed client with separate read/write credentials and bounded retries.

    Reads use GH_READ_TOKEN when set; writes retain GH_TOKEN so App mutations
    can trigger downstream workflows. Without GH_READ_TOKEN, both use normal
    gh authentication. ``max_wait`` caps cumulative retry sleeps in seconds
    across this instance, excluding ordinary request time and write spacing.
    Requests try at most three times; exhausted quota waits raise Deferred and
    block further requests on that credential until reset. Mutations are spaced
    by one second within this instance; separate processes are not coordinated.

    Pagination helpers count every response. ``report`` emits request counts,
    GraphQL costs and observed quota headers to stderr and the Actions summary.
    """

    def __init__(self, *, max_wait=180):
        self.max_wait = max_wait
        self.waited = 0
        self.blocked = {}
        self.stats = {}
        self.known_labels = set()
        self.last_write = None

    def _credential(self, read):
        env = dict(os.environ)
        env.pop("GH_DEBUG", None)  # Request debug logs can contain comment bodies.
        token = env.pop("GH_READ_TOKEN", None)
        if read and token:
            env["GH_TOKEN"] = token
            env.pop("GITHUB_TOKEN", None)
            return "workflow-read", env
        return "app-write" if token else "gh-default", env

    def _record(self, credential, method, path, status, headers, read):
        stat = self.stats.setdefault(credential, {"requests": 0, "reads": 0, "writes": 0, "buckets": {}})
        stat["requests"] += 1
        stat["reads" if read else "writes"] += 1
        resource = headers.get("x-ratelimit-resource", "core")
        quota = {k: headers.get(f"x-ratelimit-{k}") for k in ("limit", "remaining", "reset")}
        stat["buckets"][resource] = quota
        # Only fixed API paths and numeric quota values are logged, never tokens or PR bodies.
        print("github-api: " + json.dumps({"credential": credential, "method": method,
              "path": path, "status": status, "resource": resource, **quota}), file=sys.stderr)

    def request(self, method, path, data=None, *, read=None):
        read = method == "GET" if read is None else read
        credential, env = self._credential(read)
        now = time.time()
        if self.blocked.get(credential, 0) > now:
            raise Deferred(credential, self.blocked[credential])
        for attempt in range(3):
            # GitHub recommends at least a second between mutative requests.
            if not read and self.last_write is not None:
                time.sleep(max(0, self.last_write + 1 - time.monotonic()))
            argv = ["gh", "api", "--include", "--method", method, path]
            if data is not None:
                argv += ["--input", "-"]
            result = subprocess.run(argv, input=json.dumps(data) if data is not None else None,
                                    env=env, capture_output=True, text=True)
            if not read:
                self.last_write = time.monotonic()
            # Network/CLI failures are ambiguous for a POST; do not blindly repeat it.
            try:
                status, headers, payload = response(result.stdout)
            except RuntimeError:
                # Missing HTTP headers are transport/CLI failures, not API validation.
                diagnostic = (result.stderr or "no HTTP response").strip()
                for name in ("GH_TOKEN", "GITHUB_TOKEN"):
                    secret = env.get(name)
                    if secret:
                        diagnostic = diagnostic.replace(secret, "[redacted]")
                status, headers, payload = 0, {}, {"message": diagnostic[:300]}
            self._record(credential, method, path, status, headers, read)
            if path == "graphql" and isinstance(payload, dict):
                rate = (payload.get("data") or {}).get("rateLimit") or {}
                if "cost" in rate:
                    stat = self.stats[credential]
                    stat["graphql_points"] = stat.get("graphql_points", 0) + rate["cost"]
            # GraphQL can refuse a query with HTTP 200 and an errors array.
            if path == "graphql" and isinstance(payload, dict) and payload.get("errors"):
                message = "; ".join(item.get("message", "GraphQL error") for item in payload["errors"])
                payload = {"message": message, "errors": payload["errors"]}
                kinds = {item.get("type") for item in payload["errors"]}
                if "rate limit" in message.lower() or "RATE_LIMITED" in kinds or headers.get("retry-after") or headers.get("x-ratelimit-remaining") == "0":
                    status = 403
                elif kinds & {"INTERNAL", "SERVICE_UNAVAILABLE", "TIMEOUT"} or any(
                    word in message.lower() for word in ("timed out", "timeout", "something went wrong")
                ):
                    status = 503
                else:
                    status = 422
            if 200 <= status < 300 and result.returncode == 0:
                return payload
            error = APIError(method, path, status, payload)
            message = str(error).lower()
            limited = status == 429 or (status == 403 and
                       (headers.get("retry-after") or headers.get("x-ratelimit-remaining") == "0" or
                        any(word in message for word in ("rate limit", "abuse detection", "creating content too quickly", "was submitted too quickly"))))
            if limited:
                now = time.time()
                delay = retry_after(headers.get("retry-after"), now)
                primary = headers.get("x-ratelimit-remaining") == "0" or (
                    re.search(r"(?:api )?rate limit (?:already )?exceeded", message) is not None
                    and "secondary" not in message)
                if primary:
                    # Missing reset data must not license a fast retry against an exhausted quota.
                    reset = float(headers.get("x-ratelimit-reset") or now + 3600)
                    delay = max(5, delay, reset - now + 5)
                elif not delay:
                    delay = 60 * 2 ** attempt
                delay = math.ceil(delay)
                until = now + delay
                if attempt == 2 or self.waited + delay > self.max_wait:
                    self.blocked[credential] = until
                    raise Deferred(credential, until)
                print(f"github-api: {credential} waiting {delay}s before retry", file=sys.stderr)
                time.sleep(delay)
                self.waited += delay
                continue
            # Retry reads and idempotent updates after server errors. Comment and label
            # creation POSTs are ambiguous after a server error, so reconciliation rereads state.
            if (status == 0 or status >= 500) and (read or (status != 0 and method in {"PATCH", "PUT", "DELETE"})) and attempt < 2:
                delay = 2 ** (attempt + 1)
                if self.waited + delay <= self.max_wait:
                    time.sleep(delay)
                    self.waited += delay
                    continue
            raise error
        raise AssertionError("unreachable")

    def graphql(self, query, variables):
        return self.request("POST", "graphql", {"query": query, "variables": variables}, read=True)["data"]

    def pages(self, path):
        # Explicit page numbers keep every response (and its rate-limit headers) visible.
        page = 1
        while True:
            rows = self.request("GET", f"{path}{'&' if '?' in path else '?'}per_page=100&page={page}")
            if not isinstance(rows, list):
                raise RuntimeError(f"GitHub {path}: expected an array")
            yield rows
            if len(rows) < 100:
                return
            page += 1

    def items(self, path):
        return [row for page in self.pages(path) for row in page]

    def report(self):
        summary = json.dumps(self.stats, sort_keys=True)
        print("github-api-summary: " + summary, file=sys.stderr)
        target = os.environ.get("GITHUB_STEP_SUMMARY")
        if target:
            with open(target, "a") as stream:
                stream.write("\nGitHub API usage (response-header readings):\n\n```json\n" + summary + "\n```\n")


def fingerprint(info):
    return (info["head"]["sha"], info["base"]["sha"], info.get("body") or "", info["state"])


PR_QUERY = """
query($owner: String!, $name: String!, $pr: Int!, $after: String) {
  rateLimit { cost }
  repository(owner: $owner, name: $name) {
    pullRequest(number: $pr) {
      title body state headRefOid baseRefOid baseRefName changedFiles updatedAt
      labels(first: 100) { nodes { name } pageInfo { hasNextPage } }
      files(first: 100, after: $after) {
        nodes { path changeType }
        totalCount
        pageInfo { hasNextPage endCursor }
      }
    }
  }
}
"""


HISTORY_QUERY = """
query($owner: String!, $name: String!, $first: Int!, $after: String) {
  rateLimit { cost }
  repository(owner: $owner, name: $name) {
    pullRequests(first: $first, after: $after, states: [OPEN, CLOSED, MERGED],
                 orderBy: {field: CREATED_AT, direction: DESC}) {
      nodes {
        number title body state headRefOid baseRefOid baseRefName changedFiles
        labels(first: 100) { nodes { name } pageInfo { hasNextPage } }
        files(first: 100) {
          nodes { path changeType }
          totalCount
          pageInfo { hasNextPage endCursor }
        }
      }
      pageInfo { hasNextPage endCursor }
    }
  }
}
"""


def snapshot_info(row):
    return {"title": row["title"], "body": row["body"], "state": row["state"].lower(),
            "head": {"sha": row["headRefOid"]},
            "base": {"sha": row["baseRefOid"], "ref": row["baseRefName"]},
            "changed_files": row["changedFiles"], "labels": row["labels"]["nodes"]}


def history_snapshots(api, repo, limit):
    """Bulk historical reads, ordered by creation as gh pr list --state all was.

    Only PRs with paginated labels/files need an individual snapshot query.
    """
    owner, name = repo.split("/")
    count, after = 0, None
    while count < limit:
        result = api.graphql(HISTORY_QUERY, {"owner": owner, "name": name,
                            "first": min(100, limit - count), "after": after})
        connection = result["repository"]["pullRequests"]
        for row in connection["nodes"]:
            count += 1
            pr = row["number"]
            files = row["files"]
            if row["labels"]["pageInfo"]["hasNextPage"] or files["pageInfo"]["hasNextPage"] or len(files["nodes"]) != row["changedFiles"] or len(files["nodes"]) != files["totalCount"]:
                try:
                    yield pr, pr_snapshot(api, repo, pr)
                except Deferred:
                    raise
                except APIError as error:
                    if error.status == 0:
                        raise
                    yield pr, error
                except Exception as error:
                    yield pr, error
            else:
                yield pr, {"info": snapshot_info(row), "files": [
                    {"filename": item["path"], "status": item["changeType"].lower()}
                    for item in files["nodes"]]}
        if not connection["pageInfo"]["hasNextPage"]:
            return
        cursor = connection["pageInfo"]["endCursor"]
        if not cursor or cursor == after:
            raise RuntimeError("Historical PR pagination did not advance")
        after = cursor


def pr_snapshot(api, repo, pr):
    """Fetch metadata, labels and files together, sharing one small query in the common case.

    Paginated diffs must keep the same head, base and body throughout.
    Incomplete/capped file lists are marked for conservative classification. GraphQL
    reads use GH_READ_TOKEN and its GraphQL bucket, leaving REST for label writes.
    """
    owner, name = repo.split("/")
    for _ in range(3):
        files, first, after = [], None, None
        while True:
            result = api.graphql(PR_QUERY, {"owner": owner, "name": name, "pr": pr, "after": after})
            row = result["repository"]["pullRequest"]
            if row is None:
                raise RuntimeError(f"PR #{pr}: not found")
            current = snapshot_info(row)
            if first is None:
                first = fingerprint(current)
            if first != fingerprint(current):
                break  # Discard the mixed diff and restart with the new head/body/base.
            connection = row["files"]
            files.extend({"filename": item["path"], "status": item["changeType"].lower()}
                         for item in connection["nodes"])
            if not connection["pageInfo"]["hasNextPage"] or len(files) >= 3000:
                current["files_capped"] = current["changed_files"] > 3000 and len(files) >= 3000
                current["incomplete_files"] = bool(connection["pageInfo"]["hasNextPage"]) or len(files) != current["changed_files"] or len(files) != connection["totalCount"]
                if row["labels"]["pageInfo"]["hasNextPage"]:
                    current["labels"] = api.items(f"repos/{repo}/issues/{pr}/labels")
                return {"info": current, "files": files}
            next_cursor = connection["pageInfo"]["endCursor"]
            if not next_cursor or next_cursor == after:
                raise RuntimeError(f"PR #{pr}: file pagination did not advance")
            after = next_cursor
    raise RuntimeError(f"PR #{pr}: changed while fetching its diff; retry reconciliation")
