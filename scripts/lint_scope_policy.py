"""Bounded, fail-closed lookup of the PR branches and labels used by lint-scope.sh.

Only workflow-pinned tooling runs here, outside the candidate checkout. No Git
commands or candidate files/configuration are consulted while credentials exist.
There are no retries or label-pagination requests: any uncertainty selects full
lint. Metrics describe this policy lookup, excluding compare/local diff/step time.
"""

import json
import re
import resource
import subprocess
import sys
import tempfile
import time

MAX_PRS = 128
CHUNK_SIZE = 32
MAX_LABELS = 100
MAX_RESPONSE_BYTES = 1024 * 1024
REQUEST_SECONDS = 15
TOTAL_SECONDS = 45


class FullLint(Exception):
    """The caller must lint the entire library."""


def query_for(repo, numbers):
    owner, name = repo.split("/")
    fields = " ".join(
        f"pr{n}: pullRequest(number: {n}) {{ number headRefName "
        f"labels(first: {MAX_LABELS}) {{ totalCount pageInfo {{ hasNextPage }} "
        "nodes { name } } }" for n in numbers)
    return (f"query {{ repository(owner: {json.dumps(owner)}, name: {json.dumps(name)}) "
            f"{{ {fields} }} }}")


def response_limit():
    # gh writes to a private regular file: bound disk and memory even for a
    # broken server. Linux CI supplies resource; no candidate code runs here.
    resource.setrlimit(resource.RLIMIT_FSIZE, (MAX_RESPONSE_BYTES, MAX_RESPONSE_BYTES))


def request(query, timeout):
    with tempfile.TemporaryFile() as output:
        result = subprocess.run(
            ["gh", "api", "graphql", "-f", f"query={query}"],
            stdout=output, stderr=subprocess.DEVNULL, timeout=timeout,
            preexec_fn=response_limit)
        if result.returncode:
            raise FullLint("PR lint policy metadata request failed")
        output.seek(0)
        raw = output.read(MAX_RESPONSE_BYTES + 1)
    if len(raw) >= MAX_RESPONSE_BYTES:
        raise FullLint("PR lint policy response reached its size limit")
    return json.loads(raw)


def validate(data, numbers):
    # Reject partial GraphQL success even when the requested fields appear usable.
    if not isinstance(data, dict) or ("errors" in data and data["errors"] != []):
        raise FullLint("PR lint policy returned GraphQL errors or malformed data")
    repository = data["data"]["repository"]
    if not isinstance(repository, dict) or set(repository) != {f"pr{n}" for n in numbers}:
        raise FullLint("PR lint policy response is incomplete")
    for n in numbers:
        pr = repository[f"pr{n}"]
        if type(pr["number"]) is not int or pr["number"] != n:
            raise FullLint("PR lint policy returned the wrong PR")
        branch = pr["headRefName"]
        if not isinstance(branch, str) or not branch:
            raise FullLint(f"PR #{n} has no head branch metadata")
        labels = pr["labels"]
        nodes, count = labels["nodes"], labels["totalCount"]
        if (labels["pageInfo"]["hasNextPage"] is not False or type(count) is not int
                or not isinstance(nodes, list) or not 0 <= count <= MAX_LABELS
                or len(nodes) != count):
            raise FullLint(f"PR #{n} labels are truncated or malformed")
        names = [node["name"] for node in nodes]
        if any(not isinstance(name, str) or not name for name in names):
            raise FullLint(f"PR #{n} has malformed labels")
        if len(set(names)) != count:
            raise FullLint(f"PR #{n} has duplicate label metadata")
        if branch.startswith("lint-repair/"):
            raise FullLint(f"#{n} is a lint repair PR ({branch})")
        # Preserve the shell policy's comma-delimited matching even for unusual
        # label names containing commas; switching transport must not narrow lint.
        if any("full-lint" in name.split(",") for name in names):
            raise FullLint(f"#{n} is labelled full-lint")


def check_policy(repo, raw_numbers):
    start = time.monotonic()
    calls = 0
    numbers = []
    try:
        if not re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repo):
            raise FullLint("invalid policy repository")
        tokens = raw_numbers.split()
        if not 1 <= len(tokens) <= MAX_PRS or any(
                not re.fullmatch(r"[1-9][0-9]{0,9}", n) or int(n) > 2147483647 for n in tokens):
            raise FullLint("invalid or excessive attributed PR numbers")
        numbers = [int(n) for n in tokens]
        if len(set(numbers)) != len(numbers):
            raise FullLint("duplicate attributed PR numbers")
        for offset in range(0, len(numbers), CHUNK_SIZE):
            remaining = TOTAL_SECONDS - (time.monotonic() - start)
            if remaining <= 0:
                raise FullLint("PR lint policy lookup exceeded its time limit")
            chunk = numbers[offset:offset + CHUNK_SIZE]
            calls += 1
            validate(request(query_for(repo, chunk), min(REQUEST_SECONDS, remaining)), chunk)
    finally:
        print(f"lint-policy: prs={len(numbers)} requests={calls} "
              f"elapsed_seconds={time.monotonic() - start:.3f}", file=sys.stderr)


def main():
    try:
        check_policy(sys.argv[1], sys.stdin.read(2048))
    except (FullLint, OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        print(f"PR lint policy requires full-library lint: {error}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
