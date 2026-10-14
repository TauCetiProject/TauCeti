"""Validate bors dispatch identity before GitHub applies candidate supersession.

This is scheduling metadata, not approval or proof of a trusted candidate. The
existing staging-ref, ancestry, scope, sandbox and publisher gates still apply.
Run only from the dispatch workflow's pinned trusted checkout.
"""

import hashlib
import json
import os
import pathlib
import re
import subprocess


def concurrency_group(repository, payload):
    if not isinstance(repository, str) or re.fullmatch(
            r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository) is None:
        raise ValueError("invalid repository identity")
    if not isinstance(payload, dict):
        raise ValueError("missing staging payload")
    batch = payload.get("batch_id")
    if type(batch) is not int or not 0 < batch < 2**63:
        raise ValueError("batch_id must be a positive integer")
    head, base = (payload.get(field) for field in ("head_sha", "base_sha"))
    if any(not isinstance(value, str) or re.fullmatch(r"[0-9a-f]{40}", value) is None
           for value in (head, base)):
        raise ValueError("head_sha and base_sha must be commit SHAs")
    branch = payload.get("base_ref")
    if not isinstance(branch, str) or not branch or "\x00" in branch:
        raise ValueError("base_ref must be a branch name")
    if subprocess.run(["git", "check-ref-format", "refs/heads/" + branch],
                      capture_output=True).returncode:
        raise ValueError("invalid base_ref")
    # Hash a structured tuple: delimiters cannot alias fields, and GitHub's
    # case-insensitive groups cannot conflate case-sensitive branch names.
    # Repository names are case-insensitive on GitHub; branch names are not.
    identity = json.dumps([repository.lower(), branch, batch, head, base],
                          separators=(",", ":"), ensure_ascii=True)
    return "pr-build-bors-staging-" + hashlib.sha256(identity.encode()).hexdigest()


def main():
    event = json.loads(pathlib.Path(os.environ["GITHUB_EVENT_PATH"]).read_text())
    if event.get("action") != "tauceti-bors-staging":
        raise ValueError("not a bors staging dispatch")
    group = concurrency_group(os.environ["GITHUB_REPOSITORY"], event.get("client_payload"))
    with pathlib.Path(os.environ["GITHUB_OUTPUT"]).open("a") as output:
        output.write(f"group={group}\n")
    print(f"Validated candidate concurrency group: {group}")


if __name__ == "__main__":
    main()
