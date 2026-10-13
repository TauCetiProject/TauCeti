"""Verify bors's human approval before waiving the restricted-path rule.

Run only from workflow-pinned tooling. The bors HTTPS observation, rather than
dispatch payloads or contributor comments, supplies approval and batch membership.
No candidate code is executed. Missing/incomplete observations fail closed.
"""

import argparse
import json
import pathlib
import re
import subprocess
import urllib.request

REPO = "TauCetiProject/TauCeti"
ACTOR_ID = 477956  # kim-em's stable GitHub user ID
OBSERVATION_URL = "https://bors.taucetiproject.org/repositories/1/active-batches?base=main"
ALLOWED_ROOT = {"TauCeti.lean", "lake-manifest.json", "lean-toolchain",
                "docbuild/docs/references.bib"}


def sha(value):
    return isinstance(value, str) and re.fullmatch(r"[0-9a-f]{40}", value) is not None


def in_scope(path):
    return isinstance(path, str) and (path.startswith("TauCeti/") or path in ALLOWED_ROOT)


def github(path):
    return json.loads(subprocess.check_output(["gh", "api", f"repos/{REPO}/{path}"],
                                             text=True, timeout=45))


def observation(batch_id=None):
    url = OBSERVATION_URL + (f"&batch_id={batch_id}" if batch_id is not None else "")
    request = urllib.request.Request(url, headers={
        "Cache-Control": "no-cache", "User-Agent": "TauCetiScopeApproval/1.0"
    })
    with urllib.request.urlopen(request, timeout=30) as response:
        return json.load(response)


def current_pr(pr, head, api):
    data = api(f"pulls/{pr}")
    if (data.get("number") != pr or data.get("state") != "open" or data.get("draft") is not False
            or data.get("head", {}).get("sha") != head
            or data.get("base", {}).get("ref") != "main"
            or not sha(data.get("base", {}).get("sha"))):
        raise ValueError("PR revision or target changed")
    return data


def merge_base(data, head, api):
    base = api(f"compare/{data['base']['sha']}...{head}?per_page=1")["merge_base_commit"]["sha"]
    if not sha(base):
        raise ValueError("merge base unavailable")
    return base


def approved(approvals, pr, head, base):
    matches = [a for a in approvals if isinstance(a, dict) and a.get("pr") == pr]
    return len(matches) == 1 and matches[0] == {
        "pr": pr, "actor_id": ACTOR_ID, "head_sha": head, "merge_base_sha": base
    }


def paths(data, api):
    # GitHub caps PR file listings at 3000. Never treat a truncated list as a
    # complete proof; include both sides of a rename and all deleted paths.
    count = data.get("changed_files")
    if type(count) is not int or not 0 < count <= 3000:
        raise ValueError("complete PR file count unavailable")
    files = []
    for page in range(1, (count + 99) // 100 + 1):
        result = api(f"pulls/{data['number']}/files?per_page=100&page={page}")
        if not isinstance(result, list):
            raise ValueError("invalid PR files")
        files.extend(result)
    names = [entry["filename"] for entry in files]
    if len(files) != count or len(set(names)) != count or not all(isinstance(n, str) and n for n in names):
        raise ValueError("incomplete PR files")
    for entry in files:
        if entry.get("status") == "renamed":
            previous = entry.get("previous_filename")
            if not isinstance(previous, str) or not previous:
                raise ValueError("rename source unavailable")
            names.append(previous)
    return names


def verify(data, head, base, *, pr=None, batch_id=None, combined_paths=None, api=github):
    if (not sha(head) or not sha(base) or data.get("schema") != "tauceti-bors.observation/v1"
            or data.get("repo") != REPO or data.get("base") != "main"
            or not isinstance(data.get("scope_approvals"), list)):
        return False
    approvals = data["scope_approvals"]
    if pr is not None:
        live = current_pr(pr, head, api)
        return merge_base(live, head, api) == base and approved(approvals, pr, head, base)

    batch = data.get("requested_batch")
    if (type(batch_id) is not int or not isinstance(batch, dict) or batch.get("id") != batch_id
            or batch.get("state") != "running" or batch.get("base") != "main"
            or batch.get("head_sha") != head or batch.get("base_sha") != base):
        return False
    members = batch.get("members")
    if not isinstance(members, list) or not 0 < len(members) <= 128:
        return False
    if not isinstance(combined_paths, list) or not combined_paths or not all(isinstance(p, str) and p for p in combined_paths):
        return False
    covered = set()
    seen = set()
    for member in members:
        number, member_head = member.get("pr"), member.get("head_sha")
        if type(number) is not int or number <= 0 or number in seen or not sha(member_head):
            return False
        seen.add(number)
        live = current_pr(number, member_head, api)
        member_base = merge_base(live, member_head, api)
        changed = paths(live, api)
        is_approved = approved(approvals, number, member_head, member_base)
        if any(not in_scope(path) for path in changed) and not is_approved:
            return False
        if is_approved:
            covered.update(changed)
        # PR file listings follow a mutable head. Confirm their revision and diff
        # again after pagination, including force pushes with an unchanged count.
        after = current_pr(number, member_head, api)
        if after.get("changed_files") != live.get("changed_files") or merge_base(after, member_head, api) != member_base:
            return False
    return all(in_scope(path) or path in covered for path in combined_paths)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--head", required=True)
    parser.add_argument("--base", required=True)
    parser.add_argument("--paths-file", help="complete workflow-pinned combined diff paths")
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--pr", type=int)
    group.add_argument("--batch-id", type=int)
    args = parser.parse_args()
    try:
        combined_paths = pathlib.Path(args.paths_file).read_text().splitlines() if args.paths_file else None
        ok = verify(observation(args.batch_id), args.head, args.base,
                    pr=args.pr, batch_id=args.batch_id, combined_paths=combined_paths)
    except (KeyError, TypeError, ValueError, OSError, subprocess.SubprocessError) as error:
        print(f"bors scope approval unavailable: {type(error).__name__}")
        ok = False
    print("restricted paths approved by kim-em through bors" if ok else "no valid bors scope approval")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
