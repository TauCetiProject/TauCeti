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

from bors_observation import REPO, observation, requested_batch, sha, valid_observation
ALLOWED_ROOT = {"TauCeti.lean", "lake-manifest.json", "lean-toolchain",
                "docbuild/docs/references.bib"}


def in_scope(path):
    return isinstance(path, str) and (path.startswith("TauCeti/") or path in ALLOWED_ROOT)


def github(path):
    endpoint = path if path.startswith("/") else f"repos/{REPO}/{path}"
    return json.loads(subprocess.check_output(["gh", "api", endpoint],
                                             text=True, timeout=45))


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


def administrator(actor_id, api):
    """Check effective permissions, including admin access inherited from a team."""
    if type(actor_id) is not int or actor_id <= 0:
        return False
    user = api(f"/user/{actor_id}")
    if not isinstance(user, dict):
        raise ValueError("approval actor unavailable")
    login = user.get("login")
    if (user.get("id") != actor_id or not isinstance(login, str)
            or re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_-]*", login) is None):
        raise ValueError("approval actor unavailable")
    permission = api(f"collaborators/{login}/permission")
    if (not isinstance(permission, dict) or not isinstance(permission.get("user"), dict)
            or permission["user"].get("id") != actor_id):
        raise ValueError("approval actor changed during permission lookup")
    return permission.get("permission") == "admin"


def approved(approvals, pr, head, base, api):
    matches = [a for a in approvals if isinstance(a, dict) and a.get("pr") == pr]
    if len(matches) != 1:
        return False
    actor_id = matches[0].get("actor_id")
    return matches[0] == {
        "pr": pr, "actor_id": actor_id, "head_sha": head, "merge_base_sha": base
    } and administrator(actor_id, api)


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
    if (not sha(head) or not sha(base) or not valid_observation(data,"main")
            or not isinstance(data.get("scope_approvals"), list)):
        return False
    approvals = data["scope_approvals"]
    if pr is not None:
        live = current_pr(pr, head, api)
        return merge_base(live, head, api) == base and approved(approvals, pr, head, base, api)

    try:
        batch = requested_batch(data, head, base, batch_id=batch_id)
    except ValueError:
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
        is_approved = approved(approvals, number, member_head, member_base, api)
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
    print("restricted paths approved by a repository admin through bors" if ok else "no valid bors scope approval")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
