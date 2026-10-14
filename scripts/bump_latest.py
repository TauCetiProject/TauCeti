#!/usr/bin/env python3
"""Maintain one fixed-target Mathlib bump, selected by upstream cache availability."""

import argparse
import base64
import copy
import json
import os
import re
import subprocess
import tempfile
from pathlib import Path

from bump_manifest import problems
from pr_status.core import KEEP_LABELS, automatic_bump

REPO = "TauCetiProject/TauCeti"
MATHLIB = "leanprover-community/mathlib4"
BOT = "tauceti-review-bot[bot]"


def command(args, *, cwd=None, env=None, combined=False):
    result = subprocess.run(args, cwd=cwd, env=env, text=True, capture_output=True, timeout=1800)
    if result.returncode:
        raise RuntimeError(f"{args[0]} failed: {result.stderr or result.stdout}")
    return (result.stdout + ("\n" + result.stderr if combined else "")).strip()


def api(path):
    return json.loads(command(["gh", "api", path]))


def sha(value):
    if not isinstance(value, str) or not re.fullmatch("[0-9a-f]{40}", value):
        raise ValueError("Expected a full commit SHA")
    return value


def pin(manifest):
    values = [p for p in manifest["packages"] if p.get("name") == "mathlib"]
    if len(values) != 1:
        raise ValueError("Expected exactly one Mathlib dependency")
    return sha(values[0]["rev"])


def upstream_file(commit, path):
    data = api(f"repos/{MATHLIB}/contents/{path}?ref={sha(commit)}")
    if data["encoding"] != "base64":
        raise ValueError("Upstream file encoding unavailable")
    return base64.b64decode(data["content"]).decode()


def relationship(base, target):
    if base == target:
        return "identical"
    status = api(f"repos/{MATHLIB}/compare/{sha(base)}...{sha(target)}?per_page=1")["status"]
    if status not in {"ahead", "behind", "identical"}:
        raise RuntimeError("Mathlib history diverged; refusing to change a dependency target")
    return status


def open_bumps():
    found = []
    for page in range(1, 100):
        prs = api(f"repos/{REPO}/pulls?state=open&per_page=100&page={page}")
        found.extend(p for p in prs if automatic_bump(p, repo=REPO) and p["base"]["ref"] == "main")
        if len(prs) < 100:
            return found
    raise RuntimeError("Open pull request listing was truncated")


def bump_state(current, prs):
    """A held PR is left alone; otherwise only an obsolete target may be closed."""
    active, obsolete = [], []
    for pr in prs:
        if pr.get("draft") or {p["name"].lower() for p in pr.get("labels", [])} & KEEP_LABELS:
            active.append(pr)
            continue
        data = api(f"repos/{REPO}/contents/lake-manifest.json?ref={sha(pr['head']['sha'])}")
        target = pin(json.loads(base64.b64decode(data["content"])))
        (active if relationship(current, target) == "ahead" else obsolete).append(pr)
    return active, obsolete


def ordered_runs(runs, history):
    positions = {value: i for i, value in enumerate(history)}
    eligible = {}
    for run in runs:
        target = run.get("head_sha")
        if (
            run.get("event") == "push"
            and run.get("head_branch") == "master"
            and run.get("status") == "completed"
            and run.get("conclusion") == "success"
            and run.get("head_repository", {}).get("full_name") == MATHLIB
            and target in positions
        ):
            eligible.setdefault(target, run)
    return sorted(eligible.values(), key=lambda r: positions[r["head_sha"]])


def verify_cache(checkout, target):
    """Only a proven missing cache falls back. Network/tool errors fail the run."""
    command(["git", "checkout", "--force", "--detach", sha(target)], cwd=checkout)
    # The subprocesses execute only trusted upstream sources, in a separate read-only
    # workflow job. Do not inherit GitHub/runner credentials or use warmed oleans.
    probe_home = checkout.parent / "probe-home"
    probe_home.mkdir(exist_ok=True)
    env = {
        k: os.environ[k]
        for k in ("PATH", "ELAN_HOME", "SSL_CERT_FILE", "SSL_CERT_DIR")
        if k in os.environ
    }
    env["HOME"] = str(probe_home)
    env.setdefault("ELAN_HOME", str(Path.home() / ".elan"))
    env["MATHLIB_CACHE_DIR"] = str(checkout.parent / "downloads")
    env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
    env["LAKE_NO_CACHE"] = "1"
    toolchain = (checkout / "lean-toolchain").read_text().strip()
    command(["elan", "toolchain", "install", toolchain], cwd=checkout, env=env)
    lake = ["elan", "run", toolchain, "lake"]
    output = command(
        [*lake, "exe", "cache", "--cache-from=master", "get", "Mathlib"],
        cwd=checkout,
        env=env,
        combined=True,
    )
    if "were not found in the cache" in output:
        print(f"Cache incomplete at {target}; trying the next built master commit.")
        return False
    command([*lake, "build", "--no-build", "--rehash", "Mathlib"], cwd=checkout, env=env)
    print(f"Full Mathlib cache verified at {target}.")
    return True


def select_target(current):
    with tempfile.TemporaryDirectory(prefix="tauceti-bump-") as tmp:
        checkout = Path(tmp) / "mathlib"
        command(
            [
                "git",
                "clone",
                "--filter=blob:none",
                "--no-checkout",
                "--single-branch",
                "--branch",
                "master",
                f"https://github.com/{MATHLIB}",
                str(checkout),
            ]
        )
        history = command(
            ["git", "rev-list", "--first-parent", "origin/master"], cwd=checkout
        ).splitlines()
        if current not in history:
            raise RuntimeError("Current pin is not on canonical Mathlib master history")
        newer = history[: history.index(current)]
        if not newer:
            return None
        runs = []
        for page in range(1, 101):
            batch = api(
                f"repos/{MATHLIB}/actions/workflows/build.yml/runs"
                f"?branch=master&event=push&status=success&per_page=100&page={page}"
            )["workflow_runs"]
            runs.extend(batch)
            # Walk actual Git ancestry, not completion timestamps. Before probing a
            # candidate we must know no newer successful run lives on a later page.
            if len(batch) < 100 or any(
                r["head_sha"] == current or r["head_sha"] in history[len(newer) :] for r in batch
            ):
                break
        else:
            raise RuntimeError("Upstream workflow history was truncated")
        for run in ordered_runs(runs, newer):
            if verify_cache(checkout, run["head_sha"]):
                return run
        return None


def derive_manifest(base, upstream, target):
    result = copy.deepcopy(base)
    mathlib = copy.deepcopy(next(p for p in base["packages"] if p["name"] == "mathlib"))
    mathlib["rev"] = sha(target)
    result["version"] = upstream["version"]
    result["packages"] = [mathlib] + [dict(p, inherited=True) for p in upstream["packages"]]
    issues = problems(result, upstream, base)
    if issues:
        raise ValueError(issues[0])
    return result


def publish(target, run_id):
    base_sha = command(["git", "rev-parse", "HEAD"])
    current = pin(json.loads(Path("lake-manifest.json").read_text()))
    active, obsolete = bump_state(current, open_bumps())
    if active:
        print(f"Preserving active bump #{active[0]['number']} and its fixed target.")
        return
    for pr in obsolete:
        fresh = api(f"repos/{REPO}/pulls/{pr['number']}")
        if fresh["state"] != "open":
            continue
        if bump_state(current, [fresh])[0]:
            print(f"Preserving updated or held bump #{pr['number']}.")
            return
        command(
            [
                "gh",
                "pr",
                "close",
                str(pr["number"]),
                "--repo",
                REPO,
                "--comment",
                "Closing this obsolete bump: main already pins the same or a newer Mathlib commit.",
            ]
        )
    if not target or relationship(current, target) != "ahead":
        return
    run = api(f"repos/{MATHLIB}/actions/runs/{int(run_id)}")
    if ordered_runs([run], [sha(target)]) != [run]:
        raise ValueError("Target does not match a successful canonical master push run")
    branch = f"bump-mathlib/{target}"
    previous = api(f"repos/{REPO}/pulls?state=all&head=TauCetiProject:{branch}&per_page=100")
    if previous:
        print(f"Leaving existing PR #{previous[0]['number']} in its current state.")
        return
    upstream = json.loads(upstream_file(target, "lake-manifest.json"))
    manifest = derive_manifest(json.loads(Path("lake-manifest.json").read_text()), upstream, target)
    toolchain = upstream_file(target, "lean-toolchain")
    with tempfile.TemporaryDirectory(prefix="tauceti-publish-") as tmp:
        candidate = Path(tmp) / "candidate"
        command(["git", "worktree", "add", "--detach", str(candidate), base_sha])
        try:
            (candidate / "lake-manifest.json").write_text(json.dumps(manifest, indent=1) + "\n")
            (candidate / "lean-toolchain").write_text(toolchain)
            command(
                [
                    "bash",
                    str(Path("scripts/check-bump.sh").resolve()),
                    str(Path.cwd()),
                    str(Path.cwd()),
                    str(candidate),
                ]
            )
            command(["git", "add", "lake-manifest.json", "lean-toolchain"], cwd=candidate)
            git_env = dict(
                os.environ,
                GIT_AUTHOR_NAME=BOT,
                GIT_COMMITTER_NAME=BOT,
                GIT_AUTHOR_EMAIL="290224625+tauceti-review-bot[bot]@users.noreply.github.com",
                GIT_COMMITTER_EMAIL="290224625+tauceti-review-bot[bot]@users.noreply.github.com",
            )
            command(
                ["git", "commit", "-m", f"chore: bump Mathlib to {target[:8]}"],
                cwd=candidate,
                env=git_env,
            )
            remote = command(["git", "ls-remote", "--refs", "origin", f"refs/heads/{branch}"])
            if not remote:
                command(
                    [
                        "git",
                        "push",
                        f"--force-with-lease=refs/heads/{branch}:",
                        "origin",
                        f"HEAD:refs/heads/{branch}",
                    ],
                    cwd=candidate,
                )
            else:
                # Creation succeeded before a previous run was interrupted. Never
                # replace that branch: it may already contain source repairs.
                data = api(f"repos/{REPO}/contents/lake-manifest.json?ref={branch}")
                if pin(json.loads(base64.b64decode(data["content"]))) != target:
                    raise ValueError("Existing bump branch has a different dependency target")
            body = Path(tmp) / "body.md"
            body.write_text(
                f"Bump Mathlib to [{target[:8]}](https://github.com/{MATHLIB}/commit/{target}), "
                f"with its matching Lean toolchain and dependency manifest.\n\n"
                f"The full canonical Mathlib cache was verified before selecting this target. "
                f"Upstream build: {run['html_url']}.\n\n"
                "Workers repair TauCeti against this fixed target and may checkpoint partial "
                "source repairs. Full CI, audits, and current-head review are required to merge.\n\n"
                "Roadmap: none\n"
            )
            command(
                [
                    "gh",
                    "pr",
                    "create",
                    "--repo",
                    REPO,
                    "--base",
                    "main",
                    "--head",
                    branch,
                    "--title",
                    f"chore: bump Mathlib to {target[:8]}",
                    "--body-file",
                    str(body),
                ]
            )
        finally:
            command(["git", "worktree", "remove", "--force", str(candidate)])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument(
        "--select",
        action="store_true",
        help="Read-only selection for the credential-free workflow job",
    )
    parser.add_argument(
        "--publish", metavar="SHA", help="Publish the target verified by the selection job"
    )
    parser.add_argument("--run-id", type=int)
    args = parser.parse_args()
    if args.publish is not None:
        if (
            args.dry_run
            or args.select
            or args.run_id is None
            or (args.publish and args.run_id <= 0)
        ):
            parser.error("--publish requires --run-id and cannot be combined with selection")
        publish(sha(args.publish) if args.publish else "", args.run_id)
        return
    current = pin(json.loads(Path("lake-manifest.json").read_text()))
    active, obsolete = bump_state(current, open_bumps())
    selected = None if active else select_target(current)
    target = selected["head_sha"] if selected else ""
    run_id = selected["id"] if selected else 0
    print(
        f"Current pin: {current}; target: {target or 'none'}; "
        f"active bumps: {[p['number'] for p in active]}; obsolete: {[p['number'] for p in obsolete]}"
    )
    if os.environ.get("GITHUB_OUTPUT"):
        with open(os.environ["GITHUB_OUTPUT"], "a") as out:
            out.write(
                f"target={target}\nrun_id={run_id}\nreconcile={str(not active and bool(target or obsolete)).lower()}\n"
            )
    if not args.dry_run and not args.select:
        publish(target, run_id)


if __name__ == "__main__":
    main()
