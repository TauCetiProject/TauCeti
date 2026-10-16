#!/usr/bin/env python3
"""Prepare one deterministic PR integration; never execute candidate configuration.

Raw-head scope, Lake attestation and (when applicable) forward-bump validation must
precede this tool. Frozen staging/merge-group candidates are recorded unchanged.
All Git operations use a new repository and a minimal environment: candidate Git
config, hooks, filters, replacement refs and external merge drivers are not loaded.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

PINS = ("lake-manifest.json", "lean-toolchain")
LAKEFILES = ("lakefile.toml", "lakefile.lean")
MODES = ("pr-integration", "frozen-candidate")


class IntegrationConflict(ValueError):
    pass


def sha(value):
    if (not isinstance(value, str) or not re.fullmatch(r"[0-9a-f]{40}", value)
            or value == "0" * 40):
        raise ValueError("expected an immutable 40-character object ID")
    return value


def verify(record, head, base, mode):
    sha(head)
    sha(base)
    if mode not in MODES or not isinstance(record, dict):
        raise ValueError("missing integration identity")
    if (record.get("schema") != 1 or record.get("mode") != mode
            or record.get("head_sha") != head or record.get("base_sha") != base):
        raise ValueError("integration identity does not match this dispatch")
    sha(record.get("tested_sha"))
    sha(record.get("tested_tree"))
    if mode == "frozen-candidate" and record["tested_sha"] != head:
        raise ValueError("a frozen candidate must be tested unchanged")
    if record.get("pin_resolution") not in ("merged", "validated-head-pins"):
        raise ValueError("missing pin resolution identity")
    return record


def prepare(candidate, base_checkout, head, base, mode, pins_changed=False, bump_validated=False):
    sha(head)
    sha(base)
    if mode not in MODES:
        raise ValueError("unknown candidate contract")
    if pins_changed and not bump_validated:
        raise ValueError("pin-changing head lacks trusted forward-bump validation")
    candidate, base_checkout = Path(candidate).absolute(), Path(base_checkout).absolute()
    git = shutil.which("git")
    if git is None:
        raise OSError("Git unavailable")
    # Only the object databases are read from the checkouts. Their .git/config,
    # refs and working-tree attributes never configure our Git process.
    objects = [(path / ".git/objects").resolve(strict=True) for path in (candidate, base_checkout)]
    with tempfile.TemporaryDirectory(prefix="pr-integration-") as temporary:
        env = {"PATH": os.defpath, "HOME": temporary, "LC_ALL": "C",
               "GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": "/dev/null",
               "GIT_ALTERNATE_OBJECT_DIRECTORIES": os.pathsep.join(map(str, objects)),
               "GIT_AUTHOR_NAME": "Tau Ceti CI", "GIT_COMMITTER_NAME": "Tau Ceti CI",
               "GIT_AUTHOR_EMAIL": "ci@tauceti.invalid", "GIT_COMMITTER_EMAIL": "ci@tauceti.invalid",
               "GIT_AUTHOR_DATE": "2000-01-01T00:00:00Z", "GIT_COMMITTER_DATE": "2000-01-01T00:00:00Z"}
        repository = Path(temporary) / "repo.git"
        subprocess.run([git, "init", "-q", "--bare", "--template=", str(repository)], env=env, check=True)
        command = [git, "--no-replace-objects", f"--git-dir={repository}",
                   "-c", "core.hooksPath=/dev/null", "-c", "core.attributesFile=/dev/null"]

        def run(*args, data=None, check=True):
            return subprocess.run(command + list(args), input=data, env=env, check=check,
                                  stdout=subprocess.PIPE, stderr=subprocess.PIPE)

        def entry(commit, path):
            return run("ls-tree", commit, "--", path).stdout

        for commit in (head, base):
            if run("cat-file", "-t", commit).stdout != b"commit\n":
                raise ValueError("candidate endpoint is not a commit")
        # Validate the checked-out identities without reading checkout configuration.
        for checkout, expected in ((candidate, head), (base_checkout, base)):
            got = (checkout / '.git/HEAD').read_text().strip()
            if got != expected:
                raise ValueError("checkout does not match captured dispatch identity")

        resolution = "merged"
        if mode == "frozen-candidate":
            tested = head
            tree = run("rev-parse", f"{head}^{{tree}}").stdout.decode().strip()
        else:
            merged = run("merge-tree", "--write-tree", "--name-only", "-z", base, head, check=False)
            if merged.returncode not in (0, 1):
                raise ValueError("Git could not assemble the captured integration")
            fields = merged.stdout.split(b"\0")
            tree = sha(fields[0].decode())
            conflicts = []
            if merged.returncode == 1:
                for field in fields[1:]:
                    if not field:
                        break
                    conflicts.append(field)
                if not conflicts or not pins_changed or any(p.decode() not in PINS for p in conflicts):
                    raise IntegrationConflict(f"integration conflict between B={base} and H={head}: {conflicts!r}; needs human resolution (not stacking evidence)")
            if pins_changed:
                # check-bump already validated the COMPLETE head pin pair against B.
                # Preserve it as a pair, including when both branches bumped the same
                # pin. Never combine JSON fragments or silently replace an authorized
                # bump with base pins. Other conflicts still require human resolution.
                run("read-tree", tree)
                for path in PINS:
                    raw = entry(head, path).decode().split()
                    if len(raw) != 4 or raw[:2] != ["100644", "blob"]:
                        raise ValueError("validated head pin is not an ordinary file")
                    run("update-index", "--add", "--cacheinfo", f"100644,{raw[2]},{path}")
                tree = run("write-tree").stdout.decode().strip()
                resolution = "validated-head-pins"
            # The executable Lake configuration must come from captured trusted B.
            # No reset/overlay of candidate infrastructure: all other candidate
            # content remains in the tested tree, but the harness is workflow-pinned.
            for path in LAKEFILES + PINS:
                expected = head if pins_changed and path in PINS else base
                actual = entry(tree, path)
                if actual != entry(expected, path):
                    raise ValueError(f"integrated {path} differs from its authorized configuration")
                if actual and not actual.startswith(b"100644 blob "):
                    raise ValueError(f"integrated {path} is not an ordinary file")
            tested = run("commit-tree", tree, "-p", base, "-p", head,
                         data=f"CI integration of {head} into {base}\n".encode()).stdout.decode().strip()
            # Materialize using only our clean repository/config. Keep raw objects
            # available for immutable scope/lint comparisons and ancestor cache reads.
            raw_checkout = candidate.with_name(candidate.name + "-raw-head")
            if raw_checkout.exists():
                raise ValueError("raw-head archive path already exists")
            candidate.rename(raw_checkout)
            try:
                candidate.mkdir()
                shutil.move(str(repository), str(candidate / ".git"))
                objects[0] = raw_checkout / ".git/objects"
                (candidate / ".git/objects/info/alternates").write_text("\n".join(map(str, objects)) + "\n")
                # read-tree for pin resolution populated only the temporary index,
                # not a worktree. Discard it so checkout materializes every file.
                (candidate / ".git/index").unlink(missing_ok=True)
                # Drop the temporary alternates environment; the permanent paths
                # above now refer to the retained raw checkout and captured base.
                env.pop("GIT_ALTERNATE_OBJECT_DIRECTORIES")
                subprocess.run([git, "--no-replace-objects", f"--git-dir={candidate / '.git'}",
                                f"--work-tree={candidate}", "-c", "core.bare=false",
                                "-c", "core.hooksPath=/dev/null", "checkout", "--quiet", "--detach", tested],
                               env=env, check=True)
                # Persist the ordinary checkout shape for downstream trusted tools.
                subprocess.run([git, f"--git-dir={candidate / '.git'}", "config", "core.bare", "false"],
                               env=env, check=True)
            except Exception:
                shutil.rmtree(candidate)
                raw_checkout.rename(candidate)
                raise
        return verify(dict(schema=1, mode=mode, head_sha=head, base_sha=base,
                           tested_sha=tested, tested_tree=tree, pin_resolution=resolution), head, base, mode)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("prepare", "verify"))
    parser.add_argument("--head", required=True)
    parser.add_argument("--base", required=True)
    parser.add_argument("--mode", required=True, choices=MODES)
    parser.add_argument("--identity", type=Path, required=True)
    parser.add_argument("--tested-sha")
    parser.add_argument("--tested-tree")
    parser.add_argument("--candidate", default="pr")
    parser.add_argument("--base-checkout", default="base")
    parser.add_argument("--pins-changed", choices=("0", "1"), default="0")
    parser.add_argument("--bump-validated", choices=("0", "1"), default="0")
    args = parser.parse_args()
    try:
        if args.action == "verify":
            record = verify(json.loads(args.identity.read_text()), args.head, args.base, args.mode)
            if (record["tested_sha"] != sha(args.tested_sha)
                    or record["tested_tree"] != sha(args.tested_tree)):
                raise ValueError("tested outputs disagree with recorded identity")
        else:
            record = prepare(args.candidate, args.base_checkout, args.head, args.base, args.mode,
                             args.pins_changed == "1", args.bump_validated == "1")
            args.identity.write_text(json.dumps(record, sort_keys=True) + "\n")
        print(json.dumps(record, sort_keys=True))
        if args.action == "prepare":
            with open(os.environ["GITHUB_OUTPUT"], "a") as output:
                output.write(f"tested_sha={record['tested_sha']}\ntested_tree={record['tested_tree']}\n")
    except IntegrationConflict as error:
        print(f"::error::{error}")
        return 2
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"::error::integration identity/preparation failed: {error}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
