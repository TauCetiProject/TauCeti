#!/usr/bin/env python3
"""Optional, trusted local dependency prefill after integrated-config attestation."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import tarfile
import tempfile
import time

CONFIG = ("lakefile.toml", "lake-manifest.json", "lean-toolchain")


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def hydrate(project, source):
    started = time.monotonic()
    destination = project / ".lake/packages"
    temporary = None
    try:
        metadata_path = source / "manifest.json"
        if not metadata_path.is_file():
            return dict(hit=False, reason="absent", seconds=time.monotonic() - started)
        if metadata_path.stat().st_size > 16384:
            raise ValueError("oversized metadata")
        metadata = json.loads(metadata_path.read_text())
        if (metadata["schema"] != 1 or metadata["platform"] != "Linux-x86_64"
                or platform.system() != "Linux" or platform.machine() != "x86_64"
                or metadata["project_path"] != str(project.resolve())
                or metadata["uid"] != os.getuid()
                or metadata["config_sha256"] != {name: digest(project / name) for name in CONFIG}):
            raise ValueError("identity mismatch")
        if destination.exists() or destination.is_symlink():
            raise ValueError("existing packages")
        payload = source / "packages.tar.zst"
        if (not payload.is_file() or payload.is_symlink()
                or payload.stat().st_size != metadata["payload_bytes"]
                or payload.stat().st_size > 1024**3
                or digest(payload) != metadata["payload_sha256"]):
            raise ValueError("payload mismatch")
        expected = json.loads((project / "lake-manifest.json").read_text())["packages"]
        names = {p["name"] for p in expected}
        if len(names) != len(expected) or any(not n or "/" in n or n in (".", "..") for n in names):
            raise ValueError("invalid package inventory")
        lake = project / ".lake"
        if lake.is_symlink() or not lake.is_dir():
            raise ValueError("Lake directory is not normalized")
        temporary = Path(tempfile.mkdtemp(prefix="dependency-prefill-", dir=lake))
        # Python's data filter confines extraction and rejects devices/escaping
        # links. Also confine every member to this payload's packages subtree.
        def package_filter(member, target):
            parts = Path(member.name).parts
            if len(parts) < 2 or parts[:2] != (".lake", "packages") or ".." in parts:
                raise ValueError("archive member outside packages")
            return tarfile.data_filter(member, target)
        # The payload is trusted and digest-checked before decompression. Limit
        # duration; failure only abandons the private temporary tree.
        env = {"PATH": os.environ.get("PATH", "/usr/bin:/bin"), "LANG": "C.UTF-8"}
        proc = subprocess.Popen(["zstd", "-dc", str(payload)], stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, env=env)
        try:
            with tarfile.open(fileobj=proc.stdout, mode="r|") as archive:
                archive.extractall(temporary, filter=package_filter)
            if proc.wait(timeout=10):
                raise ValueError("decompression failed")
        finally:
            proc.stdout.close()
            if proc.poll() is None:
                proc.kill()
            proc.wait()
        packages = temporary / ".lake/packages"
        if {p.name for p in packages.iterdir()} != names:
            raise ValueError("package inventory mismatch")
        for package in expected:
            directory = packages / package["name"]
            if directory.is_symlink() or not directory.is_dir():
                raise ValueError("package directory mismatch")
            def git(*arguments):
                return subprocess.check_output(
                    ["git", "-c", "core.hooksPath=/dev/null", "-c", "core.fsmonitor=false", "-C", str(directory), *arguments],
                    env={**env, "GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": "/dev/null"},
                    text=True, stderr=subprocess.DEVNULL, timeout=10).strip()
            if (git("rev-parse", "HEAD") != package["rev"]
                    or git("remote", "get-url", "origin").removesuffix(".git") != package["url"].removesuffix(".git")):
                raise ValueError("package pin mismatch")
        # Private fresh guest, after normalization, before any candidate code.
        # Publish only the complete validated tree; no partial .lake/packages.
        packages.rename(destination)
        return dict(hit=True, reason="validated", seconds=time.monotonic() - started,
                    payload_sha256=metadata["payload_sha256"], payload_bytes=metadata["payload_bytes"])
    except (OSError, ValueError, TypeError, KeyError, tarfile.TarError, subprocess.SubprocessError) as exc:
        return dict(hit=False, reason=(str(exc) or type(exc).__name__)[:240], seconds=time.monotonic() - started)
    finally:
        if temporary is not None:
            shutil.rmtree(temporary, ignore_errors=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path)
    parser.add_argument("--source", type=Path, default=Path("/opt/tauceti-dependency-prefill"))
    args = parser.parse_args()
    print("dependency-prefill " + json.dumps(hydrate(args.project, args.source), sort_keys=True))


if __name__ == "__main__":
    main()
