#!/usr/bin/env python3
"""Bulk restore for TauCeti CI's fresh, private artifact cache.

On the original 17,631-module TauCeti workload with four CPUs, bulk preparation
plus a normal Lake build took 39.41/37.95s versus 88.86/86.96s stock. Every build
compiled zero modules and the output-artifact hashes matched. These local
measurements do not measure the saving on GitHub's original 190.4s restore.

Temporary workaround for https://github.com/leanprover/lean4/pull/15868.
Remove this script and its workflow invocation when the pinned toolchain provides
native bulk restoration. This only supports TauCeti's attested default layout
and its fresh private cache: mappings are removed after preparation. Run inside
the offline PR sandbox, or before main CI builds, before any library code runs.
"""

import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time


HASH = re.compile(r"[0-9a-f]{16}")
ARCHIVE = re.compile(r"[0-9a-f]{16}\.ltar")
SCHEMA = "2026-02-25"
MODULE = re.compile(r"TauCeti(?:\.[A-Za-z_][A-Za-z0-9_']*)*")


def unpack(project: Path) -> int:
    started = time.monotonic()
    project = project.resolve()
    build = project / ".lake/build"
    cache = project / ".lake/cache"
    outputs = cache / "outputs/TauCeti"
    # Historical local caches can contain overlapping archives for one module.
    # Only CI's freshly normalized, just-downloaded cache is supported here.
    # A root build directory means this is no longer the fresh CI state.
    if build.exists() or build.is_symlink() or not outputs.is_dir():
        print("bulk-unpack-cache: no fresh cache; using stock Lake restoration")
        return 0
    # This workaround knows only TauCeti's standard paths. Do not load the
    # candidate's Lake configuration or guess if its layout changes.
    try:
        import tomllib
        config = tomllib.loads((project / "lakefile.toml").read_text())
        libs = config.get("lean_lib", [])
        if ((project / "lakefile.lean").exists() or config.get("name") != "TauCeti"
                or any(config.get(key, default) != default for key, default in (
                    ("buildDir", ".lake/build"), ("leanLibDir", "lib/lean"),
                    ("irDir", "ir"), ("srcDir", ".")))
                or not isinstance(libs, list) or len(libs) != 1
                or not isinstance(libs[0], dict) or libs[0].get("name") != "TauCeti"
                or libs[0].get("srcDir", ".") != "."):
            raise ValueError("unsupported Lake layout")
    except (ImportError, OSError, ValueError, TypeError, AttributeError) as error:
        print(f"::warning::bulk-unpack-cache: {error}; using stock Lake restoration")
        return 0
    records = []
    record_paths = []
    archives = set()
    try:
        for path in sorted(outputs.glob("*.json")):
            if not HASH.fullmatch(path.stem) or path.is_symlink() or not path.is_file():
                raise ValueError("unexpected cache record")
            record = json.loads(path.read_text())
            if not isinstance(record, dict) or record.get("schemaVersion") != SCHEMA:
                raise ValueError("unknown cache schema")
            archive = record.get("data")
            # Structured output records and non-module artifacts need stock Lake.
            if not isinstance(archive, str) or not ARCHIVE.fullmatch(archive):
                raise ValueError("cache is not an archive-only revision")
            # One content-stable archive may have multiple input identities in a
            # historical cache. Avoid concurrent writes with conflicting hashes.
            if archive in archives:
                raise ValueError("overlapping historical cache entries")
            archives.add(archive)
            artifact = cache / "artifacts" / archive
            if artifact.is_symlink() or not artifact.is_file():
                raise ValueError("missing regular archive")
            records.append({"file": str(artifact), "hash": path.stem})
            record_paths.append(path)
    except (OSError, ValueError) as error:
        print(f"::warning::bulk-unpack-cache: {error}; using stock Lake restoration")
        return 0
    if not records:
        return 0
    with tempfile.TemporaryDirectory(prefix="bulk-unpack-", dir=project / ".lake") as temporary:
        staging = Path(temporary)
        # Archives store basenames, not module paths. Isolate their outputs and
        # obtain the module's full name from its .ilean JSON before installing.
        for record in records:
            base = staging / record["hash"]
            record["base"] = [str(base / "lib"), str(base / "ir")]
        sysroot = subprocess.check_output(["lean", "--print-prefix"], text=True).strip()
        leantar = Path(sysroot) / "bin/leantar"
        print(f"bulk-unpack-cache: restoring {len(records)} archives in one invocation", flush=True)
        try:
            subprocess.run([str(leantar), "-x", "-j", "-"], input=json.dumps(records),
                           text=True, check=True)
        except (OSError, subprocess.CalledProcessError) as error:
            print(f"::warning::bulk-unpack-cache: {error}; using stock Lake restoration")
            return 0
        moves = []
        modules = set()
        try:
            for record in records:
                base = staging / record["hash"]
                (ilean,) = (base / "lib").glob("*.ilean")
                info = json.loads(ilean.read_text())
                module = info.get("module")
                if (info.get("version") != 5 or not isinstance(module, str)
                        or not MODULE.fullmatch(module) or module in modules):
                    raise ValueError("unknown or overlapping module identity")
                modules.add(module)
                parts = module.split(".")
                if ilean.name != parts[-1] + ".ilean":
                    raise ValueError("archive basename disagrees with module identity")
                # A deleted module must not become importable from its old archive.
                if not (project.joinpath(*parts).with_suffix(".lean")).is_file():
                    continue
                for directory, destination, extensions in (
                        ("lib", "lib/lean", ("trace", "olean", "olean.server", "olean.private",
                                             "ilean", "ir", "ir.sig")),
                        ("ir", "ir", ("c", "bc"))):
                    for source in (base / directory).iterdir():
                        if (source.is_symlink() or not source.is_file()
                                or source.name not in {parts[-1] + "." + ext for ext in extensions}):
                            raise ValueError("unexpected archive output")
                        target = build.joinpath(destination, *parts[:-1], source.name)
                        moves.append((source, target))
        except (OSError, ValueError, TypeError, AttributeError) as error:
            print(f"::warning::bulk-unpack-cache: {error}; using stock Lake restoration")
            return 0
        for source, target in moves:
            target.parent.mkdir(parents=True, exist_ok=True)
            source.replace(target)
    # Lake prioritizes archive mappings even when matching outputs already exist.
    # Drop only these mappings so it checks the restored traces and outputs via
    # its normal local-build path, then records their individual artifact hashes.
    # Retain archive bytes for publication's existing reconnect optimization.
    for path in record_paths:
        path.unlink()
    print(f"bulk-unpack-cache: restored {len(records)} archives in {time.monotonic() - started:.1f}s", flush=True)
    return len(records)


def main(project: Path) -> None:
    # Only the job's disposable cache may lose its input-to-archive mappings.
    # Never touch a shared user cache or prepopulate a cache-disabled build.
    try:
        expected = project.resolve() / ".lake/cache"
        configured = os.environ.get("LAKE_CACHE_DIR", "")
        if (not configured or Path(configured).resolve() != expected
                or os.environ.get("LAKE_ARTIFACT_CACHE") != "true"
                or os.environ.get("LAKE_RESTORE_ARTIFACTS") != "true"):
            print("bulk-unpack-cache: private CI cache not enabled; using stock Lake restoration")
        else:
            unpack(project)
    except Exception as error:
        # All installed outputs came from the same archives stock Lake restores.
        # Records are removed only after all files are installed. A partial
        # install therefore remains recoverable by the normal hash-checked build.
        print(f"::warning::bulk-unpack-cache: {error}; using stock Lake restoration")


if __name__ == "__main__":
    main(Path(sys.argv[1]) if len(sys.argv) > 1 else Path.cwd())
