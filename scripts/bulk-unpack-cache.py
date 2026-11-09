#!/usr/bin/env python3
"""Prepare a fresh private TauCeti build, then reconcile satisfied cache records.

Temporary workaround for https://github.com/leanprover/lean4/pull/15868.
Native Lake remains responsible for input/output validity. Run inside the offline
PR sandbox, or in trusted main CI, before executing library code.
"""

import argparse
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import tempfile
import time

HASH = re.compile(r"[0-9a-f]{16}")
ARCHIVE = re.compile(r"[0-9a-f]{16}\.ltar")
SCHEMA = "2026-02-25"
MODULE = re.compile(r"TauCeti(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
OUTPUTS = (("lib", "lib/lean", ("trace", "olean", "olean.server", "olean.private", "ilean", "ir", "ir.sig")),
           ("ir", "ir", ("c", "bc")))


def regular(path):
    """Return a regular file path; reject symlinks and special files via lstat."""
    if not stat.S_ISREG(path.lstat().st_mode):
        raise ValueError("expected an ordinary file: " + str(path))
    return path


def layout(project):
    """Reject project/library paths outside the supported TauCeti default layout."""
    import tomllib
    config = tomllib.loads(regular(project / "lakefile.toml").read_text())
    libs = config.get("lean_lib", [])
    if ((project / "lakefile.lean").exists() or config.get("name") != "TauCeti"
            or any(config.get(key, default) != default for key, default in (
                ("buildDir", ".lake/build"), ("leanLibDir", "lib/lean"),
                ("irDir", "ir"), ("srcDir", ".")))
            or not isinstance(libs, list) or len(libs) != 1
            or not isinstance(libs[0], dict) or libs[0].get("name") != "TauCeti"
            or libs[0].get("srcDir", ".") != "."):
        raise ValueError("unsupported Lake layout")


def selected_records(project):
    """Read native archive-only selections and retain original mapping bytes.

    Reject unsupported schemas, unsafe archive names and duplicate archives.
    This reads existing native selections; it does not select another ancestor.
    """
    outputs = project / ".lake/cache/outputs/TauCeti"
    artifacts = project / ".lake/cache/artifacts"
    records, archives = [], set()
    for path in sorted(outputs.glob("*.json")):
        if not HASH.fullmatch(path.stem):
            raise ValueError("unexpected cache record")
        original = regular(path).read_bytes()
        value = json.loads(original)
        if not isinstance(value, dict) or value.get("schemaVersion") != SCHEMA:
            raise ValueError("unknown cache schema")
        archive = value.get("data")
        if not isinstance(archive, str) or not ARCHIVE.fullmatch(archive):
            raise ValueError("cache is not an archive-only revision")
        if archive in archives:
            raise ValueError("overlapping historical cache entries")
        archives.add(archive)
        records.append(dict(file=str(regular(artifacts / archive)), hash=path.stem,
                            archive=archive, path=path, original=original))
    return records


def module_paths(module):
    """Return permitted build-relative outputs for a supported TauCeti module."""
    if not isinstance(module, str) or not MODULE.fullmatch(module):
        raise ValueError("unknown module identity")
    parts = module.split(".")
    return {str(Path(destination, *parts[:-1], parts[-1] + "." + ext))
            for _, destination, extensions in OUTPUTS for ext in extensions}


def source_present(project, module):
    """Check that the candidate has a regular module source without symlink parents."""
    source = project.joinpath(*module.split(".")).with_suffix(".lean")
    # Source symlinks are never evidence that this module belongs to the candidate.
    for parent in source.parents:
        if parent == project:
            break
        if parent.is_symlink():
            return False
    return source.is_file() and not source.is_symlink()


def extract_records(records, staging):
    """One native extraction for all selected archives, never into a live build."""
    if not records:
        return []
    requests = []
    for record in records:
        base = staging / record["hash"]
        requests.append(dict(file=record["file"], hash=record["hash"],
                             base=[str(base / "lib"), str(base / "ir")]))
    sysroot = subprocess.check_output(["lean", "--print-prefix"], text=True).strip()
    leantar = Path(sysroot) / "bin/leantar"
    print(f"bulk-unpack-cache: restoring {len(records)} archives in one invocation", flush=True)
    subprocess.run([str(leantar), "-x", "-j", "-"], input=json.dumps(requests), text=True, check=True)
    extracted = []
    for record in records:
        base = staging / record["hash"]
        for directory in ("lib", "ir"):
            if (base / directory).is_symlink() or not (base / directory).is_dir():
                raise ValueError("unexpected archive directory")
        (ilean,) = (base / "lib").glob("*.ilean")
        info = json.loads(regular(ilean).read_text())
        module = info.get("module")
        allowed = module_paths(module)
        if info.get("version") != 5 or ilean.name != module.split(".")[-1] + ".ilean":
            raise ValueError("unknown archive module layout")
        files = []
        for directory, destination, _ in OUTPUTS:
            for source in (base / directory).iterdir():
                relative = str(Path(destination, *module.split(".")[:-1], source.name))
                if relative not in allowed:
                    raise ValueError("unexpected archive output")
                files.append((regular(source), relative))
        extracted.append((record, module, files))
    return extracted


def assemble(project, records, staging):
    """Validate one native bulk extraction and assemble a private build tree."""
    extracted = extract_records(records, staging / "unpacked")
    combined = staging / "build"
    combined.mkdir()
    modules, targets, satisfied = set(), set(), []
    plans = []
    for record, module, files in extracted:
        if module in modules:
            raise ValueError("overlapping module identity")
        modules.add(module)
        if not source_present(project, module):
            continue
        for source, relative in files:
            if relative in targets:
                raise ValueError("overlapping module output")
            targets.add(relative)
            plans.append((source, combined / relative))
        satisfied.append(record)
    # Validate all modules before publishing or changing any selected mappings.
    for source, target in plans:
        target.parent.mkdir(parents=True, exist_ok=True)
        source.rename(target)
    return combined, satisfied, dict(bulk_archives=len(records), satisfied_records=len(satisfied))


def publish(project, combined, satisfied):
    """Publish a complete private tree, then remove only satisfied mappings.

    Recheck captured mapping bytes before the atomic rename. Archive bytes and
    publication snapshots remain untouched. If a later unlink fails, the complete
    tree stays published and remaining mappings permit native Lake restoration;
    mapping cleanup is not a single atomic transaction with tree publication.
    """
    # Recheck originals before making any live change. Snapshot/reconnect data
    # and every archive remain intact; only proven satisfied mappings may leave.
    for record in satisfied:
        if regular(record["path"]).read_bytes() != record["original"]:
            raise ValueError("selected cache record changed during preparation")
    combined.rename(project / ".lake/build")
    for record in satisfied:
        record["path"].unlink()


def unpack(project: Path) -> int:
    started = time.monotonic()
    project = project.resolve()
    build = project / ".lake/build"
    outputs = project / ".lake/cache/outputs/TauCeti"
    if build.exists() or build.is_symlink() or not outputs.is_dir():
        print("bulk-unpack-cache: no fresh cache; using stock Lake restoration")
        return 0
    try:
        layout(project)
        records = selected_records(project)
        if not records:
            return 0
        with tempfile.TemporaryDirectory(prefix="bulk-unpack-", dir=project / ".lake") as temporary:
            combined, satisfied, result = assemble(project, records, Path(temporary))
            publish(project, combined, satisfied)
        result["seconds"] = time.monotonic() - started
        print("bulk-unpack-cache: " + json.dumps(result, sort_keys=True), flush=True)
        return len(satisfied)
    except (ImportError, OSError, ValueError, TypeError, AttributeError, subprocess.SubprocessError) as error:
        print(f"::warning::bulk-unpack-cache: {error}; using stock Lake restoration")
        return 0


def main(project: Path) -> None:
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
        print(f"::warning::bulk-unpack-cache: {error}; using stock Lake restoration")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path, nargs="?", default=Path.cwd())
    args = parser.parse_args()
    main(args.project)
