#!/usr/bin/env python3
"""Prepare a fresh private TauCeti build, then reconcile satisfied cache records.

Temporary workaround for https://github.com/leanprover/lean4/pull/15868.
Native Lake remains responsible for input/output validity. Run inside the offline
PR sandbox, or in trusted main CI, before executing library code. An optional
immutable seed is only a transport for the archives native Lake already selected.
"""

import argparse
import errno
import fcntl
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import stat
import subprocess
import tempfile
import time

HASH = re.compile(r"[0-9a-f]{16}")
ARCHIVE = re.compile(r"[0-9a-f]{16}\.ltar")
REVISION = re.compile(r"[0-9a-f]{40}")
SCHEMA = "2026-02-25"
TRACE_SCHEMA = "2025-09-10"
MODULE = re.compile(r"TauCeti(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
CONFIG = ("lean-toolchain", "lakefile.toml", "lake-manifest.json")
OUTPUTS = (("lib", "lib/lean", ("trace", "olean", "olean.server", "olean.private", "ilean", "ir", "ir.sig")),
           ("ir", "ir", ("c", "bc")))
UNSUPPORTED = {errno.EXDEV, errno.EOPNOTSUPP, errno.ENOTTY, errno.EINVAL, errno.ENOSYS}
FICLONE = 0x40049409


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


def configuration(project):
    """Describe exact platform, layout, toolchain and Lake configuration identity."""
    layout(project)
    return dict(platform=platform.system() + "-" + platform.machine(),
                layout="TauCeti-default-v1", toolchain=regular(project / "lean-toolchain").read_text().strip(),
                config_sha256={name: hashlib.sha256(regular(project / name).read_bytes()).hexdigest()
                               for name in CONFIG})


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


def seed_file(seed, relative):
    """Find an ordinary seed output through ordinary directories.

    The relative name must already be validated against module_paths. The seed
    owner must prevent concurrent mutation; these checks are not authentication.
    """
    path = seed / "build" / relative
    for parent in path.parents:
        if parent == seed:
            break
        if parent.is_symlink() or not parent.is_dir():
            raise ValueError("unexpected seed directory")
    return regular(path)


def read_seed(seed, project):
    """Validate seed identity and inventory, returning entries by native archive.

    Reject unsupported schema/configuration, unsafe paths and overlapping or
    incomplete outputs. A valid manifest does not authenticate its producer or
    file contents: the caller must supply a trusted, immutable seed and retain
    that immutability throughout installation.
    """
    if seed.is_symlink() or not seed.is_dir():
        raise ValueError("seed is not an ordinary directory")
    path = regular(seed / "manifest.json")
    if path.stat().st_size > 32 * 1024**2:
        raise ValueError("seed manifest exceeds supported size")
    value = json.loads(path.read_text())
    if (not isinstance(value, dict) or type(value.get("schema")) is not int or value.get("schema") != 1
            or value.get("kind") != "tauceti-prepared-root-v1"
            or value.get("identity") != configuration(project)
            or not isinstance(value.get("producer_revision"), str)
            or not REVISION.fullmatch(value["producer_revision"])
            or not isinstance(value.get("published_revision"), str)
            or not REVISION.fullmatch(value["published_revision"])
            or not isinstance(value.get("modules"), dict)):
        raise ValueError("absent, mismatched or unsupported prepared-root identity")
    by_archive, paths = {}, set()
    for module, entry in value["modules"].items():
        allowed = module_paths(module)
        if (not isinstance(entry, dict) or not isinstance(entry.get("archive"), str)
                or not ARCHIVE.fullmatch(entry["archive"]) or entry["archive"] in by_archive
                or not isinstance(entry.get("native_input_hash"), str)
                or not HASH.fullmatch(entry["native_input_hash"])
                or not isinstance(entry.get("archive_sha256"), str)
                or not re.fullmatch(r"[0-9a-f]{64}", entry["archive_sha256"])
                or not isinstance(entry.get("files"), list) or not entry["files"]
                or any(not isinstance(p, str) or p not in allowed for p in entry["files"])
                or len(set(entry["files"])) != len(entry["files"])):
            raise ValueError("unexpected or overlapping seed outputs")
        required = {str(Path("lib/lean", *module.split(".")[:-1], module.split(".")[-1] + "." + ext))
                    for ext in ("trace", "olean", "ilean")}
        if not required.issubset(entry["files"]) or paths.intersection(entry["files"]):
            raise ValueError("incomplete or overlapping seed module")
        paths.update(entry["files"])
        by_archive[entry["archive"]] = dict(entry, module=module)
    return by_archive


def extract_records(records, staging):
    """One native extraction for the entire miss set, never into a live build."""
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


def install_file(source, target, clone):
    """Probe the real pair as the consumer; never preserve immutable seed mode."""
    target.parent.mkdir(parents=True, exist_ok=True)
    cloned = False
    if clone:
        try:
            with source.open("rb") as src, target.open("xb") as dst:
                fcntl.ioctl(dst, FICLONE, src.fileno())
            cloned = True
        except OSError as error:
            target.unlink(missing_ok=True)
            if error.errno not in UNSUPPORTED:
                raise
    if not cloned:
        shutil.copyfile(source, target)
    info = source.stat()
    # Preserve timestamps without carrying producer xattrs or read-only mode.
    os.utime(target, ns=(info.st_atime_ns, info.st_mtime_ns))
    target.chmod(stat.S_IMODE(info.st_mode) & 0o777 | stat.S_IWUSR)
    return cloned


def rebound_trace(content, original, selected):
    """Change only stock leantar's input association; preserve all other bytes."""
    trace = json.loads(content.decode("utf-8"))
    if (not isinstance(trace, dict) or trace.get("schemaVersion") != TRACE_SCHEMA
            or trace.get("depHash") != original or not isinstance(trace.get("outputs"), dict)):
        raise ValueError("unsupported seed trace association")
    matches = list(re.finditer(rb'"depHash"\s*:\s*"([0-9a-f]{16})"', content))
    if len(matches) != 1 or matches[0].group(1).decode("ascii") != original:
        raise ValueError("unsupported seed trace encoding")
    match = matches[0]
    return content[:match.start(1)] + selected.encode("ascii") + content[match.end(1):]


def assemble(project, records, staging, seed=None):
    """Assemble matching seed modules and one bulk extraction into a private tree."""
    entries = {}
    reason = "absent"
    if seed is not None:
        try:
            entries = read_seed(seed, project)
            reason = "accepted"
        except (OSError, ValueError, TypeError, AttributeError) as error:
            reason = str(error)
    hits, misses, trace_updates = [], [], []
    for record in records:
        entry = entries.get(record["archive"])
        if entry and source_present(project, entry["module"]):
            try:
                files = [(seed_file(seed, p), p) for p in entry["files"]]
                rebound = None
                if entry["native_input_hash"] != record["hash"]:
                    relative = next(p for _, p in files if p.endswith(".trace"))
                    if file_digest(Path(record["file"])) != entry["archive_sha256"]:
                        raise ValueError("seed archive digest mismatch")
                    # Stock leantar binds these exact archive bytes to the
                    # selected native input; preserve every other trace byte.
                    rebound = (relative, rebound_trace(seed_file(seed, relative).read_bytes(),
                                                       entry["native_input_hash"], record["hash"]))
            except (OSError, ValueError) as error:
                # A damaged optional entry stays in the one native bulk miss set.
                reason = "unusable seed entry: " + str(error)
            else:
                hits.append((record, entry, files))
                if rebound is not None:
                    trace_updates.append(rebound)
                continue
        misses.append(record)
    extracted = extract_records(misses, staging / "unpacked")
    combined = staging / "build"
    combined.mkdir()
    modules, targets, satisfied = set(), set(), []
    # Validate every selected module and path before installing any outputs.
    selected = [(record, entry["module"], files, True) for record, entry, files in hits]
    selected += [(record, module, files, False) for record, module, files in extracted]
    plans = []
    for record, module, files, seeded in selected:
        if module in modules:
            raise ValueError("overlapping module identity")
        modules.add(module)
        if not source_present(project, module):
            continue
        for source, relative in files:
            if relative in targets:
                raise ValueError("overlapping module output")
            targets.add(relative)
            plans.append((source, combined / relative, seeded))
        satisfied.append(record)
    clone, methods = True, set()
    for source, target, seeded in plans:
        if seeded:
            cloned = install_file(source, target, clone)
            methods.add("reflink" if cloned else "copy")
            clone = clone and cloned
        else:
            target.parent.mkdir(parents=True, exist_ok=True)
            source.rename(target)
    rebound_count = 0
    for relative, content in trace_updates:
        if relative in targets:
            (combined / relative).write_bytes(content)
            rebound_count += 1
    return combined, satisfied, dict(seed_hit_modules=len(hits), seed_rebound_traces=rebound_count, bulk_archives=len(misses),
                                    satisfied_records=len(satisfied), seed_reason=reason,
                                    materialization=sorted(methods))


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


def unpack(project: Path, seed: Path | None = None) -> int:
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
            combined, satisfied, result = assemble(project, records, Path(temporary), seed)
            publish(project, combined, satisfied)
        result["seconds"] = time.monotonic() - started
        print("bulk-unpack-cache: " + json.dumps(result, sort_keys=True), flush=True)
        return len(satisfied)
    except (ImportError, OSError, ValueError, TypeError, AttributeError, subprocess.SubprocessError) as error:
        print(f"::warning::bulk-unpack-cache: {error}; using stock Lake restoration")
        return 0


def file_digest(path):
    """Hash an ordinary file's bytes with SHA-256; reject nonregular inputs."""
    with regular(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def export_seed(project, destination, snapshot, *, published_revision, producer_revision):
    """Producer-only: derive immutable seed files from verified published archives.

    The caller must be trusted main, run a successful native build first, and use
    the existing pre-build lake_cache_reuse snapshot. Exact output-byte equality
    with that validated build excludes anything rebuilt under different inputs.
    No candidate execution or publication is performed by this helper.
    """
    project, destination = Path(project).resolve(), Path(destination)
    identity = configuration(project)
    if (destination.exists() or destination.is_symlink()
            or not REVISION.fullmatch(published_revision) or not REVISION.fullmatch(producer_revision)
            or not isinstance(snapshot, dict) or snapshot.get("version") != 1
            or snapshot.get("toolchain") != identity["toolchain"]
            or not isinstance(snapshot.get("entries"), dict)):
        raise ValueError("invalid trusted seed export inputs")
    records = []
    archives = set()
    for input_hash, entry in sorted(snapshot["entries"].items()):
        if (not isinstance(input_hash, str) or not HASH.fullmatch(input_hash)
                or not isinstance(entry, list) or len(entry) != 2
                or not isinstance(entry[0], str) or not ARCHIVE.fullmatch(entry[0])
                or not isinstance(entry[1], str) or not re.fullmatch(r"[0-9a-f]{64}", entry[1])
                or entry[0] in archives):
            raise ValueError("invalid or overlapping archive snapshot")
        archive = project / ".lake/cache/artifacts" / entry[0]
        if file_digest(archive) != entry[1]:
            raise ValueError("published archive changed since snapshot")
        archives.add(entry[0])
        records.append(dict(file=str(archive), hash=input_hash, archive=entry[0], sha256=entry[1]))
    destination.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="prepared-root-", dir=destination.parent) as temporary:
        staging = Path(temporary)
        payload = staging / "payload"
        (payload / "build").mkdir(parents=True)
        modules, seen = {}, set()
        for record, module, files in extract_records(records, staging / "unpacked"):
            if module in seen:
                raise ValueError("overlapping module in trusted archives")
            seen.add(module)
            if not source_present(project, module):
                continue
            try:
                unchanged = all(file_digest(project / ".lake/build" / relative) == file_digest(source)
                                for source, relative in files)
            except FileNotFoundError:
                unchanged = False
            if not unchanged:
                continue  # Changed/missing native output: retain ordinary preparation.
            allowed = {relative for _, relative in files}
            required = {str(Path("lib/lean", *module.split(".")[:-1], module.split(".")[-1] + "." + ext))
                        for ext in ("trace", "olean", "ilean")}
            if not required.issubset(allowed):
                continue
            for source, relative in files:
                target = payload / "build" / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                source.rename(target)
                target.chmod(0o444)
            modules[module] = dict(archive=record["archive"], archive_sha256=record["sha256"], native_input_hash=record["hash"], files=sorted(allowed))
        value = dict(schema=1, kind="tauceti-prepared-root-v1", identity=identity,
                     published_revision=published_revision, producer_revision=producer_revision, modules=modules)
        (payload / "manifest.json").write_text(json.dumps(value, sort_keys=True) + "\n")
        (payload / "manifest.json").chmod(0o444)
        read_seed(payload, project)
        payload.rename(destination)
    return value


def main(project: Path, seed: Path | None = None) -> None:
    try:
        expected = project.resolve() / ".lake/cache"
        configured = os.environ.get("LAKE_CACHE_DIR", "")
        if (not configured or Path(configured).resolve() != expected
                or os.environ.get("LAKE_ARTIFACT_CACHE") != "true"
                or os.environ.get("LAKE_RESTORE_ARTIFACTS") != "true"):
            print("bulk-unpack-cache: private CI cache not enabled; using stock Lake restoration")
        else:
            unpack(project, seed)
    except Exception as error:
        print(f"::warning::bulk-unpack-cache: {error}; using stock Lake restoration")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path, nargs="?", default=Path.cwd())
    parser.add_argument("--seed", type=Path, help="trusted immutable seed supplied by the workflow")
    args = parser.parse_args()
    main(args.project, args.seed)
