#!/usr/bin/env python3
"""Key-free incremental Lake publication planning; never execute with upload credentials.

The complete Lake map remains canonical. Only archives matching the pre-build,
read-only download snapshot are eligible for omission. HEAD/MD5 is an inexpensive
staging filter, not the publisher's integrity check: the isolated publisher GETs
and SHA-256 verifies every omitted object before preparing an upload plan.
A deletion between staging and publication fails closed after bounded retries;
rerun the producer with LAKE_CACHE_FULL_PUBLICATION=1 to repair from built bytes.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time

from lake_cache_probe import (
    DEFAULT_REPOSITORY as REPOSITORY, exact_map_url, parse_map, plain_https_endpoint, TOOLCHAIN,
)
from lake_cache_reuse import ARCHIVE, SHA256, directory, hashes, read_toolchain, regular_file

WORKERS = 64
BATCH_SIZE = 128
MAX_MAP = 16 * 1024 * 1024


def artifact_url(base: str, name: str) -> str:
    if not ARCHIVE.fullmatch(name):
        raise ValueError("invalid archive name")
    return f"{plain_https_endpoint(base)}/{REPOSITORY}/{name[:-5]}.art"


def mapping(raw: bytes) -> set[str]:
    if len(raw) > MAX_MAP:
        raise ValueError("oversized output map")
    version, entries = parse_map(raw)
    if version != "2026-03-17":
        raise ValueError("unsupported Lake output map schema")
    if len({input_hash for input_hash, _ in entries}) != len(entries):
        raise ValueError("duplicate Lake mapping input")
    return {archive for _, archive in entries}


def transfer(public: str, records: dict, target: Path, head: bool = False) -> None:
    """Use one bounded curl batch, sharing connections without credentials."""
    config = target / "requests.curl"
    config.write_text("".join(
        f"url = {json.dumps(artifact_url(public, name))}\n"
        f"output = {json.dumps(str(target / name))}\n" for name in records))
    args = ["curl", "--parallel", "--parallel-max", str(WORKERS), "--fail", "--silent",
            "--show-error", "--max-time", "15" if head else "30",
            "--config", str(config)]
    if head:
        args.append("--head")
    else:
        args += ["--max-filesize", str(max(r["size"] for r in records.values()) + 1)]
    # A batch can partly succeed. Inspect each response/file; a failed transfer
    # never establishes availability and is retried or staged from built bytes.
    subprocess.run(args, capture_output=True)


def available(public: str, records: dict) -> set[str]:
    """An inconclusive HEAD is a staging miss, so its archive is transferred."""
    found = set()
    with tempfile.TemporaryDirectory(prefix="lake-object-head-") as temporary:
        target = Path(temporary)
        transfer(public, records, target, head=True)
        for name, record in records.items():
            try:
                raw = (target / name).read_text()
            except (OSError, UnicodeError):
                continue
            headers = {}
            for line in raw.splitlines():
                if ":" in line:
                    key, value = line.split(":", 1)
                    headers[key.lower()] = value.strip()
            if (headers.get("etag") == f'"{record["md5"]}"'
                    and headers.get("content-length") == str(record["size"])):
                found.add(name)
    return found


def stage(project: Path, index: Path, destination: Path, public: str,
          full: bool = False) -> dict:
    started = time.monotonic()
    # Caller runs this after all candidate processes have exited. All opens below
    # reject symlinked parents and files, including candidate-written hash sidecars.
    with directory(project, Path(".lake")) as parent, regular_file(parent, "outputs.jsonl") as handle:
        raw = handle.read(MAX_MAP + 1)
    names = mapping(raw)
    toolchain = read_toolchain(project)
    if not TOOLCHAIN.fullmatch(toolchain):
        raise ValueError("invalid toolchain")
    try:
        saved = json.loads(index.read_text())
    except (OSError, ValueError):
        saved = {}
    inherited = {}
    if (not full and public and isinstance(saved, dict) and saved.get("version") == 1
            and saved.get("toolchain") == toolchain and isinstance(saved.get("entries"), dict)):
        plain_https_endpoint(public)
        for entry in saved["entries"].values():
            if (isinstance(entry, list) and len(entry) == 2 and isinstance(entry[0], str)
                    and ARCHIVE.fullmatch(entry[0]) and isinstance(entry[1], str)
                    and SHA256.fullmatch(entry[1])):
                inherited[entry[0]] = entry[1]
    records = {}
    with directory(project, Path(".lake/cache/artifacts")) as artifacts:
        for name in sorted(names):
            with regular_file(artifacts, name) as handle:
                records[name] = hashes(handle)
        candidates = [name for name in sorted(names)
                      if inherited.get(name) == records[name]["sha256"]]
        # Start no further batches after 60 seconds or 32 observed misses.
        # One batch has at most 128 requests and 64 active transfers. Connection
        # reuse avoids one TLS session and curl process per archive.
        deadline, misses, omitted = time.monotonic() + 60, 0, set()
        for offset in range(0, len(candidates), BATCH_SIZE):
            if misses >= 32 or time.monotonic() >= deadline:
                break
            batch = candidates[offset:offset + BATCH_SIZE]
            found = available(public, {name: records[name] for name in batch})
            omitted.update(found)
            misses += len(batch) - len(found)
        # Fresh destination owned by the host, never a candidate directory.
        destination.mkdir(parents=True, exist_ok=False)
        (destination / "outputs.jsonl").write_bytes(raw)
        for name in sorted(names - omitted):
            with regular_file(artifacts, name) as handle, (destination / name).open("xb") as output:
                shutil.copyfileobj(handle, output)
        manifest = {"version": 1, "toolchain": toolchain, "objects": records,
                    "inherited": sorted(omitted)}
        (destination / "publication.json").write_text(json.dumps(manifest) + "\n")
    stats = {"objects": len(names), "inherited": len(omitted),
             "full_bytes": sum(r["size"] for r in records.values()),
             "staged_bytes": sum(records[n]["size"] for n in names - omitted),
             "fallback_objects": len(candidates) - len(omitted),
             "seconds": round(time.monotonic() - started, 3)}
    print("Lake publication staging: " + json.dumps(stats), flush=True)
    return stats


def verify_remote(public: str, records: dict) -> int:
    """GET and SHA-256 verify all inherited bytes in bounded, retryable batches."""
    names = sorted(records)
    for offset in range(0, len(names), BATCH_SIZE):
        remaining = {name: records[name] for name in names[offset:offset + BATCH_SIZE]}
        with tempfile.TemporaryDirectory(prefix="lake-object-check-") as temporary:
            target = Path(temporary)
            for _ in range(3):
                transfer(public, remaining, target)
                for name, record in list(remaining.items()):
                    try:
                        with (target / name).open("rb") as handle:
                            actual = hashes(handle)
                    except OSError:
                        continue
                    if actual == record:
                        del remaining[name]
                if not remaining:
                    break
            if remaining:
                name = next(iter(remaining))
                raise ValueError(f"inherited object {name} unavailable or corrupt; "
                                 "rerun producer with LAKE_CACHE_FULL_PUBLICATION=1")
    return sum(record["size"] for record in records.values())


def prepare(staging: Path, plan: Path, toolchain: str, revision: str,
            public: str, upload_artifacts: str, upload_revisions: str) -> dict:
    """Validate hostile data and write curl configuration outside the staged tree."""
    started = time.monotonic()
    plain_https_endpoint(public)
    plain_https_endpoint(upload_artifacts)
    plain_https_endpoint(upload_revisions)
    map_url = exact_map_url(upload_revisions, toolchain, revision)
    with directory(staging, Path()) as parent:
        entries = set(os.listdir(parent))
        # Reject all extra files, directories, symlinks and sockets (even unused ones).
        for name in entries:
            if name not in {"outputs.jsonl", "publication.json"} and not ARCHIVE.fullmatch(name):
                raise ValueError("unexpected staging entry")
            with regular_file(parent, name):
                pass
        with regular_file(parent, "outputs.jsonl") as handle:
            raw = handle.read(MAX_MAP + 1)
        names = mapping(raw)
        if "publication.json" in entries:
            with regular_file(parent, "publication.json") as handle:
                manifest = json.loads(handle.read(MAX_MAP + 1))
            if (not isinstance(manifest, dict) or manifest.get("version") != 1
                    or manifest.get("toolchain") != toolchain
                    or not isinstance(manifest.get("objects"), dict)
                    or set(manifest["objects"]) != names
                    or not isinstance(manifest.get("inherited"), list)):
                raise ValueError("invalid publication manifest or toolchain scope")
            records = manifest["objects"]
            inherited = manifest["inherited"]
            if (any(not isinstance(n, str) or n not in names for n in inherited)
                    or len(set(inherited)) != len(inherited)):
                raise ValueError("invalid inherited object list")
            inherited = set(inherited)
            for record in records.values():
                if (not isinstance(record, dict) or set(record) != {"sha256", "md5", "size"}
                        or not isinstance(record["sha256"], str) or not SHA256.fullmatch(record["sha256"])
                        or not isinstance(record["md5"], str) or len(record["md5"]) != 32
                        or any(c not in "0123456789abcdef" for c in record["md5"])
                        or type(record["size"]) is not int or not 0 < record["size"] <= 1024**3):
                    raise ValueError("invalid object digest/size")
        else:
            # A tree without a manifest is full staging: hash and upload every mapped object.
            records, inherited = {}, set()
        if entries - {"outputs.jsonl", "publication.json"} != names - inherited:
            raise ValueError("staged objects do not match the complete map/manifest")
        for name in sorted(names - inherited):
            with regular_file(parent, name) as handle:
                actual = hashes(handle)
            if name in records and actual != records[name]:
                raise ValueError("staged object digest mismatch")
            records[name] = actual
    verified_bytes = verify_remote(public, {name: records[name] for name in sorted(inherited)})
    plan.mkdir(parents=True, exist_ok=False)
    # Freeze host-validated files in a private directory before the key-bearing step.
    shutil.copyfile(staging / "outputs.jsonl", plan / "outputs.jsonl")
    for name in sorted(names - inherited):
        shutil.copyfile(staging / name, plan / name)
    with (plan / "artifacts.curl").open("w") as config:
        for name in sorted(names - inherited):
            config.write(f'upload-file = {json.dumps(str(plan / name))}\n')
            config.write(f'url = {json.dumps(artifact_url(upload_artifacts, name))}\n')
    (plan / "map-url").write_text(map_url + "\n")
    stats = {"objects": len(names), "inherited": len(inherited),
             "uploaded_objects": len(names - inherited), "verified_download_bytes": verified_bytes,
             "upload_bytes": sum(records[n]["size"] for n in names - inherited),
             "full_bytes": sum(r["size"] for r in records.values()),
             "verification_seconds": round(time.monotonic() - started, 3)}
    print("Lake publication plan: " + json.dumps(stats), flush=True)
    (plan / "metrics.json").write_text(json.dumps(stats) + "\n")
    return stats


def main():
    if any(os.environ.get(key) for key in ("LAKE_CACHE_KEY", "LAKE_CACHE_KEY_RAW")):
        raise ValueError("publication planner must never receive upload credentials")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("stage", "prepare"))
    parser.add_argument("project", type=Path)
    parser.add_argument("destination", type=Path)
    parser.add_argument("--index", type=Path)
    parser.add_argument("--toolchain")
    parser.add_argument("--revision")
    args = parser.parse_args()
    if args.action == "stage":
        if args.index is None:
            parser.error("stage requires --index")
        stage(args.project, args.index, args.destination,
              os.environ.get("PUBLIC_ARTIFACT_ENDPOINT", ""),
              os.environ.get("LAKE_CACHE_FULL_PUBLICATION") == "1")
    else:
        prepare(args.project, args.destination, args.toolchain, args.revision,
                os.environ["PUBLIC_ARTIFACT_ENDPOINT"], os.environ["S3_ARTIFACT_ENDPOINT"],
                os.environ["S3_REVISION_ENDPOINT"])


if __name__ == "__main__":
    main()
