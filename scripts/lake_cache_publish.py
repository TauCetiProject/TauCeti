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
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import threading
import time
import urllib.parse

from lake_cache_probe import exact_map_url, TOOLCHAIN
from lake_cache_reuse import ARCHIVE, HASH, SHA256, directory, regular_file

REPOSITORY = "TauCetiProject/TauCeti"
WORKERS = 16
MAX_MAP = 16 * 1024 * 1024


def endpoint(value: str) -> str:
    parsed = urllib.parse.urlsplit(value)
    if (parsed.scheme != "https" or not parsed.netloc or parsed.username is not None
            or parsed.password is not None or parsed.query or parsed.fragment
            or any(ord(c) < 33 or c in '\\"' for c in value)):
        raise ValueError("expected a plain HTTPS cache endpoint")
    return value.rstrip("/")


def artifact_url(base: str, name: str) -> str:
    if not ARCHIVE.fullmatch(name):
        raise ValueError("invalid archive name")
    return f"{endpoint(base)}/{REPOSITORY}/{name[:-5]}.art"


def mapping(raw: bytes) -> set[str]:
    if len(raw) > MAX_MAP:
        raise ValueError("oversized output map")
    lines = raw.decode().splitlines()
    if len(lines) < 2 or json.loads(lines[0]) != "2026-03-17":
        raise ValueError("unsupported or empty Lake output map")
    names, inputs = set(), set()
    for line in lines[1:]:
        entry = json.loads(line)
        if (not isinstance(entry, list) or len(entry) != 2
                or not isinstance(entry[0], str) or not HASH.fullmatch(entry[0])
                or not isinstance(entry[1], str) or not ARCHIVE.fullmatch(entry[1])
                or entry[0] in inputs):
            raise ValueError("invalid or duplicate Lake mapping")
        inputs.add(entry[0])
        names.add(entry[1])
    return names


def hashes(handle) -> dict:
    sha, md5, size = hashlib.sha256(), hashlib.md5(usedforsecurity=False), 0
    while block := handle.read(1024 * 1024):
        sha.update(block)
        md5.update(block)
        size += len(block)
    return {"sha256": sha.hexdigest(), "md5": md5.hexdigest(), "size": size}


def available(base: str, name: str, record: dict) -> bool:
    """An inconclusive HEAD is a staging miss, so its archive is transferred."""
    result = subprocess.run(
        ["curl", "--head", "--fail", "--silent", "--show-error", "--max-time", "15",
         artifact_url(base, name)], capture_output=True, text=True)
    headers = {}
    for line in result.stdout.splitlines():
        if ":" in line:
            key, value = line.split(":", 1)
            headers[key.lower()] = value.strip()
    return (result.returncode == 0
            and headers.get("etag") == f'"{record["md5"]}"'
            and headers.get("content-length") == str(record["size"]))


def stage(project: Path, index: Path, destination: Path, public: str,
          full: bool = False) -> dict:
    started = time.monotonic()
    # Caller runs this after all candidate processes have exited. All opens below
    # reject symlinked parents and files, including candidate-written hash sidecars.
    with directory(project, Path(".lake")) as parent, regular_file(parent, "outputs.jsonl") as handle:
        raw = handle.read(MAX_MAP + 1)
    names = mapping(raw)
    with directory(project, Path()) as parent, regular_file(parent, "lean-toolchain") as handle:
        toolchain = handle.read(1024).decode().strip()
    if not TOOLCHAIN.fullmatch(toolchain):
        raise ValueError("invalid toolchain")
    try:
        saved = json.loads(index.read_text())
    except (OSError, ValueError):
        saved = {}
    inherited = {}
    if (not full and public and isinstance(saved, dict) and saved.get("version") == 1
            and saved.get("toolchain") == toolchain and isinstance(saved.get("entries"), dict)):
        endpoint(public)
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
        # Stop probing after 60 seconds or 32 misses. An outage must quickly
        # degrade to full staging, not incur one timeout for every archive.
        deadline = time.monotonic() + 60
        lock, misses = threading.Lock(), 0

        def probe(name):
            nonlocal misses
            with lock:
                if misses >= 32 or time.monotonic() >= deadline:
                    return False
            found = available(public, name, records[name])
            if not found:
                with lock:
                    misses += 1
            return found

        with ThreadPoolExecutor(max_workers=WORKERS) as pool:
            present = list(pool.map(probe, candidates))
        omitted = {name for name, found in zip(candidates, present) if found}
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


def verify_remote(public: str, name: str, record: dict) -> int:
    # Three bounded GETs. Do not trust ETags, hash sidecars, or producer assertions
    # as the final integrity test. No candidate code runs on this publisher runner.
    with tempfile.TemporaryDirectory(prefix="lake-object-check-") as temporary:
        target = Path(temporary) / "object"
        for _ in range(3):
            result = subprocess.run(
                ["curl", "--fail", "--silent", "--show-error", "--max-time", "30",
                 "--max-filesize", str(record["size"] + 1), "--output", str(target),
                 artifact_url(public, name)], capture_output=True)
            if result.returncode == 0:
                with target.open("rb") as handle:
                    actual = hashes(handle)
                if actual == record:
                    return record["size"]
        raise ValueError(f"inherited object {name} unavailable or corrupt; "
                         "rerun producer with LAKE_CACHE_FULL_PUBLICATION=1")


def prepare(staging: Path, plan: Path, toolchain: str, revision: str,
            public: str, upload_artifacts: str, upload_revisions: str) -> dict:
    """Validate hostile data and write curl configuration outside the staged tree."""
    started = time.monotonic()
    endpoint(public)
    endpoint(upload_artifacts)
    endpoint(upload_revisions)
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
            # Old in-flight producers remain publishable during independent rollout.
            records, inherited = {}, set()
        if entries - {"outputs.jsonl", "publication.json"} != names - inherited:
            raise ValueError("staged objects do not match the complete map/manifest")
        for name in sorted(names - inherited):
            with regular_file(parent, name) as handle:
                actual = hashes(handle)
            if name in records and actual != records[name]:
                raise ValueError("staged object digest mismatch")
            records[name] = actual
    failed = threading.Event()

    def verify(name):
        if failed.is_set():
            return 0
        try:
            return verify_remote(public, name, records[name])
        except Exception:
            failed.set()
            raise

    with ThreadPoolExecutor(max_workers=WORKERS) as pool:
        verified_bytes = sum(pool.map(verify, sorted(inherited)))
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
