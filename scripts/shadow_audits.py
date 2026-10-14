#!/usr/bin/env python3
"""Shadow-only axiom reuse. Every observation runs full authoritative checks.

The session seals its own full results in host memory. There is deliberately no record
import/export or persistent cache interface. Reports are untrusted research telemetry.

Only per-module axiom results are reused. Inventory, global ownership and module-system
checks run afresh. Production audits, lints, approval gates and publishers never consume
these reports. This harness does not kernel-check arbitrary supplied compiled proofs:
run it on outputs of a successful normal build. Byte hashes bind identity, not correctness.

For built snapshots with a common pinned dependency tree, build the trusted driver with
build-audit-driver.sh, then run through lake env:
  python3 scripts/shadow_audits.py SNAPSHOT_A SNAPSHOT_B --driver TRUSTED_DRIVER \
    --sysroot PINNED_SYSROOT --output /tmp/shadow-report.json
Repeating one snapshot exercises warm reuse. A session requires an immutable trusted
sysroot and driver; a new toolchain starts a new session and cannot inherit its records.
All non-sysroot imported artifacts are privately copied before either comparison pass.
"""

import argparse
from dataclasses import dataclass
import hashlib
import hmac
import json
import os
from pathlib import Path
import secrets
import shutil
import subprocess
import tempfile
import time


SCRIPTS = Path(__file__).resolve().parent
PARTS = (".olean", ".olean.server", ".olean.private", ".ir", ".ir.sig")
PREFIX = "shadow-audit-snapshot: "
POLICY_FILES = ("Axioms.lean", "ModuleSystem.lean", "build-audit-driver.sh", "shadow_audits.py")


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":"),
                                    ensure_ascii=True).encode()).hexdigest()


def file_digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def tree_digest(root):
    """Complete toolchain contents, relative paths, symlink targets and permission modes."""
    rows = []

    def entries(directory, parents=frozenset()):
        real = directory.resolve()
        if real in parents:
            raise ValueError(f"cyclic toolchain directory symlink: {directory}")
        for path in sorted(directory.iterdir()):
            yield path
            if path.is_dir():
                yield from entries(path, parents | {real})

    for path in entries(root):
        if path.is_symlink():
            # Include bytes of file targets too, including targets outside the sysroot.
            rows.append((str(path.relative_to(root)), "symlink", os.readlink(path),
                         path.stat().st_mode, file_digest(path) if path.is_file() else None))
        elif path.is_file():
            rows.append((str(path.relative_to(root)), path.stat().st_mode, file_digest(path)))
        elif path.is_dir():
            rows.append((str(path.relative_to(root)), "directory", path.stat().st_mode))
        else:
            raise ValueError(f"unsupported toolchain entry: {path}")
    return digest(rows)


def sandbox_command(command, project, paths, sysroot, driver, scope=None):
    """No credentials, network, writable artifact roots, host /proc, or session records."""
    bwrap = shutil.which("bwrap")
    if not bwrap:
        raise RuntimeError("bubblewrap is required; shadow research has no unsandboxed fallback")
    argv = [bwrap, "--tmpfs", "/", "--proc", "/proc", "--dev", "/dev", "--tmpfs", "/tmp"]
    # /nix and /run/current-system/sw support the local Nix host; Ubuntu uses /usr.
    for path in ("/usr", "/etc", "/bin", "/sbin", "/lib", "/lib64", "/nix",
                 "/run/current-system/sw"):
        if Path(path).exists():
            argv += ["--ro-bind", path, path]
    for path in sorted({project.resolve(), sysroot.resolve(), driver.resolve(),
                        SCRIPTS, *[p.resolve() for p in paths]}):
        argv += ["--ro-bind", str(path), str(path)]
    if scope is not None:
        argv += ["--setenv", "AXIOMS_ONLY_MODULES", str(scope)]
    argv += ["--remount-ro", "/",
             "--setenv", "PATH", "/usr/bin:/bin:/run/current-system/sw/bin",
             "--setenv", "LEAN_SYSROOT", str(sysroot),
             "--setenv", "LEAN_PATH", os.pathsep.join(map(str, paths)),
             "--chdir", str(project), "--unshare-user", "--unshare-ipc", "--unshare-pid",
             "--unshare-net", "--unshare-uts", "--unshare-cgroup", "--disable-userns",
             "--die-with-parent", "--new-session", "--", *map(str, command)]
    return argv


def run(command, project, paths, sysroot, driver, scope=None):
    return subprocess.run(sandbox_command(command, project, paths, sysroot, driver, scope),
                          env={}, text=True, capture_output=True, timeout=3000)


def read_snapshot(result):
    rows = [line[len(PREFIX):] for line in result.stdout.splitlines() if line.startswith(PREFIX)]
    if len(rows) != 1:
        raise RuntimeError(f"full audit did not produce one snapshot (exit {result.returncode}):\n"
                           f"{result.stdout}\n{result.stderr}")
    return json.loads(rows[0])


def canonical_result(result):
    return {"count": result["count"], "messages": sorted(result["messages"])}


def closure_keys(inventory, artifacts, identity):
    """Merkle keys include ALL transitive imports, including external elaborators/macros."""
    modules = {row["module"]: row for row in inventory}
    if len(modules) != len(inventory):
        raise ValueError("duplicate inventory module")
    keys, visiting = {}, set()

    def visit(module):
        if module in visiting:
            raise ValueError(f"cyclic artifact import graph: {module}")
        if module not in modules:
            raise ValueError(f"missing dependency in inventory: {module}")
        if module not in keys:
            visiting.add(module)
            deps = [(name, visit(name)) for name in sorted(modules[module]["imports"])]
            keys[module] = digest((identity, module, artifacts[module], deps))
            visiting.remove(module)
        return keys[module]

    return {name: visit(name) for name in modules}


@dataclass(frozen=True)
class Record:
    key: str
    payload: str
    seal: str


class ShadowSession:
    """Only results computed by this process may enter its private, ephemeral baseline."""

    def __init__(self):
        self._secret = secrets.token_bytes(32)
        self._records = {}

    def _seal(self, module, key, payload):
        return hmac.new(self._secret, json.dumps((module, key, payload)).encode(),
                        hashlib.sha256).hexdigest()

    def plan(self, inventory, artifacts, identity):
        keys = closure_keys(inventory, artifacts, identity)
        reusable = {}
        for row in inventory:
            module = row["module"]
            if not row["local"]:
                continue
            record = self._records.get(module)
            if record and record.key == keys[module] and hmac.compare_digest(
                    record.seal, self._seal(module, record.key, record.payload)):
                reusable[module] = json.loads(record.payload)
        return keys, reusable

    def compare(self, snapshot, artifacts, identity, module_system, incremental=None):
        keys = closure_keys(snapshot["inventory"], artifacts, identity)
        locals_ = {row["module"] for row in snapshot["inventory"] if row["local"]}
        full = {row["module"]: canonical_result(row) for row in snapshot["results"]}
        if set(full) != locals_ or len(full) != len(snapshot["results"]):
            raise ValueError("full result/source inventory mismatch")
        _, reusable = self.plan(snapshot["inventory"], artifacts, identity)
        changed = set(full) - set(reusable)
        # Unit-level callers can supply a synthetic oracle; observe always runs the
        # separate incremental subprocess before providing its results here.
        incremental = ({name: full[name] for name in changed} if incremental is None
                       else {row["module"]: canonical_result(row) for row in incremental})
        if set(incremental) != changed:
            raise ValueError("incremental result/scope inventory mismatch")
        shadow, reused, invalid, mismatches, next_records = {}, [], [], [], {}
        for module in sorted(full):
            key, result = keys[module], full[module]
            record = self._records.get(module)
            if module in reusable:
                shadow[module] = reusable[module]
                reused.append(module)
            else:
                shadow[module] = incremental[module]
                if record:
                    invalid.append(module)
            if shadow[module] != result:
                mismatches.append({"module": module, "shadow": shadow[module], "full": result})
            # Always replace with the fresh full oracle, including after a mismatch.
            payload = json.dumps(result, sort_keys=True)
            next_records[module] = Record(key, payload, self._seal(module, key, payload))
        removed = sorted(set(self._records) - locals_)
        self._records = next_records
        full_status = max(snapshot["ownership_status"], snapshot["axioms_status"],
                          module_system.returncode)
        axiom_status = int(sum(r["count"] for r in shadow.values()) == 0 or
                           any(r["messages"] for r in shadow.values()))
        shadow_status = max(snapshot["ownership_status"], axiom_status, module_system.returncode)
        if shadow_status != full_status:
            mismatches.append({"full_status": full_status, "shadow_status": shadow_status})
        return {"shadow_only": True, "equivalent": not mismatches,
                "full_status": full_status, "shadow_status": shadow_status,
                "modules": len(full), "reused": reused,
                "recomputed": sorted(set(full) - set(reused)), "invalidated": invalid,
                "removed": removed, "mismatches": mismatches,
                "global_checks": {"inventory": sorted(locals_),
                                  "ownership_status": snapshot["ownership_status"],
                                  "module_system_status": module_system.returncode,
                                  "module_system_stdout": module_system.stdout,
                                  "module_system_stderr": module_system.stderr}}


def observe(session, project, paths, sysroot, driver, toolchain_identity):
    """Discover, freeze private artifact copies, run every full check, then compare reuse.

    The sysroot and driver are trusted immutable inputs for the session. The CLI hashes
    the entire sysroot once; changing it starts a new session. Every other imported artifact
    is copied into a fresh private tree and only those immutable copies are audited.
    """
    start = time.monotonic()
    project, sysroot, driver = project.resolve(), sysroot.resolve(), driver.resolve()
    paths = [p.resolve() for p in paths]
    with tempfile.TemporaryDirectory(prefix="shadow-audits-") as tmp:
        frozen = Path(tmp)
        sources, artifacts_root = frozen / "sources", frozen / "artifacts"
        sources.mkdir()
        artifacts_root.mkdir()
        # Snapshot every source independently of root imports, preserving root and orphans.
        source_paths = [project / "TauCeti.lean", *sorted((project / "TauCeti").rglob("*.lean"))]
        for path in source_paths:
            dest = sources / path.relative_to(project)
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, dest)
        discovery_start = time.monotonic()
        discovery = read_snapshot(run([driver, "--shadow-inventory"], sources, paths,
                                      sysroot, driver))["inventory"]
        discovery_seconds = time.monotonic() - discovery_start
        freeze_start = time.monotonic()
        artifact_ids = {}
        for row in discovery:
            origin = Path(row["path"])
            if not origin.is_absolute():
                raise ValueError("artifact search paths must be absolute")
            relative = Path(row["relative"])
            if relative.is_absolute() or ".." in relative.parts:
                raise ValueError("unsafe artifact module path")
            if not row["local"] and (relative == Path("TauCeti.olean") or
                                     relative.parts[0] == "TauCeti"):
                raise ValueError(f"audited artifact has no source: {row['module']}")
            if origin.is_relative_to(sysroot):
                artifact_ids[row["module"]] = ("trusted-sysroot", toolchain_identity)
                continue
            dest = artifacts_root / relative
            dest.parent.mkdir(parents=True, exist_ok=True)
            parts = []
            for ext in PARTS:
                source_part, dest_part = origin.with_suffix(ext), dest.with_suffix(ext)
                if source_part.exists():
                    shutil.copyfile(source_part, dest_part)
                    parts.append((ext, file_digest(dest_part)))
                else:
                    parts.append((ext, None))
            artifact_ids[row["module"]] = parts
        # Source changes also invalidate local results, even if someone supplied stale oleans.
        # Full production builds remain responsible for source/artifact correspondence.
        source_id = [(str(p.relative_to(sources)), file_digest(p))
                     for p in sources.rglob("*.lean")]
        pins = [(name, file_digest(project / name) if (project / name).is_file() else None)
                for name in ("lean-toolchain", "lake-manifest.json", "lakefile.toml", "lakefile.lean")]
        identity = digest((toolchain_identity, file_digest(driver), pins,
                           [(name, file_digest(SCRIPTS / name)) for name in POLICY_FILES],
                           file_digest(SCRIPTS.parent / ".github/workflows/shadow-audits.yml")))
        freeze_seconds = time.monotonic() - freeze_start
        frozen_paths = [artifacts_root]
        full_start = time.monotonic()
        full_run = run([driver, "--shadow-snapshot"], sources, frozen_paths, sysroot, driver)
        full = read_snapshot(full_run)
        full_seconds = time.monotonic() - full_start
        def graph(rows):
            return sorted((r["module"], r["local"], sorted(r["imports"])) for r in rows)
        if graph(discovery) != graph(full["inventory"]):
            raise ValueError("artifact inventory changed during freeze")
        if full_run.returncode != max(full["ownership_status"], full["axioms_status"]):
            raise ValueError("full audit process status disagrees with its snapshot")
        for row in discovery:
            if row["local"]:
                relative = str(Path(row["relative"]).with_suffix(".lean"))
                artifact_ids[row["module"]] = (artifact_ids[row["module"]], dict(source_id)[relative])
        _, reusable = session.plan(discovery, artifact_ids, identity)
        changed = sorted(row["module"] for row in discovery
                         if row["local"] and row["module"] not in reusable)
        scope = sources / ".shadow-scope"
        scope.write_text("".join(name + "\n" for name in changed))
        incremental_start = time.monotonic()
        incremental_run = run([driver, "--shadow-incremental"], sources, frozen_paths,
                              sysroot, driver, scope)
        incremental = read_snapshot(incremental_run)
        incremental_seconds = time.monotonic() - incremental_start
        if incremental_run.returncode != max(incremental["ownership_status"],
                                              incremental["axioms_status"]):
            raise ValueError("incremental audit process status disagrees with its snapshot")
        if incremental["ownership_status"] != full["ownership_status"]:
            raise ValueError("fresh global ownership checks disagree")
        flags_start = time.monotonic()
        flags = run([sysroot / "bin/lean", "--run", SCRIPTS / "ModuleSystem.lean"],
                    sources, frozen_paths, sysroot, driver)
        if flags.returncode not in (0, 1):
            raise RuntimeError(f"module-system process failure: {flags.stderr}")
        report = session.compare(full, artifact_ids, identity, flags, incremental["results"])
        report.update(identity=identity, elapsed_seconds=time.monotonic() - start,
                      full_declarations=sum(r["count"] for r in full["results"]),
                      incremental_declarations=sum(r["count"] for r in incremental["results"]),
                      phase_seconds={"discovery": discovery_seconds, "freeze": freeze_seconds,
                                     "full": full_seconds, "incremental": incremental_seconds,
                                     "module_system": time.monotonic() - flags_start})
        return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("projects", type=Path, nargs="+", help="ordered built source snapshots")
    parser.add_argument("--driver", type=Path, required=True, help="trusted prebuilt audit driver")
    parser.add_argument("--sysroot", type=Path, required=True, help="immutable pinned Lean sysroot")
    parser.add_argument("--output", type=Path, required=True, help="untrusted JSON research report")
    args = parser.parse_args()
    toolchain = tree_digest(args.sysroot.resolve())
    session, reports = ShadowSession(), []
    for project in args.projects:
        paths = [project / ".lake/build/lib/lean", project]
        paths += sorted((project / ".lake/packages").glob("*/.lake/build/lib/lean"))
        paths += [Path(p) for p in os.environ.get("LEAN_PATH", "").split(os.pathsep) if p]
        try:
            report = observe(session, project, [p for p in paths if p.exists()], args.sysroot,
                             args.driver, toolchain)
        except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
            report = {"shadow_only": True, "equivalent": False, "error": str(error)}
        reports.append(report)
        print(json.dumps(report, sort_keys=True), flush=True)
    args.output.write_text(json.dumps(reports, indent=2, sort_keys=True) + "\n")
    return int(any(not r["equivalent"] or r.get("full_status", 1) for r in reports))


if __name__ == "__main__":
    raise SystemExit(main())
