#!/usr/bin/env python3
"""Behavioral corruption/provenance/config tests and cache-writer boundary checks."""

from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

import yaml

from prepare_dependency_warm import materialize, prepare
from toolchain_snapshot import MANIFEST, seal, toolchain_name, verify

ROOT = Path(__file__).resolve().parents[1]
PIN = "leanprover/lean4:v4.35.0-rc3"
REVISION = "a" * 40


class Snapshot(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / "release"
        (self.root / "bin").mkdir(parents=True)
        for name in ("lean", "lake"):
            executable = self.root / "bin" / name
            executable.write_text("#!/bin/sh\nexit 0\n")
            executable.chmod(0o755)
        (self.root / "bin/compiler").symlink_to("lean")
        seal(self.root, PIN, REVISION, "123")

    def test_three_concurrent_readers_of_sealed_snapshot(self):
        with ThreadPoolExecutor(max_workers=3) as pool:
            list(pool.map(lambda _: verify(self.root, PIN), range(3)))

    def test_missing_and_wrong_toolchain(self):
        with self.assertRaises(ValueError):
            verify(self.root, "leanprover/lean4:v4.34.0")
        (self.root / MANIFEST).unlink()
        with self.assertRaises(FileNotFoundError):
            verify(self.root, PIN)

    def test_corruption_addition_and_mode_changes(self):
        for change in ("bytes", "extra", "mode"):
            with self.subTest(change=change):
                path = self.root / "bin/lean"
                old_bytes, old_mode = path.read_bytes(), path.stat().st_mode & 0o777
                if change == "bytes":
                    path.write_text("corrupt")
                elif change == "extra":
                    (self.root / "injected").write_text("payload")
                else:
                    path.chmod(0o644)
                with self.assertRaises(ValueError):
                    verify(self.root, PIN)
                path.write_bytes(old_bytes)
                path.chmod(old_mode)
                (self.root / "injected").unlink(missing_ok=True)

    def test_producer_ref_and_schema_binding(self):
        path = self.root / MANIFEST
        original = json.loads(path.read_text())
        for field, value in (("producer", "pr-build.yml"), ("ref", "refs/pull/42/head"),
                             ("schema", 0), ("revision", "main"), ("run_id", "unknown")):
            data = dict(original)
            data[field] = value
            path.write_text(json.dumps(data))
            with self.subTest(field=field), self.assertRaises(ValueError):
                verify(self.root, PIN)

    def test_escaping_symlink_and_root_alias(self):
        (self.root / "bin/compiler").unlink()
        (self.root / "bin/compiler").symlink_to("/etc/passwd")
        with self.assertRaises(ValueError):
            seal(self.root, PIN, REVISION, "123")
        alias = self.root.parent / "alias"
        alias.symlink_to(self.root)
        with self.assertRaises(ValueError):
            verify(alias, PIN)

    def test_only_official_release_names(self):
        self.assertEqual(toolchain_name(PIN), "leanprover--lean4---v4.35.0-rc3")
        for pin in ("../escape", "nightly", "fork/lean4:v4.35.0", "leanprover/lean4:v4/../x"):
            with self.subTest(pin=pin), self.assertRaises(ValueError):
                toolchain_name(pin)

    def run_consumer(self):
        action = yaml.safe_load((ROOT / ".github/actions/restore-lean-toolchain/action.yml").read_text())
        command = action["runs"]["steps"][-1]["run"]
        home = self.root.parent / "home"
        binaries = home / ".elan/bin"
        binaries.mkdir(parents=True, exist_ok=True)
        (binaries / "elan").write_text(
            '#!/usr/bin/env bash\nset -eu\nprintf "%s\\n" "$*" >> "$INSTALL_LOG"\n'
            'mkdir -p "$SNAPSHOT/bin"\n'
            'printf "official release\\n" > "$SNAPSHOT/bin/lean"\n')
        (binaries / "lean").write_text('#!/bin/sh\necho "Lean fixture"\n')
        for path in binaries.iterdir():
            path.chmod(0o755)
        (home / "lean-toolchain").write_text(PIN + "\n")
        log = home / "installs"
        subprocess.run(["bash", "-c", command], check=True, capture_output=True, env={
            **os.environ, "HOME": str(home), "SNAPSHOT": str(self.root),
            "PROJECT": str(home), "TOOLING": str(ROOT), "INSTALL_LOG": str(log)})
        return log.read_text() if log.exists() else ""

    def test_consumer_warm_path_does_not_install(self):
        self.assertEqual(self.run_consumer(), "")

    def test_consumer_corrupt_and_missing_paths_reinstall_official_pin(self):
        (self.root / "bin/lean").write_text("poison")
        self.assertEqual(self.run_consumer().splitlines(), ["toolchain install " + PIN])
        self.assertEqual((self.root / "bin/lean").read_text(), "official release\n")
        self.assertFalse((self.root / MANIFEST).exists())
        # The fallback did not manufacture trusted provenance for the corrupt entry.
        self.assertEqual(self.run_consumer().splitlines(), ["toolchain install " + PIN] * 2)


class Config(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name) / "repo"
        self.repo.mkdir()
        self.git("init", "-q")
        self.git("config", "user.name", "Fixture")
        self.git("config", "user.email", "fixture@example.invalid")
        (self.repo / "lakefile.toml").write_text('name = "Fixture"\n')
        (self.repo / "lean-toolchain").write_text(PIN + "\n")
        (self.repo / "lake-manifest.json").write_text('{"packages": []}\n')
        (self.repo / "scripts").mkdir()
        (self.repo / "scripts/check-bump.sh").write_text('cmp "$2/lean-toolchain" "$3/lean-toolchain"\n')
        self.base = self.commit()

    def git(self, *args):
        return subprocess.check_output(["git", "-C", str(self.repo), *args], stderr=subprocess.DEVNULL).decode().strip()

    def commit(self):
        self.git("add", ".")
        self.git("commit", "-qm", "fixture")
        return self.git("rev-parse", "HEAD")

    def test_materializes_only_configs_not_candidate_sources(self):
        (self.repo / "Candidate.lean").write_text("evil code")
        head = self.commit()
        self.git("checkout", "-q", self.base)
        project = prepare(self.repo, head, self.repo.parent / "prepared")
        self.assertEqual({p.name for p in project.iterdir()},
                         {"lakefile.toml", "lean-toolchain", "lake-manifest.json"})

    def test_rejects_symlink_pin_and_lakefile_edit(self):
        (self.repo / "lean-toolchain").unlink()
        (self.repo / "lean-toolchain").symlink_to("lakefile.toml")
        head = self.commit()
        with self.assertRaises(ValueError):
            materialize(self.repo, head, self.repo.parent / "symlink")
        self.git("checkout", "-q", self.base)
        (self.repo / "lakefile.toml").write_text("candidate executable configuration")
        head = self.commit()
        self.git("checkout", "-q", self.base)
        with self.assertRaises(ValueError):
            prepare(self.repo, head, self.repo.parent / "edited")

    def test_validator_failure_prevents_lake_execution(self):
        (self.repo / "lean-toolchain").write_text("leanprover/lean4:v99.0.0\n")
        head = self.commit()
        self.git("checkout", "-q", self.base)
        with self.assertRaises(subprocess.CalledProcessError):
            prepare(self.repo, head, self.repo.parent / "bad-bump")


class Boundary(unittest.TestCase):
    def test_mathlib_cold_selection_preserves_publisher_key_and_directory(self):
        action = yaml.safe_load((ROOT / ".github/actions/restore-mathlib-ltars/action.yml").read_text())
        select, restore = action["runs"]["steps"]
        self.assertNotIn("if", select)
        self.assertEqual(restore["if"], "inputs.cold != 'true'")
        self.assertEqual(action["outputs"]["cache-primary-key"]["value"],
                         "${{ steps.cache_dir.outputs.key }}")
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            for directory in ("", str(root / "custom")):
                env_file, outputs = root / "env", root / "outputs"
                subprocess.run(["bash", "-c", select["run"]], check=True, env={
                    **os.environ, "CONFIGURED_CACHE_DIR": directory,
                    "GITHUB_WORKSPACE": temp, "GITHUB_ENV": str(env_file),
                    "GITHUB_OUTPUT": str(outputs), "CACHE_KEY_PREFIX": "snapshot-prefix-",
                    "MANIFEST_HASH": "manifest-hash"})
                values = dict(line.split("=", 1) for line in outputs.read_text().splitlines())
                self.assertEqual(values["path"], directory or str(root / ".mathlib-ltar-cache"))
                self.assertEqual(values["key"], "snapshot-prefix-manifest-hash")
                self.assertIn("MATHLIB_CACHE_DIR=" + values["path"], env_file.read_text())
        warmer = yaml.safe_load((ROOT / ".github/workflows/warm-dependencies.yml").read_text())
        steps = warmer["jobs"]["warm"]["steps"]
        consumer = next(step for step in steps if step.get("id") == "mathlib")
        self.assertNotIn("if", consumer)
        self.assertIn("cold", consumer["with"])
        publisher = next(step for step in steps if step.get("name") == "Save only official compressed downloads")
        self.assertEqual(publisher["with"], {
            "path": "${{ steps.mathlib.outputs.cache-dir }}/*.ltar",
            "key": "${{ steps.mathlib.outputs.cache-primary-key }}"})

    def test_only_isolated_main_warmer_saves_toolchain(self):
        warmer = yaml.safe_load((ROOT / ".github/workflows/warm-dependencies.yml").read_text())
        job = warmer["jobs"]["warm"]
        self.assertIn("github.ref == 'refs/heads/main'", job["if"])
        self.assertEqual(job["strategy"]["max-parallel"], 3)
        steps = job["steps"]
        saves = [step for step in steps if step.get("uses") == "actions/cache/save@v4"]
        self.assertEqual(len(saves), 2)
        self.assertTrue(saves[1]["with"]["path"].endswith("/*.ltar"))
        self.assertNotIn("secrets.", json.dumps(warmer))
        self.assertNotIn("lake build", json.dumps(steps))
        pr = (ROOT / ".github/workflows/pr-build.yml").read_text()
        self.assertNotIn("actions/cache/save", pr)
        self.assertIn('--ro-bind "$HOME/.elan" "$HOME/.elan"', pr)
        self.assertNotIn('--bind "$HOME/.elan"', pr)
        self.assertLess(pr.index("Validate the Lake-pin bump before building"),
                        pr.index("Restore or install the exact official Lean toolchain"))
        action = yaml.safe_load((ROOT / ".github/actions/restore-lean-toolchain/action.yml").read_text())
        self.assertNotIn("restore-keys", json.dumps(action))
        self.assertNotIn("cache/save", json.dumps(action))
        probe = (ROOT / "scripts/probe_dependency_sandbox.sh").read_text()
        self.assertIn('--ro-bind "$HOME/.elan" "$HOME/.elan"', probe)
        for flag in ("env -i /usr/bin/bwrap", "--unshare-net", "--remount-ro /", "--disable-userns"):
            self.assertIn(flag, probe)

    def test_main_saves_mathlib_before_root_build(self):
        steps = yaml.safe_load((ROOT / ".github/workflows/ci.yml").read_text())["jobs"]["build"]["steps"]
        save = next(i for i, s in enumerate(steps) if s.get("name") == "Save Mathlib's compressed download cache")
        build = next(i for i, s in enumerate(steps) if s.get("run") == "lake build")
        self.assertLess(save, build)


if __name__ == "__main__":
    unittest.main()
