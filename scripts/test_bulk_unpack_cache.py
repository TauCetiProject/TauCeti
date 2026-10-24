"""Bulk restoration must leave stock Lake responsible for current input validity."""

import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

import yaml
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("bulk_unpack", ROOT / "scripts/bulk-unpack-cache.py")
bulk = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bulk)
INTEGRATION = "--integration" in sys.argv
if INTEGRATION:
    sys.argv.remove("--integration")


class BulkUnpackTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        (self.root / "lakefile.toml").write_text(
            'name = "TauCeti"\n[[lean_lib]]\nname = "TauCeti"\n')
        self.records = self.root / ".lake/cache/outputs/TauCeti"
        self.records.mkdir(parents=True)
        self.artifacts = self.root / ".lake/cache/artifacts"
        self.artifacts.mkdir()
        self.record = self.records / "0123456789abcdef.json"
        self.archive = self.artifacts / "fedcba9876543210.ltar"
        self.archive.write_bytes(b"archive fixture")
        self.record.write_text(json.dumps({"schemaVersion": bulk.SCHEMA,
                                          "data": self.archive.name}))

    def test_one_invocation_preserves_hashes_and_output_roots(self):
        (self.records / "1111111111111111.json").write_text(json.dumps(
            {"schemaVersion": bulk.SCHEMA, "data": "2222222222222222.ltar"}))
        (self.artifacts / "2222222222222222.ltar").write_bytes(b"another archive")
        def extract(*args, **kwargs):
            for index, record in enumerate(json.loads(kwargs["input"])):
                module = f"TauCeti.Fixture{index}"
                (self.root / "TauCeti").mkdir(exist_ok=True)
                (self.root / "TauCeti" / f"Fixture{index}.lean").write_text("module\n")
                lib, ir = map(Path, record["base"])
                lib.mkdir(parents=True)
                ir.mkdir(parents=True)
                (lib / f"Fixture{index}.ilean").write_text(json.dumps({"version": 5, "module": module}))
        with patch.object(bulk.subprocess, "check_output", return_value="/toolchain\n"), \
                patch.object(bulk.subprocess, "run", side_effect=extract) as run:
            self.assertEqual(bulk.unpack(self.root), 2)
        run.assert_called_once()
        self.assertEqual(run.call_args.args[0], ["/toolchain/bin/leantar", "-x", "-j", "-"])
        records = json.loads(run.call_args.kwargs["input"])
        self.assertEqual([r["hash"] for r in records], ["0123456789abcdef", "1111111111111111"])
        self.assertEqual([Path(p).name for p in records[0]["base"]], ["lib", "ir"])
        self.assertTrue((self.root / ".lake/build/lib/lean/TauCeti/Fixture0.ilean").exists())
        self.assertFalse(self.record.exists())

    def assert_stock_fallback(self):
        with patch.object(bulk.subprocess, "run") as run:
            self.assertEqual(bulk.unpack(self.root), 0)
        run.assert_not_called()

    def test_existing_build_is_untouched(self):
        (self.root / ".lake/build").mkdir()
        self.assert_stock_fallback()

    def test_unknown_or_malformed_records_use_stock_lake(self):
        for text in ("{", "[]", '{"schemaVersion":"future"}',
                     json.dumps({"schemaVersion": bulk.SCHEMA, "data": {"o": "artifact"}})):
            with self.subTest(text=text):
                self.record.write_text(text)
                self.assert_stock_fallback()

    def test_unsupported_layout_uses_stock_lake(self):
        for text in ('name = "Other"', 'name = "TauCeti"\nbuildDir = "out"',
                     'name = "TauCeti"\nlean_lib = "bad"',
                     'name = "TauCeti"\n[lean_lib]\nname = "TauCeti"', '{'):
            with self.subTest(text=text):
                (self.root / "lakefile.toml").write_text(text)
                self.assert_stock_fallback()

    def test_failed_extraction_leaves_cache_and_build_untouched(self):
        with patch.object(bulk.subprocess, "check_output", return_value="/toolchain\n"), \
                patch.object(bulk.subprocess, "run", side_effect=subprocess.CalledProcessError(1, "leantar")):
            self.assertEqual(bulk.unpack(self.root), 0)
        self.assertTrue(self.record.exists())
        self.assertFalse((self.root / ".lake/build").exists())

    def test_cli_does_not_touch_a_shared_or_disabled_cache(self):
        for configured, enabled, restored in (("/shared/cache", "true", "true"),
                (str(self.root / ".lake/cache"), "", "true"),
                (str(self.root / ".lake/cache"), "true", "")):
            with self.subTest(configured=configured, enabled=enabled, restored=restored):
                env = {**os.environ, "LAKE_CACHE_DIR": configured,
                       "LAKE_ARTIFACT_CACHE": enabled, "LAKE_RESTORE_ARTIFACTS": restored}
                result = subprocess.run([sys.executable, str(ROOT / "scripts/bulk-unpack-cache.py"),
                                         str(self.root)], env=env, text=True, capture_output=True)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("private CI cache not enabled", result.stdout)
                self.assertTrue(self.record.exists())
                self.assertFalse((self.root / ".lake/build").exists())

    def test_unknown_module_leaves_all_records_and_outputs_untouched(self):
        def extract(*args, **kwargs):
            lib, ir = map(Path, json.loads(kwargs["input"])[0]["base"])
            lib.mkdir(parents=True)
            ir.mkdir()
            (lib / "Other.ilean").write_text(json.dumps({"version": 5, "module": "Other"}))
        with patch.object(bulk.subprocess, "check_output", return_value="/toolchain\n"), \
                patch.object(bulk.subprocess, "run", side_effect=extract):
            self.assertEqual(bulk.unpack(self.root), 0)
        self.assertTrue(self.record.exists())
        self.assertFalse((self.root / ".lake/build").exists())

    def test_unexpected_helper_failure_leaves_normal_build_available(self):
        env = {"LAKE_CACHE_DIR": str(self.root / ".lake/cache"),
               "LAKE_ARTIFACT_CACHE": "true", "LAKE_RESTORE_ARTIFACTS": "true"}
        with patch.dict(os.environ, env), \
                patch.object(bulk, "unpack", side_effect=OSError("unavailable toolchain")):
            bulk.main(self.root)
        self.assertTrue(self.record.exists())

    def test_missing_archive_uses_stock_lake(self):
        self.archive.unlink()
        self.assert_stock_fallback()

    def test_historical_duplicate_archive_uses_stock_lake(self):
        (self.records / "1111111111111111.json").write_bytes(self.record.read_bytes())
        self.assert_stock_fallback()

    def test_symlinked_record_or_archive_uses_stock_lake(self):
        self.archive.unlink()
        self.archive.symlink_to(self.record)
        self.assert_stock_fallback()
        self.archive.unlink()
        self.archive.write_bytes(b"archive fixture")
        self.record.unlink()
        self.record.symlink_to(self.archive)
        self.assert_stock_fallback()


class WorkflowTests(unittest.TestCase):
    def test_pr_preparation_runs_offline_with_trusted_tooling_before_build(self):
        workflow = yaml.safe_load((ROOT / ".github/workflows/pr-build.yml").read_text())
        step = next(step for step in workflow["jobs"]["sandboxed-build"]["steps"]
                    if step.get("id") == "build")
        command = step["run"]
        self.assertIn("--unshare-net", command)
        self.assertIn('--ro-bind "$PWD/gate" "$PWD/gate"', command)
        self.assertIn('--bind "$PWD/pr/.lake" "$PWD/pr/.lake"', command)
        self.assertIn("'python3 ../gate/scripts/bulk-unpack-cache.py; "
                      "exec bash ../gate/scripts/sandbox-build.sh'", command)
        self.assertNotIn("continue-on-error", step)

    def test_main_snapshots_before_preparation_and_build(self):
        workflow = yaml.safe_load((ROOT / ".github/workflows/ci.yml").read_text())
        steps = workflow["jobs"]["build"]["steps"]
        commands = [step.get("run", "") for step in steps]
        snapshot = next(i for i, text in enumerate(commands) if "lake_cache_reuse.py snapshot" in text)
        prepare = next(i for i, text in enumerate(commands) if "python3 scripts/bulk-unpack-cache.py" in text)
        build = next(i for i, text in enumerate(commands) if text.strip() == "lake build")
        self.assertLess(snapshot, prepare)
        self.assertLess(prepare, build)
        self.assertNotIn("continue-on-error", steps[prepare])
        self.assertEqual(steps[prepare]["env"]["LAKE_NO_CACHE"], "true")
        self.assertTrue(any("test_bulk_unpack_cache.py --integration" in text for text in commands))


@unittest.skipUnless(INTEGRATION, "pass --integration with the pinned Lake installed")
class StockLakeTests(unittest.TestCase):
    def test_replay_and_changes_match_stock_lake(self):
        lake = shutil.which("lake")
        with tempfile.TemporaryDirectory(prefix="bulk-unpack-test-") as tmp:
            root = Path(tmp)

            def project(name):
                path = root / name
                path.mkdir()
                (path / "lean-toolchain").write_text((ROOT / "lean-toolchain").read_text())
                (path / "lakefile.toml").write_text(
                    'name = "TauCeti"\nplatformIndependent = true\ndefaultTargets = ["TauCeti"]\n'
                    '[[lean_lib]]\nname = "TauCeti"\nglobs = ["TauCeti.*"]\n')
                (path / "TauCeti").mkdir()
                for file, text in {"TauCeti.lean": "module\n",
                                   "TauCeti/A.lean": "module\npublic def a : Nat := 42\n",
                                   "TauCeti/B.lean": "module\npublic import TauCeti.A\npublic def b := a + 1\n",
                                   "TauCeti/C.lean": "module\npublic def c : Nat := 7\n"}.items():
                    (path / file).write_text(text)
                return path

            def run(path, *args, expected=0):
                env = {**os.environ, "LAKE_CACHE_DIR": str(path / ".lake/cache"),
                       "LAKE_ARTIFACT_CACHE": "true", "LAKE_RESTORE_ARTIFACTS": "true",
                       "LAKE_NO_CACHE": "true"}
                result = subprocess.run([lake, *args], cwd=path, env=env,
                                        text=True, capture_output=True, timeout=120)
                self.assertEqual(result.returncode, expected, result.stdout + result.stderr)
                return result.stdout + result.stderr

            producer = project("producer")
            run(producer, "build", "--iofail", "-o", ".lake/map.jsonl")
            run(producer, "cache", "stage", ".lake/map.jsonl", str(root / "staging"))
            for change in (False, True):
                maps = []
                for mode in ("stock", "bulk"):
                    path = project(f"{mode}-{change}")
                    run(path, "cache", "unstage", str(root / "staging"))
                    if change:
                        (path / "TauCeti/A.lean").write_text("module\npublic def a : Int := 43\n")
                        (path / "TauCeti/C.lean").unlink()
                        (path / "TauCeti/D.lean").write_text("module\npublic def d : Nat := 8\n")
                    restored = bulk.unpack(path) if mode == "bulk" else 0
                    if mode == "bulk":
                        # Future toolchain layouts may safely use stock restoration.
                        self.assertIn(restored, (0, 4))
                        if change:
                            self.assertFalse((path / ".lake/build/lib/lean/TauCeti/C.olean").exists())
                    if change:
                        run(path, "build", "--no-build", expected=3)
                    log = run(path, "build", "--iofail")
                    if restored:
                        self.assertNotIn("Unpacked", log)
                        if change:
                            self.assertIn("Built TauCeti.A", log)
                            self.assertIn("Built TauCeti.B", log)
                            self.assertIn("Built TauCeti.D", log)
                        else:
                            self.assertNotIn("Built TauCeti", log)
                    run(path, "build", "--no-build", "--rehash", "-o", ".lake/map.jsonl")
                    lines = (path / ".lake/map.jsonl").read_text().splitlines()
                    maps.append((json.loads(lines[0]), dict(map(json.loads, lines[1:]))))
                self.assertEqual(maps[0], maps[1])
            # Stale artifacts for deleted sources must not make a broken import pass.
            for mode in ("stock", "bulk"):
                path = project(f"deleted-import-{mode}")
                run(path, "cache", "unstage", str(root / "staging"))
                (path / "TauCeti/C.lean").unlink()
                (path / "TauCeti/B.lean").write_text(
                    "module\npublic import TauCeti.C\npublic def b := c + 1\n")
                if mode == "bulk":
                    self.assertIn(bulk.unpack(path), (0, 4))
                run(path, "build", "--iofail", expected=1)


if __name__ == "__main__":
    unittest.main()
