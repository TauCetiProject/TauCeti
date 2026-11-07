"""Bulk restoration must leave stock Lake responsible for current input validity."""

import errno
import hashlib
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


class PreparedSeedTests(unittest.TestCase):
    def setUp(self):
        BulkUnpackTests.setUp(self)
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.36.0-rc2\n")
        (self.root / "lake-manifest.json").write_text("{}")
        (self.root / "TauCeti").mkdir()
        (self.root / "TauCeti/Seeded.lean").write_text("module\n")
        self.seed = self.root / "seed"
        build = self.seed / "build/lib/lean/TauCeti"
        build.mkdir(parents=True)
        self.files = ["lib/lean/TauCeti/Seeded." + ext for ext in ("trace", "olean", "ilean")]
        for relative in self.files:
            (self.seed / "build" / relative).write_text("trusted output")
            (self.seed / "build" / relative).chmod(0o444)
        self.manifest = dict(schema=1, kind="tauceti-prepared-root-v1", identity=bulk.configuration(self.root),
                             published_revision="a" * 40, producer_revision="b" * 40,
                             modules={"TauCeti.Seeded": dict(archive=self.archive.name, archive_sha256=bulk.file_digest(self.archive), files=self.files)})
        self.write_manifest()

    def write_manifest(self):
        (self.seed / "manifest.json").write_text(json.dumps(self.manifest))

    def test_complete_seed_copies_private_outputs_without_unpacking(self):
        with patch.object(bulk.subprocess, "run") as extract, \
                patch.object(bulk.fcntl, "ioctl", side_effect=OSError(errno.EOPNOTSUPP, "no reflink")):
            self.assertEqual(bulk.unpack(self.root, self.seed), 1)
        extract.assert_not_called()
        for relative in self.files:
            source, target = self.seed / "build" / relative, self.root / ".lake/build" / relative
            self.assertEqual(source.read_bytes(), target.read_bytes())
            self.assertNotEqual(source.stat().st_ino, target.stat().st_ino)
            target.write_text("private change")
            self.assertEqual(source.read_text(), "trusted output")
        self.assertFalse(self.record.exists())
        self.assertTrue(self.archive.exists())

    def test_partial_seed_keeps_one_bulk_invocation_for_all_misses(self):
        for number in range(3):
            input_hash, archive_hash = f"{number + 2:016x}", f"{number + 20:016x}"
            (self.records / (input_hash + ".json")).write_text(json.dumps(
                dict(schemaVersion=bulk.SCHEMA, data=archive_hash + ".ltar")))
            (self.artifacts / (archive_hash + ".ltar")).write_bytes(b"miss")
            (self.root / f"TauCeti/M{number}.lean").write_text("module\n")
        def extract(*args, **kwargs):
            requests = json.loads(kwargs["input"])
            self.assertEqual(len(requests), 3)
            for number, record in enumerate(requests):
                lib, ir = map(Path, record["base"])
                lib.mkdir(parents=True)
                ir.mkdir()
                (lib / f"M{number}.ilean").write_text(json.dumps(dict(version=5, module=f"TauCeti.M{number}")))
        with patch.object(bulk.subprocess, "check_output", return_value="/toolchain"), \
                patch.object(bulk.subprocess, "run", side_effect=extract) as native:
            self.assertEqual(bulk.unpack(self.root, self.seed), 4)
        native.assert_called_once()
        self.assertEqual(list(self.records.iterdir()), [])

    def test_interrupted_combined_publication_preserves_every_original_mapping(self):
        original = self.record.read_bytes()
        with patch.object(bulk, "publish", side_effect=OSError("interrupted")):
            self.assertEqual(bulk.unpack(self.root, self.seed), 0)
        self.assertEqual(self.record.read_bytes(), original)
        self.assertFalse((self.root / ".lake/build").exists())
        self.assertTrue(self.archive.exists())

    def test_changed_mapping_is_rejected_before_build_publication(self):
        records = bulk.selected_records(self.root)
        with tempfile.TemporaryDirectory(dir=self.root / ".lake") as temporary:
            combined, satisfied, _ = bulk.assemble(self.root, records, Path(temporary), self.seed)
            self.record.write_text("changed")
            with self.assertRaisesRegex(ValueError, "changed during"):
                bulk.publish(self.root, combined, satisfied)
        self.assertEqual(self.record.read_text(), "changed")
        self.assertFalse((self.root / ".lake/build").exists())

    def test_seed_identity_paths_and_overlapping_archives_are_rejected(self):
        original = json.loads(json.dumps(self.manifest))
        for change in ("config", "escape", "duplicate", "schema"):
            self.manifest = json.loads(json.dumps(original))
            entry = self.manifest["modules"]["TauCeti.Seeded"]
            if change == "config":
                self.manifest["identity"]["toolchain"] = "wrong"
            elif change == "escape":
                entry["files"].append("../escape")
            elif change == "duplicate":
                self.manifest["modules"]["TauCeti.Other"] = dict(entry)
            else:
                self.manifest["schema"] = True
            self.write_manifest()
            with self.subTest(change=change), self.assertRaises(ValueError):
                bulk.read_seed(self.seed, self.root)

    def test_symlinked_seed_file_stays_in_one_bulk_miss_set(self):
        file = self.seed / "build" / self.files[0]
        file.unlink()
        file.symlink_to(self.archive)
        with patch.object(bulk, "extract_records", return_value=[]) as extract:
            self.assertEqual(bulk.unpack(self.root, self.seed), 0)
        self.assertEqual(len(extract.call_args.args[0]), 1)
        self.assertTrue(self.record.exists())

    def test_successful_clone_has_writable_private_outputs_and_preserved_mtime(self):
        source = self.seed / "build" / self.files[0]
        target = self.root / "clone"
        def clone(destination, operation, descriptor):
            self.assertEqual(operation, bulk.FICLONE)
            os.write(destination.fileno(), os.read(descriptor, 4096))
        with patch.object(bulk.fcntl, "ioctl", side_effect=clone):
            self.assertTrue(bulk.install_file(source, target, True))
        self.assertEqual(target.read_bytes(), source.read_bytes())
        self.assertNotEqual(target.stat().st_ino, source.stat().st_ino)
        self.assertEqual(target.stat().st_mtime_ns, source.stat().st_mtime_ns)
        target.write_text("private")
        self.assertEqual(source.read_text(), "trusted output")

    def test_interrupt_after_tree_rename_keeps_records_for_native_restoration(self):
        unlink = Path.unlink
        def interrupted(path, *args, **kwargs):
            if path == self.record:
                raise OSError("interrupted after tree publication")
            return unlink(path, *args, **kwargs)
        with patch.object(Path, "unlink", interrupted):
            self.assertEqual(bulk.unpack(self.root, self.seed), 0)
        self.assertTrue(self.record.exists())
        self.assertTrue((self.root / ".lake/build/lib/lean/TauCeti/Seeded.olean").is_file())

    def test_permission_and_space_errors_are_not_unsupported_capabilities(self):
        for code in (errno.EACCES, errno.ENOSPC):
            with self.subTest(code=code), patch.object(bulk.fcntl, "ioctl", side_effect=OSError(code, "resource failure")):
                self.assertEqual(bulk.unpack(self.root, self.seed), 0)
            self.assertTrue(self.record.exists())
            self.assertFalse((self.root / ".lake/build").exists())



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
        self.assertFalse(any("test_bulk_unpack_cache.py --integration" in text for text in commands))
        infrastructure = yaml.safe_load((ROOT / ".github/workflows/infrastructure-tests.yml").read_text())
        fixtures = infrastructure["jobs"]["lean-fixtures"]["steps"]
        self.assertTrue(any("test_bulk_unpack_cache.py --integration" in step.get("run", "")
                            for step in fixtures))


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
                        self.assertIn(restored, (0, 3 if change else 4))
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
                    self.assertIn(bulk.unpack(path), (0, 3))
                run(path, "build", "--iofail", expected=1)


@unittest.skipUnless(INTEGRATION, "pass --integration with the pinned Lake installed")
class PreparedSeedNativeTests(unittest.TestCase):
    def test_aged_seed_mixed_misses_interruption_and_native_invalidation(self):
        with tempfile.TemporaryDirectory(prefix="prepared-root-native-") as temporary:
            root = Path(temporary)
            def fresh(name):
                project = root / name
                project.mkdir()
                (project / "lean-toolchain").write_text((ROOT / "lean-toolchain").read_text())
                (project / "lakefile.toml").write_text(
                    'name = "TauCeti"\nplatformIndependent = true\ndefaultTargets = ["TauCeti"]\n'
                    '[[lean_lib]]\nname = "TauCeti"\nglobs = ["TauCeti.*"]\n')
                (project / "TauCeti").mkdir()
                for i in range(20):
                    (project / f"TauCeti/M{i}.lean").write_text(f"module\npublic def m{i} : Nat := {i}\n")
                (project / "TauCeti.lean").write_text("module\n" + "\n".join(
                    f"public import TauCeti.M{i}" for i in range(20)) + "\n")
                return project
            def lake(project, *args, expected=0):
                env = {**os.environ, "LAKE_CACHE_DIR": str(project / ".lake/cache"),
                       "LAKE_ARTIFACT_CACHE": "true", "LAKE_RESTORE_ARTIFACTS": "true", "LAKE_NO_CACHE": "true"}
                result = subprocess.run(["lake", *args], cwd=project, env=env, text=True, capture_output=True, timeout=120)
                self.assertEqual(result.returncode, expected, result.stdout + result.stderr)
                return result.stdout + result.stderr
            producer = fresh("producer")
            lake(producer, "build", "--iofail", "-o", ".lake/map.jsonl")
            lake(producer, "cache", "stage", ".lake/map.jsonl", str(root / "old"))
            trusted = fresh("trusted")
            lake(trusted, "cache", "unstage", str(root / "old"))
            records = bulk.selected_records(trusted)
            snapshot = dict(version=1, toolchain=(trusted / "lean-toolchain").read_text().strip(),
                            entries={r["hash"]: [r["archive"], bulk.file_digest(Path(r["file"]))] for r in records})
            self.assertEqual(bulk.unpack(trusted), 21)
            self.assertNotIn("Built TauCeti", lake(trusted, "build", "--iofail"))
            seed = root / "seed"
            manifest = bulk.export_seed(trusted, seed, snapshot, published_revision="a" * 40, producer_revision="b" * 40)
            self.assertEqual(len(manifest["modules"]), 21)
            def fingerprint(directory):
                return {str(p.relative_to(directory)): bulk.file_digest(p) for p in directory.rglob("*") if p.is_file()}
            before = fingerprint(seed)
            (producer / "TauCeti/M19.lean").write_text("module\npublic def m19 : Nat := 190\n")
            lake(producer, "build", "--iofail", "-o", ".lake/map.jsonl")
            lake(producer, "cache", "stage", ".lake/map.jsonl", str(root / "new"))
            for case, limit in (("zero", 0), ("partial", 8), ("near", 100), ("interrupted", 8), ("deleted", 100)):
                project = fresh(case)
                (project / "TauCeti/M19.lean").write_text("module\npublic def m19 : Nat := 190\n")
                lake(project, "cache", "unstage", str(root / "new"))
                if case == "deleted":
                    (project / "TauCeti/M0.lean").unlink()
                selected_seed = root / (case + "-seed")
                selected_seed.mkdir()
                available = {r["archive"] for r in bulk.selected_records(project)}
                eligible = [(m, entry) for m, entry in manifest["modules"].items()
                            if entry["archive"] in available and bulk.source_present(project, m)]
                reduced = dict(manifest, modules=dict(eligible[:limit]))
                (selected_seed / "manifest.json").write_text(json.dumps(reduced))
                shutil.copytree(seed / "build", selected_seed / "build")
                selected_before = fingerprint(selected_seed)
                originals = {p: p.read_bytes() for p in (project / ".lake/cache/outputs/TauCeti").glob("*.json")}
                with patch.object(bulk, "extract_records", wraps=bulk.extract_records) as extract:
                    if case == "interrupted":
                        with patch.object(bulk, "publish", side_effect=OSError("interrupted")):
                            self.assertEqual(bulk.unpack(project, selected_seed), 0)
                        self.assertEqual({p: p.read_bytes() for p in originals}, originals)
                        self.assertFalse((project / ".lake/build").exists())
                        lake(project, "build", "--iofail")
                        self.assertEqual(fingerprint(selected_seed), selected_before)
                        continue
                    self.assertEqual(bulk.unpack(project, selected_seed), 20 if case == "deleted" else 21)
                    extract.assert_called_once()
                    miss_count = len(extract.call_args.args[0])
                    self.assertEqual(miss_count, 21 - len(reduced["modules"]))
                if case == "deleted":
                    retained = list((project / ".lake/cache/outputs/TauCeti").glob("*.json"))
                    self.assertEqual(len(retained), 1)
                    self.assertEqual(retained[0].read_bytes(), originals[retained[0]])
                log = lake(project, "build", "--iofail", expected=1 if case == "deleted" else 0)
                if case == "deleted":
                    self.assertFalse((project / ".lake/build/lib/lean/TauCeti/M0.olean").exists())
                    self.assertEqual(retained[0].read_bytes(), originals[retained[0]])
                else:
                    self.assertNotIn("Unpacked", log)
                    self.assertNotIn("Built TauCeti", log)
                    (project / "TauCeti/M18.lean").write_text("module\npublic def m18 : Nat := 180\n")
                    self.assertIn("Built TauCeti.M18", lake(project, "build", "--iofail"))
                self.assertEqual(fingerprint(selected_seed), selected_before)
                self.assertEqual(fingerprint(seed), before)

            # Rebuilt native outputs under changed inputs must not be exported
            # under the earlier snapshot's archive identities.
            (trusted / "TauCeti/M18.lean").write_text("module\npublic def m18 : Nat := 1800\n")
            lake(trusted, "build", "--iofail")
            changed = bulk.export_seed(trusted, root / "changed-seed", snapshot,
                                       published_revision="a" * 40, producer_revision="b" * 40)
            self.assertNotIn("TauCeti.M18", changed["modules"])
            self.assertGreater(len(changed["modules"]), 0)
            missing = trusted / ".lake/build/lib/lean/TauCeti/M17.olean"
            missing.unlink()
            omitted = bulk.export_seed(trusted, root / "missing-output-seed", snapshot,
                                       published_revision="a" * 40, producer_revision="b" * 40)
            self.assertNotIn("TauCeti.M17", omitted["modules"])
            for name in ("digest", "toolchain", "overlap"):
                bad = json.loads(json.dumps(snapshot))
                first = next(iter(bad["entries"]))
                if name == "digest":
                    bad["entries"][first][1] = "0" * 64
                elif name == "toolchain":
                    bad["toolchain"] = "wrong"
                else:
                    bad["entries"]["0" * 16] = bad["entries"][first]
                with self.subTest(export=name), self.assertRaises(ValueError):
                    bulk.export_seed(trusted, root / ("invalid-" + name), bad,
                                     published_revision="a" * 40, producer_revision="b" * 40)
                self.assertFalse((root / ("invalid-" + name)).exists())



if __name__ == "__main__":
    unittest.main()
