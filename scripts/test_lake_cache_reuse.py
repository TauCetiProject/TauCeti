#!/usr/bin/env python3
"""Archive reuse safety tests; add --integration to exercise the installed stock Lake."""

import errno
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import lake_cache_reuse as reuse


INTEGRATION = "--integration" in sys.argv
if INTEGRATION:
    sys.argv.remove("--integration")
ROOT = Path(__file__).resolve().parents[1]


class ReuseTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.archive = self.root / ".lake/cache/artifacts/0123456789abcdef.ltar"
        self.record = self.root / ".lake/cache/outputs/TauCeti/fedcba9876543210.json"
        self.trace = self.root / ".lake/build/lib/lean/TauCeti/A.trace"
        self.target = self.root / ".lake/build/ir/TauCeti/A.ltar"
        for path in (self.archive, self.record, self.trace, self.target):
            path.parent.mkdir(parents=True, exist_ok=True)
        self.archive.write_bytes(b"downloaded archive")
        self.record.write_text(json.dumps({"schemaVersion": reuse.OUTPUT_SCHEMA,
                                           "data": self.archive.name}))
        self.trace.write_text(json.dumps({"schemaVersion": reuse.TRACE_SCHEMA,
                                          "depHash": self.record.stem}))
        self.saved = reuse.snapshot(self.root)

    def test_download_records_survive_lake_overwrite(self):
        self.record.write_text('{"data": {"o": "other.olean"}}')
        self.assertEqual(reuse.reconnect(self.root, self.saved), 1)
        self.assertTrue(self.target.samefile(self.archive))
        self.assertEqual(self.target.stat().st_nlink, 2)

    def test_changed_input_is_not_reused(self):
        self.trace.write_text(json.dumps({"schemaVersion": reuse.TRACE_SCHEMA,
                                          "depHash": "0000000000000000"}))
        self.assertEqual(reuse.reconnect(self.root, self.saved), 0)

    def test_modified_archive_is_not_reused(self):
        self.archive.write_bytes(b"replacement bytes under the same hash filename")
        self.assertEqual(reuse.reconnect(self.root, self.saved), 0)
        self.assertFalse(self.target.exists())

    def test_linked_bytes_are_checked(self):
        real_link = os.link

        def replace_and_link(*args, **kwargs):
            self.archive.write_bytes(b"changed while linking")
            return real_link(*args, **kwargs)

        with patch.object(reuse.os, "link", side_effect=replace_and_link):
            self.assertEqual(reuse.reconnect(self.root, self.saved), 0)
        self.assertFalse(self.target.exists())

    def test_link_failure_never_copies(self):
        for code in (errno.EXDEV, errno.EPERM, errno.EOPNOTSUPP):
            with self.subTest(code=code), patch.object(reuse.os, "link", side_effect=OSError(code, "no link")):
                self.assertEqual(reuse.reconnect(self.root, self.saved), 0)
                self.assertFalse(self.target.exists())
                self.assertEqual(self.archive.stat().st_nlink, 1)

    def test_existing_archive_is_untouched(self):
        self.target.write_bytes(b"Lake's own archive")
        self.assertEqual(reuse.reconnect(self.root, self.saved), 0)
        self.assertEqual(self.target.read_bytes(), b"Lake's own archive")

    def test_missing_cache_or_missing_ir_directory(self):
        self.archive.unlink()
        self.assertEqual(reuse.snapshot(self.root)["entries"], {})
        self.assertEqual(reuse.reconnect(self.root, self.saved), 0)
        self.archive.write_bytes(b"downloaded archive")
        self.target.parent.rmdir()
        self.assertEqual(reuse.reconnect(self.root, self.saved), 0)

    def test_unknown_or_malformed_records_are_misses(self):
        for record in ({"schemaVersion": "future", "data": self.archive.name},
                       {"schemaVersion": reuse.OUTPUT_SCHEMA, "data": {"ltar": self.archive.name}},
                       {"schemaVersion": reuse.OUTPUT_SCHEMA, "data": "../../escape.ltar"}, [], None):
            with self.subTest(record=record):
                self.record.write_text(json.dumps(record))
                self.assertEqual(reuse.snapshot(self.root)["entries"], {})
        self.record.write_bytes(b"\xff")
        self.assertEqual(reuse.snapshot(self.root)["entries"], {})
        for trace in ({"schemaVersion": "future", "depHash": self.record.stem},
                      {"schemaVersion": reuse.TRACE_SCHEMA, "depHash": []}, [], None):
            self.trace.write_text(json.dumps(trace))
            self.assertEqual(reuse.reconnect(self.root, self.saved), 0)

    def test_unrecognized_snapshot_or_unsafe_entry_is_ignored(self):
        for saved in (None, [], {"version": 2, "entries": self.saved["entries"]},
                      {"version": 1, "entries": []},
                      {"version": 1, "entries": {self.record.stem: ["../escape.ltar", "0" * 64]}}):
            self.assertEqual(reuse.reconnect(self.root, saved), 0)

    def test_symlink_archive_trace_and_parents_are_rejected(self):
        for path in (self.archive, self.archive.parent, self.trace, self.trace.parent, self.target.parent):
            with self.subTest(path=path):
                original = path.with_name(path.name + ".original")
                path.rename(original)
                path.symlink_to(original, target_is_directory=original.is_dir())
                self.assertEqual(reuse.reconnect(self.root, self.saved), 0)
                path.unlink()
                original.rename(path)

    def test_fifo_is_not_opened_as_an_archive(self):
        self.archive.unlink()
        os.mkfifo(self.archive)
        self.assertEqual(reuse.reconnect(self.root, self.saved), 0)

    def test_sandbox_snapshot_is_readonly_and_before_build(self):
        workflow = (ROOT / ".github/workflows/pr-build.yml").read_text()
        snapshot = "python3 gate/scripts/lake_cache_reuse.py snapshot pr gate/lake-cache-reuse.json"
        self.assertLess(workflow.index("run: bash gate/scripts/lake-cache-get.sh pr"), workflow.index(snapshot))
        self.assertLess(workflow.index(snapshot), workflow.index("- name: Build exact candidate under bwrap"))
        self.assertIn('--ro-bind "$PWD/gate" "$PWD/gate"', workflow)
        build = (ROOT / "scripts/sandbox-build.sh").read_text()
        self.assertLess(build.index('bash "$TRUSTED_SCRIPTS/lint-style.sh"'), build.index("lake_cache_reuse.py"))
        self.assertLess(build.index("lake_cache_reuse.py"), build.index("lake build --no-build --rehash -o"))

    def test_toolchain_bumps_test_the_validated_candidate_pin_before_building(self):
        workflow = (ROOT / ".github/workflows/pr-build.yml").read_text()
        block = workflow.split("- name: Validate Lake archive reuse against a changed toolchain", 1)[1].split("- name:", 1)[0]
        self.assertIn("env.INFRA != '1' && env.TOOLCHAIN_CHANGED == '1'", block)
        self.assertIn('ELAN_TOOLCHAIN="$(cat pr/lean-toolchain)"', block)
        self.assertIn("python3 gate/scripts/test_lake_cache_reuse.py --integration", block)
        position = workflow.index(block)
        self.assertLess(workflow.index("- name: Validate the Lake-pin bump before building"), position)
        self.assertLess(workflow.index("- name: Fetch Mathlib with the (bump-validated) config"), position)
        self.assertLess(position, workflow.index("- name: Build exact candidate under bwrap"))


@unittest.skipUnless(INTEGRATION, "pass --integration with Lake installed")
class StockLakeTests(unittest.TestCase):
    def test_complete_mapping_changed_added_deleted_and_stale_sources(self):
        lake = shutil.which("lake")
        self.assertIsNotNone(lake)
        with tempfile.TemporaryDirectory(prefix="lake-reuse-test-") as temporary:
            root = Path(temporary)

            def project(name):
                directory = root / name
                directory.mkdir()
                # pr-build sets ELAN_TOOLCHAIN to the validated candidate pin;
                # the trusted script checkout may still carry the older pin.
                toolchain = os.environ.get("ELAN_TOOLCHAIN") or (ROOT / "lean-toolchain").read_text().strip()
                (directory / "lean-toolchain").write_text(toolchain + "\n")
                (directory / "lakefile.toml").write_text(
                    'name = "TauCeti"\nplatformIndependent = true\ndefaultTargets = ["TauCeti"]\n'
                    '[[lean_lib]]\nname = "TauCeti"\nglobs = ["TauCeti.*"]\n')
                (directory / "TauCeti").mkdir()
                (directory / "TauCeti.lean").write_text("module\n")
                (directory / "TauCeti/A.lean").write_text("module\npublic def a : Nat := 42\n")
                (directory / "TauCeti/B.lean").write_text("module\npublic import TauCeti.A\npublic def b : Nat := a + 1\n")
                (directory / "TauCeti/C.lean").write_text("module\npublic def c : Nat := 7\n")
                return directory

            def run(directory, *args, expected=0):
                env = dict(os.environ, LAKE_CACHE_DIR=str(directory / ".lake/cache"),
                           LAKE_ARTIFACT_CACHE="true", LAKE_RESTORE_ARTIFACTS="true", LAKE_NO_CACHE="true")
                result = subprocess.run([lake, *args], cwd=directory, env=env,
                                        capture_output=True, text=True, timeout=120)
                self.assertEqual(result.returncode, expected, result.stdout + result.stderr)

            def mapping(directory):
                lines = (directory / ".lake/outputs.jsonl").read_text().splitlines()
                return json.loads(lines[0]), dict(map(json.loads, lines[1:]))

            producer = project("producer")
            run(producer, "build", "--iofail", "-o", ".lake/outputs.jsonl")
            run(producer, "cache", "stage", ".lake/outputs.jsonl", str(root / "staging"))
            maps = []
            for variant in ("control", "reuse"):
                consumer = project(variant)
                run(consumer, "cache", "unstage", str(root / "staging"))
                saved = reuse.snapshot(consumer)
                self.assertEqual(len(saved["entries"]), 4)
                (consumer / "TauCeti/A.lean").write_text("module\npublic def a : Nat := 43\n")
                (consumer / "TauCeti/C.lean").unlink()
                (consumer / "TauCeti/D.lean").write_text("module\npublic def d : Nat := 8\n")
                run(consumer, "build", "--iofail")
                if variant == "reuse":
                    # A future Lake with the upstream fix may already retain these.
                    unchanged = [consumer / ".lake/build/ir/TauCeti.ltar",
                                 consumer / ".lake/build/ir/TauCeti/B.ltar"]
                    retained = sum(path.exists() for path in unchanged)
                    self.assertEqual(reuse.reconnect(consumer, saved), 2 - retained)
                    self.assertTrue(all(path.exists() for path in unchanged))
                    # --rehash must ignore writable hash sidecars when Lake
                    # describes the linked archives for the final output map.
                    for archive in unchanged:
                        archive.with_suffix(".ltar.hash").write_text("0000000000000000")
                    self.assertFalse((consumer / ".lake/build/ir/TauCeti/A.ltar").exists())
                    self.assertFalse((consumer / ".lake/build/ir/TauCeti/D.ltar").exists())
                run(consumer, "build", "--no-build", "--rehash", "-o", ".lake/outputs.jsonl")
                maps.append(mapping(consumer))
                self.assertEqual(len(maps[-1][1]), 4)
            self.assertEqual(maps[0], maps[1])
            (consumer / "TauCeti/B.lean").write_text("module\npublic def changed : Nat := 9\n")
            run(consumer, "build", "--no-build", "--rehash", "-o", ".lake/stale.jsonl", expected=3)


if __name__ == "__main__":
    unittest.main()
