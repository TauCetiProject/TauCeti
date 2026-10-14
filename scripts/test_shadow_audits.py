#!/usr/bin/env python3
"""Acceptance fixtures for the shadow-only prototype; real full checks on each observation."""

from dataclasses import replace
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from shadow_audits import (Record, ShadowSession, closure_keys, digest, observe,
                           sandbox_command, tree_digest)

ROOT = Path(__file__).resolve().parents[1]
LEAN = Path(os.environ.get("LEAN", subprocess.check_output(["elan", "which", "lean"],
                                                          text=True).strip()))
SYSROOT = Path(os.environ.get("LEAN_SYSROOT", subprocess.check_output(
    [str(LEAN), "--print-prefix"], text=True).strip()))


def fixture_snapshot():
    inventory = [
        {"module": "Dependency", "local": False, "imports": []},
        {"module": "TauCeti", "local": True, "imports": []},
        {"module": "TauCeti.A", "local": True, "imports": ["Dependency"]},
        {"module": "TauCeti.B", "local": True, "imports": ["TauCeti.A"]},
        {"module": "TauCeti.Orphan", "local": True, "imports": []},
    ]
    return {"inventory": inventory, "results": [
        {"module": r["module"], "count": 1, "messages": []} for r in inventory if r["local"]
    ], "ownership_status": 0, "axioms_status": 0}


FLAGS = subprocess.CompletedProcess([], 0, "module-system: clean\n", "")


class ShadowRecordsTest(unittest.TestCase):
    def setUp(self):
        self.session = ShadowSession()
        self.snapshot = fixture_snapshot()
        self.artifacts = {r["module"]: digest(r["module"]) for r in self.snapshot["inventory"]}

    def compare(self, *, identity="trusted-policy-and-toolchain", flags=FLAGS):
        return self.session.compare(self.snapshot, self.artifacts, identity, flags)

    def test_cold_then_warm_exact_comparison(self):
        self.assertEqual(self.compare()["reused"], [])
        warm = self.compare()
        self.assertTrue(warm["equivalent"])
        self.assertEqual(len(warm["reused"]), 4)

    def test_dependency_change_invalidates_transitive_importers(self):
        self.compare()
        self.artifacts["Dependency"] = "changed elaborator/macro bytes"
        report = self.compare()
        self.assertEqual(report["invalidated"], ["TauCeti.A", "TauCeti.B"])
        self.assertEqual(report["reused"], ["TauCeti", "TauCeti.Orphan"])

    def test_each_complete_identity_change_invalidates_all(self):
        for kind in ("toolchain", "pin", "policy", "driver"):
            with self.subTest(kind=kind):
                self.compare()
                self.assertEqual(self.compare(identity=kind)["reused"], [])

    def test_tampered_payload_key_or_seal_is_not_reused(self):
        for field in ("payload", "key", "seal"):
            with self.subTest(field=field):
                self.compare()
                record = self.session._records["TauCeti.A"]
                self.session._records["TauCeti.A"] = replace(record, **{field: "tampered"})
                report = self.compare()
                self.assertNotIn("TauCeti.A", report["reused"])
                self.assertTrue(report["equivalent"])

    def test_candidate_record_even_with_valid_hash_is_rejected(self):
        self.compare()
        record = self.session._records["TauCeti.A"]
        payload = '{"count": 1, "messages": []}'
        self.session._records["TauCeti.A"] = Record(record.key, payload, digest(payload))
        self.assertIn("TauCeti.A", self.compare()["invalidated"])

    def test_other_session_seals_do_not_transfer(self):
        self.compare()
        other = ShadowSession()
        other._records = dict(self.session._records)
        self.assertEqual(other.compare(self.snapshot, self.artifacts, "trusted-policy-and-toolchain",
                                       FLAGS)["reused"], [])

    def test_valid_but_incorrect_record_produces_explicit_mismatch(self):
        self.compare()
        record = self.session._records["TauCeti.A"]
        payload = json.dumps({"count": 99, "messages": ["stale false result"]})
        self.session._records["TauCeti.A"] = Record(
            record.key, payload, self.session._seal("TauCeti.A", record.key, payload))
        report = self.compare()
        self.assertFalse(report["equivalent"])
        self.assertEqual(report["mismatches"][0]["module"], "TauCeti.A")
        self.assertTrue(self.compare()["equivalent"])

    def test_global_ownership_and_flags_never_reused(self):
        self.compare()
        self.snapshot["ownership_status"] = 1
        flags = subprocess.CompletedProcess([], 1, "", "bad module-system flag")
        report = self.compare(flags=flags)
        self.assertEqual(len(report["reused"]), 4)
        self.assertEqual(report["full_status"], 1)
        self.assertEqual(report["global_checks"]["module_system_stderr"], flags.stderr)
        self.assertTrue(report["equivalent"])

    def test_removed_renamed_and_added_modules(self):
        self.compare()
        self.snapshot["inventory"][-1]["module"] = "TauCeti.Renamed"
        self.snapshot["results"][-1]["module"] = "TauCeti.Renamed"
        self.artifacts["TauCeti.Renamed"] = "new artifact"
        report = self.compare()
        self.assertEqual(report["removed"], ["TauCeti.Orphan"])
        self.assertEqual(report["recomputed"], ["TauCeti.Renamed"])

    def test_missing_dependency_and_cycle_fail_closed(self):
        for imports in (["Missing"], ["TauCeti.B"]):
            self.snapshot["inventory"][2]["imports"] = imports
            with self.assertRaises(ValueError):
                closure_keys(self.snapshot["inventory"], self.artifacts, "identity")

    def test_no_result_input_interface(self):
        # Candidate file assertions have no path into the session's private baseline.
        self.assertFalse(hasattr(self.session, "load"))
        self.assertFalse(hasattr(self.session, "save"))

    def test_full_inventory_and_result_inventory_must_agree(self):
        self.snapshot["results"].pop()
        with self.assertRaisesRegex(ValueError, "inventory mismatch"):
            self.compare()

    def test_toolchain_bytes_paths_modes_and_symlinks_are_bound(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            artifact = root / "compiler"
            artifact.write_text("a")
            first = tree_digest(root)
            artifact.write_text("b")
            second = tree_digest(root)
            self.assertNotEqual(first, second)
            artifact.chmod(0o755)
            self.assertNotEqual(second, tree_digest(root))
            before = tree_digest(root)
            (root / "alias").symlink_to(artifact)
            self.assertNotEqual(before, tree_digest(root))
            other = root / "directory"
            other.mkdir()
            (root / "directory-alias").symlink_to(other, target_is_directory=True)
            before = tree_digest(root)
            (other / "file").write_text("new bytes")
            self.assertNotEqual(before, tree_digest(root))

    def test_sandbox_excludes_credentials_and_writable_cache(self):
        command = sandbox_command(["driver"], Path("/snapshot"), [Path("/artifacts")],
                                  SYSROOT, LEAN)
        for flag in ("--unshare-user", "--unshare-net", "--unshare-pid", "--remount-ro",
                     "--disable-userns", "--die-with-parent"):
            self.assertIn(flag, command)
        self.assertNotIn("--bind", command)
        self.assertNotIn("--unshare-all", command)
        self.assertNotIn("GH_TOKEN", command)
        self.assertNotIn("--ro-bind / /", " ".join(command))


class ShadowLeanTest(unittest.TestCase):
    reports = []

    @classmethod
    def setUpClass(cls):
        cls.tooling = tempfile.TemporaryDirectory()
        cls.addClassCleanup(cls.tooling.cleanup)
        cls.driver = Path(cls.tooling.name) / "audit-driver"
        built = subprocess.run(["bash", str(ROOT / "scripts/build-audit-driver.sh"), str(ROOT),
                                str(ROOT / "scripts"), cls.tooling.name],
                               text=True, capture_output=True)
        if built.returncode:
            raise RuntimeError(built.stdout + built.stderr)
        cls.toolchain = tree_digest(SYSROOT)
        cls.workspace = tempfile.TemporaryDirectory()
        cls.addClassCleanup(cls.workspace.cleanup)
        cls.project = Path(cls.workspace.name)

    @classmethod
    def tearDownClass(cls):
        output = os.environ.get("SHADOW_REPORT")
        if output:
            Path(output).write_text(json.dumps(cls.reports, indent=2, sort_keys=True) + "\n")

    def setUp(self):
        for path in self.project.iterdir():
            if path.is_dir():
                import shutil
                shutil.rmtree(path)
            else:
                path.unlink()
        (self.project / "TauCeti").mkdir()
        (self.project / "lean-toolchain").write_text((ROOT / "lean-toolchain").read_text())
        self.session = ShadowSession()
        self.compile({"TauCeti": "module\npublic theorem rootGood : True := True.intro\n"})

    def compile(self, modules):
        env = {"PATH": os.environ["PATH"], "LEAN_PATH": str(self.project),
               "LEAN_SYSROOT": str(SYSROOT)}
        for module, source in modules.items():
            path = self.project / (module.replace(".", "/") + ".lean")
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source)
            built = subprocess.run([str(LEAN), "-o", str(path.with_suffix(".olean")), str(path)],
                                   cwd=self.project, env=env, text=True, capture_output=True)
            self.assertEqual(built.returncode, 0, built.stdout + built.stderr)

    def check(self, *, status=0):
        report = observe(self.session, self.project, [self.project], SYSROOT,
                         self.driver, self.toolchain)
        self.reports.append({"fixture": self.id(), **report})
        self.assertTrue(report["equivalent"], report)
        self.assertEqual(report["full_status"], status, report)
        return report

    def test_warm_allowed_private_root_and_orphan_results(self):
        self.compile({"TauCeti.Orphan": "module\nprivate theorem hidden : True := True.intro\n"})
        self.check()
        warm = self.check()
        self.assertEqual(warm["reused"], ["TauCeti", "TauCeti.Orphan"])
        self.assertEqual(warm["incremental_declarations"], 0)
        self.assertGreater(warm["full_declarations"], 0)

    def test_upstream_macro_change_even_with_same_importer_artifact(self):
        self.compile({
            "Dependency": 'module\npublic import Lean\npublic section\nmacro "answer" : term => `(0)\n',
            "TauCeti.Base": 'module\npublic import Dependency\npublic def macroOutput : Nat := answer\n',
            "TauCeti.Importer": "module\npublic import TauCeti.Base\npublic def consumer := macroOutput\n",
            "TauCeti.Orphan": "module\npublic def independent := 2\n",
        })
        self.check()
        self.compile({"Dependency": 'module\npublic import Lean\npublic section\nmacro "answer" : term => `(1)\n'})
        # Deliberately leave importer bytes unchanged: closure binding must still invalidate.
        changed = self.check()
        self.assertEqual(changed["invalidated"], ["TauCeti.Base", "TauCeti.Importer"])
        self.assertIn("TauCeti.Orphan", changed["reused"])
        self.assertLess(changed["incremental_declarations"], changed["full_declarations"])

    def test_add_remove_rename_and_orphan_inventory(self):
        self.compile({"TauCeti.Orphan": "module\npublic def unique := 1\n"})
        self.check()
        (self.project / "TauCeti/Orphan.lean").unlink()
        self.compile({"TauCeti.Renamed": "module\npublic def unique := 1\n"})
        changed = self.check()
        self.assertEqual(changed["removed"], ["TauCeti.Orphan"])
        self.assertIn("TauCeti.Renamed", changed["recomputed"])
        # The leftover old .olean is not a source module and cannot resurrect its result.
        self.assertNotIn("TauCeti.Orphan", changed["global_checks"]["inventory"])

    def test_global_compatible_duplicate_names_fail_on_warm_run(self):
        self.compile({"TauCeti.A": "module\npublic theorem collision : True := True.intro\n"})
        self.check()
        self.compile({"TauCeti.B": "module\npublic theorem collision : True := True.intro\n"})
        changed = self.check(status=1)
        self.assertEqual(changed["global_checks"]["ownership_status"], 1)
        self.assertIn("TauCeti.A", changed["reused"])

    def test_removed_source_still_imported_as_stale_artifact_is_rejected(self):
        self.compile({"TauCeti.Base": "module\npublic def value := 1\n",
                      "TauCeti.Importer": "module\npublic import TauCeti.Base\n"
                                          "public def importer := value\n"})
        self.check()
        (self.project / "TauCeti/Base.lean").unlink()
        with self.assertRaisesRegex(ValueError, "audited artifact has no source: TauCeti.Base"):
            self.check()

    def test_private_and_every_disallowed_axiom(self):
        fixtures = [
            "module\nprivate axiom hidden : False\nprivate theorem bad : False := hidden\n",
            "module\npublic axiom counterfeit : False\n",
            "module\npublic theorem bad : False := by sorry\n",
            "module\npublic theorem bad : False := by admit\n",
            "module\npublic opaque bad : False := by sorry\n",
            "module\npublic import Lean\npublic theorem bad : 1 = 1 := by native_decide\n",
            "module\npublic axiom Lean.ofReduceBool : False\n",
            "module\npublic axiom Lean.ofReduceNat : False\n",
            "module\npublic axiom Lean.trustCompiler : False\n",
            "module\npublic axiom badType : Prop\npublic axiom bad : badType\n",
        ]
        for source in fixtures:
            with self.subTest(source=source):
                self.compile({"TauCeti.Orphan": source})
                self.check(status=1)
                self.assertIn("TauCeti.Orphan", self.check(status=1)["reused"])

    def test_dependency_axiom_is_not_hidden_by_reuse(self):
        self.compile({"Dependency": "module\npublic axiom counterfeit : False\n",
                      "TauCeti.Orphan": "module\npublic import Dependency\n"
                                        "public theorem bad : False := counterfeit\n"})
        self.check(status=1)
        self.check(status=1)

    def test_flags_are_global_and_missing_private_parts_fail_closed(self):
        self.compile({"TauCeti.Orphan": "def unique := 1\n"})
        self.check(status=1)
        self.assertEqual(self.check(status=1)["global_checks"]["module_system_status"], 1)
        self.compile({"TauCeti.Orphan": "module\npublic def unique := 1\n"})
        (self.project / "TauCeti/Orphan.olean.private").unlink()
        with self.assertRaisesRegex(RuntimeError, "did not produce one snapshot"):
            self.check()

    def test_policy_pins_and_source_change_invalidate(self):
        self.compile({"TauCeti.Orphan": "module\npublic def unique := 1\n"})
        self.check()
        (self.project / "lake-manifest.json").write_text('{"version": "new-dependency-pin"}')
        self.assertEqual(self.check()["reused"], [])
        # Even stale equal artifact bytes cannot cause reuse after a source edit.
        with (self.project / "TauCeti/Orphan.lean").open("a") as stream:
            stream.write("-- source changed\n")
        self.assertEqual(self.check()["invalidated"], ["TauCeti.Orphan"])

    def test_candidate_initializers_and_result_files_are_ignored(self):
        self.compile({"TauCeti.Orphan": 'module\npublic import Lean\n'
                      'initialize IO.FS.writeFile "candidate-record.json" "tampered"\n'
                      'public theorem good : True := True.intro\n'})
        (self.project / "candidate-record.json").write_text("candidate assertion")
        self.check()
        self.assertEqual((self.project / "candidate-record.json").read_text(), "candidate assertion")
        self.assertEqual(len(self.check()["reused"]), 2)


class ShadowWorkflowTest(unittest.TestCase):
    def test_research_has_no_production_or_publication_dependencies(self):
        import yaml
        workflow = yaml.safe_load((ROOT / ".github/workflows/shadow-audits.yml").read_text())
        self.assertEqual(workflow["permissions"], {"contents": "read"})
        self.assertEqual(set(workflow["jobs"]), {"shadow"})
        self.assertNotIn("needs", workflow["jobs"]["shadow"])
        self.assertIn("workflow_dispatch", workflow.get("on", workflow.get(True)))
        text = (ROOT / ".github/workflows/shadow-audits.yml").read_text()
        for forbidden in ("secrets.", "actions/cache", "gh api", "lake cache stage", "publisher:"):
            self.assertNotIn(forbidden, text)
        self.assertIn("persist-credentials: false", text)
        self.assertIn("python3 scripts/test_shadow_audits.py", text)
        full_steps = [step for step in workflow["jobs"]["shadow"]["steps"]
                      if "main-only" in step.get("name", "") or
                      "full-library" in step.get("name", "") or
                      "publisher-produced" in step.get("name", "")]
        self.assertEqual(len(full_steps), 4)
        for step in full_steps:
            self.assertEqual(step["if"],
                             "${{ github.ref == 'refs/heads/main' && github.event_name != 'pull_request' }}")
        self.assertIn('lake env python3 scripts/shadow_audits.py . .', text)

    def test_production_consumers_do_not_enable_shadow_modes(self):
        for name in (".github/workflows/pr-build.yml", ".github/workflows/ci.yml",
                     "scripts/sandbox-build.sh", ".github/workflows/lint-full.yml"):
            text = (ROOT / name).read_text()
            for forbidden in ("--shadow-", "shadow_audits.py", "shadow-audit-report"):
                self.assertNotIn(forbidden, text)


if __name__ == "__main__":
    unittest.main()
