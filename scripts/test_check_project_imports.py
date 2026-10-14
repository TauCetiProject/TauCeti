#!/usr/bin/env python3
"""Run the real pinned Lean parser; fixtures need no package or compiled outputs."""
from __future__ import annotations

import contextlib
import importlib.util
import io
import os
import subprocess
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location(
    "check_project_imports", Path(__file__).with_name("check-project-imports.py"))
check = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(check)
LEAN = os.environ.get("LEAN", "lean")


class ProjectImportsTests(unittest.TestCase):
    def run_check(self, sources, *, raw=None, symlinks=None):
        with tempfile.TemporaryDirectory(prefix="project-imports-") as temporary:
            root = Path(temporary)
            (root / "TauCeti").mkdir()
            (root / "TauCeti.lean").write_text("module\n")
            for name, source in sources.items():
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(source)
            for name, source in (raw or {}).items():
                (root / name).write_bytes(source)
            for name, target in (symlinks or {}).items():
                (root / name).symlink_to(target)
            with contextlib.redirect_stdout(io.StringIO()) as output:
                status = check.main(["--root", str(root), "--lean", LEAN])
            return status, output.getvalue()

    def test_historical_missing_import_names(self):
        cases = [
            ("TauCeti/AlgebraicTopology/DGLocalSystem/PathBimodule.lean",
             "TauCeti.Topology.PathSpace.Moore.Between"),
            ("TauCeti/Algebra/Category/GradedModuleCat/CartanMap/Duality.lean",
             "TauCeti.Algebra.Category.GradedModuleCat.CartanMap.ExtEuler"),
            ("TauCeti/AlgebraicGeometry/ModularCurve/LegendreLine.lean",
             "TauCeti.AlgebraicGeometry.EllipticCurve.FreyCurve"),
        ]
        sources = {file: f"module\npublic import {module}\n" for file, module in cases}
        status, output = self.run_check(sources)
        self.assertEqual(status, 1, output)
        for file, module in cases:
            self.assertIn(file, output)
            self.assertIn(f"missing project import {module}", output)
            self.assertIn(module.replace(".", "/") + ".lean", output)

    def test_same_candidate_root_orphans_and_external_packages(self):
        # No root imports: both importer and newly supplied dependency are orphans.
        status, output = self.run_check({
            "TauCeti/Importer.lean": "module\npublic import TauCeti.New\n"
                                     "import TauCeti\nimport Mathlib.Tactic\nimport Lean\n",
            "TauCeti/New.lean": "module\n",
        })
        self.assertEqual(status, 0, output)
        self.assertIn("3 exact-candidate source(s)", output)

    def test_unchanged_importer_loses_dependency(self):
        status, output = self.run_check({
            "TauCeti/Unchanged.lean": "module\nimport TauCeti.Deleted\n"})
        self.assertEqual(status, 1, output)
        self.assertIn("missing project import TauCeti.Deleted", output)

    def test_root_importer_is_checked(self):
        status, output = self.run_check({"TauCeti.lean": "module\nimport TauCeti.Gone\n"})
        self.assertEqual(status, 1, output)
        self.assertIn("TauCeti.lean:", output)

    def test_pinned_lean_public_and_private_import_forms(self):
        # Plain `import` and `import all` are the pinned module system's private imports.
        # There is no `private import` keyword form at this pin (tested below).
        status, output = self.run_check({
            "TauCeti/Forms.lean": "module\nprelude\npublic import TauCeti.Dep\n"
                                  "import TauCeti.Dep\nimport all TauCeti.Dep\n",
            "TauCeti/Dep.lean": "module\n",
        })
        self.assertEqual(status, 0, output)

    def test_comments_multiline_and_literals(self):
        status, output = self.run_check({
            "TauCeti/Comments.lean": """module
/- import TauCeti.Fake /- import TauCeti.Nested -/ -/
-- import TauCeti.Fake
public /- nested /- hi -/ -/
import
/- hi -/ TauCeti.Dep
/-! import TauCeti.Fake -/
def text := "import TauCeti.Fake"
def raw := r#"import TauCeti.Fake"#
def quotedName := `import
def projection (x : Nat × Nat) := x.1
@[stacks 0B52 "import TauCeti.Fake"]
theorem example' : True := trivial
""",
            "TauCeti/Dep.lean": "module\n",
        })
        self.assertEqual(status, 0, output)

    def test_quoted_semantic_names(self):
        status, output = self.run_check({
            "TauCeti/Quoted.lean": "module\nimport «TauCeti».«Has.Dot»\n"
                                   "import TauCeti.«Two Words»\nimport «TauCeti.External»\n",
            "TauCeti/Has.Dot.lean": "module\n",
            "TauCeti/Two Words.lean": "module\n",
        })
        self.assertEqual(status, 0, output)
        status, output = self.run_check({
            "TauCeti/Quoted.lean": "module\nimport «TauCeti».«Gone.Dot»\n"})
        self.assertEqual(status, 1, output)
        self.assertIn("TauCeti/Gone.Dot.lean", output)

    def test_malformed_and_ambiguous_inputs_fail_closed(self):
        headers = [
            "\ufeffmodule\nimport TauCeti.Gone\n",
            "import TauCeti.Gone\n",
            "module\nimport\n",
            "module\nimport TauCeti.Gone.\n",
            "module\nimport /- unterminated TauCeti.Gone\n",
            "module\nimport TauCeti.«unterminated\n",
            "module\npublic import all TauCeti.Gone\n",
            "module\nimport allTauCeti.Gone\n",
            "module\nimportTauCeti.Gone\n",
            "module\npublic importTauCeti.Gone\n",
        ]
        for header in headers:
            with self.subTest(header=header):
                status, output = self.run_check({"TauCeti/Bad.lean": header})
                self.assertEqual(status, 1, output)
                self.assertIn("TauCeti/Bad.lean", output)
                if "importTauCeti.Gone" in header or "allTauCeti.Gone" in header:
                    self.assertIn("missing project import TauCeti.Gone:", output)

    def test_parser_disagreement_fails_even_when_dependency_exists(self):
        status, output = self.run_check({
            "TauCeti/Bad.lean": "module\nimport allTauCeti.Dep\n",
            "TauCeti/Dep.lean": "module\n",
        })
        self.assertEqual(status, 1, output)
        self.assertIn("Lean and Lake disagree", output)

    def test_body_syntax_is_left_to_lake(self):
        # A core-only command parser cannot understand these valid Mathlib forms. The
        # preflight must read imports without trying to parse/elaborate the body.
        status, output = self.run_check({
            "TauCeti/Lemma.lean": "module\nimport Mathlib\nlemma one : 1 = 1 := by norm_num\n",
            "TauCeti/Variable.lean": "module\nimport Mathlib\nvariable {R : Type*}\n",
        })
        self.assertEqual(status, 0, output)

    def test_bad_utf8_and_symlinks_fail_closed(self):
        status, output = self.run_check({}, raw={"TauCeti/Bad.lean": b"module\n\xff"})
        self.assertEqual(status, 1, output)
        status, output = self.run_check({}, symlinks={"TauCeti/Linked.lean": "../TauCeti.lean"})
        self.assertEqual(status, 1, output)
        self.assertIn("symlink", output)

    def test_missing_root_and_unreadable_inventory_fail_closed(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(ValueError):
                check.inventory(Path(directory))
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "TauCeti").mkdir()
            (root / "TauCeti.lean").write_text("module\n")
            with patch.object(check.os, "walk", side_effect=PermissionError("unreadable")):
                with self.assertRaises(PermissionError):
                    check.inventory(root)

    def test_incomplete_or_malformed_driver_reports_fail_closed(self):
        for stdout in ['{}', '{"checked": 0, "problems": []}',
                       '{"checked": 1, "problems": null}',
                       '{"checked": 1, "problems": [{"file": "other", "message": "bad"}]}',
                       'not JSON']:
            with self.subTest(stdout=stdout):
                result = subprocess.CompletedProcess([], 0, stdout, "")
                with patch.object(check.subprocess, "run", return_value=result):
                    status, output = self.run_check({})
                self.assertEqual(status, 1, output)

    def test_workflow_runs_trusted_full_preflight_before_build_setup(self):
        workflows = Path(__file__).resolve().parent.parent / ".github/workflows"
        text = (workflows / "pr-build.yml").read_text()
        start = text.index("      - name: Preflight exact-candidate project imports")
        end = text.index("      - name:", start + 15)
        step = text[start:end]
        self.assertIn("python3 gate/scripts/check-project-imports.py --root pr", step)
        self.assertIn('$(cd pr && elan which lean)', step)
        self.assertNotIn("--changed", step)
        self.assertIn("steps.project_imports.outcome", text)
        self.assertIn("project import preflight failed", text)
        self.assertLess(start, text.index("      - name: Fetch Mathlib"))
        self.assertLess(start, text.index("      - name: Build exact candidate"))
        ci = (workflows / "ci.yml").read_text()
        self.assertLess(ci.index("run: python3 scripts/check-project-imports.py"),
                        ci.index("      - name: Build\n"))


if __name__ == "__main__":
    unittest.main()
