#!/usr/bin/env python3
"""Regression tests for ``scripts/check-meta-imports.py``.

Every case runs the real `lean --deps-json`, because the point of the check is
that the compiler's header parser decides and not a pattern over the text. The
fixtures are headers only: nothing is elaborated, built or imported.
"""

from __future__ import annotations

import importlib.util
import io
import os
import pathlib
import sys
import tempfile
import unittest

SCRIPT = pathlib.Path(__file__).with_name("check-meta-imports.py")
SPEC = importlib.util.spec_from_file_location("check_meta_imports", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
check = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = check
SPEC.loader.exec_module(check)

LEAN = os.environ.get("LEAN", "lean")

CLEAN = """\
module

public import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Ring
"""


class MetaImportCheckTests(unittest.TestCase):
    def run_check(self, sources, *, changed=None, root_module=None):
        """Lay out `sources` under a temporary checkout and return (status, output)."""
        with tempfile.TemporaryDirectory(prefix="meta-imports-") as temporary:
            root = pathlib.Path(temporary)
            for name, text in sources.items():
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text, encoding="utf-8")
            if root_module is not None:
                (root / "TauCeti.lean").write_text(root_module, encoding="utf-8")
            argv = ["--root", str(root), "--lean", LEAN]
            if changed is not None:
                listing = root / "changed.nul"
                listing.write_bytes(b"".join(entry.encode() + b"\0" for entry in changed))
                argv += ["--changed", str(listing)]
            stdout, stderr = sys.stdout, sys.stderr
            sys.stdout = sys.stderr = captured = io.StringIO()
            try:
                status = check.main(argv)
            finally:
                sys.stdout, sys.stderr = stdout, stderr
            return status, captured.getvalue()

    def test_a_clean_library_passes_and_ignores_the_implicit_init_imports(self):
        status, output = self.run_check({"TauCeti/Clean.lean": CLEAN})
        self.assertEqual(status, 0, output)
        self.assertIn("no `meta import` in 1 TauCeti source(s)", output)
        self.assertNotIn("Init", output)

    def test_a_meta_import_fails_and_names_the_module(self):
        status, output = self.run_check(
            {"TauCeti/Bad.lean": "module\n\nmeta import Lean.Elab.Tactic.Omega\n"})
        self.assertEqual(status, 1, output)
        self.assertIn("TauCeti/Bad.lean", output)
        self.assertIn("`meta import Lean.Elab.Tactic.Omega` is not allowed", output)

    def test_public_meta_import_fails(self):
        status, output = self.run_check(
            {"TauCeti/Bad.lean": "module\n\npublic meta import Lean\n"})
        self.assertEqual(status, 1, output)
        self.assertIn("`meta import Lean` is not allowed", output)

    def test_meta_import_all_fails(self):
        status, output = self.run_check(
            {"TauCeti/Bad.lean": "module\n\nmeta import all Lean\n"})
        self.assertEqual(status, 1, output)
        self.assertIn("`meta import Lean` is not allowed", output)

    def test_a_quoted_module_name_fails(self):
        status, output = self.run_check(
            {"TauCeti/Bad.lean": "module\n\nmeta import «Lean.Odd Name»\n"})
        self.assertEqual(status, 1, output)
        self.assertIn("is not allowed", output)

    def test_the_library_root_is_covered(self):
        status, output = self.run_check({}, root_module="module\n\nmeta import Lean\n")
        self.assertEqual(status, 1, output)
        self.assertIn("TauCeti.lean", output)

    def test_the_phrase_in_comments_and_docstrings_passes(self):
        # The whole reason for using Lean's parser: none of this is an import.
        sources = {
            "TauCeti/Comment.lean": "module\n\n-- meta import Lean\npublic import Init.Core\n",
            "TauCeti/Block.lean": "module\n\n/- meta import Lean /- nested -/ -/\n"
                                  "public import Init.Core\n",
            "TauCeti/Doc.lean": "module\n\npublic import Init.Core\n\n"
                                "/-!\n# Notes\n\nNever write `meta import Lean` here.\n-/\n",
        }
        status, output = self.run_check(sources)
        self.assertEqual(status, 0, output)
        self.assertIn("3 TauCeti source(s)", output)

    def test_a_meta_modifier_without_module_is_reported_as_a_header_error(self):
        # Lean rejects the modifier outright in a non-module file; that is still a failure,
        # and the message says so rather than claiming a clean header.
        status, output = self.run_check({"TauCeti/Bad.lean": "meta import Lean\n"})
        self.assertEqual(status, 1, output)
        self.assertIn("header does not parse", output)

    def test_an_unparseable_header_fails_rather_than_passing_quietly(self):
        status, output = self.run_check({"TauCeti/Bad.lean": "module\n\nimport\n"})
        self.assertEqual(status, 1, output)
        self.assertIn("header does not parse", output)

    def test_the_changed_list_bounds_the_scope(self):
        sources = {"TauCeti/Bad.lean": "module\n\nmeta import Lean\n",
                   "TauCeti/Clean.lean": CLEAN}
        status, output = self.run_check(sources, changed=["TauCeti/Clean.lean"])
        self.assertEqual(status, 0, output)
        self.assertIn("1 TauCeti source(s) (the changed files)", output)

        status, output = self.run_check(sources, changed=["TauCeti/Bad.lean"])
        self.assertEqual(status, 1, output)
        self.assertIn("TauCeti/Bad.lean", output)

    def test_the_changed_list_ignores_what_is_not_a_library_source(self):
        sources = {"TauCeti/Clean.lean": CLEAN, "scripts/Axioms.lean": "import Lean\n"}
        status, output = self.run_check(
            sources, changed=["scripts/Axioms.lean", "README.md", "TauCeti/Clean.lean"])
        self.assertEqual(status, 0, output)
        self.assertIn("1 TauCeti source(s)", output)

    def test_an_empty_changed_list_checks_nothing(self):
        status, output = self.run_check({"TauCeti/Bad.lean": "module\n\nmeta import Lean\n"},
                                        changed=["README.md"])
        self.assertEqual(status, 0, output)
        self.assertIn("no TauCeti sources in scope", output)

    def test_a_listed_but_absent_path_fails_closed(self):
        status, output = self.run_check({"TauCeti/Clean.lean": CLEAN},
                                        changed=["TauCeti/Gone.lean"])
        self.assertEqual(status, 1, output)
        self.assertIn("listed but absent", output)

    def test_a_changed_path_escaping_the_checkout_fails_closed(self):
        status, output = self.run_check({"TauCeti/Clean.lean": CLEAN},
                                        changed=["TauCeti/../../elsewhere/Evil.lean"])
        self.assertEqual(status, 1, output)
        self.assertIn("escapes the checkout", output)

    def test_the_real_library_has_no_meta_imports(self):
        # The invariant itself, over the whole checkout. The PR check is scoped to a
        # change's files, so this is where a regression already on main would surface.
        root = SCRIPT.parent.parent
        stdout, stderr = sys.stdout, sys.stderr
        sys.stdout = sys.stderr = captured = io.StringIO()
        try:
            status = check.main(["--root", str(root), "--lean", LEAN])
        finally:
            sys.stdout, sys.stderr = stdout, stderr
        self.assertEqual(status, 0, captured.getvalue())


if __name__ == "__main__":
    unittest.main()
