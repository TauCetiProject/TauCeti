#!/usr/bin/env python3
"""Regression coverage for option overrides missed by the former anchored grep."""

from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from check_source_options import option_lines


class SourceOptionsTests(unittest.TestCase):
    def test_catches_inline_indented_and_split_options(self):
        self.assertEqual(option_lines(
            'local macro "solve" : tactic => set_option hygiene false in\n'
            '  `(tactic| simp)\n'
            '  set_option maxHeartbeats 0 in\n'
            'set_option\n'
            '  linter.unusedVariables false in\n'), [1, 3, 4])

    def test_allows_documentation_strings_and_identifier_substrings(self):
        self.assertEqual(option_lines(
            '-- set_option hygiene false\n'
            '/- set_option /- nested comment -/ maxHeartbeats 0 -/\n'
            'def text := "set_option hygiene false"\n'
            'def escaped := "quoted \\" set_option hygiene false"\n'
            'def my_set_option := 1\n'), [])

    def test_nested_comments_preserve_diagnostic_lines(self):
        self.assertEqual(option_lines(
            '/- documentation\n'
            '/- set_option hygiene false -/\n'
            '-/\n'
            'example : True := by\n'
            '  set_option /- explanation -/ hygiene false in trivial\n'), [5])

    def test_cli_checks_nested_files_and_root_and_fails_on_missing_input(self):
        checker = Path(__file__).with_name("check_source_options.py")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            library = root / "TauCeti"
            (library / "Nested").mkdir(parents=True)
            (library / "Nested" / "Bad.lean").write_text(
                'example : True := by\n  set_option hygiene false in trivial\n')
            aggregator = root / "TauCeti.lean"
            aggregator.write_text('set_option maxHeartbeats 0\n')
            result = subprocess.run([sys.executable, str(checker), str(library),
                                     str(aggregator)], capture_output=True, text=True)
            self.assertEqual(result.returncode, 1)
            self.assertIn("Bad.lean:2:", result.stdout)
            self.assertIn("TauCeti.lean:1:", result.stdout)
            (library / "Nested" / "Bad.lean").write_text('-- set_option hygiene false\n')
            aggregator.write_text('module\n')
            result = subprocess.run([sys.executable, str(checker), str(library),
                                     str(aggregator)], capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            result = subprocess.run([sys.executable, str(checker), str(root / "missing")],
                                    capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)


if __name__ == "__main__":
    unittest.main()
