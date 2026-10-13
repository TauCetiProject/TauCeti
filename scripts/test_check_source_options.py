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

    def test_allows_documentation_and_identifier_substrings(self):
        self.assertEqual(option_lines(
            '-- set_option hygiene false\n'
            '/- set_option /- nested comment -/ maxHeartbeats 0 -/\n'
            'def my_set_option := 1\n'), [])

    def test_conservatively_rejects_command_names_in_literal_strings(self):
        self.assertEqual(option_lines('def text := "set_option hygiene false"\n'), [1])
        self.assertEqual(option_lines(
            'def escaped := "quoted \\" set_option hygiene false"\n'), [1])

    def test_nested_comments_preserve_diagnostic_lines(self):
        self.assertEqual(option_lines(
            '/- documentation\n'
            '/- set_option hygiene false -/\n'
            '-/\n'
            'example : True := by\n'
            '  set_option /- explanation -/ hygiene false in trivial\n'), [5])

    def test_raw_strings_cannot_hide_following_options(self):
        self.assertEqual(option_lines(
            'def quoted := r#"""#\n'
            'set_option hygiene false in\n'
            'example : True := by trivial\n'), [2])
        self.assertEqual(option_lines(
            'def text := r###"set_option "# /- not a comment\n'
            'set_option hygiene false "###\n'
            '  set_option maxHeartbeats 0 in\n'), [1, 2, 3])

    def test_quoted_identifiers_and_characters_cannot_hide_following_options(self):
        self.assertEqual(option_lines(
            'def «"» := 1\n'
            'def «ordinary_name» := 2\n'
            'def quote := \'"\'\n'
            'def primed\' := 3\n'
            'set_option hygiene false in\n'), [5])

    def test_identifier_boundaries_match_lean_names(self):
        self.assertEqual(option_lines(
            "def set_option' := 1\n"
            'def Foo.ordinary_name := 2\n'
            'def set_option? := 3\n'
            'def set_option! := 4\n'
            'set_option hygiene false in\n'), [5])

    def test_interpolation_cannot_hide_option_names_or_following_commands(self):
        sources = [
            'def text := s!"{\'"\'}"\nset_option hygiene false in\n',
            'def text := s!"{"\\\""}"\nset_option hygiene false in\n',
            'def text := s!"{s!"{1}"}"\nset_option hygiene false in\n',
        ]
        for source in sources:
            with self.subTest(source=source):
                self.assertEqual(option_lines(source), [2])
        self.assertEqual(option_lines(
            'def text := s!"{set_option maxRecDepth 4000 in (1 : Nat)}"\n'), [1])
        self.assertEqual(option_lines(
            'def text := s!"{({value := set_option maxRecDepth 4000 in 1} : Foo).value}"\n'),
            [1])
        self.assertEqual(option_lines(
            'def text := s!"literal set_option {"set_option hygiene false"}"\n'), [1])
        self.assertEqual(option_lines(
            'def text := s! /- "comment" -/\n'
            '  "{set_option maxRecDepth 4000 in (1 : Nat)}"\n'), [2])
        self.assertEqual(option_lines(
            'example : True := by\n'
            '  dbg_trace "{set_option maxRecDepth 4000 in (1 : Nat)}"\n'
            '  trivial\n'), [2])
        self.assertEqual(option_lines(
            'def text := identity! "{set_option hygiene false}"\n'), [1])
        self.assertEqual(option_lines(
            'example : True := by\n'
            '  dbg_trace "{"\n'
            '  set_option maxHeartbeats 0 in\n'
            '  dbg_trace "}"\n'
            '  trivial\n'), [3])
        self.assertEqual(option_lines(
            'def greet : IO Unit := println! "{"\\\""}"\n'
            'set_option maxHeartbeats 0 in\n'
            'theorem t : True := trivial\n'), [2])

    def test_escaped_character_cannot_hide_following_commands(self):
        self.assertEqual(option_lines(
            'def chars : List Char := [\'\\\'\',\'"\']\n'
            'set_option hygiene false in\n'), [2])

    def test_interpolation_cannot_mask_code_as_comments_or_quoted_identifiers(self):
        for marker, closing in [('/-', '-/'), ('«', '»')]:
            source = ('def text := s!"{\'"\'} ' + marker + ' "\n'
                      'set_option maxHeartbeats 0 in\n'
                      'theorem t : True := trivial\n-- ' + closing + '\n')
            with self.subTest(marker=marker):
                self.assertEqual(option_lines(source), [2])
        self.assertEqual(option_lines(
            'def text := s!"{\'"\'} -- " ++ (set_option maxRecDepth 4000 in "")\n'), [1])

    def test_qualified_raw_prefix_is_an_identifier_before_an_ordinary_string(self):
        self.assertEqual(option_lines(
            'def text := Foo.r"\\\" /- "\n'
            'set_option maxHeartbeats 0 in\n'
            'theorem t : True := trivial\n-- -/\n'), [2])

    def test_conservatively_rejects_syntax_kind_names_and_quote_bearing_comments(self):
        self.assertEqual(option_lines(
            'def kind := ``Lean.Parser.Tactic.«set_option»\n'
            'def other := `Lean.Parser.Tactic.set_option\n'
            '-- "set_option" is conservatively rejected\n'
            '/- "quoted" set_option -/\n'), [1, 2, 3, 4])

    def test_diagnostic_lines_count_only_newlines(self):
        self.assertEqual(option_lines('def text := "\v\f"\nset_option hygiene false\n'), [2])

    def test_rejects_heartbeat_helpers_that_disable_limits(self):
        self.assertEqual(option_lines(
            'guard_min_heartbeats 0 in\n'
            'theorem heavy : True := by trivial\n'
            '#count_heartbeats in\n'
            'theorem other : True := by trivial\n'
            '#count_heartbeats! in\n'
            'theorem bang : True := by trivial\n'), [1, 3, 5])
        self.assertEqual(option_lines(
            '-- guard_min_heartbeats 0 in\n'
            'def message := "count_heartbeats"\n'), [2])

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
