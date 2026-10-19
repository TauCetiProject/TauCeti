#!/usr/bin/env python3
"""Regression coverage for the cheap library source policy."""

from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from check_source_options import forbidden_tokens


def forbidden_lines(source):
    """Keep line-oriented fixtures concise; the CLI also reports the offending spellings."""
    return list(forbidden_tokens(source))


class SourceOptionsTests(unittest.TestCase):
    def test_rejects_metaprogramming_declarations_and_execution(self):
        sources = [
            'public meta def tool := 1', 'private meta def tool := 1', 'meta section',
            'unsafe def tool := 1', 'private unsafe def tool := 1',
            'elab "tool" : tactic => pure ()', 'elab_rules : command | _ => pure ()',
            'initialize tool : IO.Ref Nat ← IO.mkRef 0',
            'builtin_initialize tool : IO.Ref Nat ← IO.mkRef 0',
            'run_cmd pure ()', 'run_elab pure ()',
            'example : True := by run_tac pure (); trivial',
            'run_meta pure ()', 'def x : Nat := by_elab pure (mkNatLit 0)',
            '#eval (IO.FS.writeFile "x" "" : IO Unit)', '#eval! (pure () : IO Unit)',
        ]
        for source in sources:
            with self.subTest(source=source):
                self.assertEqual(forbidden_lines(source + '\n'), [1])

    def test_local_macros_allow_arguments_and_multiline_modifiers(self):
        self.assertEqual(forbidden_lines(
            'local macro "finish" : tactic => `(tactic| (simp; ring))\n'
            'local /- nested /- comment -/ -/\n'
            'macro "at_hyp" h:ident : tactic => `(tactic| simp at $h:ident)\n'
            'local\nmacro_rules | `(finish) => `(tactic| trivial)\n'
            'local macro_rules | `($a ^ $n:num) => `(HPow.hPow $a ($n : Nat))\n'), [])

    def test_rejects_nonlocal_macros_and_local_bodies_with_forbidden_tokens(self):
        for source in [
            'macro "finish" : tactic => `(tactic| trivial)',
            'scoped macro "finish" : tactic => `(tactic| trivial)',
            'macro_rules | `(finish) => `(tactic| trivial)',
            'scoped macro_rules | `(finish) => `(tactic| trivial)',
            'local macro "finish" : tactic => set_option hygiene false in `(tactic| trivial)',
        ]:
            with self.subTest(source=source):
                self.assertEqual(forbidden_lines(source), [1])
        self.assertEqual(forbidden_lines(
            'local macro "finish" : tactic => `(tactic| trivial)\n'
            'macro "global_finish" : tactic => `(tactic| trivial)\n'), [2])
        # This scan deliberately does not validate otherwise permitted local macro bodies.
        self.assertEqual(forbidden_lines(
            'local macro "finish" : tactic => do pure (← `(tactic| trivial))\n'), [])

    def test_rejects_manual_registrations_in_both_attribute_forms(self):
        for attribute in [
            'command_elab', 'term_elab', 'doElem_elab', 'tactic', 'grind_tactic',
            'try_tactic', 'macro', 'app_unexpander', 'delab', 'inductive_elab',
            'init',
        ]:
            for prefix in ['', 'builtin_']:
                name = prefix + attribute
                for source in [
                    f'@[{name} foo] def tool := 1\n',
                    f'@[simp, {name} foo] def tool := 1\n',
                    f'attribute [local {name} foo] tool\n',
                    f'attribute [scoped {name} foo] tool\n',
                ]:
                    with self.subTest(source=source):
                        self.assertEqual(forbidden_lines(source), [1])
        self.assertEqual(forbidden_lines(
            '@[simp,\n  tactic finish]\ndef tool := 1\n'), [2])
        self.assertEqual(forbidden_lines(
            'attribute /- gap -/\n[local /- ] -/ tactic finish] tool\n'), [2])
        self.assertEqual(forbidden_lines(
            '@[simp, /- ] -/ tactic finish] def tool := 1\n'), [1])

    def test_policy_comments_and_longer_names_are_allowed(self):
        self.assertEqual(forbidden_lines(
            '/- meta unsafe /- elab -/ initialize macro tactic -/\n'
            '-- @[tactic finish] run_cmd run_elab\n'
            'def metadata := 1\ndef unsafeValue := 2\n'
            "def αmeta := 1\ndef metaα := 1\ndef macro' := 1\n"
            'initialize_simps_projections Foo (toFun → apply)\n'
            '@[simp] theorem foo : True := by trivial\n'
            'attribute [local simp] foo\n'
            'def tactic := 1\n'), [])

    def test_policy_names_in_strings_quotes_and_interpolation_are_conservative(self):
        for source in [
            'def text := "meta"', 'def kind := ``Lean.Parser.Command.elab',
            '-- "unsafe" is conservatively rejected',
            'def text := s!"{run_cmd pure ()}"',
            'local macro "finish" : tactic => `(command| initialize pure ())',
        ]:
            with self.subTest(source=source):
                self.assertEqual(forbidden_lines(source), [1])
        self.assertEqual(forbidden_lines(
            'def text := s!"{\'"\'} /- "\n'
            'meta def tool := 1\n-- -/\n'), [2])

    def test_comment_and_literal_local_cannot_authorize_a_global_macro(self):
        for source in [
            '-- Only the "finish" proofs below need this, so keep it local\n'
            'macro "finish" : tactic => `(tactic| trivial)\n',
            '-- "quoted" local\nmacro_rules | `(finish) => `(tactic| trivial)\n',
        ]:
            with self.subTest(source=source):
                self.assertEqual(forbidden_lines(source), [2])
        self.assertEqual(forbidden_lines('def text := "local macro"\n'), [1])

    def test_character_literals_cannot_hide_adjacent_forbidden_code_from_fast_path(self):
        for source in ["'a'meta def tool := 1", "'a'#eval (pure () : IO Unit)"]:
            with self.subTest(source=source):
                self.assertEqual(forbidden_lines(source), [1])

    def test_candidate_filter_agrees_with_unconditional_scan(self):
        # Masking comments/characters can expose boundaries absent from the raw source.
        sources = [
            "'a'meta def tool := 1", "'a'#eval! (pure () : IO Unit)",
            "def macro' := 1", "def αmeta := 1", 'initialize_simps_projections Foo',
            'attribute /- gap -/ [builtin_init act] r',
            '-- "quoted" local\nmacro "finish" : tactic => `(tactic| trivial)',
            'local /- gap -/\nmacro "finish" : tactic => `(tactic| trivial)',
        ]
        for source in sources:
            with self.subTest(source=source):
                actual = forbidden_tokens(source)
                with patch('check_source_options.has_candidate', return_value=True):
                    self.assertEqual(actual, forbidden_tokens(source))

    def test_catches_inline_indented_and_split_options(self):
        self.assertEqual(forbidden_lines(
            'local macro "solve" : tactic => set_option hygiene false in\n'
            '  `(tactic| simp)\n'
            '  set_option maxHeartbeats 0 in\n'
            'set_option\n'
            '  linter.unusedVariables false in\n'), [1, 3, 4])

    def test_allows_documentation_and_identifier_substrings(self):
        self.assertEqual(forbidden_lines(
            '-- set_option hygiene false\n'
            '/- set_option /- nested comment -/ maxHeartbeats 0 -/\n'
            'def my_set_option := 1\n'), [])

    def test_conservatively_rejects_command_names_in_literal_strings(self):
        self.assertEqual(forbidden_lines('def text := "set_option hygiene false"\n'), [1])
        self.assertEqual(forbidden_lines(
            'def escaped := "quoted \\" set_option hygiene false"\n'), [1])

    def test_nested_comments_preserve_diagnostic_lines(self):
        self.assertEqual(forbidden_lines(
            '/- documentation\n'
            '/- set_option hygiene false -/\n'
            '-/\n'
            'example : True := by\n'
            '  set_option /- explanation -/ hygiene false in trivial\n'), [5])

    def test_raw_strings_cannot_hide_following_options(self):
        self.assertEqual(forbidden_lines(
            'def quoted := r#"""#\n'
            'set_option hygiene false in\n'
            'example : True := by trivial\n'), [2])
        self.assertEqual(forbidden_lines(
            'def text := r###"set_option "# /- not a comment\n'
            'set_option hygiene false "###\n'
            '  set_option maxHeartbeats 0 in\n'), [1, 2, 3])

    def test_quoted_identifiers_and_characters_cannot_hide_following_options(self):
        self.assertEqual(forbidden_lines(
            'def «"» := 1\n'
            'def «ordinary_name» := 2\n'
            'def quote := \'"\'\n'
            'def primed\' := 3\n'
            'set_option hygiene false in\n'), [5])

    def test_identifier_boundaries_match_lean_names(self):
        self.assertEqual(forbidden_lines(
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
                self.assertEqual(forbidden_lines(source), [2])
        self.assertEqual(forbidden_lines(
            'def text := s!"{set_option maxRecDepth 4000 in (1 : Nat)}"\n'), [1])
        self.assertEqual(forbidden_lines(
            'def text := s!"{({value := set_option maxRecDepth 4000 in 1} : Foo).value}"\n'),
            [1])
        self.assertEqual(forbidden_lines(
            'def text := s!"literal set_option {"set_option hygiene false"}"\n'), [1])
        self.assertEqual(forbidden_lines(
            'def text := s! /- "comment" -/\n'
            '  "{set_option maxRecDepth 4000 in (1 : Nat)}"\n'), [2])
        self.assertEqual(forbidden_lines(
            'example : True := by\n'
            '  dbg_trace "{set_option maxRecDepth 4000 in (1 : Nat)}"\n'
            '  trivial\n'), [2])
        self.assertEqual(forbidden_lines(
            'def text := identity! "{set_option hygiene false}"\n'), [1])
        self.assertEqual(forbidden_lines(
            'example : True := by\n'
            '  dbg_trace "{"\n'
            '  set_option maxHeartbeats 0 in\n'
            '  dbg_trace "}"\n'
            '  trivial\n'), [3])
        self.assertEqual(forbidden_lines(
            'def greet : IO Unit := println! "{"\\\""}"\n'
            'set_option maxHeartbeats 0 in\n'
            'theorem t : True := trivial\n'), [2])

    def test_escaped_character_cannot_hide_following_commands(self):
        self.assertEqual(forbidden_lines(
            'def chars : List Char := [\'\\\'\',\'"\']\n'
            'set_option hygiene false in\n'), [2])

    def test_interpolation_cannot_mask_code_as_comments_or_quoted_identifiers(self):
        for marker, closing in [('/-', '-/'), ('«', '»')]:
            source = ('def text := s!"{\'"\'} ' + marker + ' "\n'
                      'set_option maxHeartbeats 0 in\n'
                      'theorem t : True := trivial\n-- ' + closing + '\n')
            with self.subTest(marker=marker):
                self.assertEqual(forbidden_lines(source), [2])
        self.assertEqual(forbidden_lines(
            'def text := s!"{\'"\'} -- " ++ (set_option maxRecDepth 4000 in "")\n'), [1])

    def test_qualified_raw_prefix_is_an_identifier_before_an_ordinary_string(self):
        self.assertEqual(forbidden_lines(
            'def text := Foo.r"\\\" /- "\n'
            'set_option maxHeartbeats 0 in\n'
            'theorem t : True := trivial\n-- -/\n'), [2])

    def test_conservatively_rejects_syntax_kind_names_and_quote_bearing_comments(self):
        self.assertEqual(forbidden_lines(
            'def kind := ``Lean.Parser.Tactic.«set_option»\n'
            'def other := `Lean.Parser.Tactic.set_option\n'
            '-- "set_option" is conservatively rejected\n'
            '/- "quoted" set_option -/\n'), [1, 2, 3, 4])

    def test_diagnostic_lines_count_only_newlines(self):
        self.assertEqual(forbidden_lines('def text := "\v\f"\nset_option hygiene false\n'), [2])

    def test_rejects_heartbeat_helpers_that_disable_limits(self):
        self.assertEqual(forbidden_lines(
            'guard_min_heartbeats 0 in\n'
            'theorem heavy : True := by trivial\n'
            '#count_heartbeats in\n'
            'theorem other : True := by trivial\n'
            '#count_heartbeats! in\n'
            'theorem bang : True := by trivial\n'), [1, 3, 5])
        self.assertEqual(forbidden_lines(
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
            self.assertIn("set_option", result.stdout)
            self.assertIn("comments containing double quotes", result.stdout)
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
