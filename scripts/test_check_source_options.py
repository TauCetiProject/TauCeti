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
        self.assertEqual(forbidden_lines(
            '@[inherit_doc] local macro "finish" : tactic => `(tactic| trivial)\n'
            '@[inherit_doc]local macro "finish_adjacent" : tactic => `(tactic| trivial)\n'
            '/- A comment boundary. -/local macro "after_comment" : tactic => `(tactic| trivial)\n'
            '/-- A local proof abbreviation. -/\n'
            'local macro "finish_again" : tactic => `(tactic| trivial)\n'
            'namespace Foo local macro "inline_finish" : tactic => `(tactic| trivial)\n'
            'end Foo\n'), [])

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

    def test_attribute_openers_can_touch_identifiers_and_all_entries_are_checked(self):
        for source in [
            'theorem t : True := trivial@[command_elab finishCmd] def elabFinish := 1',
            'theorem t : True := trivial@[init act] opaque r : IO.Ref Nat',
            '@[inherit_doc my_init, init act] opaque r : IO.Ref Nat',
            '@[inherit_doc Foo.my_tactic, tactic finish] def evalFinish := 1',
        ]:
            with self.subTest(source=source):
                self.assertEqual(forbidden_lines(source), [1])
        self.assertEqual(forbidden_tokens('@[init act, command_elab finishCmd] def r := 1'),
                         {1: {'init', 'command_elab'}})
        self.assertEqual(forbidden_lines('@[inherit_doc my_init] def foo := 1'), [])

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

    def test_interpolation_cannot_make_line_comment_local_authorize_a_global_macro(self):
        source = ('def t : String := s!"{\'"\'}" -- " local\n'
                  'macro "finish" : tactic => `(tactic| trivial)\n')
        self.assertEqual(forbidden_lines(source), [2])
        rules = 'local syntax "finish" : tactic\n' + source.replace(
            'macro "finish" : tactic =>', 'macro_rules | `(tactic| finish) =>')
        self.assertEqual(forbidden_lines(rules), [3])

    def test_name_literal_and_qualified_name_cannot_authorize_a_global_macro(self):
        self.assertEqual(forbidden_lines(
            'def tag := `local\nmacro "finish" : tactic => `(tactic| trivial)\n'), [2])
        self.assertEqual(forbidden_lines(
            'def Foo.«local» := 0\nexample := Foo.local\n'
            'macro "finish" : tactic => `(tactic| trivial)\n'), [3])
        self.assertEqual(forbidden_lines(
            'def tag := ``local\nmacro_rules | `(finish) => `(tactic| trivial)\n'), [2])

    def test_symbol_commands_do_not_require_identifier_boundaries(self):
        for symbol in ['#eval', '#eval!', '#count_heartbeats', '#count_heartbeats!']:
            for source in [symbol + 'IO.FS.writeFile "x" ""',
                           'theorem t : True := trivial' + symbol + ' (pure () : IO Unit)',
                           symbol + "'a' |> fun _ => (pure () : IO Unit)"]:
                with self.subTest(source=source):
                    self.assertEqual(forbidden_lines(source), [1])
        self.assertEqual(forbidden_tokens('#count_heartbeatsin\nexample : True := by trivial'),
                         {1: {'#count_heartbeats'}})

    def test_lean_identifier_ranges_and_postfix_symbol_boundaries(self):
        # Letter-like symbols are identifier characters in Lean, unlike Python's word class.
        for letter in ['℘', '℮', '™', '⅋', 'α', 'é', '𝒜']:
            with self.subTest(letter=letter):
                self.assertEqual(forbidden_lines(f'def {letter}meta := 1'), [])
                self.assertEqual(forbidden_lines(
                    f'example ({letter}local : Nat) : Nat := {letter}local\n'
                    'macro "finish" : tactic => `(tactic| trivial)'), [2])
        # These postfix symbols are letters to Python but delimit identifiers in Lean.
        for symbol in ['ᶜ', 'ˣ', 'ᵒᵖ', 'ᵀ', 'ᵐᵒᵖ', 'λ', 'Π', 'Σ']:
            for command in ['run_cmd pure ()', 'set_option maxHeartbeats 0 in',
                            'macro "finish" : tactic => `(tactic| trivial)',
                            'attribute [tactic finish] tool']:
                with self.subTest(symbol=symbol, command=command):
                    self.assertEqual(forbidden_lines('example := s' + symbol + command), [1])
        # Rest-only characters can be notation tokens when not attached to an identifier.
        for symbol in ['!', '?', '₁', 'ᵢ']:
            self.assertEqual(forbidden_lines('example := (1)' + symbol + 'run_cmd pure ()'), [1])
        self.assertEqual(forbidden_lines('example := !foo_run_cmd\nexample := ?foo1macro'), [])

    def test_numeric_literals_can_touch_keywords_without_hiding_them(self):
        for numeral in ['1', '0x1', '0b1', '1e2', '1.0']:
            for command in ['run_cmd pure ()', 'set_option maxHeartbeats 0 in',
                            'macro "finish" : tactic => `(tactic| trivial)',
                            'attribute [init act] r']:
                with self.subTest(numeral=numeral, command=command):
                    self.assertEqual(forbidden_lines('example := ' + numeral + command), [1])
        self.assertEqual(forbidden_lines(
            'def foo1meta := 1\ndef bar2macro := 1\n'), [])
        self.assertEqual(forbidden_lines(
            'def foo1local := 1\nexample := foo1local\n'
            'macro "finish" : tactic => `(tactic| trivial)\n'), [3])
        self.assertEqual(forbidden_lines(
            'example (℘local : Nat) : Nat := 1℘local\n'
            'macro "finish" : tactic => `(tactic| trivial)\n'), [2])
        # Lean treats this unassigned Greek code point as letter-like; the approximate shared
        # masker can misread the primes inside its identifier as a character literal.
        self.assertEqual(forbidden_lines(
            "example (\u03a2'a'local : Nat) : Nat := \u03a2'a'local\n"
            'macro "finish" : tactic => `(tactic| trivial)\n'), [2])

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
            '#evalIO.FS.writeFile "x" ""',
            'theorem t : True := trivial#eval! (pure () : IO Unit)',
            'example := sᶜrun_cmd pure ()', 'example := 0x1run_cmd pure ()',
            'example (℘local : Nat) : Nat := ℘local\n'
            'macro "finish" : tactic => `(tactic| trivial)',
            'theorem t : True := trivial@[init act] opaque r : IO.Ref Nat',
            '@[inherit_doc my_init, init act] opaque r : IO.Ref Nat',
            'def t : String := s!"{\'"\'}" -- " local\n'
            'macro "finish" : tactic => `(tactic| trivial)',
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
