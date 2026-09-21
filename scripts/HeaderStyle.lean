import Mathlib.Tactic.Linter.Header

/-!
# Copyright-header audit for Tau Ceti sources

Human-owned governance machinery. Mathlib's `linter.style.header` deliberately skips a module
unless the library root imports it. Tau Ceti's root is intentionally empty, so the ordinary
command linter never reaches these files. This audit calls the linter's public
`copyrightHeaderChecks` function on the validated `TauCeti/**` source list supplied by
`scripts/lint-style.sh`. The deliberately empty library root `TauCeti.lean` is exempt, matching
Mathlib's own exclusion of its library root from the copyright-header check.

This intentionally enforces the copyright block and `Authors:` contract from issue #3546, not the
same command linter's separate broad-import, duplicate-import, directory-dependency, or module-doc
checks. The latter require elaborator state and are outside this text-based CI check.

Run via `lake env lean --run scripts/HeaderStyle.lean ...`, as part of `scripts/lint-style.sh`.
-/

open Mathlib.Linter

/-- Mathlib's default required license line, also used by Tau Ceti. -/
def expectedLicense := Mathlib.Linter.linter.style.header.license.defValue

/-- Read the portion inspected by Mathlib's copyright checker.

The checker normalizes comma-continued lines before splitting at a newline followed by a comment
terminator. A newline after a comma therefore does not end the header. Keep one line after the closing delimiter too: the
checker inspects the following character, and an immediately adjacent second delimiter makes
that intervening segment empty. If no such delimiter exists, retain the full input.

Reading just this prefix avoids running the checker's string replacements over every file body.
Mathlib still performs all validation and constructs the diagnostics. -/
def readCopyrightHeader (path : System.FilePath) : IO String :=
  IO.FS.withFile path .read fun handle => do
    let mut text := ""
    let mut previous := ""
    repeat
      let line ← handle.getLine
      if line.isEmpty then return text
      let closes := !text.isEmpty && line.startsWith "-/" && !previous.endsWith ",\n"
      text := text ++ line
      if closes then return text ++ (← handle.getLine)
      previous := line
    return text

/-- Audit every supplied source with Mathlib's copyright-header checker. Returns a nonzero exit
code when the source list is empty or at least one file has a malformed header. -/
unsafe def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "header-style: received no validated TauCeti source files; the audit is miswired."
    return 1
  let mut failures : UInt32 := 0
  for path in args do
    let errors := copyrightHeaderChecks (← readCopyrightHeader path) expectedLicense
    unless errors.isEmpty do
      failures := failures + 1
      for (_, message) in errors do
        IO.eprintln s!"{path}: {message}"
  if failures != 0 then
    IO.eprintln s!"header-style: {failures} source file(s) have malformed copyright headers."
  else
    IO.eprintln s!"header-style: all {args.length} TauCeti source file(s) have conforming headers."
  return min failures 125
