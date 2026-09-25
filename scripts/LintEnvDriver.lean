import Batteries.Tactic.Lint

/-!
# `lint-env` driver: Mathlib's default environment linters, compiled

Human-owned governance machinery, run by `scripts/lint-env.sh`. It does exactly what the
generated `#lint only <linters> in TauCeti` driver used to do, and prints the same report in the
same format, but as a compiled executable.

It is faster. Measured on the whole library in 2026-09 (16 cores, two runs each, identical reports),
`lake env lean` on the generated driver took 257s wall and 3,552 CPU-seconds, and this driver took
169s and 2,543. Userspace instructions differ by only 5% (5.13e12 against 4.85e12); most of the
saving is kernel time (486s against 88s). Why the frontend spends that kernel time is not
established.

`lint-env.sh` builds this file into a throwaway Lake workspace that depends on the candidate's
Batteries by path, so only this trusted source and the pinned Batteries are compiled, and runs it
under `lake env` from the project root.

Usage: `lint-env-driver <tag> <marker-file> <modules-file> <linter>...`

* Imports every module listed (one per line) in `<modules-file>`. `importModules` loads the closure
  at the `private` olean level, as the legacy (non-module) `#lint` driver did; see PRIVATE
  DECLARATIONS in `lint-env.sh`.
* Runs exactly the named linters on the declarations of the `TauCeti` package.
* Prints the report `#lint` would print. With violations, the header line carries the
  `<tag>:1:0: error: ` prefix that Lean gives an error diagnostic from a driver file named `<tag>`,
  and the exit code is 1. Without violations, the report is printed bare and the exit code is 0.
* Then prints the contents of `<marker-file>` (a per-run nonce) on its own line, proving the
  process ran past the linters. The nonce is passed in a file rather than on the command line so
  that learning it takes the same two steps as it did for the generated driver file.

`trace.Batteries.Lint` is enabled, so each linter's progress is also printed to stdout. All of it
comes before the report header, and `lint-env.sh` parses only what follows the header. Once Batteries
reports per-linter cost on those trace lines, CI logs will record what each linter costs.
-/

open Lean Core Batteries.Tactic.Lint

/-- The package whose declarations are linted. -/
def lintedPackage : Name := `TauCeti

unsafe def main (args : List String) : IO UInt32 := do
  let tag :: markerFile :: modulesFile :: linterNames := args
    | IO.eprintln "usage: lint-env-driver <tag> <marker-file> <modules-file> <linter>..."; return 2
  if linterNames.isEmpty then
    IO.eprintln "lint-env-driver: no linters requested"; return 2
  let modules := (← IO.FS.lines modulesFile).filter (!·.isEmpty) |>.map String.toName
  if modules.isEmpty then
    IO.eprintln "lint-env-driver: no modules to import"; return 2
  initSearchPath (← findSysroot)
  -- The legacy `#lint` driver ran imported initializers too (`lean` always does).
  enableInitializersExecution
  let env ← importModules (modules.map ({ module := · })) {} (trustLevel := 1024)
    (loadExts := true)
  let opts : Options := ({} : Options).setBool `trace.Batteries.Lint true
  let ctx : Core.Context := { fileName := tag, fileMap := default, options := opts }
  let (failed, report) ← Prod.fst <$> (CoreM.toIO · ctx { env }) do
    let decls ← getDeclsInPackage lintedPackage
    let linters ← getChecks (slow := true) (runOnly := some (linterNames.map String.toName))
      (runAlways := none)
    -- `getChecks` silently drops an unknown name; `#lint only` rejected it. Keep that behaviour.
    for n in linterNames do
      unless linters.any (·.name == n.toName) do
        throwError "not a linter: {n}"
    let results ← lintCore decls linters (inIO := true)
    let failed := results.any (!·.2.isEmpty)
    let fmt ← formatLinterResults results decls (groupByFilename := true)
      s!"in {lintedPackage}" (runSlowLinters := true) .medium linters.size
    let report ← (← addMessageContext fmt).toString
    return (failed, report)
  -- Lean prints a diagnostic followed by exactly one newline.
  let diagnostic (s : String) := if s.endsWith "\n" then s else s ++ "\n"
  if failed then
    IO.print (diagnostic s!"{tag}:1:0: error: {report}")
  else
    IO.print (diagnostic s!"{report}\n-- All linting checks passed!")
  IO.println (← IO.FS.readFile markerFile).trim
  return if failed then 1 else 0
