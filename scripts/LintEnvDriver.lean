import Batteries.Tactic.Lint

/-!
# `lint-env` driver: Mathlib's default environment linters, compiled

Human-owned governance machinery, run by `scripts/lint-env.sh`. It does exactly what the
generated `#lint only <linters> in TauCeti` driver used to do, and prints the same report in the
same format, but as a compiled executable.

It is faster because Batteries' lint framework and linters run natively; under `lean` they are
interpreted. Measured on the whole library in 2026-09 (16 cores, identical reports): `lake env lean`
on the generated driver took 257s wall and 3,552 CPU-seconds, this driver compiled took 169s and
2,543. Running this same source interpreted, with `lake env lean --run`, took 226s and 3,399, with
35 million context switches against 8 million compiled; most of the extra CPU is kernel time
(707s against 104s), consistent with interpreted, allocation-heavy linter tasks contending in
Lean's task manager. Userspace instructions differ by only about 10%.

`scripts/build-lint-driver.sh` compiles it in a throwaway Lake workspace that depends on the
project's pinned Batteries by path. In the sandboxed PR build that happens on the host before any
candidate code runs, and the executable is mounted read-only; see `lint-env.sh`.

Usage: `lint-env-driver [--only-listed] <tag> <marker-file> <modules-file> <linter>...`

* Imports every module listed (one per line) in `<modules-file>`. `importModules` loads the closure
  at the `private` olean level, as the legacy (non-module) `#lint` driver did; see PRIVATE
  DECLARATIONS in `lint-env.sh`.
* Runs exactly the named linters on the declarations of the `TauCeti` package, or, with
  `--only-listed`, on just the declarations defined in the listed modules (the TauCeti modules
  they import are not linted). `lint-env.sh` uses that to lint only what a change touched.
* Prints the report `#lint` would print. With violations, the header line carries the
  `<tag>:1:0: error: ` prefix that Lean gives an error diagnostic from a driver file named `<tag>`,
  and the exit code is 1. Without violations, the report is printed bare and the exit code is 0.
* Then prints the contents of `<marker-file>` (a per-run nonce) on its own line, proving the
  process ran past the linters. The nonce is passed in a file rather than on the command line so
  that learning it takes the same two steps as it did for the generated driver file.
* Before the report, emits bounded, optional `LINT-ENV-ORIGINS` metadata from these same
  results. `lint-env.sh` validates and joins it only to NEW findings. See
  `scripts/env-lint-locations.md`; this untrusted metadata has retry authority only.

`trace.Batteries.Lint` is enabled, so each linter's progress is also printed to stdout. All of it
comes before the report header, and `lint-env.sh` parses only what follows the header. Once Batteries
reports per-linter cost on those trace lines, CI logs will record what each linter costs.
-/

open Lean Core Batteries.Tactic.Lint

/-- The package whose declarations are linted. -/
def lintedPackage : Name := `TauCeti

/-- Optional, bounded retry hints. Never use these to decide whether lint passed. -/
def linterOrigins (modules : Array Name)
    (results : Array (NamedLinter × Std.HashMap Name MessageData)) : CoreM Json := do
  let started ← IO.monoMsNow
  let env ← getEnv
  let total := results.foldl (fun n r => n + r.2.size) 0
  let mut records : Array Json := #[]
  for (linter, findings) in results do
    for (decl, _) in findings.toArray do
      if records.size >= 128 then break
      -- Use exactly the report's rendering for the join to the existing report parser.
      -- Keep the actual environment name too; never infer an origin from either name.
      let rendered ← (← addMessageContext m!"{← mkConstWithLevelParams decl}").toString
      let reportName := if rendered.startsWith "@" then rendered.drop 1 |>.toString else rendered
      let mut fields := [("linter", toJson linter.name.toString),
        ("declaration", toJson decl.toString), ("report_name", toJson reportName)]
      let unknown (reason : String) := Json.mkObj (fields ++ [("unknown", toJson reason)])
      let record ← do
        if decl.toString.length > 1024 || reportName.length > 1024 ||
            reportName.any Char.isWhitespace then
          pure <| Json.mkObj [("unknown", toJson "unsupported_name")]
        else if env.isPrivateOrAutoDecl decl then
          pure <| unknown "private_or_generated"
        else if let some idx := env.getModuleIdxFor? decl then
          let mod := env.header.moduleNames[idx.toNat]!
          if !modules.contains mod then
            pure <| unknown "unsupported_module"
          else if let some ranges ← findDeclarationRangesCore? decl then
            -- No auxiliary-declaration fallback to a parent's range.
            let pos := ranges.selectionRange.pos
            fields := fields ++ [("module", toJson mod.toString),
              ("line", toJson pos.line), ("column", toJson (pos.column + 1))]
            pure <| Json.mkObj fields
          else pure <| unknown "missing_range"
        else pure <| unknown "missing_origin"
      records := records.push record
  return Json.mkObj [("version", toJson (1 : Nat)), ("total", toJson total),
    ("truncated", toJson (decide (total > records.size))), ("records", toJson records),
    ("elapsed_ms", toJson ((← IO.monoMsNow) - started))]

unsafe def main (args : List String) : IO UInt32 := do
  let (onlyListed, args) := match args with
    | "--only-listed" :: rest => (true, rest)
    | _ => (false, args)
  let tag :: markerFile :: modulesFile :: linterNames := args
    | IO.eprintln "usage: lint-env-driver [--only-listed] <tag> <marker-file> <modules-file> \
        <linter>..."; return 2
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
  let (failed, report, origins) ← Prod.fst <$> (CoreM.toIO · ctx { env }) do
    let decls ← getDeclsInPackage lintedPackage
    let decls ← if onlyListed then
        let env ← getEnv
        let idxs := modules.filterMap env.getModuleIdx?
        pure <| decls.filter fun d => (env.getModuleIdxFor? d).any idxs.contains
      else pure decls
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
    let origins ← try linterOrigins modules results catch _ =>
      pure <| Json.mkObj [("unknown", toJson "collection_failed")]
    return (failed, report, origins)
  -- Before the report region: existing report/nonce parsing is unchanged.
  IO.println s!"LINT-ENV-ORIGINS {origins.compress}"
  -- Lean prints a diagnostic followed by exactly one newline.
  let diagnostic (s : String) := if s.endsWith "\n" then s else s ++ "\n"
  if failed then
    IO.print (diagnostic s!"{tag}:1:0: error: {report}")
  else
    IO.print (diagnostic s!"{report}\n-- All linting checks passed!")
  IO.println (← IO.FS.readFile markerFile).trimAscii.toString
  return if failed then 1 else 0
