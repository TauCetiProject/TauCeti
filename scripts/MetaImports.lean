import Lean

/-!
# `MetaImports`: the `meta import` audit for the `TauCeti` library

Human-owned governance machinery. This script reads a list of source paths on stdin, one per
line, and reports every `meta import` in them. TauCeti contains no metaprogramming: the only
Lean meta code in the repository is this governance machinery under `scripts/`, so a
`meta import` in the library is either a copy-paste accident or the start of meta code that
belongs here instead.

The decision comes from Lean's own header parser rather than from a pattern over the text.
`Lean.Parser.parseHeader` is the parser the frontend itself runs on a module header, and
`Lean.Elab.HeaderSyntax.imports (includeInit := false)` reads the written imports out of the
resulting syntax. So the `meta` modifier is seen exactly as the compiler sees it, through
block comments, nested `/- -/`, string literals and guillemet-quoted module names.

Asking the syntax rather than the computed import list matters for one case. The computed list
adds `import Init` and `meta import Init` to every non-`prelude` module, and those synthetic
entries are indistinguishable from a header that writes `prelude`, `public import Init` and
`public meta import Init` itself. `includeInit := false` returns only what the file wrote, so
there is no `Init` exception to carve out and no spelling of `meta import` that hides in one.

A header the parser rejects is reported, not passed over: a file that does not reach `module`
cannot be read for its imports at all, and a pattern match would silently see nothing there.

Nothing is elaborated, built or imported, and the parser stops at the end of the header, so
the whole library costs a few seconds and a pull request's changed files a fraction of one.
Run via `lean --run scripts/MetaImports.lean` with the paths on stdin; `scripts/check-meta-imports.py`
is the wrapper that chooses them and reports the result.
-/

open Lean Elab

/-- One problem found in one file, as consumed by `scripts/check-meta-imports.py`. -/
structure Problem where
  file : String
  message : String
  deriving ToJson

/-- Every reason `path` must fail the audit. -/
def problems (path : String) : IO (Array Problem) := do
  let mk (message : String) : Problem := { file := path, message }
  -- A source Lean cannot read is a failure of the audit, not an absence of findings.
  let input ← try
      IO.FS.readFile path
    catch error =>
      return #[mk s!"cannot be read: {(toString error).replace "\n" " "}"]
  let (header, _, messages) ← Parser.parseHeader (Parser.mkInputContext input path)
  let mut found : Array Problem := #[]
  for message in messages.toList do
    if message.severity == .error then
      let text := (← message.data.toString).replace "\n" " "
      found := found.push <| mk s!"its header does not parse: {text}"
  -- A rejected header is the whole finding, and the only safe stopping point: the syntax can
  -- carry a `.missing` node that `HeaderSyntax.imports` panics on rather than reading.
  unless found.isEmpty do
    return found
  -- Every TauCeti source opts into the module system (`scripts/ModuleSystem.lean` enforces
  -- that on the compiled artifact). Checking it here as well keeps this audit honest: a header
  -- the parser gives up on without complaint, such as one behind a byte-order mark, reports no
  -- imports at all, and the absence of `module` is what distinguishes that from a clean file.
  unless HeaderSyntax.isModule header do
    found := found.push <| mk "it does not opt into the module system (no leading `module`)"
  for imported in HeaderSyntax.imports header (includeInit := false) do
    if imported.isMeta then
      found := found.push <| mk s!"`meta import {imported.module}` is not allowed: TauCeti/ \
        holds no metaprogramming, and meta code belongs in scripts/"
  return found

def main : IO Unit := do
  let paths := (← (← IO.getStdin).readToEnd).splitOn "\n" |>.filter (!·.isEmpty)
  let mut found : Array Problem := #[]
  for path in paths do
    found := found ++ (← problems path)
  IO.println (toJson found).compress
