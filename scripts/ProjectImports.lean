import Lean

/-!
# Exact-candidate project import preflight

Workflow-pinned trusted tooling: candidate headers are data, never elaborated or imported.
Use both pinned parsers: `parseImports'` is Lake's dependency parser, while `parseHeader` is
Lean's frontend parser. Malformed keyword prefixes can make them disagree. Check the union of
their local imports and refuse disagreement, so neither interpretation can hide a dependency.
Nested comments, multiline imports, modifiers, and escaped names are handled by the compiler.
Compare semantic `Name`s: a quoted component containing a dot is not a directory boundary.

The complete candidate inventory includes TauCeti.lean, orphan modules, and batch additions.
Only imports rooted at TauCeti are checked. External resolution and body validity remain the
authoritative Lake build's responsibility; no external syntax or candidate code is loaded.
-/

open Lean Elab

structure Source where
  file : String
  components : Array String
  deriving FromJson

structure Problem where
  file : String
  message : String
  deriving ToJson

structure Report where
  checked : Nat
  problems : Array Problem
  deriving ToJson

/-- Read both dependency interpretations without loading candidate code. -/
def problems (source : Source) (inventory : Std.HashSet Name) : IO (Array Problem) := do
  let mk (message : String) : Problem := { file := source.file, message }
  let input ← try IO.FS.readFile source.file catch error =>
    return #[mk s!"cannot be read: {error}"]
  let (header, _, messages) ← Parser.parseHeader (Parser.mkInputContext input source.file)
  let mut found := #[]
  for message in messages.toList do
    if message.severity == .error then
      found := found.push <| mk s!"Lean import header does not parse: {← message.data.toString}"
  -- Recovery syntax can contain missing nodes: never extract imports from a rejected header.
  unless found.isEmpty do return found
  let lakeHeader ← try parseImports' input source.file catch error =>
    return #[mk s!"Lake import header does not parse: {error}"]
  unless HeaderSyntax.isModule header && lakeHeader.isModule do
    return #[mk "no leading module header; refusing an ambiguous import inventory"]
  let localNames (imports : Array Import) :=
    imports.filter (·.module.getRoot == `TauCeti) |>.map (·.module)
  let frontend := localNames (HeaderSyntax.imports header (includeInit := false))
  let lake := localNames lakeHeader.imports
  for name in (frontend.toList ++ lake.toList).eraseDups do
    unless inventory.contains name do
      let path := String.intercalate "/" (name.components.map Name.getString!) ++ ".lean"
      found := found.push <| mk s!"missing project import {name}: expected {path} \
        in the exact candidate source tree (add the source or fix the import)"
  if frontend != lake then
    found := found.push <| mk "ambiguous project imports: Lean and Lake disagree; separate \
      import keywords and module names with whitespace"
  return found

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let sources : Array Source ← IO.ofExcept <| (Json.parse input).bind fromJson?
  let inventory := sources.foldl (fun names source =>
    names.insert <| source.components.foldl Name.str .anonymous) ({} : Std.HashSet Name)
  let mut found := #[]
  for source in sources do
    found := found ++ (← problems source inventory)
  IO.println (toJson ({ checked := sources.size, problems := found } : Report)).compress
