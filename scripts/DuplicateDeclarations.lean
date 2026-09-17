import Lean

/-!
# Reject declarations owned by more than one module

Lean can accept compatible duplicate declarations when importing independently compiled
modules. Inspect each artifact before import-environment merging can hide that collision.
Enumerate the source tree, including modules not imported by the intentionally empty root.
Also visit dependencies, rejecting collisions involving at least one TauCeti module.

Read all module-system artifact parts to include private declarations. Inspect `constNames`
per module, allowing Lean-reserved auxiliaries realized lazily without a source declaration.
Imported names and IR-only `extraConstNames` are not additional declarations.
Run after `lake build`: `lake env lean --run scripts/DuplicateDeclarations.lean`.
-/

open Lean

namespace DuplicateDeclarations

partial def sourceModules (dir : System.FilePath) : IO (Array Name) := do
  let mut result := #[]
  for entry in (← dir.readDir) do
    if ← entry.path.isDir then
      result := result ++ (← sourceModules entry.path)
    else if entry.path.extension == some "lean" then
      result := result.push <| (entry.path.withExtension "").components.foldl Name.mkStr .anonymous
  return result

/-- Inspect the per-module data, not `env.constants`, which has already merged equal theorems.
All mmap-backed names stay inside `withImportModules`' callback. -/
def check (env : Environment) (localModules : NameSet) : IO UInt32 := do
  let modules := env.allImportedModuleNames
  -- A reserved auxiliary can legitimately be realized in several modules. Exempt it only
  -- when Lean recognizes the reserved name and no occurrence has a source declaration range.
  -- In particular, a user-written theorem ending in `.eq_1` is not a blanket exemption.
  let mut explicitNames : NameSet := {}
  for i in [:modules.size] do
    for (name, _) in declRangeExt.getModuleEntries env i do
      explicitNames := explicitNames.insert name
  let mut owners : NameMap Name := {}
  let mut bad := 0
  for i in [:modules.size] do
    let mod := modules[i]!
    for name in env.header.moduleData[i]!.constNames do
      if !explicitNames.contains name && isReservedName env name then continue
      match owners.find? name with
      | none => owners := owners.insert name mod
      | some previous =>
        if previous != mod && (localModules.contains mod || localModules.contains previous) then
          IO.eprintln s!"duplicate-declarations: {name} is declared in both {previous} and {mod}"
          bad := bad + 1
        if localModules.contains mod then owners := owners.insert name mod
  if bad != 0 then
    IO.eprintln "Keep one canonical declaration and import its module from the other files."
    return 1
  IO.println s!"duplicate-declarations: checked {localModules.size} TauCeti modules and \
    {modules.size - localModules.size} dependency modules; no duplicate declarations."
  return 0

def audit : IO UInt32 := do
  initSearchPath (← findSysroot)
  let sources ← sourceModules "TauCeti"
  if sources.isEmpty then
    throw <| IO.userError "duplicate-declarations: no TauCeti source modules found"
  let modules := sources.push `TauCeti
  let localModules := modules.foldl (fun s n => s.insert n) ({} : NameSet)
  -- Like the axiom audit, use private-level imports to include all artifact parts. Loading
  -- extension entries does not execute candidate initializers (`loadExts := false`). Lean's
  -- importer rejects incompatible collisions; the ownership pass also rejects compatible
  -- duplicate user theorems, which the importer intentionally accepts.
  unsafe withImportModules (modules.map fun m => { module := m }) {}
    (fun env => check env localModules) (trustLevel := 1024)

end DuplicateDeclarations

def main : IO UInt32 := do
  try DuplicateDeclarations.audit
  catch e =>
    IO.eprintln s!"duplicate-declarations: {e}"
    return 1
