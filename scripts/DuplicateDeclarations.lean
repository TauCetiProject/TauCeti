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
  -- Every violation involves a TauCeti-owned name. Index those names first, then compare
  -- them against ALL modules, including dependencies; unrelated dependency names need no owner.
  let mut localNames : NameSet := {}
  for i in [:modules.size] do
    if localModules.contains modules[i]! then
      for name in env.header.moduleData[i]!.constNames do
        localNames := localNames.insert name
  let mut owners : NameMap Name := {}
  let mut collisions : Array (Name × Name × Name) := #[]
  let mut collisionNames : NameSet := {}
  for i in [:modules.size] do
    let mod := modules[i]!
    for name in env.header.moduleData[i]!.constNames do
      if !localNames.contains name then continue
      match owners.find? name with
      | none => owners := owners.insert name mod
      | some previous =>
        if previous != mod && (localModules.contains mod || localModules.contains previous) then
          collisions := collisions.push (name, previous, mod)
          collisionNames := collisionNames.insert name
        if localModules.contains mod then owners := owners.insert name mod
  -- Declaration ranges matter only for collisions. Keep the same exemption: a reserved
  -- auxiliary is allowed only when NO module supplies a source declaration range for it.
  -- In particular, user-written `.eq_1` theorems are still checked.
  let mut explicitNames : NameSet := {}
  for i in [:modules.size] do
    for (name, _) in declRangeExt.getModuleEntries env i do
      if collisionNames.contains name then
        explicitNames := explicitNames.insert name
  let mut bad := 0
  for (name, previous, mod) in collisions do
    if !explicitNames.contains name && isReservedName env name then continue
    IO.eprintln s!"duplicate-declarations: {name} is declared in both {previous} and {mod}"
    bad := bad + 1
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
