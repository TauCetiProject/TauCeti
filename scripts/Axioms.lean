import Lean

/-!
# Shared declaration-ownership and axiom audits

`lake exe axioms` and the workflow-pinned native `audit-driver` reject declarations owned
by two modules when at least one owner is in TauCeti, including compatible duplicate
user theorems. Ownership comes from each module's `constNames`, before the axiom scan
uses merged constants. Reserved auxiliaries with no explicit source declaration are exempt.

Every TauCeti declaration must depend only on `propext`, `Classical.choice`, and `Quot.sound`.
This catches `sorry`/`admit`, native-decision axioms, and custom axioms, including private
ones and dependencies reached through imports. Enumerating sources includes the empty
root and orphan modules. `--duplicates-only` isolates the ownership fixtures.

The separate canonical module-system audit is `scripts/ModuleSystem.lean`; workflows run
it after this driver to check each compiled artifact's `isModule` flag.
-/

open Lean

namespace AxiomAudit

/-- The library whose declarations are audited (the AI-owned mathematics). -/
def auditedRoot : Name := `TauCeti

/-- Axioms permitted anywhere in `TauCeti`. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Is `mod` the audited library root or one of its submodules? -/
def inAuditedLib (mod : Name) : Bool := mod == auditedRoot || auditedRoot.isPrefixOf mod

/-- The module name for a `.lean` source path, e.g. `TauCeti/Foo/Bar.lean ↦ TauCeti.Foo.Bar`. -/
def pathToModule (p : System.FilePath) : Name :=
  (p.withExtension "").components.foldl (fun n s => Name.mkStr n s) Name.anonymous

/-- Every `.lean` module under `dir`, recursively. -/
partial def collectLeanModules (dir : System.FilePath) : IO (Array Name) := do
  let mut acc := #[]
  for entry in (← dir.readDir) do
    if (← entry.path.isDir) then
      acc := acc ++ (← collectLeanModules entry.path)
    else if entry.path.extension == some "lean" then
      acc := acc.push (pathToModule entry.path)
  return acc

/-- Every module in the `TauCeti` library: the root `TauCeti` plus all `TauCeti/**/*.lean`.
Enumerating the source tree (rather than only importing the root) means every module is
audited regardless of the root, which is intentionally empty and imports nothing. -/
def auditedModules : IO (Array Name) :=
  return #[auditedRoot] ++ (← collectLeanModules (auditedRoot.toString : System.FilePath))

/-- Reader/State monad for the shared axiom-reachability pass: the `Environment` is read-only
and the `NameMap Bool` memoizes, for every constant visited, whether it transitively depends on
an axiom outside `allowedAxioms`. The map is threaded across *all* candidates so the shared
`Mathlib`/`TauCeti` closure is walked once total, not re-walked per declaration. -/
abbrev AxiomCacheM := ReaderT Environment (StateM (Lean.NameMap Bool))

/-- Does `c` transitively depend on an axiom outside `allowedAxioms`? Memoized in the shared
`NameMap Bool`. Mirrors `Lean.collectAxioms`' traversal of each declaration's type and value, but
(a) shares one cache across every call — the stock `collectAxioms` rebuilds its state and redoes
per-call setup on each invocation, which is the ~77ms/decl that dominated the audit — and
(b) collapses the result to a single `Bool`, since the audit only needs "clean or not". A constant
is marked `false` before recursing so cycles terminate; axioms are leaves, so a back edge into an
in-progress constant contributes nothing. Adapted from Robin Arnez's mathlib-wide version
(leanprover Zulip, #general > "Checking which axioms are used in a project").

The fail-if-any-disallowed-axiom guarantee is sound: the declaration that *directly* mentions a
disallowed axiom is always cached `true` (its badness comes from its own edge to the leaf axiom,
not a back edge), and since the imported libraries are axiom-clean that declaration is itself an
audited `TauCeti` candidate — so any violation fails the run. The `false` sentinel can, in a
cyclic declaration cluster, leave *other* members of the cluster cached clean, so the reported
offender list may under-count (the next run flags the rest); it never lets a violation pass. -/
partial def reachesDisallowedAxiom (c : Name) : AxiomCacheM Bool := do
  if let some res := (← get).find? c then return res
  modify (·.insert c false)
  let env ← read
  let anyExpr (es : Array Expr) : AxiomCacheM Bool :=
    es.anyM fun e => e.getUsedConstants.anyM reachesDisallowedAxiom
  let res ← match env.checked.get.find? c with
    | some (.axiomInfo v) =>
        if !allowedAxioms.contains c then pure true else anyExpr #[v.type]
    | some (.defnInfo v)   => anyExpr #[v.type, v.value]
    | some (.thmInfo v)    => anyExpr #[v.type, v.value]
    | some (.opaqueInfo v) => anyExpr #[v.type, v.value]
    | some (.quotInfo _)   => pure false
    | some (.ctorInfo v)   => anyExpr #[v.type]
    | some (.recInfo v)    => anyExpr #[v.type]
    | some (.inductInfo v) =>
        if (← anyExpr #[v.type]) then pure true else v.ctors.anyM reachesDisallowedAxiom
    | none                 => pure false
  modify (·.insert c res)
  return res

/-- `seed` together with every module that imports one of them, directly or transitively.

A module's compiled declarations depend on the code it imports as well as on its own source: a
changed macro, elaborator, tactic, attribute handler or initializer in one module can change what
an unchanged module that uses it emits when Lake rebuilds it. So the modules whose declarations a
change can affect are exactly the changed ones and everything downstream of them; every other
module compiles to what `main` already audited. -/
def importersClosure (env : Environment) (seed : Std.HashSet Name) : Std.HashSet Name := Id.run do
  let names := env.header.moduleNames
  let data := env.header.moduleData
  let mut importers : Std.HashMap Name (Array Name) := {}
  for i in [0:names.size] do
    for imp in data[i]!.imports do
      importers := importers.insert imp.module ((importers.getD imp.module #[]).push names[i]!)
  let mut seen := seed
  let mut todo := seed.toArray
  while !todo.isEmpty do
    let m := todo.back!
    todo := todo.pop
    for d in importers.getD m #[] do
      if !seen.contains d then
        seen := seen.insert d
        todo := todo.push d
  return seen

/-- Audit every declaration defined in `TauCeti` (in the scope, if one is given). Returns the number audited and a list of
violation messages, **already rendered to `String`**.

The strings must be materialized here, inside the environment callback: declaration and
axiom `Name`s loaded from `.olean`s live in a memory-mapped region that is unmapped once
`withImportModules` returns, so formatting them afterwards is a use-after-free. -/
def audit (only : Option (Std.HashSet Name)) : CoreM (Nat × Array String) := do
  let env ← getEnv
  let modNames := env.allImportedModuleNames
  let only := only.map (importersClosure env)
  let wanted (m : Name) : Bool := inAuditedLib m && (only.map (·.contains m)).getD true
  -- Candidate declarations: those defined in a `TauCeti` module (in the scope, if one is given).
  let candidates : Array Name := env.constants.fold (init := #[]) fun acc declName _ =>
    match env.getModuleIdxFor? declName with
    | some idx =>
      match modNames[idx.toNat]? with
      | some m => if wanted m then acc.push declName else acc
      | none => acc
    | none => acc
  -- One shared-cache pass over all candidates: near-linear in the reachable closure, vs the old
  -- per-declaration `collectAxioms` (≈77ms × candidates ≈ minutes). `run env` supplies the
  -- read-only environment; `run' {}` threads one memo map through every candidate.
  let offenders : Array Name := (candidates.filterM reachesDisallowedAxiom |>.run env).run' {}
  -- Attribution only for the (normally empty) offenders: re-collect their exact axioms with the
  -- stock API, so the violation message still names the specific disallowed axioms.
  let mut messages : Array String := #[]
  for declName in offenders do
    let axs ← collectAxioms declName
    let bad := axs.filter fun a => !allowedAxioms.contains a
    messages := messages.push s!"  {declName} → {bad.toList}"
  return (candidates.size, messages)

-- Return the exit code (rather than `IO.Process.exit`) so the Lean runtime tears the
-- imported environment down in order; an abrupt `exit()` can segfault during teardown.
/-- The optional audit scope: `AXIOMS_ONLY_MODULES` names a file listing module names, one per line
(pr-build.yml passes the changed modules of an ordinary PR). Unset or empty means the whole library.
The audit then covers those modules and everything that imports them (`importersClosure`).

That is sound because the library on `main` passed the full audit (every push to `main` and every
merge-queue build runs it unscoped): a module outside the closure imports nothing that changed, so
it compiles to exactly what was audited. Lake-pin bumps, which change what everything depends on,
and any change the module list cannot name are audited in full by the caller. -/
def scope : IO (Option (Std.HashSet Name)) := do
  match (← IO.getEnv "AXIOMS_ONLY_MODULES") with
  | none | some "" => return none
  | some path =>
    let text ← IO.FS.readFile path
    return some (Std.HashSet.ofList (((text.splitOn "\n").map (·.trimAscii.toString)).filter (· ≠ "")
      |>.map String.toName))

/-- Render the axiom result and return 1 for violations or an empty unscoped candidate set. -/
def report (only : Option (Std.HashSet Name)) (audited : Nat) (messages : Array String) : IO UInt32 := do
  if let some s := only then
    IO.println s!"axioms: auditing the {s.size} changed module(s) and everything importing them \
      (AXIOMS_ONLY_MODULES)"
  if audited == 0 && only.isNone then
    -- Governance tooling must fail loudly if it audited nothing (e.g. miswired import).
    IO.eprintln s!"axioms: audited 0 declarations in {auditedRoot}: the audit is miswired."
    return 1
  if messages.isEmpty then
    IO.println s!"axioms: audited {audited} {auditedRoot} declaration(s); \
      all within the allowlist {allowedAxioms}."
    return 0
  else
    IO.eprintln s!"axioms: {messages.size} declaration(s) in {auditedRoot} use disallowed axioms:"
    for m in messages do IO.eprintln m
    IO.eprintln s!"allowed: {allowedAxioms}"
    return 1

end AxiomAudit

namespace DuplicateDeclarations

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

end DuplicateDeclarations

/-!
## Import and teardown discipline

One private-level import loads the full artifact parts without executing candidate
initializers (`loadExts := false`). `trustLevel := 1024` accepts constants as type-correct:
these checks follow a kernel-checked build and do not validate arbitrary compiled proofs.
Byte integrity alone does not establish proof correctness.

`withImportModules` keeps mmap-backed names alive through both checks and frees the
regions before returning an exit code. Render every imported name inside the callback.
A failed ownership check stops the axiom scan.
-/

/-- Print a phase and write best-effort epoch timestamps to `AUDIT_PHASES_FILE`, if set. -/
def phase (name : String) : IO Unit := do
  IO.println s!"audit-driver: phase {name}"
  (← IO.getStdout).flush
  if let some path ← IO.getEnv "AUDIT_PHASES_FILE" then
    -- Telemetry is best-effort and never decides audit success.
    try
      let timestamp ← IO.Process.output { cmd := "date", args := #["+%s.%N"] }
      if timestamp.exitCode == 0 then
        let file ← IO.FS.Handle.mk path .append
        file.putStr s!"{name}\t{timestamp.stdout.trimAscii}\n"
    catch _ => pure ()

/-- Run ownership then axioms, or ownership alone with `--duplicates-only`.
Return 0 on success, 1 on an audit/import failure, and 2 on unsupported arguments.
The environment callback/CoreM adapter is inlined from importGraph's `Core.withImportModules`
(Kim Morrison, Paul Lezeau; Apache 2.0). -/
def main (args : List String) : IO UInt32 := do
  if !args.isEmpty && args != ["--duplicates-only"] then
    IO.eprintln "usage: audit-driver [--duplicates-only]"
    return 2
  try
    phase "audit-import"
    initSearchPath (← findSysroot)
    let modules ← AxiomAudit.auditedModules
    if modules.size <= 1 then
      throw <| IO.userError "duplicate-declarations: no TauCeti source modules found"
    let localModules := modules.foldl (fun s n => s.insert n) ({} : NameSet)
    let only ← AxiomAudit.scope
    unsafe withImportModules (modules.map fun m => { module := m }) {}
      (fun env => do
        phase "audit-duplicates"
        let status ← DuplicateDeclarations.check env localModules
        if status != 0 || args == ["--duplicates-only"] then return status
        phase "audit-axioms"
        let (audited, messages) ← Prod.fst <$> Core.CoreM.toIO (AxiomAudit.audit only)
          { fileName := "<axioms>", fileMap := default } { env }
        AxiomAudit.report only audited messages) (trustLevel := 1024)
  catch e =>
    IO.eprintln s!"audit-driver: {e}"
    return 1
