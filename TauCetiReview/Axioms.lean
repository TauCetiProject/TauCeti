import Lean

/-!
# `axioms`: the axiom-allowlist audit for the `TauCeti` library

Human-owned governance machinery. This executable builds the `TauCeti` environment from
its compiled `.olean`s and inspects, for every declaration *defined in `TauCeti`*, the
axioms it transitively depends on (`Lean.collectAxioms`). It fails unless every such
declaration uses only the standard allowlist

  `propext`, `Classical.choice`, `Quot.sound`.

Because it works on the kernel environment rather than on source text, it catches what a
`grep` cannot: `sorry`/`admit` (which surface as `sorryAx`), `native_decide` (which adds
`Lean.ofReduceBool`), and any home-rolled `axiom` — including ones reaching in through
imports. Run via `lake exe axioms` (after `lake build`).
-/

open Lean

/-- The library whose declarations are audited (the AI-owned mathematics). -/
def auditedRoot : Name := `TauCeti

/-- Axioms permitted anywhere in `TauCeti`. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Build the environment from the given imported modules and run `act` in `CoreM`.
Inlined from `importGraph`'s `Core.withImportModules` (Kim Morrison, Paul Lezeau; Apache 2.0).

`trustLevel := 1024` means imported constants are taken as type-correct rather than
re-checked. That is correct here because CI runs `lake build` (which kernel-checks the
library from source) *before* `lake exe axioms`; this audit checks *which axioms* a
declaration depends on, not whether the proofs are valid. It is not a defense against
stale or hand-forged `.olean`s. -/
def withImportedEnv {α} (modules : Array Name) (act : CoreM α) : IO α := do
  initSearchPath (← findSysroot)
  unsafe Lean.withImportModules (modules.map (fun m => { module := m })) {} (trustLevel := 1024)
    fun env => Prod.fst <$> Core.CoreM.toIO act
      (ctx := { fileName := "<axioms>", fileMap := default }) (s := { env := env })

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
Enumerating the source tree (rather than only importing the root) means an orphan module
that is not imported from `TauCeti.lean` is still audited. -/
def auditedModules : IO (Array Name) :=
  return #[auditedRoot] ++ (← collectLeanModules (auditedRoot.toString : System.FilePath))

/-- Audit every declaration defined in `TauCeti`. Returns the number audited and a list of
violation messages, **already rendered to `String`**.

The strings must be materialized here, inside the environment callback: declaration and
axiom `Name`s loaded from `.olean`s live in a memory-mapped region that is unmapped once
`withImportModules` returns, so formatting them afterwards is a use-after-free. -/
def audit : CoreM (Nat × Array String) := do
  let env ← getEnv
  let modNames := env.allImportedModuleNames
  -- Candidate declarations: those defined in a `TauCeti` module.
  let candidates : Array Name := env.constants.fold (init := #[]) fun acc declName _ =>
    match env.getModuleIdxFor? declName with
    | some idx =>
      match modNames[idx.toNat]? with
      | some m => if inAuditedLib m then acc.push declName else acc
      | none => acc
    | none => acc
  let mut messages : Array String := #[]
  for declName in candidates do
    let axs ← collectAxioms declName
    let bad := axs.filter fun a => !allowedAxioms.contains a
    if !bad.isEmpty then messages := messages.push s!"  {declName} → {bad.toList}"
  return (candidates.size, messages)

-- Return the exit code (rather than `IO.Process.exit`) so the Lean runtime tears the
-- imported environment down in order; an abrupt `exit()` can segfault during teardown.
def main : IO UInt32 := do
  let modules ← auditedModules
  let (audited, messages) ← withImportedEnv modules audit
  if audited == 0 then
    -- Governance tooling must fail loudly if it audited nothing (e.g. miswired import).
    IO.eprintln s!"axioms: audited 0 declarations in {auditedRoot} — the audit is miswired."
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
