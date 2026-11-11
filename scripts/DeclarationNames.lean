import Lean

/-!
# Declaration names a PR adds

`lean --run scripts/DeclarationNames.lean HEAD BASE TESTED MODULES TESTED-LIB BASE-OLEANS`
prints one line, `DECLARATION-NAMES {...}`, listing for each module named in `MODULES`
(one module name per line) the constant names present in the module's compiled header
under `TESTED-LIB/<Module/Path>.olean` that are absent from the same module's header
under `BASE-OLEANS/<Module/Path>.olean`. A module with no base header is new, and every
name it declares counts as added. Headers are read with `readModuleData`; nothing is
imported, elaborated or executed.

The record lets the merge queue defer two batch-mates that both add the same name in
different modules before any staging build. It is advisory: the post-build audit in
`scripts/Axioms.lean` remains the authority on duplicate declarations.

Excluded from every set, deliberately: private names (their internal names are
module-qualified and cannot collide across modules) and auxiliary names. Lean's
`isReservedName` needs an environment, so this script uses a structural superset of it:
a name is auxiliary when any component is numeric or starts with `_`, when
`Name.isInternalDetail` accepts it (`eq_`, `match_`, `proof_`, `omega_` prefixes), or when
any component is one of the suffixes Lean generates beside a declaration (`rec`, `casesOn`,
`noConfusion`, `eq_def`, `fun_cases`, `injEq`, ...). Excluding more names only reduces what
the queue can defer early; the audit still checks all of them.

The line is bounded: at most 4,096 modules, 16,384 added names and 1 MiB. Over any bound,
or when any listed module's tested header, or an existing base header, cannot be read,
the record is `"complete": false` with no names. The exit status is always 0; errors go
to stderr. Staging batches never run this script.
-/

open Lean

namespace DeclarationNames

def maxModules : Nat := 4096
def maxNames : Nat := 16384
def maxBytes : Nat := 1024 * 1024

/-- Suffix components Lean generates beside a user declaration. A superset of the
environment-dependent reserved-name predicates; over-exclusion is safe. -/
def auxiliarySuffixes : List String :=
  ["rec", "recOn", "casesOn", "below", "brecOn", "binductionOn", "ibelow", "noConfusion",
   "noConfusionType", "injEq", "inj", "sizeOf_spec", "ctorIdx", "ctorIdx_hinj", "ctorElim",
   "toCtorIdx", "ofNat", "induct", "induct_unfolding", "mutual_induct", "fun_cases",
   "fun_cases_unfolding", "partial_correctness", "eq_def", "eq_unfold", "congr_simp", "spec",
   "mk", "eta", "sizeOf"]

partial def auxiliaryComponents : Name → Bool
  | .anonymous => false
  | .num .. => true
  | .str p s => s.startsWith "_" || auxiliarySuffixes.contains s || auxiliaryComponents p

/-- Names the record never enforces. -/
def excluded (n : Name) : Bool :=
  isPrivateName n || n.isInternalDetail || auxiliaryComponents n

/-- `TauCeti.A.B` becomes `TauCeti/A/B`. -/
def modulePath (module : String) : String :=
  "/".intercalate (module.splitOn ".")

/-- JSON string escaping with every non-ASCII character written as `\uXXXX`. -/
def escape (s : String) : String := Id.run do
  let hex (n : Nat) : String :=
    let digits := Nat.toDigits 16 n
    String.ofList (List.replicate (4 - digits.length) '0' ++ digits)
  let mut out := "\""
  for c in s.toList do
    let v := c.toNat
    if c == '"' then out := out ++ "\\\""
    else if c == '\\' then out := out ++ "\\\\"
    else if v < 0x20 || v > 0x7e then
      if v > 0xffff then
        let w := v - 0x10000
        out := out ++ "\\u" ++ hex (0xd800 + w / 0x400) ++ "\\u" ++ hex (0xdc00 + w % 0x400)
      else out := out ++ "\\u" ++ hex v
    else out := out.push c
  return out ++ "\""

def render (head base tested : String) (complete : Bool)
    (added : Array (String × Array String)) : String :=
  let modules := added.map fun (m, names) =>
    escape m ++ ":[" ++ ",".intercalate (names.map escape).toList ++ "]"
  "DECLARATION-NAMES {\"version\":1,\"head\":" ++ escape head ++ ",\"base\":" ++ escape base ++
    ",\"tested\":" ++ escape tested ++ ",\"complete\":" ++ (if complete then "true" else "false") ++
    ",\"added\":{" ++ ",".intercalate modules.toList ++ "}}"

/-- `none` when the header cannot be read. Names are copied out of the compacted region
before anything else happens. -/
def readNames (path : System.FilePath) : IO (Option (Array String)) := do
  try
    let (data, _) ← readModuleData path
    let names := data.constNames.filter (!excluded ·) |>.map (·.toString (escape := false))
    return some names
  catch e =>
    IO.eprintln s!"declaration-names: cannot read {path}: {e}"
    return none

inductive Outcome where
  | complete (added : Array (String × Array String))
  | incomplete (reason : String)

def collect (modulesFile testedDir baseDir : String) : IO Outcome := do
  let modules := (← IO.FS.lines modulesFile).map (·.trimAscii.toString) |>.filter (· ≠ "")
  if modules.size > maxModules then return .incomplete s!"{modules.size} modules"
  let mut added : Array (String × Array String) := #[]
  let mut total := 0
  for module in modules do
    let rel := modulePath module ++ ".olean"
    let some testedNames ← readNames (testedDir / rel)
      | return .incomplete s!"tested header unreadable for {module}"
    let basePath : System.FilePath := baseDir / rel
    let baseNames ←
      if ← basePath.pathExists then
        match ← readNames basePath with
        | some names => pure names
        | none => return .incomplete s!"base header unreadable for {module}"
      else pure #[]
    let baseSet := baseNames.foldl (fun (s : Std.HashSet String) n => s.insert n) {}
    let names := (testedNames.filter (!baseSet.contains ·)).qsort (· < ·)
    total := total + names.size
    if total > maxNames then return .incomplete s!"{total} added names"
    added := added.push (module, names)
  return .complete added

end DeclarationNames

open DeclarationNames in
def main (args : List String) : IO UInt32 := do
  let [head, base, tested, modulesFile, testedDir, baseDir] := args
    | IO.eprintln "usage: DeclarationNames.lean HEAD BASE TESTED MODULES TESTED-LIB BASE-OLEANS"
      return 2
  let incomplete (reason : String) : IO Unit := do
    IO.eprintln s!"declaration-names: incomplete: {reason}"
    IO.println (render head base tested false #[])
  try
    match ← collect modulesFile testedDir baseDir with
    | .incomplete reason => incomplete reason
    | .complete added =>
      let line := render head base tested true added
      if line.utf8ByteSize > maxBytes then incomplete s!"{line.utf8ByteSize} bytes"
      else IO.println line
  catch e => incomplete (toString e)
  return 0
