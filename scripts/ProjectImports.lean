import Lean

/-!
# Exact-candidate project import preflight

Workflow-pinned trusted tooling: candidate headers are data, never elaborated or imported.
Use the pinned compiler's header parser, including nested comments, modifiers, multiline
imports, and escaped identifiers. Compare semantic `Name`s rather than dotted strings: a
quoted component containing a dot is one component, not a directory boundary.

The wrapper supplies the complete candidate source inventory, including TauCeti.lean and
orphan modules. No changed-file scope or compiled-artifact inventory is sufficient: deleting
one source can break an unchanged importer, and a batch can supply a new dependency itself.
Only imports rooted at TauCeti are checked; Lake still resolves external packages and performs
the authoritative build. Parse errors and missing module headers fail closed.
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

/-- Doc comments are body commands to Lean, but comments to this lexical safety check. -/
partial def scanWhitespace : Parser.ParserFn := fun c s =>
  let s := Parser.whitespace c s
  if s.errorMsg.isSome || c.atEnd s.pos then s
  else if c.get s.pos == '/' && c.getNext s.pos == '-' then
    let s := s.setPos (c.next (c.next s.pos))
    scanWhitespace c (Parser.finishCommentBlock (pushMissingOnError := false) 1 c s)
  else s

/-- Detect imports stranded outside the header (for example after a module doc or `private`).
Lean's lexer skips comments and literals. Unknown notation symbols and context-sensitive
numeric projections or apostrophes are advanced one character at a time: their parsers belong
to external packages, which this preflight deliberately never loads. Never skip a whole error
span, which could conceal an import. Other lexical errors are ambiguous and fail closed. -/
def checkRemainder (ctx : Parser.InputContext) (pos : String.Pos.Raw)
    (env : Environment) : Option String := Id.run do
  let tokens := Parser.Module.updateTokens (Parser.getTokenTable env)
  let first := (Parser.andthenFn scanWhitespace (Parser.tokenFn [])).run ctx
    { env, options := {} } tokens { cache := Parser.initCacheForInput ctx.inputString, pos }
  if first.errorMsg.isNone then
    if let .ident _ _ name _ := first.stxStack.back then
      if name.getRoot == `TauCeti then
        return some "unexpected project module name after the import header; use a separate \
          import directive for each module"
  -- Every import keyword contains these bytes. Most bodies have none; avoid lexing them.
  -- This is only a negative fast path, never a textual decision that an import is valid.
  unless (ctx.extract pos ctx.endPos).contains "import" do return none
  let mut pos := pos
  while !ctx.atEnd pos do
    let s := (Parser.andthenFn scanWhitespace (Parser.tokenFn [])).run ctx
      { env, options := {} } tokens { cache := Parser.initCacheForInput ctx.inputString, pos }
    if let some error := s.errorMsg then
      if (error.expected == ["token"] && error.unexpected.isEmpty) ||
          (ctx.get pos).isDigit ||
          error.unexpected == "missing end of character literal" then
        pos := ctx.next pos
      else if ctx.atEnd s.pos && error.unexpected == "unexpected end of input" then
        break
      else
        return some s!"ambiguous source after the import header: {error}"
    else
      if s.stxStack.back.isAtom && s.stxStack.back.getAtomVal == "import" then
        return some "import outside the parsed header; move imports before body commands and \
          use the import modifiers supported by the pinned Lean compiler"
      pos := s.pos
  return none

/-- Read every written project import without loading any candidate code. -/
def problems (source : Source) (inventory : Std.HashSet Name)
    (env : Environment) : IO (Array Problem) := do
  let mk (message : String) : Problem := { file := source.file, message }
  let input ← try IO.FS.readFile source.file catch error =>
    return #[mk s!"cannot be read: {error}"]
  let ctx := Parser.mkInputContext input source.file
  let (header, state, messages) ← Parser.parseHeader ctx
  let mut found := #[]
  for message in messages.toList do
    if message.severity == .error then
      found := found.push <| mk s!"header does not parse: {← message.data.toString}"
  -- Recovery syntax can contain missing nodes: never extract imports from a rejected header.
  unless found.isEmpty do return found
  unless HeaderSyntax.isModule header do
    return #[mk "no leading module header; refusing an ambiguous import inventory"]
  for imported in HeaderSyntax.imports header (includeInit := false) do
    if imported.module.getRoot == `TauCeti && !inventory.contains imported.module then
      let path := String.intercalate "/" (imported.module.components.map Name.getString!) ++ ".lean"
      found := found.push <| mk s!"missing project import {imported.module}: expected {path} \
        in the exact candidate source tree (add the source or fix the import)"
  if let some message := checkRemainder ctx state.pos env then
    found := found.push <| mk message
  return found

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let sources : Array Source ← IO.ofExcept <| (Json.parse input).bind fromJson?
  let inventory := sources.foldl (fun names source =>
    names.insert <| source.components.foldl Name.str .anonymous) ({} : Std.HashSet Name)
  let mut found := #[]
  let env ← mkEmptyEnvironment
  for source in sources do
    found := found ++ (← problems source inventory env)
  IO.println (toJson ({ checked := sources.size, problems := found } : Report)).compress
