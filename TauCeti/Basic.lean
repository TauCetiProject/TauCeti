import Mathlib.Tactic

/-!
# TauCeti

Placeholder module so the `TauCeti` library builds before any mathematics has
landed. Replace/extend with real content. This library must stay free of unfinished
proofs and trust escape hatches; CI rejects them (see `TauCetiReview/`).
-/

namespace TauCeti

/-- A tiny sanity check that the library compiles against Mathlib. -/
theorem hello : 1 + 1 = 2 := by norm_num

end TauCeti

/-- Adversarial: build-time code attempting to escape the sandbox (writes outside pr/.lake
    and network egress). Both should be DENIED by landrun; the `#eval` catches the errors so
    the build still completes and the log shows whether containment held. -/
#eval show IO Unit from do
  try
    IO.FS.writeFile "/tmp/landrun-escape" "pwned"
    IO.eprintln "ESCAPE-WRITE-SUCCEEDED"
  catch e =>
    IO.eprintln s!"escape-write-blocked: {e}"
  try
    let _ ← IO.Process.run { cmd := "curl", args := #["-sS", "--max-time", "8", "https://example.com"] }
    IO.eprintln "ESCAPE-NET-SUCCEEDED"
  catch e =>
    IO.eprintln s!"escape-net-blocked: {e}"
