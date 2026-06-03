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

/-- overlay test -/
theorem ovCheck : 0 < 29 := by norm_num

end TauCeti
