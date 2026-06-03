import Mathlib.Tactic

/-!
# Centauri

Placeholder module so the `Centauri` library builds before any mathematics has
landed. Replace/extend with real content. This library must stay free of unfinished
proofs and trust escape hatches; CI rejects them (see `CentauriReview/`).
-/

namespace Centauri

/-- A tiny sanity check that the library compiles against Mathlib. -/
theorem hello : 1 + 1 = 2 := by norm_num

end Centauri
