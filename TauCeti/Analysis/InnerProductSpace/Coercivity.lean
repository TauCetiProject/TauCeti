/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Elementary coercivity lemmas

This file records small general-purpose facts about Mathlib's `IsCoercive` predicate for
continuous bilinear forms.

## Main declarations

* `IsCoercive.mono`: coercivity is preserved by pointwise increasing the diagonal of a
  bilinear form.
-/

public section

namespace TauCeti

namespace IsCoercive

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
variable {B C : E →L[ℝ] E →L[ℝ] ℝ}

/-- Coercivity is preserved by pointwise increasing the diagonal of a bilinear form. -/
theorem mono (hB : IsCoercive B) (hBC : ∀ u, B u u ≤ C u u) :
    IsCoercive C := by
  rcases hB with ⟨K, hKpos, hK⟩
  exact ⟨K, hKpos, fun u => (hK u).trans (hBC u)⟩

end IsCoercive

end TauCeti
