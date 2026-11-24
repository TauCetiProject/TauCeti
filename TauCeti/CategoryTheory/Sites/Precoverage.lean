/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Precoverage

/-!
# Joins of precoverages

The join of two precoverages stable under base change is stable under base change.
-/

public section

namespace CategoryTheory.Precoverage

variable {C : Type*} [Category* C]

instance (J K : Precoverage C) [J.IsStableUnderBaseChange] [K.IsStableUnderBaseChange] :
    (J ⊔ K).IsStableUnderBaseChange where
  mem_coverings_of_isPullback {ι} S X f hf Y g P p₁ p₂ h := by
    rcases hf with hf | hf
    · exact Or.inl (mem_coverings_of_isPullback f hf g p₁ p₂ h)
    · exact Or.inr (mem_coverings_of_isPullback f hf g p₁ p₂ h)

end CategoryTheory.Precoverage
