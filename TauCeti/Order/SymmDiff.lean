/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.SymmDiff

/-!
# Symmetric differences of infima

In a generalized co-Heyting algebra, the symmetric difference of an infimum with an element lies
below the supremum of the symmetric differences. For sets this is the intersection member of
Mathlib's `Set.union_symmDiff_subset` family.
-/

public section

namespace TauCeti

open scoped symmDiff

variable {α : Type*} [GeneralizedCoheytingAlgebra α] {a b c : α}

/-- The symmetric difference of `a ⊓ b` with `c` lies below the supremum of the symmetric
differences of `a` and `b` with `c`. -/
theorem inf_symmDiff_le_symmDiff_sup_symmDiff : (a ⊓ b) ∆ c ≤ a ∆ c ⊔ b ∆ c := by
  rw [symmDiff_def, sdiff_inf]
  exact sup_le (le_sup_of_le_left <| le_sup_of_le_left <| sdiff_le_sdiff_right inf_le_left)
    (sup_le_sup le_sup_right le_sup_right)

end TauCeti
