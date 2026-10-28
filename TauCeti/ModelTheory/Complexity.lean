/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Complexity

/-!
# Atomic formulas in subsingleton structures

In an algebraic language, every atomic formula holds in a subsingleton structure: atomic
formulas can only assert equality of terms.
-/

public section

namespace FirstOrder.Language.BoundedFormula

open FirstOrder

/-- Every atomic formula over an algebraic language holds in a subsingleton structure. -/
theorem realize_of_isAtomic_subsingleton {L : Language} [L.IsAlgebraic]
    {G α : Type*} [Subsingleton G] [L.Structure G]
    {n : ℕ} {φ : L.BoundedFormula α n} (hφ : φ.IsAtomic)
    (v : α → G) (xs : Fin n → G) : φ.Realize v xs := by
  cases hφ with
  | equal _ _ => exact Subsingleton.elim _ _
  | rel r _ => exact isEmptyElim r

end FirstOrder.Language.BoundedFormula
