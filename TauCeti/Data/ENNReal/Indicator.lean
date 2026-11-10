/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Algebra.Order.Group.Indicator

/-!
# Positive-level indicator approximations in `ℝ≥0∞`

Restricting an extended nonnegative function to the sets where it is at least `1 / (n + 1)`
gives a monotone sequence with supremum equal to the original function. No measurability
hypothesis is needed.

## Main declarations

* `ENNReal.monotone_indicator_inv_natCast_add_one_le`: the level-set restrictions are monotone.
* `ENNReal.iSup_indicator_inv_natCast_add_one_le_eq_self`: their supremum is the original function.
-/

public section

open scoped ENNReal

namespace ENNReal

/-- Restricting a nonnegative function to the levels above `1 / (n + 1)` is monotone in `n`. -/
theorem monotone_indicator_inv_natCast_add_one_le {X : Type*} (f : X → ℝ≥0∞) :
    Monotone (fun n : ℕ => {x | (n + 1 : ℝ≥0∞)⁻¹ ≤ f x}.indicator f) := by
  intro m n hmn
  exact Set.indicator_le_indicator_of_subset
    (fun x hx => (ENNReal.inv_le_inv.mpr (by exact_mod_cast Nat.add_le_add_right hmn 1)).trans hx)
    (fun _ => bot_le)

/-- The restrictions to the levels above `1 / (n + 1)` exhaust any nonnegative function. -/
theorem iSup_indicator_inv_natCast_add_one_le_eq_self {X : Type*} (f : X → ℝ≥0∞) :
    (fun x => ⨆ n : ℕ, {x | (n + 1 : ℝ≥0∞)⁻¹ ≤ f x}.indicator f x) = f := by
  classical
  funext x
  apply le_antisymm
  · exact iSup_le fun n => Set.indicator_le_self _ f x
  · by_cases hx : f x = 0
    · simp [hx]
    obtain ⟨n, hn⟩ := exists_inv_nat_lt hx
    have hxn : (n + 1 : ℝ≥0∞)⁻¹ ≤ f x :=
      (ENNReal.inv_le_inv.mpr (le_add_of_nonneg_right zero_le)).trans hn.le
    exact le_iSup_of_le n (by simp [hxn])

end ENNReal
