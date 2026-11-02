/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Rational identities under inversion

These identities use the field's total inverse, so they hold also at zero and one. In a division
ring, a nonzero `a` is separated from its inverse unless it is a square root of `1`:
`a - a⁻¹` vanishes exactly when `a ^ 2 = 1` (`TauCeti.sub_inv_eq_zero_iff`). Two square roots
`x`, `u` of `-1` in a division ring are conjugate by the unit `1 - u * x` unless `u = -x`, that is
unless `u * x = 1` (`TauCeti.exists_unit_conj_of_mul_ne_one`).
-/

public section

namespace TauCeti

/-- **A nonzero element is separated from its inverse unless it squares to `1`**: in a division
ring, `a - a⁻¹` vanishes at a nonzero `a` exactly when `a ^ 2 = 1`. -/
theorem sub_inv_eq_zero_iff {K : Type*} [DivisionRing K] {a : K} (ha : a ≠ 0) :
    a - a⁻¹ = 0 ↔ a ^ 2 = 1 := by
  rw [sub_eq_zero, ← mul_eq_one_iff_eq_inv₀ ha, sq]

/-- **Two square roots of `-1` in a division ring that are not negatives of one another are
conjugate.** The conjugating element is `1 - u * x`: it satisfies
`u * (1 - u * x) = (1 - u * x) * x`, both sides being `x + u`, and it is nonzero exactly by the
hypothesis `u * x ≠ 1`, which says `u ≠ -x` because `x⁻¹ = -x`. -/
theorem exists_unit_conj_of_mul_ne_one {D : Type*} [DivisionRing D] {x u : D} (hx : x * x = -1)
    (hu : u * u = -1) (h : u * x ≠ 1) :
    ∃ w : Dˣ, u = (w : D) * x * ((w⁻¹ : Dˣ) : D) := by
  refine ⟨Units.mk0 _ (sub_ne_zero.2 (Ne.symm h)), (Units.eq_mul_inv_iff_mul_eq _).2 ?_⟩
  rw [Units.val_mk0, sub_mul, mul_sub, mul_assoc, hx, ← mul_assoc, hu]
  simp [add_comm]

variable {K : Type*} [Field K]

/-- Inversion preserves the rational function `x / (1 - x)²`, including at zero and one. -/
theorem inv_div_one_sub_inv_sq (x : K) :
    x⁻¹ / (1 - x⁻¹) ^ 2 = x / (1 - x) ^ 2 := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases h : x = 1
  · simp [h]
  · field_simp
    ring

/-- Inverting the argument of `x² / (1 - x)³` gives `-x / (1 - x)³`. -/
theorem inv_sq_div_one_sub_inv_cube (x : K) :
    (x⁻¹) ^ 2 / (1 - x⁻¹) ^ 3 = -x / (1 - x) ^ 3 := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases h : x = 1
  · simp [h]
  · field_simp [hx, sub_ne_zero.mpr h, sub_ne_zero.mpr (Ne.symm h)]
    ring

/-- The inverted cubic-denominator expression splits into two rational summands. -/
theorem inv_sq_div_one_sub_inv_cube_eq_neg_sub (x : K) :
    (x⁻¹) ^ 2 / (1 - x⁻¹) ^ 3 = -(x ^ 2 / (1 - x) ^ 3) - x / (1 - x) ^ 2 := by
  rw [inv_sq_div_one_sub_inv_cube]
  by_cases h : x = 1
  · simp [h]
  · field_simp
    ring

end TauCeti

end
