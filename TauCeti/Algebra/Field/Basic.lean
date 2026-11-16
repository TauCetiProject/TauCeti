/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Basic
import Mathlib.RingTheory.SimpleRing.Field
import Mathlib.Tactic.Abel

/-!
# Rational identities under inversion

The rational identities in `x` hold in any division ring, since `x` commutes with `1 - x` and
with the inverses of both. They use the total inverse, so they hold also at zero and one. In a
division ring, a nonzero `a` is separated from its inverse unless it is a square root of `1`:
`a - a⁻¹` vanishes exactly when `a ^ 2 = 1` (`TauCeti.sub_inv_eq_zero_iff`). Two square roots
`x`, `u` of `-1` in a division ring are conjugate by the unit `1 - u * x` unless `u = -x`, that is
unless `u * x = 1` (`TauCeti.exists_unit_conj_of_mul_ne_one`). The rational functions
`x / (1 - x)²`, `x² / (1 - x)³` and `x / (1 - x)³` of the Tate coordinates satisfy the linear
relation `TauCeti.div_one_sub_sq_add_sq_div_one_sub_cube`. A square root in a field extension of a
non-square of the base field does not lie in the base field
(`TauCeti.notMem_range_algebraMap_of_sq_eq_of_not_isSquare`).
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

/-- A square root in an extension field of an element that is not a square in `K` does not lie
in `K`. -/
theorem notMem_range_algebraMap_of_sq_eq_of_not_isSquare {K L : Type*} [Field K] [Field L]
    [Algebra K L] {u : K} (hsq : ¬IsSquare u) {x : L} (hx2 : x ^ 2 = algebraMap K L u) :
    x ∉ Set.range (algebraMap K L) := by
  rintro ⟨y, rfl⟩
  rw [← map_pow, (algebraMap K L).injective.eq_iff] at hx2
  exact hsq ⟨y, by simpa only [sq] using hx2.symm⟩

variable {K : Type*} [DivisionRing K]

/-- Inversion preserves the rational function `x / (1 - x)²`, including at zero and one. -/
theorem inv_div_one_sub_inv_sq (x : K) :
    x⁻¹ / (1 - x⁻¹) ^ 2 = x / (1 - x) ^ 2 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h : 1 - x⁻¹ = -((1 - x) * x⁻¹) := by
    rw [← neg_mul, neg_sub, sub_mul, mul_inv_cancel₀ hx, one_mul]
  have hc : Commute (1 - x)⁻¹ x := ((Commute.one_left x).sub_left (.refl x)).inv_left₀
  simp [h, div_eq_mul_inv, mul_inv_rev, sq, mul_assoc, hx, hc.left_comm]

/-- Inverting the argument of `x² / (1 - x)³` gives `-x / (1 - x)³`. -/
theorem inv_sq_div_one_sub_inv_cube (x : K) :
    (x⁻¹) ^ 2 / (1 - x⁻¹) ^ 3 = -x / (1 - x) ^ 3 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h : 1 - x⁻¹ = -((1 - x) * x⁻¹) := by
    rw [← neg_mul, neg_sub, sub_mul, mul_inv_cancel₀ hx, one_mul]
  have hc : Commute (1 - x)⁻¹ x := ((Commute.one_left x).sub_left (.refl x)).inv_left₀
  simp [h, div_eq_mul_inv, mul_inv_rev, pow_succ, mul_assoc, hx, hc.left_comm]

/-- The rational functions `x / (1 - x)²` and `x² / (1 - x)³` add up to `x / (1 - x)³`, including
at one. -/
theorem div_one_sub_sq_add_sq_div_one_sub_cube (x : K) :
    x / (1 - x) ^ 2 + x ^ 2 / (1 - x) ^ 3 = x / (1 - x) ^ 3 := by
  rcases eq_or_ne (1 - x) 0 with h | h
  · simp [h]
  have hx : x / (1 - x) ^ 2 = x * (1 - x) / (1 - x) ^ 3 := by
    rw [pow_succ _ 2, mul_div_mul_right _ _ h]
  rw [hx, ← add_div, mul_one_sub, sq, sub_add_cancel]

/-- The inverted cubic-denominator expression splits into two rational summands. -/
theorem inv_sq_div_one_sub_inv_cube_eq_neg_sub (x : K) :
    (x⁻¹) ^ 2 / (1 - x⁻¹) ^ 3 = -(x ^ 2 / (1 - x) ^ 3) - x / (1 - x) ^ 2 := by
  rw [inv_sq_div_one_sub_inv_cube, neg_div, ← div_one_sub_sq_add_sq_div_one_sub_cube]
  abel

end TauCeti

end
