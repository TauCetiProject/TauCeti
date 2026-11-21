/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Hyperbolic.Bounds
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Curvature.Cotangent
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Comparing the model cotangent with the linear-profile trace

For negative curvature and positive radius, the model cotangent is strictly smaller than the
reciprocal radius minus one third of curvature times radius. This compares the exact matched
and linear profile traces in constant negative curvature. The nonstrict bound holds for
nonpositive curvature and nonnegative radius, with equality exactly when curvature or radius
vanishes. Multiplying the strict inequality by a dimension-minus-one factor requires that
factor to be positive.
-/

public noncomputable section

namespace TauCeti

/-- At positive radius in negative curvature, the matched model trace is strictly smaller
than the linear-profile expression. -/
theorem curvatureCotangent_lt_inv_sub_mul_div_three {κ r : ℝ} (hκ : κ < 0) (hr : 0 < r) :
    curvatureCotangent κ r < r⁻¹ - κ * r / 3 := by
  let a := Real.sqrt (-κ)
  have ha : 0 < a := Real.sqrt_pos.mpr (neg_pos.mpr hκ)
  have hs : a ^ 2 = -κ := Real.sq_sqrt (neg_nonneg.mpr hκ.le)
  have hi : a * (a * r)⁻¹ = r⁻¹ := by field_simp [ha.ne', hr.ne']
  rw [curvatureCotangent_of_neg hκ]
  change a * (Real.cosh (a * r) / Real.sinh (a * r)) < _
  calc
    _ < a * ((a * r)⁻¹ + (a * r) / 3) :=
      mul_lt_mul_of_pos_left (Real.cosh_div_sinh_lt_inv_add_div_three (mul_pos ha hr)) ha
    _ = r⁻¹ - κ * r / 3 := by
      rw [mul_add, hi, ← mul_div_assoc, ← mul_assoc, ← sq, hs]
      ring

/-- The linear-profile expression bounds the model cotangent for nonpositive curvature and
nonnegative radius, including their totalized values at radius zero. -/
theorem curvatureCotangent_le_inv_sub_mul_div_three {κ r : ℝ} (hκ : κ ≤ 0) (hr : 0 ≤ r) :
    curvatureCotangent κ r ≤ r⁻¹ - κ * r / 3 := by
  rcases hr.eq_or_lt with rfl | hr
  · simp
  rcases hκ.lt_or_eq with hκ | rfl
  · exact (curvatureCotangent_lt_inv_sub_mul_div_three hκ hr).le
  · simp

/-- Equality in the nonpositive-curvature linear-profile bound occurs exactly at zero
curvature or zero radius. -/
theorem curvatureCotangent_eq_inv_sub_mul_div_three_iff {κ r : ℝ}
    (hκ : κ ≤ 0) (hr : 0 ≤ r) :
    curvatureCotangent κ r = r⁻¹ - κ * r / 3 ↔ κ = 0 ∨ r = 0 := by
  constructor
  · intro heq
    by_cases hk : κ = 0
    · exact Or.inl hk
    right
    by_contra hrne
    have hklt : κ < 0 := lt_of_le_of_ne hκ hk
    have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hrne)
    exact (curvatureCotangent_lt_inv_sub_mul_div_three hklt hrpos).ne heq
  · rintro (rfl | rfl) <;> simp

end TauCeti
