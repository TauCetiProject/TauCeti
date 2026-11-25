/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Otis Chodosh, The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Curvature.Cotangent
import TauCeti.Analysis.SpecialFunctions.Hyperbolic.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Bounds for the nonpositive-curvature model cotangent

For nonpositive curvature, the model cotangent is at most the sum of the square root of
minus the curvature and the reciprocal of the radial parameter. At positive radii this
turns the model Laplacian comparison into an elementary bound. The inequality also holds
at negative parameters and at the totalized value at zero.

The linear-profile comparison bounds the model cotangent by the reciprocal radius minus
one third of curvature times radius, for nonpositive curvature and nonnegative radius.
It is strict for negative curvature and positive radius. These are contributions per
transverse direction: multiplying by `n - 1` gives the full distance-support trace
comparison, which is strict only when `n > 1`. For nonpositive curvature and any signed
radius, the model cotangent equals the linear-profile expression exactly when curvature
or radius vanishes.

The elementary hyperbolic estimate follows from `1 + 2x ≤ exp (2x)`.

Adapted from Otis Chodosh's formalization in
`ForTauCeti/Analysis/SpecialFunctions/Trigonometric/Curvature/Bounds.lean` in
[ColdingMinicozziTheory][source].

The linear-profile comparison is adapted from Otis Chodosh's formalization in
`ForTauCeti/Analysis/SpecialFunctions/Trigonometric/Curvature/LinearBound.lean` in
[ColdingMinicozziTheory][linear-source].

[linear-source]: https://github.com/riccardobrasca/ColdingMinicozziTheory/blob/fe6fa284d9cc53f70c80ba9c9be619cb13ab1b89/ForTauCeti/Analysis/SpecialFunctions/Trigonometric/Curvature/LinearBound.lean
[source]: https://github.com/riccardobrasca/ColdingMinicozziTheory/blob/6966e539d9352a70e8cdeb9596f6cc098b2a18cb/ForTauCeti/Analysis/SpecialFunctions/Trigonometric/Curvature/Bounds.lean
-/

public noncomputable section

namespace TauCeti

/-- An elementary upper bound for the model cotangent in nonpositive curvature. -/
theorem curvatureCotangent_le_sqrt_neg_add_inv {κ : ℝ} (hκ : κ ≤ 0) (r : ℝ) :
    curvatureCotangent κ r ≤ Real.sqrt (-κ) + r⁻¹ := by
  rcases hκ.lt_or_eq with hneg | rfl
  · rw [curvatureCotangent_of_neg hneg]
    let a := Real.sqrt (-κ)
    have ha : 0 < a := Real.sqrt_pos.mpr (neg_pos.mpr hneg)
    by_cases hr : r = 0
    · simp [hr]
    have hs : Real.sinh (a * r) ≠ 0 := Real.sinh_ne_zero.mpr (mul_ne_zero ha.ne' hr)
    have hrs : 0 < r * Real.sinh (a * r) := by
      rcases lt_or_gt_of_ne hr with hrneg | hrpos
      · exact mul_pos_of_neg_of_neg hrneg
          (Real.sinh_neg_iff.mpr (mul_neg_of_pos_of_neg ha hrneg))
      · exact mul_pos hrpos (Real.sinh_pos_iff.mpr (mul_pos ha hrpos))
    have he := mul_le_mul_of_nonneg_right
      (Real.add_one_le_exp (2 * (a * r))) (Real.exp_pos (-(a * r))).le
    have hcancel : Real.exp (2 * (a * r)) * Real.exp (-(a * r)) = Real.exp (a * r) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hcancel] at he
    have hhyper : (a * r) * Real.cosh (a * r) ≤
        (1 + a * r) * Real.sinh (a * r) := by
      rw [Real.cosh_eq, Real.sinh_eq]
      nlinarith
    -- Fold the local abbreviation `a` so denominator clearing matches `hhyper` below.
    change a * (Real.cosh (a * r) / Real.sinh (a * r)) ≤ a + r⁻¹
    apply (mul_le_mul_iff_left₀ hrs).mp
    calc
      a * (Real.cosh (a * r) / Real.sinh (a * r)) * (r * Real.sinh (a * r)) =
          (a * r) * Real.cosh (a * r) := by field_simp
      _ ≤ (1 + a * r) * Real.sinh (a * r) := hhyper
      _ = (a + r⁻¹) * (r * Real.sinh (a * r)) := by field_simp; ring
  · simp

/-- At positive radius in negative curvature, the model cotangent is strictly smaller
than the linear-profile contribution per transverse direction. -/
theorem curvatureCotangent_lt_inv_sub_mul_div_three {κ r : ℝ} (hκ : κ < 0) (hr : 0 < r) :
    curvatureCotangent κ r < r⁻¹ - κ * r / 3 := by
  rw [curvatureCotangent_of_neg hκ]
  set a := Real.sqrt (-κ)
  have ha : 0 < a := Real.sqrt_pos.mpr (neg_pos.mpr hκ)
  have hs : a ^ 2 = -κ := Real.sq_sqrt (neg_nonneg.mpr hκ.le)
  have hi : a * (a * r)⁻¹ = r⁻¹ := by rw [mul_inv, mul_inv_cancel_left₀ ha.ne']
  calc
    _ < a * ((a * r)⁻¹ + (a * r) / 3) :=
      mul_lt_mul_of_pos_left (Real.cosh_div_sinh_lt_inv_add_div_three (mul_pos ha hr)) ha
    _ = r⁻¹ - κ * r / 3 := by
      rw [mul_add, hi]
      linear_combination (r / 3) * hs

/-- The linear-profile expression bounds the model cotangent for nonpositive curvature and
nonnegative radius, including their totalized values at radius zero. -/
theorem curvatureCotangent_le_inv_sub_mul_div_three {κ r : ℝ} (hκ : κ ≤ 0) (hr : 0 ≤ r) :
    curvatureCotangent κ r ≤ r⁻¹ - κ * r / 3 := by
  rcases hr.eq_or_lt with rfl | hr
  · simp
  rcases hκ.lt_or_eq with hκ | rfl
  · exact (curvatureCotangent_lt_inv_sub_mul_div_three hκ hr).le
  · simp

/-- For nonpositive curvature and any signed radius, the model cotangent equals the
linear-profile expression exactly when curvature or radius vanishes. -/
@[simp] theorem curvatureCotangent_eq_inv_sub_mul_div_three_iff {κ r : ℝ}
    (hκ : κ ≤ 0) :
    curvatureCotangent κ r = r⁻¹ - κ * r / 3 ↔ κ = 0 ∨ r = 0 := by
  constructor
  · intro heq
    by_cases hk : κ = 0
    · exact Or.inl hk
    right
    by_contra hrne
    have hklt : κ < 0 := lt_of_le_of_ne hκ hk
    rcases lt_or_gt_of_ne hrne with hrneg | hrpos
    · have h := curvatureCotangent_lt_inv_sub_mul_div_three hklt (neg_pos.mpr hrneg)
      rw [curvatureCotangent_neg, inv_neg, mul_neg, neg_div] at h
      linarith
    · exact (curvatureCotangent_lt_inv_sub_mul_div_three hklt hrpos).ne heq
  · rintro (rfl | rfl) <;> simp

end TauCeti
