/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Dilation scaling of the lower Lebesgue integral

Dilating the variable of a function on a finite-dimensional real normed space `E` by a nonzero
scalar `r` rescales its integral against an additive Haar measure by `|(r ^ n)⁻¹|`, where `n` is
the dimension of `E`. Mathlib records this for the Bochner integral as
`MeasureTheory.Measure.integral_comp_smul`; this file is the lower-Lebesgue-integral counterpart,
proved the same way from `MeasureTheory.Measure.map_addHaar_smul`, and, like the Bochner version,
needing no integrability hypothesis.

## Main declarations

* `TauCeti.lintegral_comp_smul`: `∫⁻ x, g (r • x) ∂μ = |(r ^ n)⁻¹| * ∫⁻ x, g x ∂μ`.
* `TauCeti.lintegral_comp_inv_smul`: the same law written for `r⁻¹` and `0 < r`.
* `TauCeti.lintegral_comp_homothety`: the same law for the homothety of ratio `r` about any
  centre.
* `TauCeti.lintegral_comp_add_smul_sub_mul_ite`: the change of variables for a homothety with a
  radial cutoff and weight.
-/

public section

namespace TauCeti

open MeasureTheory Module
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **Dilation scaling of the lower Lebesgue integral.** This is the counterpart, for `∫⁻`, of
Mathlib's `MeasureTheory.Measure.integral_comp_smul`; as there, no integrability of `g` is
needed. -/
theorem lintegral_comp_smul (g : E → ℝ≥0∞) {r : ℝ} (hr : r ≠ 0) :
    ∫⁻ x, g (r • x) ∂μ = ENNReal.ofReal |(r ^ finrank ℝ E)⁻¹| * ∫⁻ x, g x ∂μ := by
  calc ∫⁻ x, g (r • x) ∂μ = ∫⁻ y, g y ∂Measure.map (fun x => r • x) μ :=
        (lintegral_map_equiv g
          (Homeomorph.smul (isUnit_iff_ne_zero.2 hr).unit).toMeasurableEquiv).symm
    _ = ENNReal.ofReal |(r ^ finrank ℝ E)⁻¹| * ∫⁻ x, g x ∂μ := by
        rw [Measure.map_addHaar_smul μ hr, lintegral_smul_measure, smul_eq_mul]

/-- Dilating the variable by `r⁻¹`, for `0 < r`, multiplies a lower Lebesgue integral by
`r ^ n`, where `n` is the dimension of the ambient space. -/
theorem lintegral_comp_inv_smul (g : E → ℝ≥0∞) {r : ℝ} (hr : 0 < r) :
    ∫⁻ x, g (r⁻¹ • x) ∂μ = ENNReal.ofReal (r ^ finrank ℝ E) * ∫⁻ x, g x ∂μ := by
  rw [lintegral_comp_smul μ g (inv_ne_zero hr.ne'), inv_pow, inv_inv,
    abs_of_nonneg (by positivity)]

/-- **Homothety scaling of the lower Lebesgue integral.** Precomposing with the homothety of
ratio `r ≠ 0` about any centre `x` rescales a lower Lebesgue integral against an additive Haar
measure by `|(r ^ n)⁻¹|`, where `n` is the dimension of the ambient space. -/
theorem lintegral_comp_homothety (g : E → ℝ≥0∞) (x : E) {r : ℝ} (hr : r ≠ 0) :
    ∫⁻ y, g (AffineMap.homothety x r y) ∂μ =
      ENNReal.ofReal |(r ^ finrank ℝ E)⁻¹| * ∫⁻ y, g y ∂μ := by
  simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
  rw [lintegral_sub_right_eq_self (fun z => g (r • z + x)) x,
    lintegral_comp_smul μ (fun z => g (z + x)) hr, lintegral_add_right_eq_self]

/-- The substitution `w = x + t • (y - x)`, of Jacobian `t ^ n`, in the integral over
`y ∈ closedBall x D` of `g` at the point of parameter `t` on the segment from `x` to `y`,
weighted by the length of the segment. -/
theorem lintegral_comp_add_smul_sub_mul_ite (g : E → ℝ≥0∞) (x : E) (D : ℝ) {t : ℝ}
    (ht : 0 < t) :
    ∫⁻ y, g (x + t • (y - x)) * (if ‖x - y‖ ≤ D then ENNReal.ofReal ‖x - y‖ else 0) ∂μ =
      ∫⁻ w, ENNReal.ofReal (t ^ (-(finrank ℝ E : ℝ) - 1)) *
        (g w * if ‖x - w‖ ≤ t * D then ENNReal.ofReal ‖x - w‖ else 0) ∂μ := by
  set f : E → ℝ≥0∞ := fun w =>
    g w * if ‖x - w‖ ≤ t * D then ENNReal.ofReal ‖x - w‖ else 0
  have hKf : ∀ y, g (x + t • (y - x)) *
      (if ‖x - y‖ ≤ D then ENNReal.ofReal ‖x - y‖ else 0) =
      ENNReal.ofReal t⁻¹ * f (AffineMap.homothety x t y) := by
    intro y
    have hw : AffineMap.homothety x t y = x + t • (y - x) := by
      rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, add_comm]
    have hnorm : ‖x - (x + t • (y - x))‖ = t * ‖x - y‖ := by
      rw [sub_add_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg ht.le, norm_sub_rev]
    simp only [f, hw, hnorm, mul_le_mul_iff_right₀ ht]
    split_ifs
    · have h1 : ENNReal.ofReal t⁻¹ * ENNReal.ofReal t = 1 := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 ht.le), inv_mul_cancel₀ ht.ne',
          ENNReal.ofReal_one]
      rw [ENNReal.ofReal_mul ht.le]
      calc
        _ = ENNReal.ofReal t⁻¹ * ENNReal.ofReal t * (g (x + t • (y - x)) *
            ENNReal.ofReal ‖x - y‖) := by rw [h1, one_mul]
        _ = _ := by ring
    · simp
  calc
    _ = ∫⁻ y, ENNReal.ofReal t⁻¹ * f (AffineMap.homothety x t y) ∂μ := lintegral_congr hKf
    _ = ENNReal.ofReal t⁻¹ * (ENNReal.ofReal |(t ^ finrank ℝ E)⁻¹| * ∫⁻ w, f w ∂μ) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_comp_homothety μ f x ht.ne']
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
        ← ENNReal.ofReal_mul (inv_nonneg.2 ht.le)]
      congr 2
      rw [abs_of_nonneg (by positivity), Real.rpow_sub ht, Real.rpow_neg ht.le,
        Real.rpow_natCast, Real.rpow_one, div_eq_mul_inv, mul_comm]

end TauCeti
