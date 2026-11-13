/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Curvature.Basic

/-!
# Logarithmic derivatives of constant-curvature model functions

The ratio `curvatureCotangent κ = curvatureCosine κ / curvatureSine κ` of the constant-curvature
model functions solves the scalar Riccati equation `f' = -f² - κ` on its regular domain. Its
singular initial asymptotic is `t * curvatureCotangent κ t → 1`. It is positive before the
spherical half-radius, and at all positive times in nonpositive curvature. These are the
scalar-model inputs to local Hessian comparison.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 11.
-/

public noncomputable section
namespace TauCeti
open Filter Real Set
open scoped ContDiff Topology

/-- The logarithmic derivative `s_κ' / s_κ` of the constant-curvature model sine. -/
def curvatureCotangent (κ t : ℝ) : ℝ := curvatureCosine κ t / curvatureSine κ t

/-- Evaluation of the model logarithmic derivative. -/
theorem curvatureCotangent_def (κ t : ℝ) :
    curvatureCotangent κ t = curvatureCosine κ t / curvatureSine κ t := by rfl

@[simp] theorem curvatureCotangent_zero_left (t : ℝ) : curvatureCotangent 0 t = t⁻¹ := by
  simp [curvatureCotangent_def, one_div]

@[simp] theorem curvatureCotangent_zero_right (κ : ℝ) : curvatureCotangent κ 0 = 0 := by
  simp [curvatureCotangent_def]

/-- The scalar Riccati equation wherever the model sine is nonzero. -/
theorem hasDerivAt_curvatureCotangent {κ t : ℝ} (ht : curvatureSine κ t ≠ 0) :
    HasDerivAt (curvatureCotangent κ) (-curvatureCotangent κ t ^ 2 - κ) t := by
  apply ((hasDerivAt_curvatureCosine κ t).div (hasDerivAt_curvatureSine κ t) ht).congr_deriv
  rw [curvatureCotangent_def]
  field_simp
  ring

/-- Ordinary derivative form of the model Riccati equation. -/
@[simp] theorem deriv_curvatureCotangent {κ t : ℝ} (ht : curvatureSine κ t ≠ 0) :
    deriv (curvatureCotangent κ) t = -curvatureCotangent κ t ^ 2 - κ :=
  (hasDerivAt_curvatureCotangent ht).deriv

/-- The rescaled model logarithmic derivative tends to one at its singular origin. -/
theorem tendsto_mul_curvatureCotangent_zero (κ : ℝ) :
    Tendsto (fun t ↦ t * curvatureCotangent κ t) (𝓝[≠] 0) (𝓝 1) := by
  have hs := tendsto_curvatureSine_div_zero κ
  have hc : Tendsto (curvatureCosine κ) (𝓝[≠] 0) (𝓝 1) := by
    simpa only [curvatureCosine_zero_right] using
      (contDiff_curvatureCosine κ).continuous.continuousAt (x := 0) |>.tendsto.mono_left
        nhdsWithin_le_nhds
  convert hc.div hs one_ne_zero using 1
  · ext t
    rw [curvatureCotangent_def, Pi.div_apply, div_div_eq_mul_div]
    ring
  · norm_num

/-- The model logarithmic derivative is positive in the squared-distance convexity range. -/
theorem curvatureCotangent_pos {κ t : ℝ} (ht : 0 < t)
    (hbound : 0 < κ → t < π / (2 * √κ)) : 0 < curvatureCotangent κ t := by
  rw [curvatureCotangent_def]
  apply div_pos (curvatureCosine_pos ht.le hbound) (curvatureSine_pos ht ?_)
  intro hκ
  apply (hbound hκ).trans
  rw [← div_div]
  exact (div_lt_div_iff_of_pos_right (sqrt_pos.mpr hκ)).mpr (by linarith [pi_pos])

/-- In positive curvature the logarithmic derivative is the rescaled cotangent. -/
theorem curvatureCotangent_of_pos {κ : ℝ} (hκ : 0 < κ) (t : ℝ) :
    curvatureCotangent κ t = √κ * Real.cot (√κ * t) := by
  rw [curvatureCotangent_def, curvatureCosine_of_pos hκ,
    curvatureSine_of_pos hκ, Real.cot_eq_cos_div_sin, div_div_eq_mul_div]
  ring

/-- In negative curvature the logarithmic derivative is the rescaled hyperbolic cotangent. -/
theorem curvatureCotangent_of_neg {κ : ℝ} (hκ : κ < 0) (t : ℝ) :
    curvatureCotangent κ t = √(-κ) * (cosh (√(-κ) * t) / sinh (√(-κ) * t)) := by
  rw [curvatureCotangent_def, curvatureCosine_of_neg hκ,
    curvatureSine_of_neg hκ, div_div_eq_mul_div]
  ring

/-- The model logarithmic derivative is smooth on its regular domain. -/
theorem contDiffOn_curvatureCotangent (κ : ℝ) :
    ContDiffOn ℝ ∞ (curvatureCotangent κ) {t | curvatureSine κ t ≠ 0} := by
  exact (contDiff_curvatureCosine κ).contDiffOn.div
    (contDiff_curvatureSine κ).contDiffOn (fun _ ht ↦ ht)

/-- The Riccati equation holds at every positive time before the first model zero. -/
theorem hasDerivAt_curvatureCotangent_of_pos {κ t : ℝ} (ht : 0 < t)
    (hbound : 0 < κ → t < π / √κ) :
    HasDerivAt (curvatureCotangent κ) (-curvatureCotangent κ t ^ 2 - κ) t :=
  hasDerivAt_curvatureCotangent (curvatureSine_pos ht hbound).ne'

end TauCeti
