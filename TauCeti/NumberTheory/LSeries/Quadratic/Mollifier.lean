/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Mollifier
public import TauCeti.NumberTheory.LSeries.Quadratic.ThetaTail.Basic

/-!
# The Gaussian mollifier on the critical line

On the critical line, the norm of the truncated Mellin integrand equals the norm of the
normalized Möbius-weighted theta series divided by the scale. Thus the joint theta tail controls
the mollifier with no loss on this boundary of the strip used in three-lines interpolation.

The critical-line estimate corresponds to the mollifier bound in
`grh/src/Lib/Analytic/QuadraticTwist.lean` of lsernau/grh-lean (`72fead1`).
-/

public section

open Complex MeasureTheory Set TauCeti
open scoped ArithmeticFunction.Moebius

namespace DirichletCharacter

/-- On the critical line the Gaussian mollifier is bounded by the joint theta tail, with no
additional constant. This holds for either Gaussian weight, regardless of the character's parity. -/
theorem norm_gaussianMollifier_le_quadraticTwistGaussianThetaTailIntegral {N : ℕ}
    (χ : DirichletCharacter ℂ N) (j : Fin 2) {T : ℝ} (hT : 0 < T) {s : ℂ} (hs : s.re = 1 / 2) :
    ‖χ.gaussianMollifier j.val T⁻¹ s‖ ≤
      quadraticTwistGaussianThetaTailIntegral j (fun n ↦ χ n) T := by
  have hc (n : ℕ+) : ‖χ (n : ℕ)‖ ≤ 1 := χ.norm_le_one n
  rw [gaussianMollifier_def, quadraticTwistGaussianThetaTailIntegral_def]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_ae
    (χ.integrableOn_gaussianMollifier_integrand j.val (inv_pos.mpr hT) s).norm
    (integrableOn_quadraticTwistGaussianThetaTailIntegrand hc hT) ?_)
  filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := T⁻¹))] with t ht
  have ht₀ : 0 < t := (inv_pos.mpr hT).trans ht
  rw [norm_cpow_mul_gaussianDirichletTheta j _ s ht₀, hs]
  calc
    _ = ‖gaussianThetaSeries j (fun n ↦ χ n * (μ n : ℂ)) t‖ / t := by
      rw [norm_gaussianThetaSeries, Real.rpow_sub_one ht₀.ne', ← Real.sqrt_eq_rpow,
        div_mul_eq_mul_div]
    _ ≤ _ := div_le_div_of_nonneg_right (le_add_of_nonneg_left (norm_nonneg _)) ht₀.le

end DirichletCharacter
