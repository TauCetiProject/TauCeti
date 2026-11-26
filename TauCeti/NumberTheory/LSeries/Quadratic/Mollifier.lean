/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Mollifier
public import TauCeti.NumberTheory.LSeries.Quadratic.ThetaTail

/-!
# Bounds for the Gaussian mollifier on a vertical strip

On the critical line, the norm of the truncated Mellin integrand is exactly the norm of the
normalized Möbius-weighted theta series divided by the scale. Thus the joint theta tail controls
the mollifier with no loss at this boundary. On the full strip up to `Re s = 2`, a Gaussian
majorant gives a bound independent of the height, as needed for three-lines interpolation.

The critical-line estimate corresponds to the mollifier bound in
`grh/src/Lib/Analytic/QuadraticTwist.lean` of lsernau/grh-lean (`72fead1`).
-/

public section

open Complex MeasureTheory Set TauCeti
open scoped ArithmeticFunction.Moebius

namespace DirichletCharacter

/-- On the critical line the Gaussian mollifier is bounded by the joint theta tail, with no
additional constant. This holds for either Gaussian weight, regardless of the character's parity. -/
theorem norm_gaussianMollifier_le_thetaTail {N : ℕ} (χ : DirichletCharacter ℂ N) (j : Fin 2)
    {T : ℝ} (hT : 0 < T) {s : ℂ} (hs : s.re = 1 / 2) :
    ‖χ.gaussianMollifier j.val T⁻¹ s‖ ≤
      quadraticTwistGaussianThetaTailIntegral j (fun n ↦ χ n) T := by
  have hc (n : ℕ+) : ‖χ (n : ℕ)‖ ≤ 1 := χ.norm_le_one n
  rw [gaussianMollifier_def, quadraticTwistGaussianThetaTailIntegral_def]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_ae
    (χ.integrableOn_gaussianMollifier_integrand j.val (inv_pos.mpr hT) s).norm
    (integrableOn_quadraticTwistGaussianThetaTailIntegrand hc hT) ?_)
  filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := T⁻¹))] with t ht
  have ht₀ : 0 < t := (inv_pos.mpr hT).trans ht
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht₀, sub_re, one_re, hs,
    gaussianDirichletTheta_eq_gaussianTheta, gaussianThetaSeries_def j (fun n ↦ χ n * (μ n : ℂ)),
    norm_mul, norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hscale : t ^ ((1 / 2 : ℝ) - 1) = Real.sqrt t / t := by
    rw [Real.rpow_sub ht₀, Real.rpow_one, Real.sqrt_eq_rpow]
  rw [hscale, div_mul_eq_mul_div]
  gcongr
  exact le_add_of_nonneg_left (norm_nonneg _)

/-- A bound independent of the imaginary part, on the whole strip from `1/2` to `2`.
It is uniform in the modulus, character, and choice of Gaussian parity. -/
theorem norm_gaussianMollifier_le_of_re_mem_Icc {N : ℕ} (χ : DirichletCharacter ℂ N)
    (j : Fin 2) {r : ℝ} (hr : 0 < r) {s : ℂ} (hs : s.re ∈ Icc (1 / 2 : ℝ) 2) :
    ‖χ.gaussianMollifier j.val r s‖ ≤
      (3 * max 1 (r ^ (-(3 / 2 : ℝ)))) * Real.exp (-r) := by
  let C := 3 * max 1 (r ^ (-(3 / 2 : ℝ)))
  rw [gaussianMollifier_def, ← integral_exp_neg_Ioi, ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_ae
    (χ.integrableOn_gaussianMollifier_integrand j.val hr s).norm
    ((integrableOn_exp_neg_Ioi r).const_mul C) ?_)
  filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := r))] with t ht
  have ht₀ : 0 < t := hr.trans ht
  have hpow : t ^ (s.re - 2) ≤ max 1 (r ^ (-(3 / 2 : ℝ))) := by
    rcases le_or_gt 1 t with ht₁ | ht₁
    · exact (Real.rpow_le_one_of_one_le_of_nonpos ht₁ (by linarith [hs.2])).trans
        (le_max_left _ _)
    · have hσ : -(3 / 2 : ℝ) ≤ s.re - 2 := by linarith [hs.1]
      exact (Real.rpow_le_rpow_of_exponent_ge ht₀ ht₁.le hσ).trans
        ((Real.rpow_le_rpow_of_nonpos hr ht.le (by norm_num)).trans (le_max_right _ _))
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht₀, sub_re, one_re,
    gaussianDirichletTheta_eq_gaussianTheta]
  calc
    _ ≤ t ^ (s.re - 1) * (3 * Real.exp (-t) / t) := by
      gcongr
      exact norm_gaussianTheta_le (fun n ↦ χ.norm_mul_moebius_le_one n) ht₀
    _ = 3 * t ^ (s.re - 2) * Real.exp (-t) := by
      have he : t ^ (s.re - 2) = t ^ (s.re - 1) / t := by
        calc
          _ = t ^ ((s.re - 1) - 1) := by ring_nf
          _ = _ := by rw [Real.rpow_sub ht₀, Real.rpow_one]
      rw [he]
      ring
    _ ≤ C * Real.exp (-t) := by
      dsimp only [C]
      gcongr

end DirichletCharacter
