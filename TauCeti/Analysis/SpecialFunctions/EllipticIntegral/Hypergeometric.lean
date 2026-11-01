/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.Analytic.Binomial
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Hypergeometric series of the complete elliptic integrals

For `|m| < 1` and every real `a`,
`∫₀^{π/2} (1 - m sin² θ)^(-a) dθ = (π/2) ₂F₁(a, 1/2; 1; m)`.
The complete elliptic integrals of the first and second kinds with modulus `k` are the cases
`a = 1/2` and `a = -1/2` at `m = k²`, giving `K(k) = (π/2) ₂F₁(1/2, 1/2; 1; k²)` and
`E(k) = (π/2) ₂F₁(-1/2, 1/2; 1; k²)` (DLMF 19.5.1, 19.5.2). As a consequence the integral is a
real-analytic function of `m` on `(-1, 1)`.

The proof expands `(1 - m sin² θ)^(-a)` by the binomial series, which converges uniformly in `θ`
for `|m| < 1`, and integrates term by term with the Wallis integrals
`∫₀^{π/2} sin²ⁿ θ dθ = (π/2) (1/2)ₙ / n!`.

## Main statements

* `TauCeti.integral_one_sub_mul_sin_sq_rpow_neg_eq_ordinaryHypergeometric`: the hypergeometric
  series of `∫₀^{π/2} (1 - m sin² θ)^(-a) dθ`.
* `TauCeti.analyticOnNhd_integral_one_sub_mul_sin_sq_rpow_neg`: this integral is analytic in `m`
  on `(-1, 1)`.

## References

* NIST *Digital Library of Mathematical Functions*, §19.5, <https://dlmf.nist.gov/19.5>.
-/

public section

open MeasureTheory Set
open scoped Nat Real

namespace TauCeti

/-- The hypergeometric series of a complete elliptic integral (DLMF 19.5.1, 19.5.2): for
`|m| < 1` and every real `a`, `∫₀^{π/2} (1 - m sin² θ)^(-a) dθ = (π/2) ₂F₁(a, 1/2; 1; m)`.
The complete integrals of the first and second kinds with modulus `k` are the cases `a = 1/2`
and `a = -1/2` at `m = k²`. -/
theorem integral_one_sub_mul_sin_sq_rpow_neg_eq_ordinaryHypergeometric {a m : ℝ}
    (hm : |m| < 1) :
    ∫ θ in (0 : ℝ)..π / 2, (1 - m * Real.sin θ ^ 2) ^ (-a) =
      π / 2 * ₂F₁ a (1 / 2) 1 m := by
  have hx (θ : ℝ) : |m * Real.sin θ ^ 2| ≤ |m| := by
    rw [abs_mul, abs_pow]
    exact mul_le_of_le_one_right (abs_nonneg m)
      (pow_le_one₀ (abs_nonneg _) (Real.abs_sin_le_one θ))
  -- the binomial series of `(1 - x) ^ (-a)` converges absolutely at `x = |m|`
  have hsum : Summable fun n : ℕ => ‖Ring.multichoose a n‖ * |m| ^ n := by
    have hmem : m ∈ Metric.eball (0 : ℝ) (FormalMultilinearSeries.ofScalars ℝ
        fun n => Ring.choose (a + n - 1) n).radius := by
      refine Metric.eball_subset_eball
        (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero a).r_le ?_
      simpa [edist_dist, Real.dist_0_eq_abs, enorm_eq_nnnorm] using hm
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, norm_smul, ← Ring.multichoose_eq,
      mul_comm] using FormalMultilinearSeries.summable_norm_apply _ hmem
  -- integrate the binomial series term by term, dominated by its absolute series at `|m|`
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence
    (F := fun n θ => Ring.multichoose a n * (m * Real.sin θ ^ 2) ^ n)
    (f := fun θ => (1 - m * Real.sin θ ^ 2) ^ (-a)) (μ := volume) (a := 0) (b := π / 2)
    (fun n _ => ‖Ring.multichoose a n‖ * |m| ^ n)
    (fun n => (by fun_prop : Continuous _).aestronglyMeasurable)
    (fun n => ae_of_all _ fun θ _ => by
      rw [norm_mul, norm_pow, Real.norm_eq_abs (m * _)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hx θ) n)
        (norm_nonneg _))
    (ae_of_all _ fun _ _ => hsum)
    intervalIntegrable_const
    (ae_of_all _ fun θ _ => by
      have h := hasSum_multichoose_mul_geometric_of_abs_lt_one (r := a) ((hx θ).trans_lt hm)
      have h0 : 0 ≤ 1 - m * Real.sin θ ^ 2 := by
        linarith [(le_abs_self _).trans ((hx θ).trans hm.le)]
      rwa [one_div, ← Real.rpow_neg h0] at h)
  -- identify the termwise integrals with the hypergeometric terms
  have hc (n : ℕ) : Ring.multichoose a n = (ascPochhammer ℝ n).eval a / n ! := by
    have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer a n
    rw [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval] at h
    rw [← h]
    field_simp
  rw [← key.tsum_eq, ordinaryHypergeometric_eq_tsum, ← tsum_mul_left]
  congr 1
  ext n
  simp_rw [mul_pow, ← pow_mul]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_sin_pow_even_eq_ascPochhammer, hc, ascPochhammer_eval_one, smul_eq_mul]
  field_simp

/-- For every real `a`, the integral `∫₀^{π/2} (1 - m sin² θ)^(-a) dθ` is a real-analytic function
of `m` on `(-1, 1)`. For `a = ±1/2` this is the analyticity of the complete elliptic integrals of
the first and second kinds in the parameter `m = k²`. -/
theorem analyticOnNhd_integral_one_sub_mul_sin_sq_rpow_neg (a : ℝ) :
    AnalyticOnNhd ℝ (fun m : ℝ => ∫ θ in (0 : ℝ)..π / 2, (1 - m * Real.sin θ ^ 2) ^ (-a))
      (Ioo (-1) 1) := by
  intro m hm
  have hF := analyticOnNhd_ordinaryHypergeometric ℝ a (1 / 2) 1 m
    (by simpa [Real.dist_0_eq_abs, abs_lt] using hm)
  refine ((analyticAt_const (v := π / 2)).mul hF).congr ?_
  filter_upwards [isOpen_Ioo.mem_nhds hm] with x hx
  exact (integral_one_sub_mul_sin_sq_rpow_neg_eq_ordinaryHypergeometric (abs_lt.mpr hx)).symm

end TauCeti
