/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Ordinary.Basic
public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Legendre
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

Subtracting the two series term by term gives
`D(k) = (K(k) - E(k))/k² = (π/4) ₂F₁(1/2, 3/2; 2; k²)` for `0 < k² < 1` (DLMF 15.9.26).

## Main statements

* `TauCeti.integral_one_sub_mul_sin_sq_rpow_neg_eq_ordinaryHypergeometric`: the hypergeometric
  series of `∫₀^{π/2} (1 - m sin² θ)^(-a) dθ`.
* `TauCeti.analyticOnNhd_integral_one_sub_mul_sin_sq_rpow_neg`: this integral is analytic in `m`
  on `(-1, 1)`.
* `TauCeti.Real.legendreK_eq_ordinaryHypergeometric` and
  `TauCeti.Real.legendreEc_eq_ordinaryHypergeometric`: the series formulas in the modulus `k`.
* `TauCeti.Real.legendreD_eq_ordinaryHypergeometric`: the series formula for
  `D(k) = (K(k) - E(k))/k²`.
* `TauCeti.Real.analyticOnNhd_legendreK` and `TauCeti.Real.analyticOnNhd_legendreEc`:
  analyticity in the modulus on `(-1, 1)`, for use in higher differential identities.

## References

* NIST *Digital Library of Mathematical Functions*, §19.5, <https://dlmf.nist.gov/19.5>.
* NIST *Digital Library of Mathematical Functions*, §15.9(iii), <https://dlmf.nist.gov/15.9.iii>.
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
      simpa [edist_dist, Real.dist_0_eq_abs, eNorm_eq_nnNorm] using hm
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
  rw [← key.tsum_eq, ordinaryHypergeometric_eq_tsum, ← tsum_mul_left]
  congr 1
  ext n
  simp_rw [mul_pow, ← pow_mul]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_sin_pow_even_eq_ascPochhammer,
    Ring.multichoose_eq_inv_factorial_mul_eval_ascPochhammer, ascPochhammer_eval_one, smul_eq_mul]
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

/-- For every real `a`, the integral `∫₀^{π/2} (1 - k² sin² θ)^(-a) dθ` is real analytic
in the modulus `k` on `(-1, 1)`. -/
theorem analyticOnNhd_integral_one_sub_sq_mul_sin_sq_rpow_neg (a : ℝ) :
    AnalyticOnNhd ℝ (fun k : ℝ => ∫ θ in (0 : ℝ)..π / 2,
      (1 - k ^ 2 * Real.sin θ ^ 2) ^ (-a)) (Ioo (-1) 1) := by
  intro k hk
  have hsq : k ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one k).mpr (abs_lt.mpr hk)
  have h := analyticOnNhd_integral_one_sub_mul_sin_sq_rpow_neg a
    (k ^ 2) ⟨by linarith [sq_nonneg k], hsq⟩
  simpa only [Function.comp_def] using
    h.comp (f := fun x : ℝ => x ^ 2) (by fun_prop : AnalyticAt ℝ (fun x : ℝ => x ^ 2) k)

namespace Real

/-- The complete elliptic integral of the first kind is a hypergeometric function of the
squared modulus (DLMF 19.5.1). -/
theorem legendreK_eq_ordinaryHypergeometric {k : ℝ} (hk : k ^ 2 < 1) :
    legendreK k = π / 2 * ₂F₁ (1 / 2 : ℝ) (1 / 2) 1 (k ^ 2) := by
  simpa only [legendreK_def, legendreF_def, neg_div] using
    (integral_one_sub_mul_sin_sq_rpow_neg_eq_ordinaryHypergeometric
      (a := (1 / 2 : ℝ)) (by simpa only [abs_of_nonneg (sq_nonneg k)] using hk))

/-- The complete elliptic integral of the second kind is a hypergeometric function of the
squared modulus (DLMF 19.5.2). -/
theorem legendreEc_eq_ordinaryHypergeometric {k : ℝ} (hk : k ^ 2 < 1) :
    legendreEc k = π / 2 * ₂F₁ (-1 / 2 : ℝ) (1 / 2) 1 (k ^ 2) := by
  simpa only [legendreEc_def, legendreE_def, neg_div, neg_neg] using
    (integral_one_sub_mul_sin_sq_rpow_neg_eq_ordinaryHypergeometric
      (a := (-1 / 2 : ℝ)) (by simpa only [abs_of_nonneg (sq_nonneg k)] using hk))

/-- The complete elliptic integral `D(k) = (K(k) - E(k))/k²` (DLMF 19.2.6) is a hypergeometric
function of the squared modulus (DLMF 15.9.26): for `0 < k² < 1`,
`(K(k) - E(k))/k² = (π/4) ₂F₁(1/2, 3/2; 2; k²)`. -/
theorem legendreD_eq_ordinaryHypergeometric {k : ℝ} (hk₀ : 0 < k ^ 2) (hk : k ^ 2 < 1) :
    (legendreK k - legendreEc k) / k ^ 2 = π / 4 * ₂F₁ (1 / 2 : ℝ) (3 / 2) 2 (k ^ 2) := by
  -- Termwise: the constant terms of the series of `K` and `E` cancel, and since
  -- `(1/2)ₙ₊₁ - (-1/2)ₙ₊₁ = (n + 1) (1/2)ₙ`, the `(n + 1)`-st term of their difference is `k²/2`
  -- times the `n`-th term of `₂F₁(1/2, 3/2; 2; k²)`.
  rw [legendreK_eq_ordinaryHypergeometric hk, legendreEc_eq_ordinaryHypergeometric hk, ← mul_sub]
  set m := k ^ 2
  have hm : ‖m‖ < 1 := by rwa [Real.norm_of_nonneg hk₀.le]
  have hdiff := (hasSum_nat_add_iff' 1).mpr
    ((hasSum_ordinaryHypergeometric (1 / 2 : ℝ) (1 / 2) 1 hm).sub
      (hasSum_ordinaryHypergeometric (-1 / 2 : ℝ) (1 / 2) 1 hm))
  have h0 (a b c : ℝ) : ordinaryHypergeometricCoefficient a b c 0 = 1 := by
    simp [ordinaryHypergeometricCoefficient]
  simp only [Finset.range_one, Finset.sum_singleton, h0, sub_self, sub_zero] at hdiff
  have hterm (n : ℕ) :
      ordinaryHypergeometricCoefficient (1 / 2 : ℝ) (1 / 2) 1 (n + 1) • m ^ (n + 1) -
          ordinaryHypergeometricCoefficient (-1 / 2 : ℝ) (1 / 2) 1 (n + 1) • m ^ (n + 1) =
        m / 2 * (ordinaryHypergeometricCoefficient (1 / 2 : ℝ) (3 / 2) 2 n • m ^ n) := by
    -- `(a)ₙ₊₁ = a (a + 1)ₙ`
    have hl (a : ℝ) : (ascPochhammer ℝ (n + 1)).eval a = a * (ascPochhammer ℝ n).eval (a + 1) :=
      (ascPochhammer_succ_eval n a).trans (ascPochhammer_eval_succ n a).symm
    have h1 : (ascPochhammer ℝ (n + 1)).eval (1 / 2 : ℝ) =
        (ascPochhammer ℝ n).eval (1 / 2) * (1 / 2 + n) := ascPochhammer_succ_eval _ _
    have h2 : (ascPochhammer ℝ (n + 1)).eval (-1 / 2 : ℝ) =
        -1 / 2 * (ascPochhammer ℝ n).eval (1 / 2) := by
      rw [hl]
      norm_num
    have h3 : (ascPochhammer ℝ n).eval (3 / 2 : ℝ) =
        2 * ((ascPochhammer ℝ n).eval (1 / 2) * (1 / 2 + n)) := by
      rw [← h1, hl]
      norm_num
      ring
    have h4 : (ascPochhammer ℝ n).eval (2 : ℝ) = ((n + 1)! : ℝ) := by
      simpa [Nat.add_comm 1 n, one_add_one_eq_two] using factorial_mul_ascPochhammer ℝ 1 n
    have hn : (n ! : ℝ) ≠ 0 := by positivity
    simp only [ordinaryHypergeometricCoefficient, smul_eq_mul, h1, h2, h3, h4,
      ascPochhammer_eval_one, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  simp only [hterm] at hdiff
  rw [hdiff.unique ((hasSum_ordinaryHypergeometric (1 / 2 : ℝ) (3 / 2) 2 hm).mul_left (m / 2))]
  field_simp
  ring

/-- The complete elliptic integral of the first kind is real analytic in the modulus on
`(-1, 1)`. -/
theorem analyticOnNhd_legendreK : AnalyticOnNhd ℝ legendreK (Ioo (-1) 1) := by
  refine AnalyticOnNhd.congr isOpen_Ioo
    (analyticOnNhd_integral_one_sub_sq_mul_sin_sq_rpow_neg (1 / 2 : ℝ)) ?_
  intro k _
  simp only [legendreK_def, legendreF_def, neg_div]

/-- The complete elliptic integral of the second kind is real analytic in the modulus on
`(-1, 1)`. -/
theorem analyticOnNhd_legendreEc : AnalyticOnNhd ℝ legendreEc (Ioo (-1) 1) := by
  refine AnalyticOnNhd.congr isOpen_Ioo
    (analyticOnNhd_integral_one_sub_sq_mul_sin_sq_rpow_neg (-1 / 2 : ℝ)) ?_
  intro k _
  simp only [legendreEc_def, legendreE_def, neg_div, neg_neg]

end Real

end TauCeti
