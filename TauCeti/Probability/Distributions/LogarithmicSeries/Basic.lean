/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import TauCeti.Probability.GeneratingFunction
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import TauCeti.Analysis.SpecialFunctions.Log.NegLogOneSub
import TauCeti.MeasureTheory.Measure.Measurability

/-!
# The logarithmic-series distribution

For `0 < q < 1`, the logarithmic-series law is the probability measure on `ℕ` with mass
`-q ^ k / (k log (1 - q))` at every positive integer `k` and no mass at zero. Its normalization is
the power series `∑ qᵏ / k = -log (1 - q)`. Every other parameter value gives the zero measure.

The file supplies the normalized measure, its native singleton and support interfaces, joint
parameter measurability, and the exact integrability domain and closed form
`log (1 - q t) / log (1 - q)` of its probability-generating function.

## Main results

* `isProbabilityMeasure_logarithmicSeriesMeasure` proves normalization;
* `logarithmicSeriesMeasure_singleton` and `logarithmicSeriesMeasure_real_singleton` compute the
  native masses, and `logarithmicSeriesMeasure_singleton_ne_zero_iff` identifies the support as
  the positive integers;
* `measurable_logarithmicSeriesMeasure` proves parameter measurability of the totalized family;
* `integrable_pow_logarithmicSeriesMeasure_iff` and `pgf_logarithmicSeriesMeasure` give the exact
  domain `|q t| < 1` and the value of the probability-generating function.

The distributional convention follows N. L. Johnson, A. W. Kemp, and S. Kotz,
*Univariate Discrete Distributions*, 3rd ed., Wiley, 2005, Chapter 7.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace TauCeti

namespace Probability

/-- The real logarithmic-series mass `-q ^ k / (k log (1 - q))` at `k`.

At `k = 0` the denominator vanishes, so the mass there is zero by the convention `a / 0 = 0`;
see `logarithmicSeriesWeightReal_zero`. -/
def logarithmicSeriesWeightReal (q : ℝ) (k : ℕ) : ℝ :=
  -q ^ k / (k * Real.log (1 - q))

/-- The `ℝ≥0∞`-valued logarithmic-series mass at `k`. -/
def logarithmicSeriesWeight (q : ℝ) (k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (logarithmicSeriesWeightReal q k)

/-- The logarithmic-series law with parameter `q`.

For `0 < q < 1` this is the weighted Dirac sum with masses `-q ^ k / (k log (1 - q))` on the
positive integers; every other parameter value gives the zero measure. -/
def logarithmicSeriesMeasure (q : ℝ) : Measure ℕ :=
  if 0 < q ∧ q < 1 then
    Measure.sum (fun k => logarithmicSeriesWeight q k • Measure.dirac k)
  else 0

/-- In the valid parameter range, the measure is its weighted Dirac sum. -/
theorem logarithmicSeriesMeasure_eq_sum_dirac {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    logarithmicSeriesMeasure q =
      Measure.sum (fun k => logarithmicSeriesWeight q k • Measure.dirac k) := by
  simp [logarithmicSeriesMeasure, hq0, hq1]

/-- Outside the parameter range `0 < q < 1`, the measure is explicitly totalized to zero. -/
@[simp]
theorem logarithmicSeriesMeasure_eq_zero_of_invalid {q : ℝ} (h : ¬ (0 < q ∧ q < 1)) :
    logarithmicSeriesMeasure q = 0 := by
  simp [logarithmicSeriesMeasure, h]

/-- The logarithmic-series law puts no mass at zero. -/
@[simp]
theorem logarithmicSeriesWeightReal_zero (q : ℝ) : logarithmicSeriesWeightReal q 0 = 0 := by
  simp [logarithmicSeriesWeightReal]

/-- The real mass written as `(q ^ k / k) / (-log (1 - q))`, a term of the series for
`-log (1 - q)` divided by its sum. -/
theorem logarithmicSeriesWeightReal_eq_div (q : ℝ) (k : ℕ) :
    logarithmicSeriesWeightReal q k = q ^ k / k / -Real.log (1 - q) := by
  rw [logarithmicSeriesWeightReal]
  ring

/-- In the valid parameter range, the real mass is positive exactly at the positive integers. -/
@[simp]
theorem logarithmicSeriesWeightReal_pos_iff {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (k : ℕ) :
    0 < logarithmicSeriesWeightReal q k ↔ k ≠ 0 := by
  have hlog : 0 < -Real.log (1 - q) := neg_pos.mpr (Real.log_one_sub_neg hq0 hq1)
  refine ⟨fun h hk => by simp [hk] at h, fun hk => ?_⟩
  rw [logarithmicSeriesWeightReal_eq_div]
  have : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  positivity

private theorem logarithmicSeriesWeightReal_nonneg {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (k : ℕ) : 0 ≤ logarithmicSeriesWeightReal q k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · exact ((logarithmicSeriesWeightReal_pos_iff hq0 hq1 k).mpr hk).le

/-- The real-valued mass agrees with the `toReal` of the nonnegative mass. -/
theorem logarithmicSeriesWeight_toReal {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (k : ℕ) :
    (logarithmicSeriesWeight q k).toReal = logarithmicSeriesWeightReal q k := by
  rw [logarithmicSeriesWeight, ENNReal.toReal_ofReal (logarithmicSeriesWeightReal_nonneg hq0 hq1 k)]

/-- Weighting the masses by `t ^ k` gives the series `∑ (q t)ᵏ / k = -log (1 - q t)`, divided by
the normalizing constant `-log (1 - q)`. -/
private theorem hasSum_logarithmicSeriesWeightReal_mul_pow {q t : ℝ} (ht : |q * t| < 1) :
    HasSum (fun k => logarithmicSeriesWeightReal q k * t ^ k)
      (Real.log (1 - q * t) / Real.log (1 - q)) := by
  have hsum := (Real.hasSum_pow_div_natCast ht).div_const (-Real.log (1 - q))
  rw [neg_div_neg_eq] at hsum
  refine hsum.congr_fun fun k => ?_
  rw [logarithmicSeriesWeightReal_eq_div, mul_pow]
  ring

/-- The logarithmic-series measure is a probability measure for `0 < q < 1`. -/
theorem isProbabilityMeasure_logarithmicSeriesMeasure {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    IsProbabilityMeasure (logarithmicSeriesMeasure q) := by
  rw [logarithmicSeriesMeasure_eq_sum_dirac hq0 hq1]
  refine HasSum.isProbabilityMeasure_sum_dirac (logarithmicSeriesWeightReal_nonneg hq0 hq1) ?_
  have hq : |q * 1| < 1 := by rwa [mul_one, abs_of_pos hq0]
  have hlog : Real.log (1 - q) ≠ 0 := (Real.log_one_sub_neg hq0 hq1).ne
  simpa [hlog] using hasSum_logarithmicSeriesWeightReal_mul_pow hq

/-- The singleton mass of the logarithmic-series law in its valid parameter range. -/
@[simp]
theorem logarithmicSeriesMeasure_singleton {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (k : ℕ) :
    logarithmicSeriesMeasure q {k} = logarithmicSeriesWeight q k := by
  rw [logarithmicSeriesMeasure_eq_sum_dirac hq0 hq1]
  exact Measure.sum_smul_dirac_singleton

/-- The real singleton mass of the logarithmic-series law in its valid parameter range. -/
theorem logarithmicSeriesMeasure_real_singleton {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (k : ℕ) :
    (logarithmicSeriesMeasure q).real {k} = logarithmicSeriesWeightReal q k := by
  rw [measureReal_def, logarithmicSeriesMeasure_singleton hq0 hq1,
    logarithmicSeriesWeight_toReal hq0 hq1]

/-! ### Support -/

/-- Every logarithmic-series measure, including the totalized zero measure, vanishes at zero. -/
@[simp]
theorem logarithmicSeriesMeasure_singleton_zero (q : ℝ) : logarithmicSeriesMeasure q {0} = 0 := by
  by_cases h : 0 < q ∧ q < 1
  · simp [logarithmicSeriesMeasure_singleton h.1 h.2, logarithmicSeriesWeight]
  · simp [h]

/-- In the valid parameter range, the singleton mass is nonzero exactly at the positive
integers. -/
theorem logarithmicSeriesMeasure_singleton_ne_zero_iff {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (k : ℕ) : logarithmicSeriesMeasure q {k} ≠ 0 ↔ k ≠ 0 := by
  rw [logarithmicSeriesMeasure_singleton hq0 hq1, logarithmicSeriesWeight,
    ENNReal.ofReal_ne_zero_iff, logarithmicSeriesWeightReal_pos_iff hq0 hq1]

/-- A logarithmic-series variable is almost surely positive. -/
theorem ae_pos_logarithmicSeriesMeasure (q : ℝ) : ∀ᵐ k ∂logarithmicSeriesMeasure q, 0 < k := by
  rw [ae_iff]
  simp

/-! ### Parameter measurability -/

/-- The logarithmic-series family is measurable in its parameter, including the totalized zero
measure outside `0 < q < 1`. -/
@[fun_prop]
theorem measurable_logarithmicSeriesMeasure : Measurable logarithmicSeriesMeasure := by
  have hweight (k : ℕ) : Measurable fun q : ℝ => logarithmicSeriesWeight q k := by
    unfold logarithmicSeriesWeight logarithmicSeriesWeightReal
    fun_prop
  have hvalid : MeasurableSet {q : ℝ | 0 < q ∧ q < 1} :=
    measurableSet_Ioi.inter measurableSet_Iio
  unfold logarithmicSeriesMeasure
  exact Measurable.ite hvalid (TauCeti.MeasureTheory.measurable_sum_smul_dirac hweight)
    measurable_const

/-! ### Probability-generating function -/

/-- The logarithmic-series probability-generating-function integrand is integrable exactly when
`|q t| < 1`; it is non-integrable on and beyond the boundary of that disk. -/
theorem integrable_pow_logarithmicSeriesMeasure_iff {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (t : ℝ) :
    Integrable (fun k : ℕ => t ^ k) (logarithmicSeriesMeasure q) ↔ |q * t| < 1 := by
  rw [logarithmicSeriesMeasure_eq_sum_dirac hq0 hq1,
    integrable_sum_dirac_iff (by simp [logarithmicSeriesWeight])]
  have hlog : 0 < -Real.log (1 - q) := neg_pos.mpr (Real.log_one_sub_neg hq0 hq1)
  have hfun : (fun k : ℕ => (logarithmicSeriesWeight q k).toReal * ‖t ^ k‖) =
      fun k : ℕ => (-Real.log (1 - q))⁻¹ * (|q * t| ^ k / k) := by
    funext k
    rw [logarithmicSeriesWeight_toReal hq0 hq1, logarithmicSeriesWeightReal_eq_div, norm_pow,
      Real.norm_eq_abs, abs_mul, abs_of_pos hq0, mul_pow]
    ring
  rw [hfun, summable_mul_left_iff (inv_ne_zero hlog.ne'), Real.summable_pow_div_natCast_iff,
    abs_abs]

/-- The probability-generating function of a logarithmic-series law on its exact domain
`|q t| < 1`. -/
theorem pgf_logarithmicSeriesMeasure {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {t : ℝ}
    (ht : |q * t| < 1) :
    pgf id (logarithmicSeriesMeasure q) t = Real.log (1 - q * t) / Real.log (1 - q) := by
  rw [pgf_def, logarithmicSeriesMeasure_eq_sum_dirac hq0 hq1,
    integral_sum_dirac (by simp [logarithmicSeriesWeight])]
  simp only [id_eq, smul_eq_mul]
  rw [← (hasSum_logarithmicSeriesWeightReal_mul_pow ht).tsum_eq]
  congr with k
  rw [logarithmicSeriesWeight_toReal hq0 hq1]

end Probability

end TauCeti
