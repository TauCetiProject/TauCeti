/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Dirichlet
import TauCeti.MeasureTheory.Measure.Measurability
import TauCeti.NumberTheory.LSeries.RiemannZeta

/-!
# The Zipf distribution

For `s > 1`, the Zipf (or zeta) law with exponent `s` is the probability measure on `ℕ` with mass
`k ^ (-s) / ζ(s)` at every positive integer `k` and no mass at zero. Its normalization is the real
`p`-series `∑ k ^ (-s) = ζ(s)`. Every other exponent gives the zero measure.

The file supplies the normalized measure, its native singleton and support interfaces, and joint
parameter measurability. The moments are in `TauCeti.Probability.Distributions.Zipf.Moments`.

## Main results

* `isProbabilityMeasure_zipfMeasure` proves normalization;
* `zipfMeasure_singleton` and `zipfMeasure_real_singleton` compute the native masses, and
  `zipfMeasure_singleton_ne_zero_iff` identifies the support as the positive integers;
* `measurable_zipfMeasure` proves parameter measurability of the totalized family.

The distributional convention follows N. L. Johnson, A. W. Kemp, and S. Kotz,
*Univariate Discrete Distributions*, 3rd ed., Wiley, 2005, on zeta distributions.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {s : ℝ}

/-- The real Zipf mass `k ^ (-s) / ζ(s)` at `k`, where `ζ(s)` is the real part of
`riemannZeta s`.

For `s ≠ 0` the mass at `k = 0` is zero by the convention `0 ^ (-s) = 0`; see
`zipfWeightReal_zero`. -/
def zipfWeightReal (s : ℝ) (k : ℕ) : ℝ :=
  (k : ℝ) ^ (-s) / (riemannZeta s).re

/-- The defining formula of the real Zipf mass. -/
theorem zipfWeightReal_def (s : ℝ) (k : ℕ) :
    zipfWeightReal s k = (k : ℝ) ^ (-s) / (riemannZeta s).re := (rfl)

/-- The `ℝ≥0∞`-valued Zipf mass at `k`. -/
def zipfWeight (s : ℝ) (k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (zipfWeightReal s k)

/-- The Zipf law with exponent `s`.

For `s > 1` this is the weighted Dirac sum with masses `k ^ (-s) / ζ(s)` on the positive
integers; every other exponent gives the zero measure. -/
def zipfMeasure (s : ℝ) : Measure ℕ :=
  if 1 < s then Measure.sum (fun k => zipfWeight s k • Measure.dirac k) else 0

/-- The `ℝ≥0∞`-valued Zipf mass is the `ENNReal.ofReal` of the real mass. -/
theorem zipfWeight_def (s : ℝ) (k : ℕ) : zipfWeight s k = ENNReal.ofReal (zipfWeightReal s k) :=
  (rfl)

/-- For `s > 1`, the measure is its weighted Dirac sum. -/
theorem zipfMeasure_eq_sum_dirac (hs : 1 < s) :
    zipfMeasure s = Measure.sum (fun k => zipfWeight s k • Measure.dirac k) := by
  simp [zipfMeasure, hs]

/-- For `s ≤ 1`, the measure is explicitly totalized to zero. -/
@[simp]
theorem zipfMeasure_of_le_one (hs : s ≤ 1) : zipfMeasure s = 0 := by
  simp [zipfMeasure, hs.not_gt]

/-- The Zipf mass vanishes at zero for every nonzero exponent. -/
@[simp]
theorem zipfWeightReal_zero (hs : s ≠ 0) : zipfWeightReal s 0 = 0 := by
  simp [zipfWeightReal, Real.zero_rpow (neg_ne_zero.2 hs)]

/-- The `ℝ≥0∞`-valued Zipf mass is never infinite. -/
@[simp]
theorem zipfWeight_ne_top (s : ℝ) (k : ℕ) : zipfWeight s k ≠ ∞ :=
  ENNReal.ofReal_ne_top

/-- For `s > 1`, the real mass is positive exactly at the positive integers. -/
@[simp]
theorem zipfWeightReal_pos_iff (hs : 1 < s) (k : ℕ) : 0 < zipfWeightReal s k ↔ k ≠ 0 := by
  refine ⟨fun h hk => by simp [hk, (zero_lt_one.trans hs).ne'] at h, fun hk => ?_⟩
  have hk' : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have := riemannZeta_re_pos_of_one_lt hs
  unfold zipfWeightReal
  positivity

/-- For `s > 1`, the real Zipf masses are nonnegative. -/
theorem zipfWeightReal_nonneg (hs : 1 < s) (k : ℕ) : 0 ≤ zipfWeightReal s k := by
  have := riemannZeta_re_pos_of_one_lt hs
  unfold zipfWeightReal
  positivity

/-- For `s > 1`, the real-valued mass agrees with the `toReal` of the nonnegative mass. -/
theorem zipfWeight_toReal (hs : 1 < s) (k : ℕ) : (zipfWeight s k).toReal = zipfWeightReal s k := by
  rw [zipfWeight, ENNReal.toReal_ofReal (zipfWeightReal_nonneg hs k)]

/-- For `s > 1`, the real Zipf masses sum to one: `∑ k ^ (-s) = ζ(s)`. -/
theorem hasSum_zipfWeightReal (hs : 1 < s) : HasSum (zipfWeightReal s) 1 := by
  have hsum := (hasSum_nat_rpow_neg_riemannZeta_re hs).div_const (riemannZeta s).re
  rw [div_self (riemannZeta_re_pos_of_one_lt hs).ne'] at hsum
  exact hsum.congr_fun fun k => by rw [zipfWeightReal]

/-- The Zipf measure is a probability measure for `s > 1`. -/
theorem isProbabilityMeasure_zipfMeasure (hs : 1 < s) : IsProbabilityMeasure (zipfMeasure s) := by
  rw [zipfMeasure_eq_sum_dirac hs]
  exact HasSum.isProbabilityMeasure_sum_dirac (zipfWeightReal_nonneg hs) (hasSum_zipfWeightReal hs)

/-- The singleton mass of the Zipf law for `s > 1`. -/
@[simp]
theorem zipfMeasure_singleton (hs : 1 < s) (k : ℕ) : zipfMeasure s {k} = zipfWeight s k := by
  rw [zipfMeasure_eq_sum_dirac hs]
  exact Measure.sum_smul_dirac_singleton

/-- The real singleton mass of the Zipf law for `s > 1`. -/
theorem zipfMeasure_real_singleton (hs : 1 < s) (k : ℕ) :
    (zipfMeasure s).real {k} = zipfWeightReal s k := by
  rw [measureReal_def, zipfMeasure_singleton hs, zipfWeight_toReal hs]

/-! ### Support -/

/-- Every Zipf measure, including the totalized zero measure, vanishes at zero. -/
@[simp]
theorem zipfMeasure_singleton_zero (s : ℝ) : zipfMeasure s {0} = 0 := by
  rcases lt_or_ge 1 s with hs | hs
  · simp [zipfMeasure_singleton hs, zipfWeight, (zero_lt_one.trans hs).ne']
  · simp [hs]

/-- For `s > 1`, the singleton mass is nonzero exactly at the positive integers. -/
theorem zipfMeasure_singleton_ne_zero_iff (hs : 1 < s) (k : ℕ) :
    zipfMeasure s {k} ≠ 0 ↔ k ≠ 0 := by
  rw [zipfMeasure_singleton hs, zipfWeight, ENNReal.ofReal_ne_zero_iff, zipfWeightReal_pos_iff hs]

/-- A Zipf variable is almost surely positive. -/
theorem ae_pos_zipfMeasure (s : ℝ) : ∀ᵐ k ∂zipfMeasure s, 0 < k := by
  rw [ae_iff]
  simp

/-! ### Parameter measurability -/

/-- The Zipf family is measurable in its exponent, including the totalized zero measure for
`s ≤ 1`. -/
@[fun_prop]
theorem measurable_zipfMeasure : Measurable zipfMeasure := by
  have hweight (k : ℕ) : Measurable fun s : ℝ => zipfWeight s k := by
    unfold zipfWeight zipfWeightReal
    fun_prop
  unfold zipfMeasure
  exact Measurable.ite measurableSet_Ioi (TauCeti.MeasureTheory.measurable_sum_smul_dirac hweight)
    measurable_const

end Probability

end TauCeti
