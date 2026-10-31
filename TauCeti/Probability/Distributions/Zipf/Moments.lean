/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Probability.Moments.Variance
public import TauCeti.Probability.Distributions.Zipf.Basic
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.NumberTheory.LSeries.Dirichlet
import TauCeti.NumberTheory.LSeries.RiemannZeta
import TauCeti.Probability.Moments.IntegrableExpMul

/-!
# Moments of the Zipf distribution

The Zipf mass `k ^ (-s) / ζ(s)` weighted by `k ^ m` is `k ^ (-(s - m)) / ζ(s)`, a shifted
`p`-series. Hence the `m`-th moment of the Zipf law exists exactly when `m < s - 1`, in which case
it is `E[X ^ m] = ζ(s - m) / ζ(s)`; here `ζ` denotes the real part of `riemannZeta` at a real
argument. The mean `ζ(s - 1) / ζ(s)` exists exactly for `s > 2`, the variance
`ζ(s - 2) / ζ(s) - (ζ(s - 1) / ζ(s)) ^ 2` exactly for `s > 3`, and the exponential moments exist
exactly at nonpositive arguments.

All statements concern the real cast of the law, which is its analytic interface.

## Main results

* `integrable_pow_map_cast_zipfMeasure_iff`: the `m`-th moment exists exactly when `m < s - 1`;
* `integral_pow_map_cast_zipfMeasure`: the raw moments `ζ(s - m) / ζ(s)`;
* `integral_id_map_cast_zipfMeasure` and `variance_id_map_cast_zipfMeasure`: the mean and
  variance, with `integrable_id_map_cast_zipfMeasure_iff` and
  `memLp_two_id_map_cast_zipfMeasure_iff` giving their thresholds `s > 2` and `s > 3`;
* `integrableExpSet_id_map_cast_zipfMeasure`: the exponential-integrability domain is
  `(-∞, 0]`.

## References

* N. L. Johnson, A. W. Kemp, and S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, on zeta distributions.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set

namespace TauCeti

namespace Probability

variable {s : ℝ}

/-- At a positive integer, the Zipf mass weighted by `k ^ m` is `k ^ (m - s) / ζ(s)`. -/
private theorem zipfWeightReal_succ_mul_pow (s : ℝ) (m n : ℕ) :
    zipfWeightReal s (n + 1) * ((n + 1 : ℕ) : ℝ) ^ m =
      ((n + 1 : ℕ) : ℝ) ^ ((m : ℝ) - s) / (riemannZeta s).re := by
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  rw [zipfWeightReal_def, sub_eq_neg_add, rpow_add hn, rpow_natCast]
  ring

/-- Below the pole `m = s`, the Zipf mass weighted by `k ^ m` is `k ^ (-(s - m)) / ζ(s)` at every
natural number, including `k = 0`. -/
private theorem zipfWeightReal_mul_pow {m : ℕ} (hm : (m : ℝ) < s) (k : ℕ) :
    zipfWeightReal s k * (k : ℝ) ^ m = (k : ℝ) ^ (-(s - m)) / (riemannZeta s).re := by
  rcases k with _ | n
  · have hs : s ≠ 0 := ((Nat.cast_nonneg m).trans_lt hm).ne'
    rw [Nat.cast_zero, zipfWeightReal_zero hs, zero_mul, zero_rpow (by linarith), zero_div]
  · rw [zipfWeightReal_succ_mul_pow, neg_sub]

/-- On the natural numbers, the `m`-th power is integrable for a Zipf law exactly when
`m < s - 1`. -/
private theorem integrable_pow_zipfMeasure_iff (hs : 1 < s) (m : ℕ) :
    Integrable (fun k : ℕ => (k : ℝ) ^ m) (zipfMeasure s) ↔ (m : ℝ) < s - 1 := by
  rw [zipfMeasure_eq_sum_dirac hs, integrable_sum_dirac_iff (zipfWeight_ne_top s),
    ← summable_nat_add_iff 1]
  simp_rw [zipfWeight_toReal hs, norm_pow, Real.norm_natCast, zipfWeightReal_succ_mul_pow]
  rw [summable_div_const_iff (riemannZeta_re_pos_of_one_lt hs).ne',
    summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ ((m : ℝ) - s)) 1, summable_nat_rpow]
  constructor <;> intro h <;> linarith

/-- The `m`-th moment of the real cast of a Zipf law exists exactly when `m < s - 1`. -/
theorem integrable_pow_map_cast_zipfMeasure_iff (hs : 1 < s) (m : ℕ) :
    Integrable (fun x : ℝ => x ^ m) ((zipfMeasure s).map (Nat.cast : ℕ → ℝ)) ↔
      (m : ℝ) < s - 1 := by
  rw [MeasurableEmbedding.natCast.integrable_map_iff]
  exact integrable_pow_zipfMeasure_iff hs m

/-- The `m`-th moment of the real cast of a Zipf law is `ζ(s - m) / ζ(s)` whenever `m < s - 1`. -/
theorem integral_pow_map_cast_zipfMeasure {m : ℕ} (hm : (m : ℝ) < s - 1) :
    ∫ x, x ^ m ∂((zipfMeasure s).map (Nat.cast : ℕ → ℝ)) =
      (riemannZeta (s - m : ℝ)).re / (riemannZeta s).re := by
  have hs : 1 < s := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  rw [MeasurableEmbedding.natCast.integral_map, zipfMeasure_eq_sum_dirac hs,
    integral_sum_dirac (zipfWeight_ne_top s)]
  simp_rw [smul_eq_mul, zipfWeight_toReal hs, zipfWeightReal_mul_pow (by linarith : (m : ℝ) < s)]
  rw [tsum_div_const, (hasSum_nat_rpow_neg_riemannZeta_re (by linarith : 1 < s - m)).tsum_eq]

/-! ### Mean and variance -/

/-- The mean of the real cast of a Zipf law is `ζ(s - 1) / ζ(s)` for `s > 2`. -/
theorem integral_id_map_cast_zipfMeasure (hs : 2 < s) :
    ∫ x, x ∂((zipfMeasure s).map (Nat.cast : ℕ → ℝ)) =
      (riemannZeta (s - 1 : ℝ)).re / (riemannZeta s).re := by
  simpa using integral_pow_map_cast_zipfMeasure (m := 1) (s := s) (by norm_num; linarith)

/-- The real cast of a Zipf law has a finite mean exactly when `s > 2`. -/
theorem integrable_id_map_cast_zipfMeasure_iff (hs : 1 < s) :
    Integrable id ((zipfMeasure s).map (Nat.cast : ℕ → ℝ)) ↔ 2 < s := by
  have h := integrable_pow_map_cast_zipfMeasure_iff hs 1
  simp only [pow_one, Nat.cast_one] at h
  exact h.trans ⟨fun h => by linarith, fun h => by linarith⟩

/-- The real cast of a Zipf law has finite variance exactly when `s > 3`. -/
theorem memLp_two_id_map_cast_zipfMeasure_iff (hs : 1 < s) :
    MemLp id 2 ((zipfMeasure s).map (Nat.cast : ℕ → ℝ)) ↔ 3 < s := by
  rw [memLp_two_iff_integrable_sq aestronglyMeasurable_id]
  simp only [id_eq]
  rw [integrable_pow_map_cast_zipfMeasure_iff hs]
  constructor <;> intro h <;> push_cast at h ⊢ <;> linarith

/-- The variance of the real cast of a Zipf law is `ζ(s - 2) / ζ(s) - (ζ(s - 1) / ζ(s)) ^ 2` for
`s > 3`. -/
theorem variance_id_map_cast_zipfMeasure (hs : 3 < s) :
    variance id ((zipfMeasure s).map (Nat.cast : ℕ → ℝ)) =
      (riemannZeta (s - 2 : ℝ)).re / (riemannZeta s).re -
        ((riemannZeta (s - 1 : ℝ)).re / (riemannZeta s).re) ^ 2 := by
  have hs1 : 1 < s := by linarith
  have := isProbabilityMeasure_zipfMeasure hs1
  rw [variance_eq_sub ((memLp_two_id_map_cast_zipfMeasure_iff hs1).2 hs)]
  simp only [Pi.pow_apply, id_eq]
  rw [integral_pow_map_cast_zipfMeasure (m := 2) (by norm_num; linarith),
    integral_id_map_cast_zipfMeasure (by linarith)]
  norm_num

/-! ### Exponential moments -/

/-- The exponential moments of the real cast of a Zipf law exist exactly at nonpositive
arguments. -/
theorem integrableExpSet_id_map_cast_zipfMeasure (hs : 1 < s) :
    integrableExpSet id ((zipfMeasure s).map (Nat.cast : ℕ → ℝ)) = Iic 0 := by
  have := isProbabilityMeasure_zipfMeasure hs
  have hnonneg : ∀ᵐ x ∂((zipfMeasure s).map (Nat.cast : ℕ → ℝ)), (0 : ℝ) ≤ id x :=
    MeasurableEmbedding.natCast.ae_map_iff.2 (Eventually.of_forall fun k => Nat.cast_nonneg k)
  ext t
  simp only [integrableExpSet, mem_ofPred_eq, mem_Iic]
  refine ⟨fun h => ?_, fun ht => integrable_exp_mul_of_ge t 0 ht aemeasurable_id hnonneg⟩
  by_contra ht
  push Not at ht
  -- A positive exponential moment would give the infinite moment of order `⌈s⌉₊`.
  refine not_integrable_exp_mul_of_not_integrable_pow ⌈s⌉₊ aemeasurable_id hnonneg ?_ ht h
  intro hi
  linarith [Nat.le_ceil s, (integrable_pow_map_cast_zipfMeasure_iff hs _).1 hi]

end Probability

end TauCeti
