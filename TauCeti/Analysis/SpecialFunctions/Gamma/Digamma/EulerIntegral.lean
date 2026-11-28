/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.SpecialFunctions.Gamma.Digamma.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.SpecialFunctions.Gamma.Digamma.GaussSeries
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.SpecialFunctions.Integrals.EulerKernel

/-!
# Euler's integral representation of real digamma

For every `0 < a`, the Euler digamma kernel `(w ^ (a - 1) - 1) / (1 - w)` is interval
integrable on `[0, 1]` and satisfies
`∫ w in (0 : ℝ)..1, (w ^ (a - 1) - 1) / (1 - w) = digamma 1 - digamma a` (DLMF 5.9.16),
proved by dominated convergence from Gauss' series for `digamma`.

## Main results

* `Real.integral_rpow_sub_one_div_one_sub`: Euler's integral representation
  `∫ w in (0 : ℝ)..1, (w ^ (a - 1) - 1) / (1 - w) = digamma 1 - digamma a`.
* `Real.tendsto_integral_one_sub_rpow_sub_one_mul_rpow_mul_add_mul_rpow`: the regularized
  Euler-kernel limit as `x → 0⁺` for `0 < a ≤ 1`.

## References

* [NIST DLMF, equation 5.9.16](https://dlmf.nist.gov/5.9.E16).
-/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace Real

private theorem integral_finset_range_rpow_sub_pow {a : ℝ} (ha : 0 < a) (N : ℕ) :
    ∫ w in (0 : ℝ)..1, ∑ k ∈ Finset.range N, (w ^ ((k : ℝ) + a - 1) - w ^ k) =
      ∑ k ∈ Finset.range N, (1 / ((k : ℝ) + a) - 1 / ((k : ℝ) + 1)) := by
  have h1 := TauCeti.integral_finset_rpow_zero_one (Finset.range N)
    (fun k ↦ (k : ℝ) + a - 1) fun k _ ↦ by linarith [k.cast_nonneg (α := ℝ)]
  simp only [sub_add_cancel] at h1
  have h2 := TauCeti.integral_finset_rpow_zero_one (Finset.range N)
    (fun k ↦ (k : ℝ)) fun k _ ↦ by linarith [k.cast_nonneg (α := ℝ)]
  have hi1 : IntervalIntegrable (fun w : ℝ ↦ ∑ k ∈ Finset.range N, w ^ ((k : ℝ) + a - 1))
      volume 0 1 :=
    (IntervalIntegrable.sum (Finset.range N) fun k _ ↦
      intervalIntegral.intervalIntegrable_rpow' (r := (k : ℝ) + a - 1)
        (by linarith [k.cast_nonneg (α := ℝ)])).congr
      fun w _ ↦ Finset.sum_apply w _ _
  have hi2 : IntervalIntegrable (fun w : ℝ ↦ ∑ k ∈ Finset.range N, w ^ (k : ℕ)) volume 0 1 :=
    Continuous.intervalIntegrable (by fun_prop) 0 1
  have h2' : ∫ w in (0 : ℝ)..1, ∑ k ∈ Finset.range N, w ^ (k : ℕ) =
      ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 1) := by
    rw [← h2]
    refine intervalIntegral.integral_congr fun w hw ↦ Finset.sum_congr rfl fun k _ ↦ ?_
    rw [uIcc_of_le zero_le_one] at hw
    exact (rpow_natCast w k).symm
  have hsub : ∫ w in (0 : ℝ)..1,
        (∑ k ∈ Finset.range N, w ^ ((k : ℝ) + a - 1) - ∑ k ∈ Finset.range N, w ^ (k : ℕ)) =
      ∑ k ∈ Finset.range N, (1 / ((k : ℝ) + a) - 1 / ((k : ℝ) + 1)) := by
    rw [intervalIntegral.integral_sub hi1 hi2, h1, h2', ← Finset.sum_sub_distrib]
  simpa only [Finset.sum_sub_distrib] using hsub

/-- **Euler's integral representation of real digamma** (DLMF 5.9.16): for every `0 < a`,
`∫ w in (0 : ℝ)..1, (w ^ (a - 1) - 1) / (1 - w) = digamma 1 - digamma a`
(equivalently `-eulerMascheroniConstant - digamma a`). -/
theorem integral_rpow_sub_one_div_one_sub {a : ℝ} (ha : 0 < a) :
    ∫ w in (0 : ℝ)..1, (w ^ (a - 1) - 1) / (1 - w) = digamma 1 - digamma a := by
  -- Pass the geometric-series expansion under the integral by dominated convergence,
  -- evaluate each finite sum termwise, and identify the limit via Gauss's digamma series.
  have hdct := tendsto_integral_finset_range_rpow_sub_pow ha
  simp_rw [integral_finset_range_rpow_sub_pow ha] at hdct
  have hd := digamma_eq_gaussSeries (x := a) fun m ↦ by linarith [m.cast_nonneg (α := ℝ)]
  have hgauss := (summable_gaussSeries a).hasSum.neg
  rw [(by rw [digamma_one]; linarith :
    -(∑' n : ℕ, (1 / ((n : ℝ) + 1) - 1 / (a + n))) = digamma 1 - digamma a)] at hgauss
  exact tendsto_nhds_unique hdct (hgauss.congr_fun fun k ↦ by ring).tendsto_sum_nat

/-- Regularized Euler-kernel limit: for `0 < a ≤ 1`, as `x → 0⁺`,
`∫ s in (0 : ℝ)..1, ((1 - s) ^ (a - 1) - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ (-a)`
converges to `digamma 1 - digamma a`. -/
theorem tendsto_integral_one_sub_rpow_sub_one_mul_rpow_mul_add_mul_rpow {a : ℝ}
    (ha₀ : 0 < a) (ha₁ : a ≤ 1) :
    Tendsto (fun x ↦ ∫ s in (0 : ℝ)..1,
      ((1 - s) ^ (a - 1) - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ (-a))
      (𝓝[>] 0) (𝓝 (digamma 1 - digamma a)) := by
  have hb_int : IntervalIntegrable (fun s : ℝ ↦ (1 - s) ^ (a - 1)) volume 0 1 :=
    TauCeti.intervalIntegrable_sub_rpow (by linarith : -1 < a - 1) 0 1
  have hdct := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝[>] (0 : ℝ))
    (F := fun x s ↦ ((1 - s) ^ (a - 1) - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ (-a))
    (f := fun s ↦ ((1 - s) ^ (a - 1) - 1) / s) (fun s ↦ (1 - s) ^ (a - 1)) ?_ ?_ hb_int ?_
  · have h := intervalIntegral.integral_comp_sub_left
      (fun w ↦ (w ^ (a - 1) - 1) / (1 - w)) 1 (a := 0) (b := 1)
    simp only [sub_self, sub_zero, sub_sub_cancel] at h
    rwa [h.trans (integral_rpow_sub_one_div_one_sub ha₀)] at hdct
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with x hx
    exact (intervalIntegrable_iff.mp
      (TauCeti.intervalIntegrable_one_sub_rpow_sub_one_mul_rpow_mul_add_mul_rpow
        ha₀ ha₀ hx.1 (-a))).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with x hx
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with s hs1 hs
    rw [uIoc_of_le zero_le_one] at hs
    simpa only [Real.norm_eq_abs] using
      abs_one_sub_rpow_sub_one_mul_rpow_mul_add_mul_rpow_le ha₀ ha₁ hx.1.le
        hs.1 (lt_of_le_of_ne hs.2 hs1)
  · refine Eventually.of_forall fun s hs ↦ ?_
    rw [uIoc_of_le zero_le_one] at hs
    have hlim : Tendsto
        (fun x : ℝ ↦ ((1 - s) ^ (a - 1) - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ (-a))
        (𝓝[>] 0) (𝓝 (((1 - s) ^ (a - 1) - 1) * s ^ (a - 1) * (0 + (1 - 0) * s) ^ (-a))) :=
      ((continuousAt_const.mul (ContinuousAt.rpow_const (by fun_prop)
        (Or.inl (by simp [hs.1.ne'])))).continuousWithinAt (s := Ioi (0 : ℝ))).tendsto
    rwa [(by rw [zero_add, sub_zero, one_mul, mul_assoc, ← rpow_add hs.1,
        (by ring : a - 1 + -a = -1), rpow_neg_one, div_eq_mul_inv] :
      ((1 - s) ^ (a - 1) - 1) * s ^ (a - 1) * (0 + (1 - 0) * s) ^ (-a) =
        ((1 - s) ^ (a - 1) - 1) / s)] at hlim

end Real
