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
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# Euler's integral representation of real digamma

For every `0 < a`, the Euler digamma kernel `(w ^ (a - 1) - 1) / (1 - w)` is interval
integrable on `[0, 1]` and satisfies
`∫ w in (0 : ℝ)..1, (w ^ (a - 1) - 1) / (1 - w) = digamma 1 - digamma a` (DLMF 5.9.16),
proved by dominated convergence from Gauss' series for `digamma`.

## Main results

* `Real.intervalIntegrable_rpow_sub_one_div_one_sub`: interval integrability of the Euler
  digamma kernel on `[0, 1]` for `0 < a`.
* `Real.one_sub_rpow_mul_integral_rpow_mul_add_mul_rpow_eq_sub_log`: for `0 < a` and
  `x ∈ (0, 1)`, rewriting `(1 - x) ^ a * ∫ s in 0..1, s^(a-1) (x + (1-x) s)^(-a)` as
  `(∫ w in 0..(1-x), (w^(a-1) - 1) / (1 - w)) - log x`.
* `Real.integral_rpow_sub_one_div_one_sub`: Euler's integral representation
  `∫ w in (0 : ℝ)..1, (w ^ (a - 1) - 1) / (1 - w) = digamma 1 - digamma a`.
* `Real.abs_one_sub_rpow_sub_one_mul_rpow_mul_add_mul_rpow_le`: uniform domination bound for
  the regularized Euler kernel on `(0, 1)` when `0 < a ≤ 1`.
* `Real.tendsto_integral_one_sub_rpow_sub_one_mul_rpow_mul_add_mul_rpow`: the regularized
  Euler-kernel limit as `x → 0⁺` for `0 < a ≤ 1`.

## References

* [NIST DLMF, equation 5.9.16](https://dlmf.nist.gov/5.9.E16).
-/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace Real

/-- For every `0 < a`, the Euler digamma kernel `(w ^ (a - 1) - 1) / (1 - w)` is interval
integrable on `[0, 1]`. -/
theorem intervalIntegrable_rpow_sub_one_div_one_sub {a : ℝ} (ha : 0 < a) :
    IntervalIntegrable (fun w : ℝ ↦ (w ^ (a - 1) - 1) / (1 - w)) volume 0 1 := by
  have hdom : IntervalIntegrable (fun w : ℝ ↦ w ^ (a - 1) + (⌈a⌉₊ : ℝ)) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)).add intervalIntegrable_const
  rw [intervalIntegrable_iff, IntegrableOn, uIoc_of_le zero_le_one,
    ← Measure.restrict_congr_set Ioo_ae_eq_Ioc] at hdom ⊢
  refine hdom.mono' ((((ContinuousOn.rpow_const (s := Ioo (0 : ℝ) 1) continuousOn_id
    fun w hw ↦ Or.inl hw.1.ne').sub continuousOn_const).div (continuousOn_const.sub continuousOn_id)
      fun w hw ↦ sub_ne_zero.mpr hw.2.ne').aestronglyMeasurable measurableSet_Ioo) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with w hw
  simpa only [Real.norm_eq_abs] using Real.abs_rpow_sub_one_div_one_sub_le ha hw.1 hw.2

/-- Splitting the singular Euler-type integral on `[0, 1]` for `0 < a` and `x ∈ (0, 1)` into
the truncated Euler digamma kernel on `[0, 1 - x]` minus `log x`:
`(1 - x) ^ a * ∫ s in (0 : ℝ)..1, s ^ (a - 1) * (x + (1 - x) * s) ^ (-a) =`
`(∫ w in (0 : ℝ)..(1 - x), (w ^ (a - 1) - 1) / (1 - w)) - Real.log x`.
-/
theorem one_sub_rpow_mul_integral_rpow_mul_add_mul_rpow_eq_sub_log {a x : ℝ}
    (ha : 0 < a) (hx : x ∈ Ioo (0 : ℝ) 1) :
    (1 - x) ^ a * (∫ s in (0 : ℝ)..1, s ^ (a - 1) * (x + (1 - x) * s) ^ (-a)) =
      (∫ w in (0 : ℝ)..(1 - x), (w ^ (a - 1) - 1) / (1 - w)) - Real.log x := by
  have hint1 : IntervalIntegrable (fun w ↦ (w ^ (a - 1) - 1) / (1 - w)) volume 0 (1 - x) :=
    (Real.intervalIntegrable_rpow_sub_one_div_one_sub ha).mono_set <| by
      rw [uIcc_of_le (sub_nonneg.mpr hx.2.le), uIcc_of_le zero_le_one]
      exact Icc_subset_Icc_right (by linarith [hx.1])
  have hint2 : IntervalIntegrable (fun w : ℝ ↦ (1 - w)⁻¹) volume 0 (1 - x) :=
    (ContinuousOn.inv₀ (by fun_prop) fun w hw ↦ by
      rw [uIcc_of_le (sub_nonneg.mpr hx.2.le)] at hw; linarith [hw.2, hx.1]).intervalIntegrable
  have hlog : ∫ w in (0 : ℝ)..(1 - x), (1 - w)⁻¹ = -Real.log x := by
    have h := intervalIntegral.integral_comp_sub_left (fun u : ℝ ↦ u⁻¹) 1 (a := 0) (b := 1 - x)
    simp only [sub_sub_cancel, sub_zero] at h
    rw [h, integral_inv_of_pos hx.1 zero_lt_one, one_div, Real.log_inv]
  rw [TauCeti.one_sub_rpow_mul_integral_rpow_mul_add_mul_rpow hx,
    intervalIntegral.integral_congr (fun _ _ ↦ by ring :
      ∀ w ∈ uIcc 0 (1 - x), w ^ (a - 1) / (1 - w) = (w ^ (a - 1) - 1) / (1 - w) + (1 - w)⁻¹),
    intervalIntegral.integral_add hint1 hint2, hlog, ← sub_eq_add_neg]

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

private theorem rpow_add_sub_one_sub_pow {w a : ℝ} (hw : 0 < w) (k : ℕ) :
    w ^ ((k : ℝ) + a - 1) - w ^ k = (w ^ (a - 1) - 1) * w ^ k := by
  rw [sub_mul, one_mul, (by ring : (k : ℝ) + a - 1 = (a - 1) + k), rpow_add hw, rpow_natCast]

private theorem norm_finset_range_rpow_sub_pow_le {a w : ℝ} (ha : 0 < a)
    (hw₀ : 0 < w) (hw₁ : w < 1) (N : ℕ) :
    ‖∑ k ∈ Finset.range N, (w ^ ((k : ℝ) + a - 1) - w ^ k)‖ ≤ w ^ (a - 1) + (⌈a⌉₊ : ℝ) := by
  have hsum : ∑ k ∈ Finset.range N, (w ^ ((k : ℝ) + a - 1) - w ^ k) =
      (w ^ (a - 1) - 1) * ∑ k ∈ Finset.range N, w ^ k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ rpow_add_sub_one_sub_pow hw₀ k
  rw [hsum, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Finset.sum_nonneg fun k _ ↦ pow_nonneg hw₀.le k)]
  refine (mul_le_mul_of_nonneg_left (sum_le_hasSum _ (fun _ _ ↦ pow_nonneg hw₀.le _)
    (hasSum_geometric_of_lt_one hw₀.le hw₁)) (abs_nonneg _)).trans ?_
  rw [← abs_of_pos (inv_pos.mpr (sub_pos.mpr hw₁)), ← abs_mul, ← div_eq_mul_inv]
  exact Real.abs_rpow_sub_one_div_one_sub_le ha hw₀ hw₁

private theorem tendsto_integral_finset_range_rpow_sub_pow {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ ↦ ∫ w in (0 : ℝ)..1, ∑ k ∈ Finset.range N, (w ^ ((k : ℝ) + a - 1) - w ^ k))
      atTop (𝓝 (∫ w in (0 : ℝ)..1, (w ^ (a - 1) - 1) / (1 - w))) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (F := fun N w ↦ ∑ k ∈ Finset.range N, (w ^ ((k : ℝ) + a - 1) - w ^ k))
    (fun w ↦ w ^ (a - 1) + (⌈a⌉₊ : ℝ)) (Eventually.of_forall fun N ↦ ?_)
    (Eventually.of_forall fun N ↦ ?_)
    ((intervalIntegral.intervalIntegrable_rpow' (by linarith)).add intervalIntegrable_const) ?_
  · exact (intervalIntegrable_iff.mp (IntervalIntegrable.sum (Finset.range N) fun k _ ↦
      (intervalIntegral.intervalIntegrable_rpow' (by linarith [k.cast_nonneg (α := ℝ)])).sub
        (Continuous.intervalIntegrable (by fun_prop) 0 1))).aestronglyMeasurable.congr
      (Eventually.of_forall fun w ↦ Finset.sum_apply w _ _)
  · filter_upwards [Measure.ae_ne volume (1 : ℝ)] with w hw1 hw
    rw [uIoc_of_le zero_le_one] at hw
    exact norm_finset_range_rpow_sub_pow_le ha hw.1 (lt_of_le_of_ne hw.2 hw1) N
  · filter_upwards [Measure.ae_ne volume (1 : ℝ)] with w hw1 hw
    rw [uIoc_of_le zero_le_one] at hw
    exact (div_eq_mul_inv (w ^ (a - 1) - 1) (1 - w) ▸
      ((hasSum_geometric_of_lt_one hw.1.le (lt_of_le_of_ne hw.2 hw1)).mul_left _).congr_fun
        fun k ↦ rpow_add_sub_one_sub_pow hw.1 k).tendsto_sum_nat

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

/-- Uniform domination bound for the regularized Euler kernel on `(0, 1)`: for `0 < a ≤ 1`,
`0 ≤ x`, and `0 < s < 1`,
`|((1 - s) ^ (a - 1) - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ (-a)| ≤ (1 - s) ^ (a - 1)`.
-/
theorem abs_one_sub_rpow_sub_one_mul_rpow_mul_add_mul_rpow_le {a x s : ℝ}
    (ha₀ : 0 < a) (ha₁ : a ≤ 1) (hx₀ : 0 ≤ x) (hs₀ : 0 < s) (hs₁ : s < 1) :
    |((1 - s) ^ (a - 1) - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ (-a)| ≤
      (1 - s) ^ (a - 1) := by
  have h1s_pos : 0 < 1 - s := sub_pos.mpr hs₁
  have h1s_nn : 0 ≤ (1 - s) ^ (a - 1) - 1 := sub_nonneg.mpr <| by
    simpa using rpow_le_rpow_of_exponent_ge h1s_pos (by linarith) (by linarith : a - 1 ≤ 0)
  have hdiv_le : ((1 - s) ^ (a - 1) - 1) / s ≤ (1 - s) ^ (a - 1) := by
    simpa only [sub_sub_cancel] using
      rpow_sub_one_div_one_sub_le ha₀ ha₁ h1s_pos (by linarith)
  have hD_ge : s ≤ x + (1 - x) * s := by nlinarith
  have hD_rpow : (x + (1 - x) * s) ^ (-a) ≤ s ^ (-a) :=
    rpow_le_rpow_of_nonpos hs₀ hD_ge (by linarith)
  rw [abs_of_nonneg (mul_nonneg (mul_nonneg h1s_nn (rpow_nonneg hs₀.le _))
    (rpow_nonneg (hs₀.le.trans hD_ge) _))]
  have hs_comb : s ^ (a - 1) * s ^ (-a) = s⁻¹ := by
    rw [← rpow_add hs₀, (by ring : a - 1 + -a = -1), rpow_neg_one]
  exact ((mul_le_mul_of_nonneg_left hD_rpow (mul_nonneg h1s_nn (rpow_nonneg hs₀.le _))).trans_eq
    (by rw [div_eq_mul_inv, ← hs_comb]; ring :
      _ = ((1 - s) ^ (a - 1) - 1) / s)).trans hdiv_le

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
