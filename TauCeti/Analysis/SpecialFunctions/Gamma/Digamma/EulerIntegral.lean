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

private theorem integral_finset_rpow_sub_pow {a : ℝ} (ha : 0 < a) (N : ℕ) :
    ∫ w in (0 : ℝ)..1, (∑ k ∈ Finset.range N, (w ^ ((k : ℝ) + a - 1) - w ^ k)) =
      ∑ k ∈ Finset.range N, (1 / ((k : ℝ) + a) - 1 / ((k : ℝ) + 1)) := by
  rw [intervalIntegral.integral_finsetSum fun k _ ↦
    (intervalIntegral.intervalIntegrable_rpow' (by linarith [k.cast_nonneg (α := ℝ)])).sub
      (Continuous.intervalIntegrable (by fun_prop) 0 1)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hka : (0 : ℝ) < (k : ℝ) + a := by linarith [k.cast_nonneg (α := ℝ)]
  rw [intervalIntegral.integral_sub (intervalIntegral.intervalIntegrable_rpow' (by linarith))
      (Continuous.intervalIntegrable (by fun_prop) 0 1),
    integral_rpow (Or.inl (by linarith)), integral_pow, sub_add_cancel, one_rpow,
    zero_rpow hka.ne']
  simp [zero_pow (Nat.succ_ne_zero k)]

/-- **Euler's integral representation of real digamma** (DLMF 5.9.16): for every `0 < a`,
`∫ w in (0 : ℝ)..1, (w ^ (a - 1) - 1) / (1 - w) = digamma 1 - digamma a`
(equivalently `-eulerMascheroniConstant - digamma a`). -/
theorem integral_rpow_sub_one_div_one_sub {a : ℝ} (ha : 0 < a) :
    ∫ w in (0 : ℝ)..1, (w ^ (a - 1) - 1) / (1 - w) = digamma 1 - digamma a := by
  let F : ℕ → ℝ → ℝ := fun N w ↦ ∑ k ∈ Finset.range N, (w ^ ((k : ℝ) + a - 1) - w ^ k)
  have hrpow_mul {w : ℝ} (hw : 0 < w) (k : ℕ) :
      w ^ ((k : ℝ) + a - 1) - w ^ k = (w ^ (a - 1) - 1) * w ^ k := by
    rw [sub_mul, one_mul, (by ring : (k : ℝ) + a - 1 = (a - 1) + k), rpow_add hw, rpow_natCast]
  have hdct : Tendsto (fun N ↦ ∫ w in (0 : ℝ)..1, F N w) atTop
      (𝓝 (∫ w in (0 : ℝ)..1, (w ^ (a - 1) - 1) / (1 - w))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (F := F)
      (fun w ↦ w ^ (a - 1) + (⌈a⌉₊ : ℝ)) (Eventually.of_forall fun N ↦ ?_)
      (Eventually.of_forall fun N ↦ ?_)
      ((intervalIntegral.intervalIntegrable_rpow' (by linarith)).add intervalIntegrable_const) ?_
    · exact (intervalIntegrable_iff.mp (IntervalIntegrable.sum (Finset.range N) fun k _ ↦
        (intervalIntegral.intervalIntegrable_rpow' (by linarith [k.cast_nonneg (α := ℝ)])).sub
          (Continuous.intervalIntegrable (by fun_prop) 0 1))).aestronglyMeasurable.congr
        (Eventually.of_forall fun w ↦ Finset.sum_apply w _ _)
    · filter_upwards [Measure.ae_ne volume (1 : ℝ)] with w hw1 hw
      rw [uIoc_of_le zero_le_one] at hw
      have hwoo : w ∈ Ioo (0 : ℝ) 1 := ⟨hw.1, lt_of_le_of_ne hw.2 hw1⟩
      have hFN : F N w = (w ^ (a - 1) - 1) * ∑ k ∈ Finset.range N, w ^ k := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ ↦ hrpow_mul hwoo.1 k
      rw [hFN, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (Finset.sum_nonneg fun k _ ↦ pow_nonneg hwoo.1.le k)]
      refine (mul_le_mul_of_nonneg_left (sum_le_hasSum _ (fun _ _ ↦ pow_nonneg hwoo.1.le _)
        (hasSum_geometric_of_lt_one hwoo.1.le hwoo.2)) (abs_nonneg _)).trans ?_
      rw [← abs_of_pos (inv_pos.mpr (sub_pos.mpr hwoo.2)), ← abs_mul, ← div_eq_mul_inv]
      exact Real.abs_rpow_sub_one_div_one_sub_le ha hwoo.1 hwoo.2
    · filter_upwards [Measure.ae_ne volume (1 : ℝ)] with w hw1 hw
      rw [uIoc_of_le zero_le_one] at hw
      exact (div_eq_mul_inv (w ^ (a - 1) - 1) (1 - w) ▸
        ((hasSum_geometric_of_lt_one hw.1.le (lt_of_le_of_ne hw.2 hw1)).mul_left _).congr_fun
          fun k ↦ hrpow_mul hw.1 k).tendsto_sum_nat
  simp_rw [F, integral_finset_rpow_sub_pow ha] at hdct
  have hd := digamma_eq_gaussSeries (x := a) fun m ↦ by linarith [m.cast_nonneg (α := ℝ)]
  have hgauss := (summable_gaussSeries a).hasSum.neg
  rw [(by rw [digamma_one]; linarith :
    -(∑' n : ℕ, (1 / ((n : ℝ) + 1) - 1 / (a + n))) = digamma 1 - digamma a)] at hgauss
  exact tendsto_nhds_unique hdct (hgauss.congr_fun fun k ↦ by ring).tendsto_sum_nat

end Real
