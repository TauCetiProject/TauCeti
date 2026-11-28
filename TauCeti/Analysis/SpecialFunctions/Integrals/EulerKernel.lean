/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# Euler-kernel substitution and interval integrability

Interval integrability, geometric-series convergence, domination estimates, and the rational
substitution `w = (1 - x) s / (x + (1 - x) s)` on `[0, 1]` for real Euler-type kernels
`(1 - s)^(b - 1) s^(a - 1) (x + (1 - x) s)^c`, shared between the Euler integral representation
of real digamma and the zero-balanced hypergeometric connection formula.

## Main declarations

* `TauCeti.one_sub_rpow_mul_integral_rpow_mul_add_mul_rpow`: the substitution
  `w = (1 - x) s / (x + (1 - x) s)` relating `(1 - x)^a ∫₀¹ s^(a-1) (x + (1-x) s)^(-a)` to
  `∫₀^(1-x) w^(a-1) / (1 - w)` for `x ∈ (0, 1)`.
* `TauCeti.intervalIntegrable_rpow_mul_add_mul_rpow`,
  `TauCeti.intervalIntegrable_one_sub_rpow_mul_rpow_mul_add_mul_rpow`, and
  `TauCeti.intervalIntegrable_one_sub_rpow_sub_one_mul_rpow_mul_add_mul_rpow`: interval
  integrability on `[0, 1]` of the singular and regularized Euler kernels.
* `Real.intervalIntegrable_rpow_sub_one_div_one_sub`: interval integrability of the Euler
  digamma kernel `(w ^ (a - 1) - 1) / (1 - w)` on `[0, 1]` for `0 < a`.
* `Real.one_sub_rpow_mul_integral_rpow_mul_add_mul_rpow_eq_sub_log`: for `0 < a` and
  `x ∈ (0, 1)`, rewriting `(1 - x) ^ a * ∫ s in 0..1, s^(a-1) (x + (1-x) s)^(-a)` as
  `(∫ w in 0..(1-x), (w^(a-1) - 1) / (1 - w)) - log x`.
* `Real.tendsto_integral_finset_range_rpow_sub_pow`: dominated convergence of the integrated
  geometric expansion of `(w ^ (a - 1) - 1) / (1 - w)` on `[0, 1]`.
* `Real.abs_one_sub_rpow_sub_one_mul_rpow_mul_add_mul_rpow_le`: uniform domination bound for
  the regularized Euler kernel on `(0, 1)` when `0 < a ≤ 1`.
-/

public section

namespace TauCeti

private theorem add_one_sub_mul_pos {x s : ℝ} (hx : 0 < x) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    0 < x + (1 - x) * s := by
  rcases hs.1.eq_or_lt with rfl | hs0
  · simpa using hx
  · rw [show x + (1 - x) * s = s + x * (1 - s) by ring]
    linarith [mul_nonneg hx.le (sub_nonneg.mpr hs.2)]

private theorem continuousOn_add_one_sub_mul_rpow {x : ℝ} (hx : 0 < x) (c : ℝ) :
    ContinuousOn (fun s : ℝ ↦ (x + (1 - x) * s) ^ c) (Set.Icc 0 1) :=
  ContinuousOn.rpow_const (by fun_prop) fun s hs ↦ Or.inl (add_one_sub_mul_pos hx hs).ne'

/-- For every `a : ℝ` and `x ∈ (0, 1)`, substituting `w = (1 - x) s / (x + (1 - x) s)` on `[0, 1]`
gives
`(1 - x) ^ a * ∫ s in (0 : ℝ)..1, s ^ (a - 1) * (x + (1 - x) * s) ^ (-a) =`
`∫ w in (0 : ℝ)..(1 - x), w ^ (a - 1) / (1 - w)`.
-/
theorem one_sub_rpow_mul_integral_rpow_mul_add_mul_rpow {a x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    (1 - x) ^ a * (∫ s in (0 : ℝ)..1, s ^ (a - 1) * (x + (1 - x) * s) ^ (-a)) =
      ∫ w in (0 : ℝ)..(1 - x), w ^ (a - 1) / (1 - w) := by
  let u : ℝ → ℝ := fun s ↦ (1 - x) * s / (x + (1 - x) * s)
  let u' : ℝ → ℝ := fun s ↦ x * (1 - x) / (x + (1 - x) * s) ^ 2
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := u) (f' := u') (a := (0 : ℝ)) (b := 1)
    (ContinuousOn.div (by fun_prop) (by fun_prop) fun s hs ↦ by
      rw [Set.uIcc_of_le zero_le_one] at hs
      exact (add_one_sub_mul_pos hx.1 hs).ne')
    (fun s hs ↦ by
      rw [min_eq_left zero_le_one, max_eq_right zero_le_one] at hs
      exact (((hasDerivAt_id s).const_mul (1 - x)).div
        (((hasDerivAt_id s).const_mul (1 - x)).const_add x)
        (add_one_sub_mul_pos hx.1 (Set.Ioo_subset_Icc_self hs)).ne').congr_deriv
        (by dsimp [u']; ring))
    (fun _ _ ↦ div_nonneg (mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le)) (sq_nonneg _))
    (g := fun w : ℝ ↦ w ^ (a - 1) / (1 - w))
  rw [(by simp [u] : u 0 = 0),
    (by dsimp [u]; rw [mul_one, add_sub_cancel, div_one] : u 1 = 1 - x)] at hsub
  rw [← hsub, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun s hs ↦ ?_)
  rw [Set.uIoc_of_le zero_le_one] at hs
  have h1x := sub_pos.mpr hx.2
  have hD := add_one_sub_mul_pos hx.1 ⟨hs.1.le, hs.2⟩
  have h1u : 1 - (1 - x) * s / (x + (1 - x) * s) = x / (x + (1 - x) * s) := by
    field_simp [hD.ne']; ring
  have h1xa : (1 - x) ^ a = (1 - x) ^ (a - 1) * (1 - x) := by
    simpa only [sub_add_cancel] using Real.rpow_add_one h1x.ne' (a - 1)
  have hDa : (x + (1 - x) * s) ^ a = (x + (1 - x) * s) ^ (a - 1) * (x + (1 - x) * s) := by
    simpa only [sub_add_cancel] using Real.rpow_add_one hD.ne' (a - 1)
  dsimp [u, u']
  rw [Real.div_rpow (mul_nonneg h1x.le hs.1.le) hD.le, Real.mul_rpow h1x.le hs.1.le, h1u,
    h1xa, Real.rpow_neg hD.le, hDa]
  field_simp [hx.1.ne', hD.ne', (Real.rpow_pos_of_pos hD (a - 1)).ne']

/-- Interval integrability on `[0, 1]` of the half-singular Euler kernel
`s ^ (a - 1) * (x + (1 - x) * s) ^ c` for `0 < a` and `0 < x`. -/
theorem intervalIntegrable_rpow_mul_add_mul_rpow {a x : ℝ} (ha : 0 < a) (hx₀ : 0 < x) (c : ℝ) :
    IntervalIntegrable (fun s : ℝ ↦ s ^ (a - 1) * (x + (1 - x) * s) ^ c)
      MeasureTheory.volume 0 1 :=
  (intervalIntegral.intervalIntegrable_rpow' (by linarith)).mul_continuousOn <| by
    rw [Set.uIcc_of_le zero_le_one]
    exact continuousOn_add_one_sub_mul_rpow hx₀ c

/-- Interval integrability on `[0, 1]` of the beta-weighted Euler kernel
`(1 - s) ^ (b - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ c` for `0 < a`, `0 < b`, and
`0 < x`. -/
theorem intervalIntegrable_one_sub_rpow_mul_rpow_mul_add_mul_rpow {a b x : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hx₀ : 0 < x) (c : ℝ) :
    IntervalIntegrable (fun s : ℝ ↦ (1 - s) ^ (b - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ c)
      MeasureTheory.volume 0 1 := by
  have h1 : IntervalIntegrable
      (fun s : ℝ ↦ (1 - s) ^ (b - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ c)
      MeasureTheory.volume 0 (1 / 2) := by
    have hcont : ContinuousOn
        (fun s : ℝ ↦ (1 - s) ^ (b - 1) * (x + (1 - x) * s) ^ c) (Set.uIcc 0 (1 / 2)) := by
      rw [Set.uIcc_of_le (by norm_num)]
      exact ((continuousOn_const.sub continuousOn_id).rpow_const fun s hs ↦
          Or.inl (by linarith [hs.2] : 1 - s ≠ 0)).mul
        ((continuousOn_add_one_sub_mul_rpow hx₀ c).mono (Set.Icc_subset_Icc_right (by norm_num)))
    exact ((intervalIntegral.intervalIntegrable_rpow' (r := a - 1)
      (by linarith)).mul_continuousOn hcont).congr fun _ _ ↦ by ring
  have h2 : IntervalIntegrable
      (fun s : ℝ ↦ (1 - s) ^ (b - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ c)
      MeasureTheory.volume (1 / 2) 1 := by
    have hcont : ContinuousOn
        (fun s : ℝ ↦ s ^ (a - 1) * (x + (1 - x) * s) ^ c) (Set.uIcc (1 / 2) 1) := by
      rw [Set.uIcc_of_le (by norm_num)]
      exact (continuousOn_id.rpow_const fun s hs ↦
          Or.inl (by linarith [hs.1] : s ≠ 0)).mul
        ((continuousOn_add_one_sub_mul_rpow hx₀ c).mono (Set.Icc_subset_Icc_left (by norm_num)))
    exact ((intervalIntegrable_sub_rpow (by linarith : -1 < b - 1) (1 / 2) 1).mul_continuousOn
      hcont).congr fun _ _ ↦ by ring
  exact h1.trans h2

/-- Interval integrability on `[0, 1]` of the regularized Euler kernel
`((1 - s) ^ (b - 1) - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ c` for `0 < a`, `0 < b`, and
`0 < x`. -/
theorem intervalIntegrable_one_sub_rpow_sub_one_mul_rpow_mul_add_mul_rpow {a b x : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hx₀ : 0 < x) (c : ℝ) :
    IntervalIntegrable
      (fun s : ℝ ↦ ((1 - s) ^ (b - 1) - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ c)
      MeasureTheory.volume 0 1 :=
  ((intervalIntegrable_one_sub_rpow_mul_rpow_mul_add_mul_rpow ha hb hx₀ c).sub
    (intervalIntegrable_rpow_mul_add_mul_rpow ha hx₀ c)).congr fun _ _ ↦ by ring

end TauCeti

namespace Real

open Filter MeasureTheory Set

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
`(∫ w in (0 : ℝ)..(1 - x), (w ^ (a - 1) - 1) / (1 - w)) - Real.log x`. -/
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

open scoped Topology in
/-- For `0 < a`, the integrated geometric-series partial sums of `(w ^ (a - 1) - 1) / (1 - w)` on
`[0, 1]` converge to `∫ w in (0 : ℝ)..1, (w ^ (a - 1) - 1) / (1 - w)`. -/
theorem tendsto_integral_finset_range_rpow_sub_pow {a : ℝ} (ha : 0 < a) :
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

/-- Uniform domination bound for the regularized Euler kernel on `(0, 1)`: for `0 < a ≤ 1`,
`0 ≤ x`, and `0 < s < 1`,
`|((1 - s) ^ (a - 1) - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ (-a)| ≤ (1 - s) ^ (a - 1)`. -/
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

end Real
