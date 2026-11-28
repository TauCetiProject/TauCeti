/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Basic
public import TauCeti.NumberTheory.LSeries.CompensatedSummatoryMellin
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.AbelSummation
import TauCeti.Algebra.BigOperators.Intervals

/-!
# The normalized first Riesz sum and the summatory error

If the summatory function of `a` has main term `A * x`, its error divided by `x²`
controls the first Riesz sum divided by its length. When that weighted error is
integrable, its integral is the constant term of the normalized sum. If the Dirichlet
series also converges for real `s` sufficiently close to `1` from above, this constant is
its right-hand limit at `1` after subtracting `A * s / (s - 1)`.
The remaining error is exactly minus the integral over the tail, so a bound for the
unsmoothed error yields one for the smoothed error by integration.

The normalization for signed prime sums is the one in L. Sernau's `grh-lean`,
`grh/src/New/Reduction/Zeros/PrimeError` (revision `72fead1`).
-/

public section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace TauCeti

/-- The first Riesz sum divided by its length is the integral of the summatory function
against `t⁻²` on `(1, y]`, where `y` is the length. Both sides vanish for `y ≤ 1`. -/
theorem rieszSum_div_eq_integral_summatory (a : ℕ → ℂ) (y : ℝ) :
    rieszSum a y / (y : ℂ) =
      ∫ t in Ioc (1 : ℝ) y, (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, a n) / (t : ℂ) ^ 2 := by
  rcases le_or_gt y 1 with hy | hy
  · rw [rieszSum_eq_zero_of_le_one a hy, zero_div, Ioc_eq_empty_of_le hy, setIntegral_empty]
  let b (n : ℕ) := if n = 0 then 0 else a n
  let f (t : ℝ) := ((t⁻¹ - y⁻¹ : ℝ) : ℂ)
  have hderiv (t : ℝ) (ht : 0 < t) : HasDerivAt f (-(t : ℂ)⁻¹ ^ 2) t := by
    simpa [f, inv_pow] using ((hasDerivAt_inv ht.ne').sub_const y⁻¹).ofReal_comp
  have hc : ContinuousOn (fun t : ℝ ↦ (t : ℂ)⁻¹) (Icc 1 y) :=
    continuous_ofReal.continuousOn.inv₀ fun _ ht ↦
      ofReal_ne_zero.mpr (zero_lt_one.trans_le ht.1).ne'
  have hInt : IntegrableOn (deriv f) (Icc 1 y) :=
    (hc.pow 2).neg.integrableOn_Icc.congr_fun
      (fun t ht ↦ (hderiv t (zero_lt_one.trans_le ht.1)).deriv.symm) measurableSet_Icc
  have hsum (m : ℕ) (g : ℕ → ℂ) :
      ∑ n ∈ Finset.Icc 0 m, g n * b n = ∑ n ∈ Finset.Icc 1 m, g n * a n := by
    rw [Finset.sum_Icc_zero_eq_sum_Icc_one (f := fun n ↦ g n * b n) (by simp [b])]
    exact Finset.sum_congr rfl fun n hn ↦ by
      simp only [b, ite_eq_right (Nat.ne_zero_of_lt (Finset.mem_Icc.mp hn).1)]
  have hsum' (m : ℕ) : ∑ n ∈ Finset.Icc 0 m, b n = ∑ n ∈ Finset.Icc 1 m, a n := by
    simpa using hsum m (fun _ ↦ 1)
  have h := sum_mul_eq_sub_integral_mul₀ b (by simp [b]) y
    (fun t ht ↦ (hderiv t (zero_lt_one.trans_le ht.1)).differentiableAt) hInt
  simp only [f, sub_self, ofReal_zero, zero_mul, zero_sub, hsum, hsum'] at h
  rw [rieszSum_def, Finset.sum_div]
  refine (Finset.sum_congr rfl fun n _ ↦ ?_).trans (h.trans ?_)
  · have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr (zero_lt_one.trans hy).ne'
    push_cast
    field_simp
  · rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
    rw [(hderiv t (zero_lt_one.trans ht.1)).deriv]
    ring

/-- Subtracting the logarithmic main term from the normalized first Riesz sum leaves
the integral of the summatory error against `t⁻²`. -/
theorem rieszSum_div_sub_log_eq_integral (a : ℕ → ℂ) (A : ℂ) {y : ℝ} (hy : 1 ≤ y) :
    rieszSum a y / (y : ℂ) - A * (Real.log y : ℂ) =
      ∫ t in Ioc (1 : ℝ) y, ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, a n) - A * t) / (t : ℂ) ^ 2 := by
  have hpos {t : ℝ} (ht : t ∈ Icc (1 : ℝ) y) : (t : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (zero_lt_one.trans_le ht.1).ne'
  have hc : ContinuousOn (fun t : ℝ ↦ (t : ℂ)⁻¹) (Icc 1 y) :=
    continuous_ofReal.continuousOn.inv₀ fun _ ht ↦ hpos ht
  have h₁ : IntegrableOn (fun t : ℝ ↦ (t : ℂ)⁻¹ ^ 2 * ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, a n)
      (Ioc 1 y) := (integrableOn_mul_sum_Icc a zero_le_one
        (hc.pow 2).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have h₂ : IntegrableOn (fun t : ℝ ↦ A * (t : ℂ)⁻¹) (Ioc 1 y) :=
    (hc.const_mul A).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hlog : (∫ t in Ioc (1 : ℝ) y, A * (t : ℂ)⁻¹) = A * (Real.log y : ℂ) := by
    simp_rw [integral_const_mul, ← ofReal_inv]
    rw [integral_complex_ofReal, ← intervalIntegral.integral_of_le hy,
      integral_inv_of_pos zero_lt_one (zero_lt_one.trans_le hy), div_one]
  rw [rieszSum_div_eq_integral_summatory, ← hlog]
  have hEq (t : ℝ) : (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, a n) / (t : ℂ) ^ 2 =
      (t : ℂ)⁻¹ ^ 2 * ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, a n := by
    rw [div_eq_mul_inv, inv_pow, mul_comm]
  simp_rw [hEq]
  rw [← integral_sub h₁ h₂]
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
  field_simp [hpos (Ioc_subset_Icc_self ht)]

/-- The constant term of the normalized first Riesz sum is the integral of the summatory
error against `t⁻²`, provided this weighted error is absolutely integrable. -/
theorem tendsto_rieszSum_div_sub_log (a : ℕ → ℂ) (A : ℂ)
    (hE : IntegrableOn (fun t : ℝ ↦ ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, a n) - A * t) / (t : ℂ) ^ 2)
      (Ioi 1)) :
    Tendsto (fun y : ℝ ↦ rieszSum a y / (y : ℂ) - A * (Real.log y : ℂ)) atTop
      (𝓝 (∫ t in Ioi (1 : ℝ), ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, a n) - A * t) / (t : ℂ) ^ 2)) := by
  refine (intervalIntegral_tendsto_integral_Ioi 1 hE tendsto_id).congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
  simp only [id_eq, rieszSum_div_sub_log_eq_integral a A hy, intervalIntegral.integral_of_le hy]

/-- After subtracting the logarithmic term and the constant at infinity, the normalized
first Riesz sum is the negative tail integral of the weighted summatory error. -/
theorem rieszSum_div_sub_log_sub_integral_eq_neg_integral (a : ℕ → ℂ) (A : ℂ)
    (hE : IntegrableOn (fun t : ℝ ↦ ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, a n) - A * t) / (t : ℂ) ^ 2)
      (Ioi 1)) {y : ℝ} (hy : 1 ≤ y) :
    rieszSum a y / (y : ℂ) - A * (Real.log y : ℂ) -
      (∫ t in Ioi (1 : ℝ), ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, a n) - A * t) / (t : ℂ) ^ 2) =
      -(∫ t in Ioi y, ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, a n) - A * t) / (t : ℂ) ^ 2) := by
  rw [rieszSum_div_sub_log_eq_integral a A hy, ← intervalIntegral.integral_of_le hy,
    ← intervalIntegral.integral_Ioi_sub_Ioi hE hy, sub_sub_cancel_left]

/-- Suppose the weighted summatory error is integrable on `(1, ∞)` and the Dirichlet series
converges just to the right of `1`, where its compensated version tends to `c`. For `y ≥ 1`,
subtracting `c` and the logarithmic main term from the normalized first Riesz sum leaves the
negative tail integral of the weighted summatory error. -/
theorem rieszSum_div_sub_log_sub_eq_neg_integral_of_tendsto {a : ℕ → ℂ} {A c : ℂ}
    (ha : ∀ᶠ σ : ℝ in 𝓝[>] 1, LSeriesSummable a (σ : ℂ))
    (hE : IntegrableOn (fun t : ℝ ↦ ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, a n) - A * t) / (t : ℂ) ^ 2)
      (Ioi 1))
    (hc : Tendsto (fun σ : ℝ ↦ LSeries a (σ : ℂ) - A * σ / ((σ : ℂ) - 1)) (𝓝[>] 1) (𝓝 c))
    {y : ℝ} (hy : 1 ≤ y) :
    rieszSum a y / (y : ℂ) - A * (Real.log y : ℂ) - c =
      -(∫ t in Ioi y, ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, a n) - A * t) / (t : ℂ) ^ 2) := by
  have hlimit := LSeries.tendsto_sub_linear_pole_of_integrable_summatory_error A ha hE
  rw [tendsto_nhds_unique hc hlimit]
  exact rieszSum_div_sub_log_sub_integral_eq_neg_integral a A hE hy

end TauCeti
