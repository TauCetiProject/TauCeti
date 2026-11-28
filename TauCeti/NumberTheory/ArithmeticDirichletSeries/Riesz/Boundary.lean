/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.NumberTheory.LSeries.Basic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import TauCeti.Analysis.LaplaceTransform.Elementary
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.SummatoryTail
import TauCeti.NumberTheory.LSeries.Newman.Tauberian

/-!
# Boundary values of first Riesz sums

Newman's Tauberian theorem gives convergence of a normalized first Riesz sum after subtracting
its logarithmic main term, when the summatory function has linear growth and the compensated
Dirichlet series continues holomorphically across `Re s = 1`. The use of the bounded summatory
error in logarithmic coordinates follows Newman's prime number theorem argument
(D. J. Newman, *Simple analytic proof of the prime number theorem*, 1980).
-/

public section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace TauCeti

/-- With summatory function of at most linear growth, the normalized first Riesz sum minus
its logarithmic main term tends to the value at `1` of the compensated Dirichlet series.
The compensation subtracts `A * s / (s - 1)`; `F` must be analytic on the boundary line. -/
theorem tendsto_rieszSum_div_sub_log_of_analyticAt {a : ℕ → ℂ} {A : ℂ} {F : ℂ → ℂ} {M : ℝ}
    (hbound : ∀ x : ℝ, 1 ≤ x → ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n‖ ≤ M * x)
    (hF : ∀ s : ℂ, s.re = 1 → AnalyticAt ℂ F s)
    (hseries : ∀ s : ℂ, 1 < s.re → LSeriesHasSum a s (F s + A * s / (s - 1))) :
    Tendsto (fun y : ℝ ↦ rieszSum a y / (y : ℂ) - A * (Real.log y : ℂ)) atTop (𝓝 (F 1)) := by
  let f (t : ℝ) : ℂ := (∑ n ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, a n) / (Real.exp t : ℂ) - A
  have hf : Measurable f :=
    ((measurable_from_nat (f := fun k ↦ ∑ n ∈ Finset.Icc 1 k, a n)).comp
      Real.measurable_exp.nat_floor |>.div (measurable_ofReal.comp Real.measurable_exp)).sub_const _
  have hfbound (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) : ‖f t‖ ≤ M + ‖A‖ := by
    refine (norm_sub_le _ _).trans (add_le_add_left ?_ _)
    rw [norm_div, norm_real, Real.norm_of_nonneg (Real.exp_nonneg _),
      div_le_iff₀ (Real.exp_pos _)]
    exact hbound _ (Real.one_le_exp ht)
  have hG (z : ℂ) (hz : z.re = 0) :
      AnalyticAt ℂ (fun w ↦ F (w + 1) / (w + 1)) z := by
    have hz₁ : (z + 1).re = 1 := by simp [hz]
    have hne : z + 1 ≠ 0 := by intro h; simp [h] at hz₁
    have hshift : AnalyticAt ℂ (fun w : ℂ ↦ w + 1) z := analyticAt_id.add analyticAt_const
    exact ((hF (z + 1) hz₁).fun_comp (f := fun w : ℂ ↦ w + 1) hshift).div hshift hne
  have hLap (z : ℂ) (hz : 0 < z.re) :
      HasLaplace f z (F (z + 1) / (z + 1)) := by
    have hz₁ : 1 < (z + 1).re := by simpa using hz
    have hnz : z ≠ 0 := by rintro rfl; simp at hz
    have hnz₁ : z + 1 ≠ 0 := by intro h; rw [h, zero_re] at hz₁; linarith
    have hs := hseries _ hz₁
    have h := HasLaplace.cexp_mul_smul (s := z) (w := -1) (by
      simpa using hs.LSeriesSummable.hasLaplace_summatory_comp_exp (zero_lt_one.trans hz₁))
    convert h.sub (hasLaplace_const A hz) using 1
    · ext t
      simp [f, smul_eq_mul, Complex.exp_neg, ← Complex.ofReal_exp, div_eq_mul_inv, mul_comm]
    · rw [hs.LSeries_eq, smul_eq_mul, add_sub_cancel_right]
      field_simp
      ring
  have hlim := LSeries.newmanLaplace_tendsto_integral_of_analyticAt hf.aestronglyMeasurable
    hfbound hG (fun z hz ↦ by
      rw [integral_Ici_eq_integral_Ioi]
      simpa [smul_eq_mul, mul_comm] using (hLap z hz).integral_eq.symm)
  simp only [zero_add, div_one] at hlim
  refine (hlim.comp Real.tendsto_log_atTop).congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
  have hy₀ : 0 < y := zero_lt_one.trans_le hy
  have hsub := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (g := fun x : ℝ ↦ ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) - A * x) / (x : ℂ) ^ 2)
    (a := 0) (b := Real.log y) Real.continuous_exp.continuousOn
    (fun t _ ↦ Real.hasDerivAt_exp t) (fun t _ ↦ Real.exp_nonneg t)
  rw [Real.exp_zero, Real.exp_log hy₀] at hsub
  rw [Function.comp_apply, rieszSum_div_sub_log_eq_integral _ _ hy,
    ← intervalIntegral.integral_of_le hy, ← hsub]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only [f, Function.comp_apply]
  rw [real_smul]
  field_simp [(ofReal_ne_zero.mpr (Real.exp_pos t).ne' : (Real.exp t : ℂ) ≠ 0)]

end TauCeti
