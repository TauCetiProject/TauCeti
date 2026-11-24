/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.NumberTheory.LSeries.Basic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Perron.Basic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Perron–Riesz inversion for Dirichlet series

On a vertical line `Re s = c > 1`, the Riesz kernel

`TauCeti.rieszKernel x c t = x ^ (c + i t) / ((c + i t) * (c + i t - 1))`

is absolutely integrable over `t ∈ ℝ` (being `O((c - 1)² + t²)⁻¹`), and decomposes by partial
fractions as `x * perronIntegrand x (c - 1) t - perronIntegrand x c t`. Passing the symmetric
truncated integrals to the limit via `TauCeti.tendsto_truncatedPerronKernel` yields

`((2 * π : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, rieszKernel x c t = if 1 ≤ x then x - 1 else 0`

for all `x ≥ 0` and `c > 1`. Summing termwise against an absolutely convergent Dirichlet series
`LSeriesSummable a (c : ℂ)` via `MeasureTheory.integral_tsum` gives the absolutely convergent
inversion formula for the first Riesz sum:

`((2 * π : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, LSeries a (c + i t) * rieszKernel y c t = TauCeti.rieszSum a y`.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I*, Chapter 5.
* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, §3.12 and §9.
-/

public section

open Complex Filter MeasureTheory
open scoped Real Topology

namespace TauCeti

private lemma line_ne_zero {c : ℝ} (hc : c ≠ 0) (t : ℝ) : (c : ℂ) + t * I ≠ 0 := by
  intro h
  have hre : ((c : ℂ) + t * I).re = (0 : ℂ).re := congrArg Complex.re h
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    mul_zero, Complex.ofReal_im, mul_one, sub_self, add_zero, Complex.zero_re] at hre
  exact hc hre

/-- The Perron–Riesz kernel at ratio `x`, abscissa `c`, and height `t`:
`x ^ (c + i t) / ((c + i t) * (c + i t - 1))`. -/
@[expose]
noncomputable def rieszKernel (x c t : ℝ) : ℂ :=
  (x : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I - 1))

/-- Defining equation of `TauCeti.rieszKernel`. -/
theorem rieszKernel_def (x c t : ℝ) :
    rieszKernel x c t =
      (x : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I - 1)) :=
  rfl

/-- At ratio zero off the imaginary axis, the Riesz kernel vanishes. -/
@[simp]
theorem rieszKernel_zero {c : ℝ} (hc : c ≠ 0) (t : ℝ) : rieszKernel 0 c t = 0 := by
  have hline : (c : ℂ) + t * I ≠ 0 := line_ne_zero hc t
  rw [rieszKernel_def, Complex.ofReal_zero, Complex.zero_cpow hline, zero_div]

/-- Partial-fraction decomposition of the Riesz kernel in terms of `TauCeti.perronIntegrand` on
vertical lines `c` and `c - 1` for `c > 1` and `x ≥ 0`. -/
theorem rieszKernel_eq_sub {x c : ℝ} (hx : 0 ≤ x) (hc : 1 < c) (t : ℝ) :
    rieszKernel x c t = (x : ℂ) * perronIntegrand x (c - 1) t - perronIntegrand x c t := by
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · have hc0 : (c : ℂ) + t * I ≠ 0 := line_ne_zero (by linarith) t
    have hc1 : ((c - 1 : ℝ) : ℂ) + t * I ≠ 0 := line_ne_zero (by linarith) t
    rw [rieszKernel_zero (by linarith : c ≠ 0) t, perronIntegrand_def, perronIntegrand_def,
      Complex.ofReal_zero, Complex.zero_cpow hc0, Complex.zero_cpow hc1, zero_div, zero_div,
      mul_zero, sub_zero]
  · have hc0 : (c : ℂ) + t * I ≠ 0 := line_ne_zero (by linarith) t
    have hc1 : (c : ℂ) + t * I - 1 ≠ 0 := by
      have h : ((c - 1 : ℝ) : ℂ) + t * I ≠ 0 := line_ne_zero (by linarith) t
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
    have hpow : (x : ℂ) * (x : ℂ) ^ (((c - 1 : ℝ) : ℂ) + t * I) =
        (x : ℂ) ^ ((c : ℂ) + t * I) := by
      have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxpos.ne'
      nth_rw 1 [← Complex.cpow_one (x : ℂ)]
      rw [← Complex.cpow_add _ _ hxc]
      congr 1
      push_cast
      ring
    rw [rieszKernel_def, perronIntegrand_def, perronIntegrand_def, mul_div_assoc', hpow,
      show ((c - 1 : ℝ) : ℂ) + t * I = (c : ℂ) + t * I - 1 by push_cast; ring]
    field_simp
    ring

/-- Pointwise quadratic decay of the Riesz kernel on `Re s = c > 1`:
`‖rieszKernel x c t‖ ≤ (x ^ c / (c - 1) ^ 2) * (1 + (t / (c - 1)) ^ 2)⁻¹`. -/
theorem norm_rieszKernel_le {x c : ℝ} (hx : 0 ≤ x) (hc : 1 < c) (t : ℝ) :
    ‖rieszKernel x c t‖ ≤ (x ^ c / (c - 1) ^ 2) * (1 + (t / (c - 1)) ^ 2)⁻¹ := by
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · rw [rieszKernel_zero (by linarith : c ≠ 0) t, norm_zero, Real.zero_rpow (by linarith)]
    simp
  · have hc1 : 0 < c - 1 := by linarith
    have hnum : ‖(x : ℂ) ^ ((c : ℂ) + t * I)‖ = x ^ c := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
      simp
    have hn1 : Real.sqrt ((c - 1) ^ 2 + t ^ 2) ≤ ‖(c : ℂ) + t * I‖ := by
      rw [Complex.norm_add_mul_I]
      refine Real.sqrt_le_sqrt ?_
      have : (c - 1) ^ 2 ≤ c ^ 2 := by nlinarith
      linarith
    have hn2 : ‖(c : ℂ) + t * I - 1‖ = Real.sqrt ((c - 1) ^ 2 + t ^ 2) := by
      rw [show (c : ℂ) + t * I - 1 = ((c - 1 : ℝ) : ℂ) + t * I by push_cast; ring,
        Complex.norm_add_mul_I]
    have hden : (c - 1) ^ 2 + t ^ 2 ≤ ‖(c : ℂ) + t * I‖ * ‖(c : ℂ) + t * I - 1‖ := by
      have hsq : Real.sqrt ((c - 1) ^ 2 + t ^ 2) * Real.sqrt ((c - 1) ^ 2 + t ^ 2) =
          (c - 1) ^ 2 + t ^ 2 := Real.mul_self_sqrt (by positivity)
      calc (c - 1) ^ 2 + t ^ 2
          = Real.sqrt ((c - 1) ^ 2 + t ^ 2) * Real.sqrt ((c - 1) ^ 2 + t ^ 2) := hsq.symm
        _ ≤ ‖(c : ℂ) + t * I‖ * Real.sqrt ((c - 1) ^ 2 + t ^ 2) :=
            mul_le_mul_of_nonneg_right hn1 (Real.sqrt_nonneg _)
        _ = ‖(c : ℂ) + t * I‖ * ‖(c : ℂ) + t * I - 1‖ := by rw [hn2]
    rw [rieszKernel_def, norm_div, norm_mul, hnum]
    calc x ^ c / (‖(c : ℂ) + t * I‖ * ‖(c : ℂ) + t * I - 1‖)
        ≤ x ^ c / ((c - 1) ^ 2 + t ^ 2) := by
          exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx c) (by positivity) hden
      _ = (x ^ c / (c - 1) ^ 2) * (1 + (t / (c - 1)) ^ 2)⁻¹ := by
          have : (c - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hc1.ne'
          field_simp

/-- The Riesz kernel is continuous in the height `t` on any line `Re s = c > 1`. -/
theorem continuous_rieszKernel (x : ℝ) {c : ℝ} (hc : 1 < c) : Continuous (rieszKernel x c) := by
  rcases eq_or_ne x 0 with rfl | hx
  · have : rieszKernel 0 c = 0 := funext fun t ↦ rieszKernel_zero (by linarith) t
    rw [this]
    exact continuous_const
  · have hline : Continuous fun t : ℝ ↦ (c : ℂ) + t * I :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hnum : Continuous fun t : ℝ ↦ (x : ℂ) ^ ((c : ℂ) + t * I) :=
      (continuous_iff_continuousAt.mpr fun _ ↦
        continuousAt_const_cpow (Complex.ofReal_ne_zero.mpr hx)).comp hline
    refine hnum.div (hline.mul (hline.sub continuous_const)) fun t ↦ mul_ne_zero ?_ ?_
    · exact line_ne_zero (by linarith) t
    · have h : ((c - 1 : ℝ) : ℂ) + t * I ≠ 0 := line_ne_zero (by linarith) t
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h

/-- The Riesz kernel `t ↦ rieszKernel x c t` is integrable over `ℝ` for `0 ≤ x` and `1 < c`. -/
theorem integrable_rieszKernel {x c : ℝ} (hx : 0 ≤ x) (hc : 1 < c) :
    Integrable (rieszKernel x c) := by
  have hc1 : c - 1 ≠ 0 := by linarith
  have hbase : Integrable fun t : ℝ ↦ (x ^ c / (c - 1) ^ 2) * (1 + (t / (c - 1)) ^ 2)⁻¹ :=
    ((integrable_inv_one_add_sq).comp_div hc1).const_mul _
  refine hbase.mono' (continuous_rieszKernel x hc).aestronglyMeasurable (.of_forall fun t ↦ ?_)
  exact norm_rieszKernel_le hx hc t

/-- **Evaluation of the Perron–Riesz kernel** (8.4a (a)): for `0 ≤ x` and `1 < c`,
`((2 * π)⁻¹) * ∫ t : ℝ, rieszKernel x c t = if 1 ≤ x then x - 1 else 0`. -/
theorem integral_rieszKernel {x c : ℝ} (hx : 0 ≤ x) (hc : 1 < c) :
    ((2 * π : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, rieszKernel x c t =
      if 1 ≤ x then (x : ℂ) - 1 else 0 := by
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · simp [rieszKernel_zero (by linarith : c ≠ 0)]
  · have hlim_lhs : Tendsto (fun T : ℝ ↦ ((2 * π : ℝ) : ℂ)⁻¹ * ∫ t in -T..T, rieszKernel x c t)
        atTop (𝓝 (((2 * π : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, rieszKernel x c t)) :=
      (intervalIntegral_tendsto_integral (integrable_rieszKernel hx hc)
        tendsto_neg_atTop_atBot tendsto_id).const_mul _
    have hsplit : ∀ T : ℝ, ((2 * π : ℝ) : ℂ)⁻¹ * ∫ t in -T..T, rieszKernel x c t =
        (x : ℂ) * truncatedPerronKernel x (c - 1) T - truncatedPerronKernel x c T := by
      intro T
      have hint₁ := intervalIntegrable_perronIntegrand hxpos.ne' (by linarith : c - 1 ≠ 0) (-T) T
      have hint₂ := intervalIntegrable_perronIntegrand hxpos.ne' (by linarith : c ≠ 0) (-T) T
      have hcongr : ∫ t in -T..T, rieszKernel x c t =
          ∫ t in -T..T, ((x : ℂ) * perronIntegrand x (c - 1) t - perronIntegrand x c t) :=
        intervalIntegral.integral_congr fun t _ ↦ rieszKernel_eq_sub hx hc t
      rw [hcongr, intervalIntegral.integral_sub (hint₁.const_mul _) hint₂,
        intervalIntegral.integral_const_mul, truncatedPerronKernel_def, truncatedPerronKernel_def]
      ring
    have hlim_rhs : Tendsto (fun T : ℝ ↦
        (x : ℂ) * truncatedPerronKernel x (c - 1) T - truncatedPerronKernel x c T)
        atTop (𝓝 ((x : ℂ) * perronStep x - perronStep x)) :=
      ((tendsto_truncatedPerronKernel hxpos (by linarith : 0 < c - 1)).const_mul _).sub
        (tendsto_truncatedPerronKernel hxpos (by linarith : 0 < c))
    have hval : ((2 * π : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, rieszKernel x c t =
        (x : ℂ) * perronStep x - perronStep x :=
      tendsto_nhds_unique hlim_lhs (hlim_rhs.congr fun T ↦ (hsplit T).symm)
    rw [hval]
    rcases lt_trichotomy x 1 with hlt | rfl | hgt
    · rw [perronStep_of_lt_one hlt]
      simp only [hlt.not_ge, ↓reduceIte]
      ring
    · rw [perronStep_one]
      simp only [le_rfl, ↓reduceIte, Complex.ofReal_one]
      ring
    · rw [perronStep_of_one_lt hgt]
      simp only [hgt.le, ↓reduceIte]
      ring

/-- Collecting the `n`-th `L`-series term into `TauCeti.rieszKernel`. -/
theorem term_mul_rieszKernel {y c : ℝ} (hy : 0 ≤ y) (a : ℕ → ℂ) (n : ℕ) (t : ℝ) :
    LSeries.term a ((c : ℂ) + t * I) n * rieszKernel y c t = a n * rieszKernel (y / n) c t := by
  rcases eq_or_ne n 0 with rfl | hn
  · by_cases h0 : (c : ℂ) + t * I = 0 <;> simp [rieszKernel_def, h0]
  · rw [LSeries.term_of_ne_zero hn, rieszKernel_def, rieszKernel_def, Complex.ofReal_div,
      Complex.div_cpow_ofReal_nonneg hy (Nat.cast_nonneg n), Complex.ofReal_natCast]
    ring

private theorem continuous_LSeries_line {a : ℕ → ℂ} {c : ℝ} (h : LSeriesSummable a (c : ℂ)) :
    Continuous fun t : ℝ ↦ LSeries a ((c : ℂ) + t * I) := by
  refine continuous_tsum (fun n ↦ ?_) h.norm fun n t ↦ ?_
  · rcases eq_or_ne n 0 with rfl | hn
    · simpa using continuous_const
    · have hline : Continuous fun t : ℝ ↦ (c : ℂ) + t * I :=
        continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
      have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
      simp only [LSeries.term_of_ne_zero hn]
      refine continuous_const.div (hline.const_cpow (Or.inl hn0)) fun t hzero ↦
        hn0 ((Complex.cpow_eq_zero_iff _ _).mp hzero).1
  · exact LSeries.norm_term_le_of_re_le_re a (by simp) n

private theorem lintegral_norm_term_mul_rieszKernel_ne_top {a : ℕ → ℂ} {y c : ℝ} (hy : 0 ≤ y)
    (hc : 1 < c) (h : LSeriesSummable a (c : ℂ)) :
    ∑' n : ℕ, ∫⁻ t : ℝ, ‖LSeries.term a ((c : ℂ) + t * I) n * rieszKernel y c t‖ₑ ≠ ⊤ := by
  have hc1 : c - 1 ≠ 0 := by linarith
  have hbase : Integrable fun t : ℝ ↦ (y ^ c / (c - 1) ^ 2) * (1 + (t / (c - 1)) ^ 2)⁻¹ :=
    ((integrable_inv_one_add_sq).comp_div hc1).const_mul _
  set I0 : ℝ := ∫ t : ℝ, (y ^ c / (c - 1) ^ 2) * (1 + (t / (c - 1)) ^ 2)⁻¹
  have hI0_nn : 0 ≤ I0 := integral_nonneg fun _ ↦ by positivity
  have hstep : ∀ n : ℕ, ∫⁻ t : ℝ, ‖LSeries.term a ((c : ℂ) + t * I) n * rieszKernel y c t‖ₑ ≤
      ENNReal.ofReal (‖LSeries.term a (c : ℂ) n‖ * I0) := by
    intro n
    have hle : ∀ t : ℝ, ‖LSeries.term a ((c : ℂ) + t * I) n * rieszKernel y c t‖ₑ ≤
        ENNReal.ofReal (‖LSeries.term a (c : ℂ) n‖ *
          ((y ^ c / (c - 1) ^ 2) * (1 + (t / (c - 1)) ^ 2)⁻¹)) := by
      intro t
      rw [← ofReal_norm, norm_mul]
      refine ENNReal.ofReal_le_ofReal (mul_le_mul ?_ (norm_rieszKernel_le hy hc t)
        (norm_nonneg _) (norm_nonneg _))
      exact LSeries.norm_term_le_of_re_le_re a (by simp) n
    calc ∫⁻ t : ℝ, ‖LSeries.term a ((c : ℂ) + t * I) n * rieszKernel y c t‖ₑ
        ≤ ∫⁻ t : ℝ, ENNReal.ofReal (‖LSeries.term a (c : ℂ) n‖ *
            ((y ^ c / (c - 1) ^ 2) * (1 + (t / (c - 1)) ^ 2)⁻¹)) := lintegral_mono hle
      _ = ENNReal.ofReal (∫ t : ℝ, ‖LSeries.term a (c : ℂ) n‖ *
            ((y ^ c / (c - 1) ^ 2) * (1 + (t / (c - 1)) ^ 2)⁻¹)) :=
          (ofReal_integral_eq_lintegral_ofReal (hbase.const_mul _)
            (.of_forall fun _ ↦ by positivity)).symm
      _ = ENNReal.ofReal (‖LSeries.term a (c : ℂ) n‖ * I0) := by rw [integral_const_mul]
  refine ne_of_lt (lt_of_le_of_lt (tsum_le_tsum hstep) ?_)
  have hsum : Summable fun n : ℕ ↦ ‖LSeries.term a (c : ℂ) n‖ * I0 := h.norm.mul_right I0
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ mul_nonneg (norm_nonneg _) hI0_nn) hsum]
  exact ENNReal.ofReal_lt_top

/-- **Absolute integrability in Perron–Riesz inversion** (8.4a (a)): for `1 < c`, `0 ≤ y`, and
`LSeriesSummable a (c : ℂ)`, `t ↦ LSeries a (c + i t) * rieszKernel y c t` is integrable on `ℝ`. -/
theorem integrable_LSeries_mul_rieszKernel {a : ℕ → ℂ} {y c : ℝ} (hy : 0 ≤ y) (hc : 1 < c)
    (h : LSeriesSummable a (c : ℂ)) :
    Integrable fun t : ℝ ↦ LSeries a ((c : ℂ) + t * I) * rieszKernel y c t := by
  have hcont : Continuous fun t : ℝ ↦ LSeries a ((c : ℂ) + t * I) * rieszKernel y c t :=
    (continuous_LSeries_line h).mul (continuous_rieszKernel y hc)
  have hbase : Integrable fun t : ℝ ↦
      (∑' n : ℕ, ‖LSeries.term a (c : ℂ) n‖) *
        ((y ^ c / (c - 1) ^ 2) * (1 + (t / (c - 1)) ^ 2)⁻¹) :=
    (((integrable_inv_one_add_sq).comp_div (by linarith : c - 1 ≠ 0)).const_mul _).const_mul _
  refine hbase.mono' hcont.aestronglyMeasurable (.of_forall fun t ↦ ?_)
  have hL : ‖LSeries a ((c : ℂ) + t * I)‖ ≤ ∑' n : ℕ, ‖LSeries.term a (c : ℂ) n‖ := by
    have hst : Summable fun n : ℕ ↦ LSeries.term a ((c : ℂ) + t * I) n :=
      LSeriesSummable.of_re_le_re (by simp) h
    calc ‖∑' n : ℕ, LSeries.term a ((c : ℂ) + t * I) n‖
        ≤ ∑' n : ℕ, ‖LSeries.term a ((c : ℂ) + t * I) n‖ :=
          norm_tsum_le_tsum_norm hst.norm
      _ ≤ ∑' n : ℕ, ‖LSeries.term a (c : ℂ) n‖ :=
          hst.norm.tsum_le_tsum (fun n ↦ LSeries.norm_term_le_of_re_le_re a (by simp) n) h.norm
  rw [norm_mul]
  exact mul_le_mul hL (norm_rieszKernel_le hy hc t) (norm_nonneg _)
    (tsum_nonneg fun _ ↦ norm_nonneg _)

private theorem aestronglyMeasurable_term_mul_rieszKernel (a : ℕ → ℂ) (y : ℝ) {c : ℝ}
    (hc : 1 < c) (n : ℕ) :
    AEStronglyMeasurable
      (fun t : ℝ ↦ LSeries.term a ((c : ℂ) + t * I) n * rieszKernel y c t) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [LSeries.term_zero, zero_mul]
    exact aestronglyMeasurable_const
  · have hline : Continuous fun t : ℝ ↦ (c : ℂ) + t * I :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
    have hterm : Continuous fun t : ℝ ↦ LSeries.term a ((c : ℂ) + t * I) n := by
      simp only [LSeries.term_of_ne_zero hn]
      refine continuous_const.div (hline.const_cpow (Or.inl hn0)) fun t hzero ↦
        hn0 ((Complex.cpow_eq_zero_iff _ _).mp hzero).1
    exact (hterm.mul (continuous_rieszKernel y hc)).aestronglyMeasurable

/-- **Perron–Riesz inversion formula** (8.4a (a)): for `1 < c`, `0 ≤ y`, and
`LSeriesSummable a (c : ℂ)`,
`((2 * π)⁻¹) * ∫ t : ℝ, LSeries a (c + i t) * rieszKernel y c t = TauCeti.rieszSum a y`. -/
theorem rieszSum_eq_integral_LSeries {a : ℕ → ℂ} {y c : ℝ} (hy : 0 ≤ y) (hc : 1 < c)
    (h : LSeriesSummable a (c : ℂ)) :
    ((2 * π : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, LSeries a ((c : ℂ) + t * I) * rieszKernel y c t =
      rieszSum a y := by
  have htsum : ∀ t : ℝ, LSeries a ((c : ℂ) + t * I) * rieszKernel y c t =
      ∑' n : ℕ, LSeries.term a ((c : ℂ) + t * I) n * rieszKernel y c t :=
    fun t ↦ tsum_mul_right.symm
  simp_rw [htsum]
  rw [MeasureTheory.integral_tsum (aestronglyMeasurable_term_mul_rieszKernel a y hc)
    (lintegral_norm_term_mul_rieszKernel_ne_top hy hc h), ← tsum_mul_left]
  have hterm : ∀ n : ℕ, ((2 * π : ℝ) : ℂ)⁻¹ *
      ∫ t : ℝ, LSeries.term a ((c : ℂ) + t * I) n * rieszKernel y c t =
      if 1 ≤ n ∧ (n : ℝ) ≤ y then a n * ((y : ℂ) / n - 1) else 0 := by
    intro n
    simp_rw [term_mul_rieszKernel hy a n]
    rw [integral_const_mul, mul_left_comm,
      integral_rieszKernel (div_nonneg hy (Nat.cast_nonneg n)) hc]
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
      simp only [hn1, true_and, one_le_div hnpos]
      split_ifs <;> simp [Complex.ofReal_div]
  simp_rw [hterm]
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊y⌋₊)]
  · rw [rieszSum]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hny : (n : ℝ) ≤ y := (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2).trans (Nat.floor_le hy)
    simp [hn1, hny]
  · intro n hn
    simp only [Finset.mem_Icc, not_and, not_le] at hn
    split_ifs with h
    · exact False.elim (Nat.not_lt_of_ge (Nat.le_floor h.2) (hn h.1))
    · rfl

end TauCeti
