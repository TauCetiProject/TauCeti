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
import TauCeti.Analysis.Complex.Coordinates
import TauCeti.Analysis.Complex.NormSq
import TauCeti.Analysis.MellinInversion
import TauCeti.NumberTheory.LSeries.Continuity

/-!
# Perron–Riesz inversion for Dirichlet series

On a vertical line `Re s = c > 1`, the Perron–Riesz kernel

`TauCeti.perronRieszKernel x c t = x ^ (c + i t) / ((c + i t) * (c + i t - 1))`

is absolutely integrable over `t ∈ ℝ` (being `O((c - 1)² + t²)⁻¹`), and decomposes by partial
fractions as `x * perronIntegrand x (c - 1) t - perronIntegrand x c t`. Shifting `c` by `1` to
the Mellin inversion integral `TauCeti.integral_cpow_div_mul_add_one` yields

`((2 * π : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, perronRieszKernel x c t = if 1 ≤ x then x - 1 else 0`

for all `x ≥ 0` and `c > 1`. Summing termwise against an absolutely convergent Dirichlet series
`LSeriesSummable a (c : ℂ)` via `MeasureTheory.integral_tsum` gives the absolutely convergent
inversion formula for the first Riesz sum:

`((2 * π : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, LSeries a (c + i t) * perronRieszKernel y c t =`
`  TauCeti.rieszSum a y`.

## Main definitions

* `TauCeti.perronRieszKernel`: the Perron–Riesz kernel
  `x ^ (c + i t) / ((c + i t) * (c + i t - 1))`.

## Main results

* `TauCeti.perronRieszKernel_eq_sub`: partial-fraction decomposition into `TauCeti.perronIntegrand`.
* `TauCeti.norm_perronRieszKernel_le`: quadratic decay bound in height `t`.
* `TauCeti.integrable_perronRieszKernel`, `TauCeti.integral_perronRieszKernel`: full-line
  integrability and evaluation against `if 1 ≤ x then x - 1 else 0`.
* `TauCeti.integrable_LSeries_mul_perronRieszKernel`,
  `TauCeti.rieszSum_eq_integral_LSeries`:
  absolute integrability along `Re s = c > 1` and the Perron–Riesz inversion formula.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I*, Chapter 5.
* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, §3.12 and §9.
* L. Alpöge's formalization of the generalized Riemann hypothesis, via the Mellin cutoff inversion
  `TauCeti.integral_cpow_div_mul_add_one`.
-/

public section

open Complex Filter MeasureTheory
open scoped Real Topology

namespace TauCeti

/-- The **Perron–Riesz kernel** at ratio `x`, abscissa `c`, and height `t`:
`x ^ (c + i t) / ((c + i t) * (c + i t - 1))`. -/
@[expose]
noncomputable def perronRieszKernel (x c t : ℝ) : ℂ :=
  (x : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I - 1))

/-- Defining equation of `TauCeti.perronRieszKernel`. -/
theorem perronRieszKernel_def (x c t : ℝ) :
    perronRieszKernel x c t =
      (x : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I - 1)) :=
  rfl

/-- At ratio zero, the Perron–Riesz kernel vanishes. -/
@[simp]
theorem perronRieszKernel_zero (c t : ℝ) : perronRieszKernel 0 c t = 0 := by
  by_cases hline : (c : ℂ) + t * I = 0
  · simp [perronRieszKernel_def, hline]
  · rw [perronRieszKernel_def, Complex.ofReal_zero, Complex.zero_cpow hline, zero_div]

private theorem cpow_mul_self {x : ℝ} (hx : x ≠ 0) (c t : ℝ) :
    (x : ℂ) * (x : ℂ) ^ (((c - 1 : ℝ) : ℂ) + t * I) = (x : ℂ) ^ ((c : ℂ) + t * I) := by
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  nth_rw 1 [← Complex.cpow_one (x : ℂ)]
  rw [← Complex.cpow_add _ _ hxc]
  congr 1
  push_cast
  ring

/-- Partial-fraction decomposition of the Perron–Riesz kernel in terms of `TauCeti.perronIntegrand`
on vertical lines `c` and `c - 1` for `c ≠ 0` and `c ≠ 1`. -/
theorem perronRieszKernel_eq_sub (x : ℝ) {c : ℝ} (hc0 : c ≠ 0) (hc1 : c ≠ 1) (t : ℝ) :
    perronRieszKernel x c t = (x : ℂ) * perronIntegrand x (c - 1) t - perronIntegrand x c t := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hc0' : (c : ℂ) + t * I ≠ 0 := Complex.ofReal_add_mul_I_ne_zero hc0 t
    have hc1' : (c : ℂ) + t * I - 1 ≠ 0 := by
      have h := Complex.ofReal_add_mul_I_ne_zero (sub_ne_zero.mpr hc1) t
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
    rw [perronRieszKernel_def, perronIntegrand_def, perronIntegrand_def, mul_div_assoc',
      cpow_mul_self hx c t,
      show ((c - 1 : ℝ) : ℂ) + t * I = (c : ℂ) + t * I - 1 by push_cast; ring]
    field_simp
    ring

/-- Pointwise quadratic decay of the Perron–Riesz kernel on `Re s = c > 1`:
`‖perronRieszKernel x c t‖ ≤ (x ^ c / (c - 1) ^ 2) * (1 + (t / (c - 1)) ^ 2)⁻¹`. -/
theorem norm_perronRieszKernel_le {x c : ℝ} (hx : 0 ≤ x) (hc : 1 < c) (t : ℝ) :
    ‖perronRieszKernel x c t‖ ≤ (x ^ c / (c - 1) ^ 2) * (1 + (t / (c - 1)) ^ 2)⁻¹ := by
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · rw [perronRieszKernel_zero c t, norm_zero, Real.zero_rpow (by linarith)]
    simp
  · have hc1 : 0 < c - 1 := by linarith
    have hnum : ‖(x : ℂ) ^ ((c : ℂ) + t * I)‖ = x ^ c := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
      simp
    have hn1 : Real.sqrt ((c - 1) ^ 2 + t ^ 2) ≤ ‖(c : ℂ) + t * I‖ :=
      Complex.sqrt_sq_add_sq_le_norm_add_mul_I hc1.le
        (by rw [abs_of_pos (by linarith : 0 < c)]; linarith)
    have hn2 : Real.sqrt ((c - 1) ^ 2 + t ^ 2) ≤ ‖(c : ℂ) + t * I - 1‖ := by
      rw [show (c : ℂ) + t * I - 1 = ((c - 1 : ℝ) : ℂ) + t * I by push_cast; ring]
      exact Complex.sqrt_sq_add_sq_le_norm_add_mul_I hc1.le (by rw [abs_of_pos hc1])
    have hden : (c - 1) ^ 2 + t ^ 2 ≤ ‖(c : ℂ) + t * I‖ * ‖(c : ℂ) + t * I - 1‖ := by
      calc (c - 1) ^ 2 + t ^ 2
          = Real.sqrt ((c - 1) ^ 2 + t ^ 2) * Real.sqrt ((c - 1) ^ 2 + t ^ 2) :=
            (Real.mul_self_sqrt (by positivity)).symm
        _ ≤ ‖(c : ℂ) + t * I‖ * ‖(c : ℂ) + t * I - 1‖ :=
            mul_le_mul hn1 hn2 (Real.sqrt_nonneg _) (norm_nonneg _)
    rw [perronRieszKernel_def, norm_div, norm_mul, hnum]
    calc x ^ c / (‖(c : ℂ) + t * I‖ * ‖(c : ℂ) + t * I - 1‖)
        ≤ x ^ c / ((c - 1) ^ 2 + t ^ 2) :=
          div_le_div_of_nonneg_left (Real.rpow_nonneg hx c) (by positivity) hden
      _ = (x ^ c / (c - 1) ^ 2) * (1 + (t / (c - 1)) ^ 2)⁻¹ := by
          have : (c - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hc1.ne'
          field_simp

/-- The Perron–Riesz kernel is continuous in the height `t` on any line `Re s = c > 1`. -/
theorem continuous_perronRieszKernel (x : ℝ) {c : ℝ} (hc : 1 < c) :
    Continuous (perronRieszKernel x c) := by
  rcases eq_or_ne x 0 with rfl | hx
  · have : perronRieszKernel 0 c = 0 := funext fun t ↦ perronRieszKernel_zero c t
    rw [this]
    exact continuous_const
  · have hline : Continuous fun t : ℝ ↦ (c : ℂ) + t * I :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hnum : Continuous fun t : ℝ ↦ (x : ℂ) ^ ((c : ℂ) + t * I) :=
      (continuous_iff_continuousAt.mpr fun _ ↦
        continuousAt_const_cpow (Complex.ofReal_ne_zero.mpr hx)).comp hline
    refine hnum.div (hline.mul (hline.sub continuous_const)) fun t ↦ mul_ne_zero ?_ ?_
    · exact Complex.ofReal_add_mul_I_ne_zero (by linarith) t
    · have h := Complex.ofReal_add_mul_I_ne_zero (by linarith : c - 1 ≠ 0) t
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h

/-- The Perron–Riesz kernel `t ↦ perronRieszKernel x c t` is integrable over `ℝ` for `0 ≤ x` and
`1 < c`. -/
theorem integrable_perronRieszKernel {x c : ℝ} (hx : 0 ≤ x) (hc : 1 < c) :
    Integrable (perronRieszKernel x c) := by
  have hc1 : c - 1 ≠ 0 := by linarith
  have hbase : Integrable fun t : ℝ ↦ (x ^ c / (c - 1) ^ 2) * (1 + (t / (c - 1)) ^ 2)⁻¹ :=
    ((integrable_inv_one_add_sq).comp_div hc1).const_mul _
  refine hbase.mono' (continuous_perronRieszKernel x hc).aestronglyMeasurable ?_
  exact .of_forall fun t ↦ norm_perronRieszKernel_le hx hc t

/-- **Evaluation of the Perron–Riesz kernel**: for `0 ≤ x` and `1 < c`,
`((2 * π)⁻¹) * ∫ t : ℝ, perronRieszKernel x c t = if 1 ≤ x then x - 1 else 0`. -/
theorem integral_perronRieszKernel {x c : ℝ} (hx : 0 ≤ x) (hc : 1 < c) :
    ((2 * π : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, perronRieszKernel x c t =
      if 1 ≤ x then (x : ℂ) - 1 else 0 := by
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · simp
  · have hshift : (fun t : ℝ ↦ perronRieszKernel x c t) = fun t : ℝ ↦
        (x : ℂ) * ((x : ℂ) ^ (((c - 1 : ℝ) : ℂ) + t * I) /
          ((((c - 1 : ℝ) : ℂ) + t * I) * (((c - 1 : ℝ) : ℂ) + t * I + 1))) := by
      ext t
      rw [perronRieszKernel_def, ← cpow_mul_self hxpos.ne' c t, mul_div_assoc']
      push_cast
      ring
    have hint := integral_cpow_div_mul_add_one (sub_pos.mpr hc) hxpos
    rw [hshift, integral_const_mul, hint]
    have hπ : ((2 * π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero two_ne_zero Real.pi_ne_zero
    have hcancel : ((2 * π : ℝ) : ℂ)⁻¹ * (x : ℂ) *
        (((2 * π : ℝ) : ℂ) * ((max (1 - x⁻¹) 0 : ℝ) : ℂ)) =
        (x : ℂ) * ((max (1 - x⁻¹) 0 : ℝ) : ℂ) := by
      field_simp
    rw [← mul_assoc, hcancel]
    by_cases hx1 : 1 ≤ x
    · have hnn : 0 ≤ 1 - x⁻¹ := sub_nonneg.mpr (inv_le_one_of_one_le₀ hx1)
      have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxpos.ne'
      simp only [hx1, ↓reduceIte, max_eq_left hnn, Complex.ofReal_sub, Complex.ofReal_one,
        Complex.ofReal_inv]
      field_simp
    · have hle : 1 - x⁻¹ ≤ 0 := sub_nonpos.mpr ((one_le_inv₀ hxpos).mpr (not_le.mp hx1).le)
      simp [hx1, max_eq_right hle]

/-- Collecting the `n`-th `L`-series term into `TauCeti.perronRieszKernel`. -/
theorem term_mul_perronRieszKernel (y c : ℝ) (a : ℕ → ℂ) (n : ℕ) (t : ℝ) :
    LSeries.term a ((c : ℂ) + t * I) n * perronRieszKernel y c t =
      a n * perronRieszKernel (y / n) c t := by
  rcases eq_or_ne n 0 with rfl | hn
  · by_cases h0 : (c : ℂ) + t * I = 0 <;> simp [perronRieszKernel_def, h0]
  · rw [LSeries.term_of_ne_zero hn, perronRieszKernel_def, perronRieszKernel_def,
      show y / (n : ℝ) = (n : ℝ)⁻¹ * y by rw [div_eq_inv_mul, mul_comm],
      Complex.ofReal_mul, Complex.ofReal_mul_cpow (by positivity),
      Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (Nat.cast_nonneg n),
      Complex.ofReal_natCast]
    ring

private theorem lintegral_norm_term_mul_perronRieszKernel_ne_top {a : ℕ → ℂ} {y c : ℝ} (hy : 0 ≤ y)
    (hc : 1 < c) (h : LSeriesSummable a (c : ℂ)) :
    ∑' n : ℕ, ∫⁻ t : ℝ, ‖LSeries.term a ((c : ℂ) + t * I) n * perronRieszKernel y c t‖ₑ ≠ ⊤ := by
  have hc1 : c - 1 ≠ 0 := by linarith
  have hbase : Integrable fun t : ℝ ↦ (y ^ c / (c - 1) ^ 2) * (1 + (t / (c - 1)) ^ 2)⁻¹ :=
    ((integrable_inv_one_add_sq).comp_div hc1).const_mul _
  set I0 : ℝ := ∫ t : ℝ, (y ^ c / (c - 1) ^ 2) * (1 + (t / (c - 1)) ^ 2)⁻¹
  have hI0_nn : 0 ≤ I0 := integral_nonneg fun _ ↦ by positivity
  have hstep : ∀ n : ℕ, ∫⁻ t : ℝ, ‖LSeries.term a ((c : ℂ) + t * I) n * perronRieszKernel y c t‖ₑ ≤
      ENNReal.ofReal (‖LSeries.term a (c : ℂ) n‖ * I0) := by
    intro n
    have hle : ∀ t : ℝ, ‖LSeries.term a ((c : ℂ) + t * I) n * perronRieszKernel y c t‖ₑ ≤
        ENNReal.ofReal (‖LSeries.term a (c : ℂ) n‖ *
          ((y ^ c / (c - 1) ^ 2) * (1 + (t / (c - 1)) ^ 2)⁻¹)) := by
      intro t
      rw [← ofReal_norm, norm_mul]
      refine ENNReal.ofReal_le_ofReal (mul_le_mul ?_ (norm_perronRieszKernel_le hy hc t)
        (norm_nonneg _) (norm_nonneg _))
      exact LSeries.norm_term_le_of_re_le_re a (by simp) n
    calc ∫⁻ t : ℝ, ‖LSeries.term a ((c : ℂ) + t * I) n * perronRieszKernel y c t‖ₑ
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

/-- **Integrability in Perron–Riesz inversion**: for `1 < c` and `0 ≤ y`, `t ↦ LSeries a`
`(c + i t) * perronRieszKernel y c t` is integrable on `ℝ` (when `LSeriesSummable` fails at
`c`, `LSeries` vanishes along the line so the integrand is zero). -/
theorem integrable_LSeries_mul_perronRieszKernel (a : ℕ → ℂ) {y c : ℝ} (hy : 0 ≤ y) (hc : 1 < c) :
    Integrable fun t : ℝ ↦ LSeries a ((c : ℂ) + t * I) * perronRieszKernel y c t := by
  by_cases h : LSeriesSummable a (c : ℂ)
  · have hcont : Continuous fun t : ℝ ↦ LSeries a ((c : ℂ) + t * I) * perronRieszKernel y c t :=
      (TauCeti.LSeries.continuous_vertical a (c : ℂ)).mul (continuous_perronRieszKernel y hc)
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
    exact mul_le_mul hL (norm_perronRieszKernel_le hy hc t) (norm_nonneg _)
      (tsum_nonneg fun _ ↦ norm_nonneg _)
  · have hzero : (fun t : ℝ ↦ LSeries a ((c : ℂ) + t * I) * perronRieszKernel y c t) = 0 := by
      ext t
      have hz : LSeries a ((c : ℂ) + t * I) = 0 :=
        LSeries.eq_zero_of_not_LSeriesSummable _ _ fun hs ↦
          h ((LSeriesSummable_iff_of_re_eq_re (by simp)).mp hs)
      simp [hz]
    rw [hzero]
    exact integrable_zero ℝ ℂ volume

/-- **Perron–Riesz inversion formula**: for `1 < c`, `0 ≤ y`, and
`LSeriesSummable a (c : ℂ)`,
`((2 * π)⁻¹) * ∫ t : ℝ, LSeries a (c + i t) * perronRieszKernel y c t = TauCeti.rieszSum a y`. -/
theorem rieszSum_eq_integral_LSeries {a : ℕ → ℂ} {y c : ℝ} (hy : 0 ≤ y) (hc : 1 < c)
    (h : LSeriesSummable a (c : ℂ)) :
    ((2 * π : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, LSeries a ((c : ℂ) + t * I) * perronRieszKernel y c t =
      rieszSum a y := by
  have htsum : ∀ t : ℝ, LSeries a ((c : ℂ) + t * I) * perronRieszKernel y c t =
      ∑' n : ℕ, LSeries.term a ((c : ℂ) + t * I) n * perronRieszKernel y c t :=
    fun t ↦ tsum_mul_right.symm
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun t : ℝ ↦ LSeries.term a ((c : ℂ) + t * I) n * perronRieszKernel y c t) := fun n ↦ by
    have hcont : Continuous fun t : ℝ ↦ LSeries.term a ((c : ℂ) + t * I) n := by
      rw [continuous_iff_continuousAt]
      intro t
      exact (LSeries.hasDerivAt_term a n _).continuousAt.comp
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt
    exact (hcont.mul (continuous_perronRieszKernel y hc)).aestronglyMeasurable
  simp_rw [htsum]
  rw [MeasureTheory.integral_tsum hmeas (lintegral_norm_term_mul_perronRieszKernel_ne_top hy hc h),
    ← tsum_mul_left]
  have hterm : ∀ n : ℕ, ((2 * π : ℝ) : ℂ)⁻¹ *
      ∫ t : ℝ, LSeries.term a ((c : ℂ) + t * I) n * perronRieszKernel y c t =
      if 1 ≤ n ∧ (n : ℝ) ≤ y then a n * ((y : ℂ) / n - 1) else 0 := by
    intro n
    simp_rw [term_mul_perronRieszKernel y c a n]
    rw [integral_const_mul, mul_left_comm,
      integral_perronRieszKernel (div_nonneg hy (Nat.cast_nonneg n)) hc]
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
