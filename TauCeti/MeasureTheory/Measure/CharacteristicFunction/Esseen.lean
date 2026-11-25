/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import TauCeti.Analysis.Bochner.CharFun.Basic
import TauCeti.Analysis.SpecialFunctions.Integrals.Trigonometric.Fejer
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Sinc
import TauCeti.MeasureTheory.Integral.OddSymmetric

/-!
# Esseen's concentration inequality

For a finite measure `μ` on `ℝ`, every closed ball of radius `ε > 0` has mass at most
`2 * ε * ∫ t in -ε⁻¹..ε⁻¹, ‖charFun μ t‖`
(`MeasureTheory.measureReal_closedBall_le_integral_norm_charFun`). The bound is uniform in the
centre, so it bounds the Lévy concentration function `sup_v μ (closedBall v ε)`. The bound is
four times the average of `‖charFun μ t‖` over `[-ε⁻¹, ε⁻¹]`, so it is small when that average
modulus is small; then every interval of length `2 ε` has small mass. This is the analytic input
of small-ball estimates for sums of independent random variables, whose characteristic function is
a product.

The proof smooths `μ` with the Fejér kernel `T / 2 * sinc (T * (x - v) / 2) ^ 2`. Its integral
against `μ` is the oriented interval integral from `0` to `T`, weighted by `1 - t / T`, of the
real part of the characteristic function rotated by the phase `-t * v`
(`MeasureTheory.integral_mul_sinc_sq_eq_integral_re_charFun`).

## References

* C.-G. Esseen, *On the Kolmogorov–Rogozin inequality for the concentration function*,
  Z. Wahrscheinlichkeitstheorie verw. Gebiete 5 (1966), 210–216.
* M. Rudelson and R. Vershynin, *The Littlewood–Offord problem and invertibility of random
  matrices*, Advances in Mathematics 218 (2008), §4, where the inequality bounds the small-ball
  probability of a weighted sum through its arithmetic structure.
* Mathlib's `MeasureTheory.integral_charFun_Icc`, whose interchange of an interval integral with
  an integral against `μ` the Fubini step here adapts.
-/

public section

open Complex Real Set Metric intervalIntegral

namespace MeasureTheory

variable {μ : Measure ℝ} [IsFiniteMeasure μ]

/-- For all real `v` and `T`, the integral of the Fejér kernel `T / 2 * sinc (T * (x - v) / 2) ^ 2`
against a finite measure `μ` on `ℝ` equals the oriented interval integral `∫ t in 0..T`, weighted
by `1 - t / T`, of the real part of the characteristic function of `μ` at `t` after rotation by
the phase `-t * v`. -/
theorem integral_mul_sinc_sq_eq_integral_re_charFun (v T : ℝ) :
    ∫ x, T / 2 * sinc (T * (x - v) / 2) ^ 2 ∂μ =
      ∫ t in 0..T, (1 - t / T) * (cexp (↑(-(t * v)) * I) * charFun μ t).re := by
  -- Fubini's theorem, swapping the interval integral with the integral against `μ` through
  -- `intervalIntegral_integral_swap`, as in the proof of Mathlib's
  -- `MeasureTheory.integral_charFun_Icc`.
  have hint : Integrable (Function.uncurry fun t x : ℝ ↦ (1 - t / T) * Real.cos (t * (x - v)))
      ((volume.restrict (uIoc 0 T)).prod μ) := by
    have hw : Integrable (fun t : ℝ ↦ |1 - t / T|) (volume.restrict (uIoc 0 T)) :=
      intervalIntegrable_iff.1 (Continuous.intervalIntegrable (by fun_prop) 0 T)
    refine (hw.mul_prod (integrable_const (1 : ℝ))).mono' (by fun_prop)
      (ae_of_all _ fun ⟨t, x⟩ ↦ ?_)
    simp only [Function.uncurry_apply_pair, Real.norm_eq_abs, mul_one, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  calc ∫ x, T / 2 * sinc (T * (x - v) / 2) ^ 2 ∂μ
      = ∫ x, (∫ t in 0..T, (1 - t / T) * Real.cos (t * (x - v))) ∂μ := by
        simp only [TauCeti.integral_one_sub_div_mul_cos_mul]
    _ = ∫ t in 0..T, ∫ x, (1 - t / T) * Real.cos (t * (x - v)) ∂μ :=
        (intervalIntegral_integral_swap hint).symm
    _ = ∫ t in 0..T, (1 - t / T) * (cexp (↑(-(t * v)) * I) * charFun μ t).re := by
        simp only [integral_const_mul, TauCeti.integral_cos_mul_sub_eq_re_exp_mul_charFun]

omit [IsFiniteMeasure μ] in
/-- For `T > 0`, the integral over `[0, T]`, weighted by `1 - t / T`, of the real part of the
characteristic function of `μ` at `t` after rotation by the phase `-t * v` is at most the
unweighted integral of `‖charFun μ t‖` over `[0, T]`. -/
private theorem integral_one_sub_div_mul_re_le {T : ℝ} (hT : 0 < T) (v : ℝ) :
    ∫ t in 0..T, (1 - t / T) * (cexp (↑(-(t * v)) * I) * charFun μ t).re ≤
      ∫ t in 0..T, ‖charFun μ t‖ := by
  refine integral_mono_on hT.le (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _) fun t ht ↦ ?_
  obtain ⟨ht₀, htT⟩ := Set.mem_Icc.mp ht
  have h₁ : 0 ≤ 1 - t / T := by
    rw [sub_nonneg, div_le_one hT]
    exact htT
  have h₂ : 1 - t / T ≤ 1 := by
    rw [sub_le_self_iff]
    exact div_nonneg ht₀ hT.le
  calc (1 - t / T) * (cexp (↑(-(t * v)) * I) * charFun μ t).re ≤
        (1 - t / T) * ‖charFun μ t‖ :=
        mul_le_mul_of_nonneg_left ((Complex.re_le_norm _).trans_eq
          (by rw [norm_mul, norm_exp_ofReal_mul_I, one_mul])) h₁
    _ ≤ ‖charFun μ t‖ := mul_le_of_le_one_left (norm_nonneg _) h₂

/-- **Esseen's concentration inequality.** For a finite measure `μ` on `ℝ`, every closed ball of
radius `ε > 0` has mass at most `2 * ε * ∫ t in -ε⁻¹..ε⁻¹, ‖charFun μ t‖`. -/
theorem measureReal_closedBall_le_integral_norm_charFun (v : ℝ) {ε : ℝ} (hε : 0 < ε) :
    μ.real (closedBall v ε) ≤ 2 * ε * ∫ t in -ε⁻¹..ε⁻¹, ‖charFun μ t‖ := by
  set T := ε⁻¹ with hT
  have hT₀ : 0 < T := inv_pos.2 hε
  -- The kernel is the cosine transform of the triangular weight on `[0, T]`, centred at `v`.
  set K : ℝ → ℝ := fun x ↦ T / 2 * sinc (T * (x - v) / 2) ^ 2
  have hK_int : Integrable K μ :=
    Integrable.of_bound (by fun_prop) (T / 2) (ae_of_all _ fun x ↦ by
      rw [Real.norm_of_nonneg (by positivity)]
      exact mul_le_of_le_one_right (by positivity)
        ((sq_le_one_iff_abs_le_one _).2 (abs_sinc_le_one _)))
  have hsymm : ∫ t in -T..T, ‖charFun μ t‖ = 2 * ∫ t in 0..T, ‖charFun μ t‖ := by
    rw [intervalIntegral.integral_eq_two_smul_of_even (fun t ↦ by
      rw [charFun_neg, Complex.norm_conj]), smul_eq_mul]
  calc μ.real (closedBall v ε) = 4 / T * ∫ x in closedBall v ε, T / 4 ∂μ := by
        rw [setIntegral_const, smul_eq_mul]
        field_simp
    _ ≤ 4 / T * ∫ x in closedBall v ε, K x ∂μ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine setIntegral_mono_on integrableOn_const hK_int.integrableOn
          measurableSet_closedBall fun x hx ↦ TauCeti.div_four_le_mul_sinc_sq ?_
        simpa [hT, Real.dist_eq] using Metric.mem_closedBall.mp hx
    _ ≤ 4 / T * ∫ x, K x ∂μ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact setIntegral_le_integral hK_int (ae_of_all _ fun x ↦ by positivity)
    _ ≤ 4 / T * ∫ t in 0..T, ‖charFun μ t‖ := by
        rw [integral_mul_sinc_sq_eq_integral_re_charFun v T]
        gcongr
        exact integral_one_sub_div_mul_re_le hT₀ v
    _ = 2 * ε * ∫ t in -T..T, ‖charFun μ t‖ := by
        rw [hsymm, hT]
        field_simp
        ring

end MeasureTheory
