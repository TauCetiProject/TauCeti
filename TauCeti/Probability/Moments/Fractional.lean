/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Integrals.CosinePower
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fractional absolute moments from characteristic functions

For a finite real measure and `0 < q < 2`, the absolute moment of order `q` is determined by
the power-weighted integral of the difference between its total mass and the real part of its
characteristic function. The extended-real identity applies even when the moment is infinite;
it yields an exact integrability criterion and, in the finite case, a real integral formula.
These identities allow fractional moments to be computed directly from characteristic
functions without first finding a density.

The normalization follows `TauCeti.integral_Ioi_rpow_neg_mul_one_sub_cos`, with the
characteristic kernel `exp (i t x)` rather than a Fourier kernel containing `2π`.
-/

public section

noncomputable section

open MeasureTheory Real Set
open scoped ENNReal

namespace TauCeti

variable {μ : Measure ℝ} [IsFiniteMeasure μ] {q : ℝ}

/-- Tonelli's identity for fractional absolute moments, allowing an infinite moment on either
side. The coefficient is strictly positive for `0 < q < 2`. -/
theorem lintegral_rpow_mul_sub_re_charFun (hq : 0 < q) (hq2 : q < 2) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal
        (t ^ (-(q + 1)) * (μ.real univ - (charFun μ t).re)) =
      ENNReal.ofReal (π / (2 * Gamma (q + 1) * sin (π * q / 2))) *
        ∫⁻ x, ENNReal.ofReal (|x| ^ q) ∂μ := by
  have hnonneg (t x : ℝ) : 0 ≤ 1 - cos (t * x) := sub_nonneg.mpr (cos_le_one _)
  have hinner (t : ℝ) (ht : 0 < t) :
      ∫⁻ x, ENNReal.ofReal (t ^ (-(q + 1)) * (1 - cos (t * x))) ∂μ =
        ENNReal.ofReal (t ^ (-(q + 1)) * (μ.real univ - (charFun μ t).re)) := by
    have hcos : Integrable (fun x : ℝ ↦ cos (t * x)) μ :=
      (integrable_const (1 : ℝ)).mono' (by fun_prop)
        (ae_of_all _ fun x ↦ by simpa using abs_cos_le_one (t * x))
    have hchar : ∫ x, cos (t * x) ∂μ = (charFun μ t).re := by
      have he : Integrable (fun x : ℝ ↦ Complex.exp (t * x * Complex.I)) μ := by
        apply Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
        filter_upwards with x
        simp [Complex.norm_exp]
      simpa [charFun_apply_real, Complex.exp_re] using integral_re he
    have hint : Integrable (fun x : ℝ ↦ t ^ (-(q + 1)) * (1 - cos (t * x))) μ :=
      ((integrable_const (1 : ℝ)).sub hcos).const_mul _
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun x ↦ mul_nonneg (rpow_nonneg ht.le _) (hnonneg t x)),
      integral_const_mul, integral_sub (integrable_const _) hcos,
      integral_const, smul_eq_mul, mul_one, hchar]
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x,
        ENNReal.ofReal (t ^ (-(q + 1)) * (1 - cos (t * x))) ∂μ := by
      exact lintegral_congr_ae (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact (hinner t ht).symm)
    _ = ∫⁻ x, (∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal (t ^ (-(q + 1)) * (1 - cos (t * x)))) ∂μ :=
      lintegral_lintegral_swap (by fun_prop)
    _ = ∫⁻ x, ENNReal.ofReal (|x| ^ q *
        (π / (2 * Gamma (q + 1) * sin (π * q / 2)))) ∂μ := by
      congr 1
      ext x
      simp_rw [mul_comm _ x]
      rw [← ofReal_integral_eq_lintegral_ofReal
        (integrableOn_rpow_neg_mul_one_sub_cos hq hq2)]
      · exact congrArg ENNReal.ofReal (integral_Ioi_rpow_neg_mul_one_sub_cos hq hq2 x)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg (rpow_nonneg ht.le _) (hnonneg x t)
    _ = _ := by
      simp_rw [ENNReal.ofReal_mul (rpow_nonneg (abs_nonneg _) _)]
      rw [lintegral_mul_const _ (by fun_prop)]
      exact mul_comm _ _

/-- A finite real measure has a fractional absolute moment exactly when the corresponding
power-weighted characteristic-function difference is integrable on the positive half-line. -/
theorem integrable_abs_rpow_iff_integrableOn_sub_re_charFun (hq : 0 < q) (hq2 : q < 2) :
    Integrable (fun x : ℝ ↦ |x| ^ q) μ ↔
      IntegrableOn (fun t : ℝ ↦ t ^ (-(q + 1)) *
        (μ.real univ - (charFun μ t).re)) (Ioi 0) := by
  have hc : 0 < π / (2 * Gamma (q + 1) * sin (π * q / 2)) :=
    div_pos pi_pos (mul_pos (mul_pos (by norm_num) (Gamma_pos_of_pos (by linarith)))
      (sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [pi_pos])))
  have hn : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      0 ≤ t ^ (-(q + 1)) * (μ.real univ - (charFun μ t).re) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (rpow_nonneg ht.le _)
      (sub_nonneg.mpr ((Complex.re_le_norm _).trans (norm_charFun_le _)))
  simp only [IntegrableOn, Integrable, hasFiniteIntegral_iff_ofReal (ae_of_all μ fun x ↦
    rpow_nonneg (abs_nonneg x) q), hasFiniteIntegral_iff_ofReal hn]
  have hm : AEStronglyMeasurable (fun x : ℝ ↦ |x| ^ q) μ := by fun_prop
  have hf : AEStronglyMeasurable (fun t : ℝ ↦ t ^ (-(q + 1)) *
      (μ.real univ - (charFun μ t).re)) (volume.restrict (Ioi 0)) := by fun_prop
  simp only [hm, hf, true_and, lintegral_rpow_mul_sub_re_charFun hq hq2]
  simp only [ENNReal.mul_lt_top_iff, ENNReal.ofReal_lt_top, (ENNReal.ofReal_pos.mpr hc).ne',
    true_and, false_or]
  exact ⟨Or.inl, fun h ↦ h.elim id (fun hz ↦ by simp [hz])⟩

/-- The power-weighted integral of a finite measure's characteristic-function difference is
its fractional absolute moment times the cosine-kernel constant. -/
theorem integral_rpow_mul_sub_re_charFun (hq : 0 < q) (hq2 : q < 2)
    (hint : Integrable (fun x : ℝ ↦ |x| ^ q) μ) :
    ∫ t in Ioi (0 : ℝ), t ^ (-(q + 1)) * (μ.real univ - (charFun μ t).re) =
      (π / (2 * Gamma (q + 1) * sin (π * q / 2))) * ∫ x, |x| ^ q ∂μ := by
  have hn : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      0 ≤ t ^ (-(q + 1)) * (μ.real univ - (charFun μ t).re) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (rpow_nonneg ht.le _)
      (sub_nonneg.mpr ((Complex.re_le_norm _).trans (norm_charFun_le _)))
  have hc : 0 ≤ π / (2 * Gamma (q + 1) * sin (π * q / 2)) :=
    (div_pos pi_pos (mul_pos (mul_pos (by norm_num) (Gamma_pos_of_pos (by linarith)))
      (sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [pi_pos])))).le
  have hm : 0 ≤ ∫ x, |x| ^ q ∂μ := integral_nonneg fun x ↦ rpow_nonneg (abs_nonneg x) q
  apply (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg_of_ae hn) (mul_nonneg hc hm)).mp
  rw [ofReal_integral_eq_lintegral_ofReal
      ((integrable_abs_rpow_iff_integrableOn_sub_re_charFun hq hq2).mp hint) hn,
    ENNReal.ofReal_mul hc, ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all μ fun x ↦ rpow_nonneg (abs_nonneg x) q)]
  exact lintegral_rpow_mul_sub_re_charFun hq hq2

end TauCeti
