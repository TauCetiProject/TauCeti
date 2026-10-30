/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Negative powers as Gamma mixtures of exponentials

For `-1 < α` and `0 < x`, Euler's integral gives
`x ^ (-(α + 1)) = Γ(α + 1)⁻¹ * ∫ s in Ioi 0, s ^ α * exp (-(x * s))`.
Substituting this into a power-weighted half-line integral and exchanging the two integrals
turns it into a power-weighted integral of the Laplace transform of the integrand:

`∫ x in Ioi 0, x ^ (-(α + 1)) • g x =
  Γ(α + 1)⁻¹ • ∫ s in Ioi 0, s ^ α • ∫ x in Ioi 0, exp (-(x * s)) • g x`.

The only hypothesis is integrability of the left-hand integrand, which by Tonelli's theorem
is exactly the absolute integrability needed for Fubini's theorem. This reduces singular
power-law integrals, such as the compensated integrals against stable Lévy measures, to
integrals of rational Laplace transforms.

## Main results

* `TauCeti.integrableOn_rpow_smul_integral_exp_neg_mul_smul`: the power-weighted Laplace
  transform is integrable on the positive half-line.
* `TauCeti.integral_Ioi_rpow_neg_smul`: the exchange identity displayed above.
-/

public section

noncomputable section

open MeasureTheory Real Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {α : ℝ} {g : ℝ → E}

/-- Euler's integral in the form used to write `x ^ (-(α + 1))` as a Gamma mixture of
exponentials. -/
private lemma integral_rpow_mul_exp_neg_mul_Ioi_eq (hα : -1 < α) {x : ℝ} (hx : 0 < x) :
    ∫ s in Ioi (0 : ℝ), s ^ α * exp (-(x * s)) = x ^ (-(α + 1)) * Gamma (α + 1) := by
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := α + 1) (by linarith) hx
  rwa [add_sub_cancel_right, one_div, inv_rpow hx.le, ← rpow_neg hx.le] at h

/-- The joint integrand of the Gamma-mixture representation is integrable on the product of
two positive half-lines. -/
private lemma integrable_rpow_mul_exp_neg_mul_smul_prod (hα : -1 < α)
    (hint : IntegrableOn (fun x ↦ x ^ (-(α + 1)) • g x) (Ioi 0)) :
    Integrable (Function.uncurry fun x s : ℝ ↦ (s ^ α * exp (-(x * s))) • g x)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have hsint (x : ℝ) (hx : 0 < x) :
      IntegrableOn (fun s ↦ s ^ α * exp (-(x * s))) (Ioi 0) := by
    refine Integrable.of_integral_ne_zero ?_
    rw [integral_rpow_mul_exp_neg_mul_Ioi_eq hα hx]
    have := Gamma_pos_of_pos (by linarith : 0 < α + 1)
    positivity
  -- `g` is recovered from the integrand by multiplying back the nonvanishing power.
  have hg : AEStronglyMeasurable g (volume.restrict (Ioi 0)) := by
    refine ((Measurable.aestronglyMeasurable (by fun_prop : Measurable fun x : ℝ ↦
      x ^ (α + 1))).smul hint.aestronglyMeasurable).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x (hx : 0 < x)
    rw [Pi.smul_apply', smul_smul, ← rpow_add hx, add_neg_cancel, rpow_zero, one_smul]
  have hmeas : AEStronglyMeasurable (Function.uncurry fun x s : ℝ ↦
      (s ^ α * exp (-(x * s))) • g x)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) :=
    (Measurable.aestronglyMeasurable (by fun_prop)).smul hg.comp_fst
  rw [integrable_prod_iff hmeas]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x (hx : 0 < x)
    exact (hsint x hx).smul_const (g x)
  · refine (hint.norm.const_mul (Gamma (α + 1))).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x (hx : 0 < x)
    simp only [Function.uncurry_apply_pair, norm_smul, Real.norm_eq_abs]
    rw [integral_mul_const, ← setIntegral_congr_fun measurableSet_Ioi
      (fun s (hs : 0 < s) ↦ (abs_of_nonneg (by positivity : 0 ≤ s ^ α * exp (-(x * s)))).symm),
      integral_rpow_mul_exp_neg_mul_Ioi_eq hα hx, abs_of_nonneg (by positivity)]
    ring

/-- The power-weighted Laplace transform `s ↦ s ^ α • ∫ x in Ioi 0, exp (-(x * s)) • g x` is
integrable on the positive half-line whenever `x ↦ x ^ (-(α + 1)) • g x` is. -/
theorem integrableOn_rpow_smul_integral_exp_neg_mul_smul (hα : -1 < α)
    (hint : IntegrableOn (fun x ↦ x ^ (-(α + 1)) • g x) (Ioi 0)) :
    IntegrableOn (fun s ↦ s ^ α • ∫ x in Ioi (0 : ℝ), exp (-(x * s)) • g x) (Ioi 0) := by
  refine (integrable_rpow_mul_exp_neg_mul_smul_prod hα hint).integral_prod_right.congr ?_
  filter_upwards with s
  simp only [Function.uncurry_apply_pair, mul_smul, integral_smul]

/-- **Negative powers as Gamma mixtures of exponentials.** For `-1 < α`, a power-weighted
half-line integral is a power-weighted integral of Laplace transforms:
`∫ x in Ioi 0, x ^ (-(α + 1)) • g x =
  Γ(α + 1)⁻¹ • ∫ s in Ioi 0, s ^ α • ∫ x in Ioi 0, exp (-(x * s)) • g x`. -/
theorem integral_Ioi_rpow_neg_smul [CompleteSpace E] (hα : -1 < α)
    (hint : IntegrableOn (fun x ↦ x ^ (-(α + 1)) • g x) (Ioi 0)) :
    ∫ x in Ioi (0 : ℝ), x ^ (-(α + 1)) • g x =
      (Gamma (α + 1))⁻¹ •
        ∫ s in Ioi (0 : ℝ), s ^ α • ∫ x in Ioi (0 : ℝ), exp (-(x * s)) • g x := by
  have hΓ : 0 < Gamma (α + 1) := Gamma_pos_of_pos (by linarith)
  calc
    _ = ∫ x in Ioi (0 : ℝ), (Gamma (α + 1))⁻¹ •
          ∫ s in Ioi (0 : ℝ), (s ^ α * exp (-(x * s))) • g x := by
      refine setIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) ↦ ?_
      rw [integral_smul_const, integral_rpow_mul_exp_neg_mul_Ioi_eq hα hx, smul_smul]
      congr 1
      field_simp
    _ = (Gamma (α + 1))⁻¹ • ∫ s in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ),
          (s ^ α * exp (-(x * s))) • g x := by
      rw [integral_smul, integral_integral_swap
        (integrable_rpow_mul_exp_neg_mul_smul_prod hα hint)]
    _ = _ := by
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi fun s _ ↦ ?_
      simp only [mul_smul, integral_smul]

end TauCeti
