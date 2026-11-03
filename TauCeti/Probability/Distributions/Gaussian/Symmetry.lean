/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import TauCeti.MeasureTheory.Integral.OddSymmetric

/-!
# Symmetry of Gaussian measures

A centered Gaussian measure on a real separable Banach space is invariant under negation.
Consequently, an odd function of a Gaussian vector centered at its mean has integral zero.
This applies in particular to odd products of centered linear observables, without assuming
independence or a nonsingular covariance.
-/

public section

noncomputable section

open MeasureTheory

namespace ProbabilityTheory.IsGaussian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

/-- A Gaussian measure with mean zero is invariant under negation. -/
@[simp]
theorem map_neg_eq_self (μ : Measure E) [IsGaussian μ] (hμ : (∫ x, x ∂μ) = 0) :
    μ.map (fun x ↦ -x) = μ := by
  apply Measure.ext_of_charFunDual
  ext L
  calc
    _ = charFunDual μ (-L) := by
      rw [charFunDual_apply, charFunDual_apply,
        integral_map (by fun_prop) (by fun_prop)]
      simp
    _ = _ := by
      simp only [charFunDual_eq, integral_complex_ofReal, FunLike.coe_neg, Pi.neg_apply,
        integral_neg, variance_neg, integral_dual, hμ, map_zero, neg_zero]

/-- An odd function of a Gaussian vector centered at its mean has integral zero.
The statement also holds for nonintegrable functions, with the usual Bochner integral
totalization. -/
theorem integral_comp_sub_eq_zero_of_odd (μ : Measure E) [IsGaussian μ]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hf : Function.Odd f) : (∫ x, f (x - μ[id]) ∂μ) = 0 := by
  let ν := μ.map (fun x ↦ x - μ[id])
  have hν : ν[id] = 0 := by
    rw [integral_map (by fun_prop) (by fun_prop)]
    simp only [id_eq]
    rw [integral_sub integrable_fun_id (integrable_const _), integral_const]
    simp
  have : ν.IsNegInvariant := ⟨map_neg_eq_self ν hν⟩
  calc
    _ = ∫ x, f x ∂ν := by
      simpa only [ν, MeasurableEquiv.coe_addRight, sub_eq_add_neg] using
        (integral_map_equiv (μ := μ) (MeasurableEquiv.addRight (-μ[id])) f).symm
    _ = 0 := integral_eq_zero_of_odd hf

end ProbabilityTheory.IsGaussian
