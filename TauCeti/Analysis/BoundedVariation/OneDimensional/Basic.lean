/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.VectorMeasure.IntegrationByParts
public import Mathlib.MeasureTheory.VectorMeasure.BoundedVariation
public import TauCeti.Analysis.BoundedVariation.TotalVariation
import Mathlib.Analysis.BoundedVariation

/-!
# Classical bounded variation and the distributional derivative

For a Banach-valued function of bounded variation on the real line, Mathlib's
`BoundedVariationOn.vectorMeasure` is its distributional derivative: integrating the
function against the derivative of a compactly supported `C¹` test function is the negative
of the integral of the test function against that measure. Values at individual jumps do not
matter; the measure records the difference between the right and left limits.

For real-valued functions we also bound the dual total variation on any open set by the
variation of this measure there. In particular classical global bounded variation implies
finite distributional variation, without requiring integrability on the whole real line.

We use Mathlib's construction of the vector measure associated to a bounded-variation
function and the cumulative-measure integration-by-parts identity.

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.2 (functions of one variable).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Distributions

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : ℝ → E}

/-- The classical derivative measure of a globally bounded-variation function is its
measure-valued distributional derivative. The test function is only required to be `C¹`.
Neither continuity of `f` nor integrability of `f` on the whole line is assumed. -/
theorem _root_.BoundedVariationOn.integral_deriv_smul_eq_neg_integral_vectorMeasure
    (hf : BoundedVariationOn f univ) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) :
    ∫ x, deriv φ x • f x = -∫ᵛ x, φ x ∂•hf.vectorMeasure := by
  have hdφ : Integrable (deriv φ) :=
    (hφ.continuous_deriv le_rfl).integrable_of_hasCompactSupport hcφ.deriv
  have hzero : ∫ x, deriv φ x = 0 :=
    integral_eq_zero_of_hasDerivAt_of_integrable
      (fun x ↦ (hφ.differentiable one_ne_zero x).hasDerivAt) hdφ
      (hφ.continuous.integrable_of_hasCompactSupport hcφ)
  have hcont : ∀ᵐ x, ContinuousAt f x := by
    rw [ae_iff]
    exact hf.countable_not_continuousAt.measure_zero volume
  have heq : (fun x ↦ deriv φ x • hf.vectorMeasure (Iic x)) =ᵐ[volume]
      (fun x ↦ deriv φ x • f x - deriv φ x • limUnder atBot f) := by
    filter_upwards [hcont] with x hx
    rw [hf.vectorMeasure_Iic, hx.continuousWithinAt.rightLim_eq, smul_sub]
  have hprod : Integrable (fun x ↦ deriv φ x • f x) := by
    simpa only [Pi.smul_def'] using hdφ.smul_of_top_left hf.memLp_top
  have h := hf.vectorMeasure.integral_deriv_smul_apply_Iic_eq_neg_integral hφ hcφ
  rw [integral_congr_ae heq,
    integral_sub hprod (hdφ.smul_const _),
    integral_smul_const, hzero, zero_smul, sub_zero] at h
  exact h

/-- On any open subset of the line, distributional total variation is bounded by the
variation of the classical derivative measure. No global integrability is required. -/
theorem _root_.BoundedVariationOn.totalVariationOn_le_variation_vectorMeasure
    {f : ℝ → ℝ} (hf : BoundedVariationOn f univ) (Ω : TopologicalSpace.Opens ℝ) :
    totalVariationOn volume Ω f ≤ hf.vectorMeasure.variation Ω := by
  refine totalVariationOn_le_iff.mpr fun φ hφ ↦ ?_
  have hpair : ∫ x, TestFunction.divergenceCLM φ x * f x =
      -∫ᵛ x, φ x ∂•hf.vectorMeasure := by
    simp_rw [TestFunction.divergenceCLM_apply_eq_deriv]
    exact hf.integral_deriv_smul_eq_neg_integral_vectorMeasure
      (φ.contDiff.of_le (by simp)) φ.hasCompactSupport
  have hloc : ∫ᵛ x in Ω, φ x ∂•hf.vectorMeasure = ∫ᵛ x, φ x ∂•hf.vectorMeasure :=
    VectorMeasure.setIntegral_eq_integral_of_forall_compl_eq_zero Ω.isOpen.measurableSet
      (fun x hx ↦ φ.zero_on_compl hx)
  rw [hpair]
  refine (Real.ofReal_le_enorm _).trans ?_
  rw [enorm_neg, ← hloc]
  have hφnorm (x : ℝ) : ‖φ x‖ₑ ≤ 1 := by
    rw [← ofReal_norm, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (hφ x)
  have hsmul : ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖ₑ ≤ 1 :=
    ContinuousLinearMap.opENorm_lsmul_le
  calc
    ‖∫ᵛ x in Ω, φ x ∂•hf.vectorMeasure‖ₑ ≤
        1 * ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖ₑ *
          hf.vectorMeasure.variation Ω :=
      VectorMeasure.enorm_setIntegral_le_of_enorm_le_const (fun x _ ↦ hφnorm x)
    _ ≤ 1 * 1 * hf.vectorMeasure.variation Ω := by gcongr
    _ = hf.vectorMeasure.variation Ω := by rw [one_mul, one_mul]

/-- Classical global bounded variation implies finite distributional variation on every
open set, including the whole line and functions with nonzero limits at infinity. -/
theorem _root_.BoundedVariationOn.totalVariationOn_lt_top
    {f : ℝ → ℝ} (hf : BoundedVariationOn f univ) (Ω : TopologicalSpace.Opens ℝ) :
    totalVariationOn volume Ω f < ∞ :=
  (hf.totalVariationOn_le_variation_vectorMeasure Ω).trans_lt (measure_lt_top _ _)

end TauCeti
