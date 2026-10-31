/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Gaussian integration by parts

This file proves the one-dimensional integration-by-parts identity for a standard Gaussian and a
continuously differentiable, compactly supported test function.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

private theorem hasDerivAt_gaussianPDFReal_standard (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  rw [gaussianPDFReal_def]
  have hq : HasDerivAt (fun x : ℝ => -(x ^ 2) / 2) (-x) x := by
    convert ((hasDerivAt_id x).pow 2).neg.div_const 2 using 1
    · ext y
      simp
    · simp only [id_eq]
      field_simp
      ring
  have he : HasDerivAt (fun x : ℝ => Real.exp (-(x ^ 2) / 2))
      (Real.exp (-(x ^ 2) / 2) * -x) x := by
    exact (Real.hasDerivAt_exp (-(x ^ 2) / 2)).comp x hq
  have hp := (hasDerivAt_const x (√(2 * Real.pi))⁻¹).mul he
  convert hp using 1
  · ext y
    simp only [NNReal.coe_one, mul_one, sub_zero]
    rfl
  · simp only [NNReal.coe_one, mul_one, sub_zero, zero_mul]
    ring

/-- For a continuously differentiable compactly supported test function, the expectation of
`Z * f Z` under the standard Gaussian equals the expectation of `f' Z`. -/
theorem integral_mul_eq_integral_deriv_gaussianReal (f : ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) (hcf : HasCompactSupport f) :
    ∫ x, x * f x ∂(gaussianReal 0 1) = ∫ x, deriv f x ∂(gaussianReal 0 1) := by
  let p : ℝ → ℝ := gaussianPDFReal 0 1
  have hcontp : Continuous p := by
    dsimp [p, gaussianPDFReal_def]
    fun_prop
  have hderivp : ∀ x, HasDerivAt p (-x * p x) x := by
    intro x
    exact hasDerivAt_gaussianPDFReal_standard x
  have hcontf : Continuous f := hf.continuous
  have hcontdf : Continuous (deriv f) := hf.continuous_deriv_one
  have hcompactdf : HasCompactSupport (deriv f) := hcf.deriv
  have hintf_p : Integrable (fun x => f x * p x) := by
    apply (hcontf.mul hcontp).integrable_of_hasCompactSupport
    exact HasCompactSupport.mul_right (f' := p) hcf
  have hintfp : Integrable (fun x => f x * (-x * p x)) := by
    apply (hcontf.mul ((continuous_id.neg).mul hcontp)).integrable_of_hasCompactSupport
    exact HasCompactSupport.mul_right (f' := fun x => -x * p x) hcf
  have hintdfp : Integrable (fun x => deriv f x * p x) := by
    apply (hcontdf.mul hcontp).integrable_of_hasCompactSupport
    exact HasCompactSupport.mul_right (f' := p) hcompactdf
  have hparts :
      ∫ x, f x * (-x * p x) = -∫ x, deriv f x * p x := by
    apply integral_mul_deriv_eq_deriv_mul_of_integrable
      (u := f) (u' := deriv f) (v := p) (v' := fun x => -x * p x)
    · intro x hx
      exact (hf.differentiable_one x).hasDerivAt
    · intro x hx
      exact hderivp x
    · exact hintfp
    · exact hintdfp
    · exact hintf_p
  have hgauss (g : ℝ → ℝ) :
      ∫ x, g x ∂(gaussianReal 0 (1 : NNReal)) = ∫ x, p x * g x := by
    simpa [p, smul_eq_mul] using
      (integral_gaussianReal_eq_integral_smul (E := ℝ) (μ := 0) (v := (1 : NNReal))
        (f := g) (by simp))
  calc
    ∫ x, x * f x ∂(gaussianReal 0 1) = ∫ x, p x * (x * f x) := hgauss _
    _ = -∫ x, f x * (-x * p x) := by
      rw [← integral_neg]
      congr 1
      ext x
      ring
    _ = ∫ x, deriv f x * p x := by rw [hparts]; simp
    _ = ∫ x, p x * deriv f x := by congr 1; ext x; ring
    _ = ∫ x, deriv f x ∂(gaussianReal 0 1) := (hgauss _).symm

end TauCeti.Probability
