/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import TauCeti.Probability.Distributions.Gaussian.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Gaussian integration by parts

This file proves Gaussian integration by parts for any mean and variance, for test functions with
values in a Banach space. It assumes only that the derivative and the centered first moment are
integrable; integrability of the function itself follows. Real-valued and standard-normal forms
are recorded as corollaries.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TauCeti.Probability

/-- A continuous function whose centered first moment is integrable under `gaussianReal μ v` is
itself integrable under it: near the mean it is bounded, and away from the mean it is dominated by
its centered first moment. -/
theorem integrable_of_integrable_sub_smul_gaussianReal {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {μ : ℝ} {v : ℝ≥0} {f : ℝ → E} (hf : Continuous f)
    (hxf : Integrable (fun x => (x - μ) • f x) (gaussianReal μ v)) :
    Integrable f (gaussianReal μ v) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := μ - 1) (b := μ + 1)).exists_bound_of_continuousOn
    hf.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC μ ⟨by linarith, by linarith⟩)
  refine Integrable.mono' (g := fun x => C + ‖(x - μ) • f x‖) ((integrable_const C).add hxf.norm)
    hf.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  by_cases hx : |x - μ| < 1
  · have hx' : x ∈ Set.Icc (μ - 1) (μ + 1) := by
      rw [abs_lt] at hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact (hC x hx').trans (le_add_of_nonneg_right (norm_nonneg _))
  · calc
      ‖f x‖ ≤ |x - μ| * ‖f x‖ := le_mul_of_one_le_left (norm_nonneg _) (not_lt.mp hx)
      _ = ‖(x - μ) • f x‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ C + ‖(x - μ) • f x‖ := le_add_of_nonneg_left hC0

/-- **Gaussian integration by parts** for vector-valued test functions. For a differentiable
function whose derivative and centered first moment are integrable under `gaussianReal μ v`, its
centered first moment is the variance times the expectation of its derivative. At zero variance
both sides vanish. -/
theorem integral_sub_smul_eq_variance_smul_integral_deriv_gaussianReal {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (μ : ℝ) (v : ℝ≥0) (f : ℝ → E)
    (hf : Differentiable ℝ f)
    (hxf : Integrable (fun x => (x - μ) • f x) (gaussianReal μ v))
    (hdf : Integrable (deriv f) (gaussianReal μ v)) :
    ∫ x, (x - μ) • f x ∂(gaussianReal μ v) =
      (v : ℝ) • ∫ x, deriv f x ∂(gaussianReal μ v) := by
  rcases eq_or_ne v 0 with rfl | hv
  · have hm : StronglyMeasurable (fun x : ℝ => (x - μ) • f x) :=
      ((continuous_id.sub continuous_const).smul hf.continuous).stronglyMeasurable
    rw [gaussianReal_zero_var, integral_dirac' _ _ hm]
    simp
  have hv' : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  have hfi := integrable_of_integrable_sub_smul_gaussianReal hf.continuous hxf
  let p : ℝ → ℝ := gaussianPDFReal μ v
  have hfp : Integrable (fun x => (-(x - μ) / (v : ℝ) * p x) • f x) volume := by
    have h := Integrable.smul (-(v : ℝ)⁻¹) (integrable_gaussianPDFReal_smul_of_integrable hv hxf)
    refine h.congr (ae_of_all _ fun x => ?_)
    simp only [Pi.smul_apply, smul_smul]
    congr 1
    ring
  have hparts : ∫ x, p x • deriv f x = -∫ x, (-(x - μ) / (v : ℝ) * p x) • f x := by
    have h := integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (u := p) (v := f)
      (u' := fun x => -(x - μ) / (v : ℝ) * p x) (v' := deriv f)
      (fun x _ => hasDerivAt_gaussianPDFReal μ v x) (fun x _ => (hf x).hasDerivAt)
      (by simpa only [ContinuousLinearMap.lsmul_apply] using
        integrable_gaussianPDFReal_smul_of_integrable hv hdf)
      (by simpa only [ContinuousLinearMap.lsmul_apply] using hfp)
      (by simpa only [ContinuousLinearMap.lsmul_apply] using
        integrable_gaussianPDFReal_smul_of_integrable hv hfi)
    simpa only [ContinuousLinearMap.lsmul_apply] using h
  have hgauss (g : ℝ → E) : ∫ x, g x ∂(gaussianReal μ v) = ∫ x, p x • g x :=
    integral_gaussianReal_eq_integral_smul hv
  have hkernel (x : ℝ) :
      p x • (x - μ) • f x = (-(v : ℝ)) • ((-(x - μ) / (v : ℝ) * p x) • f x) := by
    rw [smul_smul, smul_smul]
    congr 1
    field_simp
  calc
    ∫ x, (x - μ) • f x ∂(gaussianReal μ v) = ∫ x, p x • (x - μ) • f x := hgauss _
    _ = ∫ x, (-(v : ℝ)) • ((-(x - μ) / (v : ℝ) * p x) • f x) :=
      integral_congr_ae (ae_of_all _ hkernel)
    _ = (-(v : ℝ)) • ∫ x, (-(x - μ) / (v : ℝ) * p x) • f x := integral_smul _ _
    _ = (v : ℝ) • ∫ x, p x • deriv f x := by rw [hparts, smul_neg, neg_smul]
    _ = (v : ℝ) • ∫ x, deriv f x ∂(gaussianReal μ v) := by rw [hgauss (deriv f)]

/-- **Gaussian integration by parts** for real test functions. -/
theorem integral_sub_mul_eq_variance_mul_integral_deriv_gaussianReal
    (μ : ℝ) (v : ℝ≥0) (f : ℝ → ℝ)
    (hf : Differentiable ℝ f)
    (hxf : Integrable (fun x => (x - μ) * f x) (gaussianReal μ v))
    (hdf : Integrable (deriv f) (gaussianReal μ v)) :
    ∫ x, (x - μ) * f x ∂(gaussianReal μ v) =
      (v : ℝ) * ∫ x, deriv f x ∂(gaussianReal μ v) :=
  integral_sub_smul_eq_variance_smul_integral_deriv_gaussianReal μ v f hf hxf hdf

/-- For the standard Gaussian, a differentiable test function satisfies Stein's identity whenever
its derivative and `x * f x` are integrable. -/
theorem integral_mul_eq_integral_deriv_gaussianReal (f : ℝ → ℝ)
    (hf : Differentiable ℝ f)
    (hxf : Integrable (fun x => x * f x) (gaussianReal 0 1))
    (hdf : Integrable (deriv f) (gaussianReal 0 1)) :
    ∫ x, x * f x ∂(gaussianReal 0 1) =
      ∫ x, deriv f x ∂(gaussianReal 0 1) := by
  have hxf' : Integrable (fun x => (x - 0) * f x) (gaussianReal 0 1) := by
    simpa using hxf
  simpa using
    (integral_sub_mul_eq_variance_mul_integral_deriv_gaussianReal
      (μ := 0) (v := 1) f hf hxf' hdf)

end TauCeti.Probability
