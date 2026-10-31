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

This file proves Gaussian integration by parts for any mean and positive variance, under the
integrability hypotheses needed by the integration-by-parts theorem.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TauCeti.Probability

/-- **Gaussian integration by parts.** For a differentiable function whose value, derivative, and
centered first moment are integrable under `gaussianReal μ v`, its centered first moment is the
variance times the expectation of its derivative. -/
theorem integral_sub_mul_eq_variance_mul_integral_deriv_gaussianReal
    (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (f : ℝ → ℝ)
    (hf : Differentiable ℝ f)
    (hxf : Integrable (fun x => (x - μ) * f x) (gaussianReal μ v))
    (hdf : Integrable (deriv f) (gaussianReal μ v))
    (hfi : Integrable f (gaussianReal μ v)) :
    ∫ x, (x - μ) * f x ∂(gaussianReal μ v) =
      (v : ℝ) * ∫ x, deriv f x ∂(gaussianReal μ v) := by
  let p : ℝ → ℝ := gaussianPDFReal μ v
  have hconvert {g : ℝ → ℝ} (hg : Integrable g (gaussianReal μ v)) :
      Integrable (fun x => g x * p x) volume := by
    have h := hg
    rw [gaussianReal_of_var_ne_zero μ hv,
      integrable_withDensity_iff (measurable_gaussianPDF μ v)
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at h
    simpa [p, toReal_gaussianPDF, smul_eq_mul, mul_comm] using h
  have hfp : Integrable
      (fun x => f x * (-(x - μ) / (v : ℝ) * p x)) volume := by
    have h := (hconvert hxf).const_mul (-(v : ℝ)⁻¹)
    refine h.congr (ae_of_all _ fun x => ?_)
    dsimp [p]
    field_simp [NNReal.coe_ne_zero.mpr hv]
  have hdfp : Integrable (fun x => deriv f x * p x) volume :=
    hconvert hdf
  have hfip : Integrable (fun x => f x * p x) volume :=
    hconvert hfi
  have hderivp (x : ℝ) :
      HasDerivAt p (-(x - μ) / (v : ℝ) * p x) x := by
    exact hasDerivAt_gaussianPDFReal μ hv x
  have hparts :
      ∫ x, f x * (-(x - μ) / (v : ℝ) * p x) =
        -∫ x, deriv f x * p x := by
    apply integral_mul_deriv_eq_deriv_mul_of_integrable (u := f) (u' := deriv f)
      (v := p) (v' := fun x => -(x - μ) / (v : ℝ) * p x)
    · exact fun x _ => (hf x).hasDerivAt
    · exact fun x _ => hderivp x
    · exact hfp
    · exact hdfp
    · exact hfip
  have hgauss (g : ℝ → ℝ) :
      ∫ x, g x ∂(gaussianReal μ v) = ∫ x, p x * g x := by
    simpa [p, smul_eq_mul] using
      (integral_gaussianReal_eq_integral_smul (E := ℝ) (μ := μ) (v := v)
        (f := g) hv)
  have hkernel (x : ℝ) :
      p x * ((x - μ) * f x) =
        -(v : ℝ) * (f x * (-(x - μ) / (v : ℝ) * p x)) := by
    dsimp [p]
    field_simp [NNReal.coe_ne_zero.mpr hv]
  calc
    ∫ x, (x - μ) * f x ∂(gaussianReal μ v) =
        ∫ x, p x * ((x - μ) * f x) := by rw [hgauss]
    _ = ∫ x, -(v : ℝ) * (f x * (-(x - μ) / (v : ℝ) * p x)) := by
      apply integral_congr_ae
      exact ae_of_all _ hkernel
    _ = -(v : ℝ) * ∫ x, f x * (-(x - μ) / (v : ℝ) * p x) := by
      rw [integral_const_mul]
    _ = (v : ℝ) * ∫ x, deriv f x * p x := by rw [hparts]; ring
    _ = (v : ℝ) * ∫ x, deriv f x ∂(gaussianReal μ v) := by
      congr 1
      calc
        ∫ x, deriv f x * p x = ∫ x, p x * deriv f x := by
          congr 1
          ext x
          ring
        _ = ∫ x, deriv f x ∂(gaussianReal μ v) := (hgauss _).symm

/-- For the standard Gaussian, a differentiable test function satisfies Stein's identity whenever
the function, its derivative, and `x * f x` are integrable. -/
theorem integral_mul_eq_integral_deriv_gaussianReal (f : ℝ → ℝ)
    (hf : Differentiable ℝ f)
    (hxf : Integrable (fun x => x * f x) (gaussianReal 0 1))
    (hdf : Integrable (deriv f) (gaussianReal 0 1))
    (hfi : Integrable f (gaussianReal 0 1)) :
    ∫ x, x * f x ∂(gaussianReal 0 1) =
      ∫ x, deriv f x ∂(gaussianReal 0 1) := by
  have hxf' : Integrable (fun x => (x - 0) * f x) (gaussianReal 0 1) := by
    simpa using hxf
  simpa using
    (integral_sub_mul_eq_variance_mul_integral_deriv_gaussianReal
      (μ := 0) (v := 1) one_ne_zero f hf hxf' hdf hfi)

end TauCeti.Probability
