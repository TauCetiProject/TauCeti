/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.L1Space.CenteredMoment
public import TauCeti.Probability.Distributions.Gaussian.Basic
public import TauCeti.Probability.Distributions.Gaussian.Moments
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.HasLaw
import TauCeti.Probability.Distributions.Gaussian.Symmetry

/-!
# Gaussian integration by parts

This file proves Gaussian integration by parts for any mean and variance, for test functions with
values in a Banach space. For a differentiable test function, it assumes only that the derivative
and the centered first moment are integrable; integrability of the function itself follows.
Real-valued and standard-normal forms are recorded as corollaries, as is a parametric form that
integrates the identity against an s-finite measure in an auxiliary variable.
It also records the identity for affine test functions and the two-variable trigonometric
interpolation identity (`integral_mul_deriv_rot_gaussianReal`) used in the Gaussian Poincaré and
logarithmic Sobolev inequalities.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TauCeti.Probability

/-- **Gaussian integration by parts** for vector-valued test functions. For a differentiable
function whose derivative and centered first moment are integrable under `gaussianReal μ v`, its
centered first moment is `v` times the expectation of its derivative. At zero variance both sides
vanish. -/
theorem integral_sub_smul_eq_smul_integral_deriv_gaussianReal {E : Type*}
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
  have hfi := hf.continuous.integrable_of_integrable_sub_smul hxf
  let p : ℝ → ℝ := gaussianPDFReal μ v
  have hfp : Integrable (fun x => (-(x - μ) / (v : ℝ) * p x) • f x) volume := by
    have h := Integrable.smul (-(v : ℝ)⁻¹)
      ((integrable_gaussianReal_iff_integrable_gaussianPDFReal_smul hv).1 hxf)
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
        (integrable_gaussianReal_iff_integrable_gaussianPDFReal_smul hv).1 hdf)
      (by simpa only [ContinuousLinearMap.lsmul_apply] using hfp)
      (by simpa only [ContinuousLinearMap.lsmul_apply] using
        (integrable_gaussianReal_iff_integrable_gaussianPDFReal_smul hv).1 hfi)
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

/-- **Gaussian integration by parts with a parameter.** For a family of differentiable test
functions `g y`, Gaussian integration by parts in the second variable holds after integrating
against an s-finite measure `ν` in the first variable, provided both integrands are integrable for
the product measure `ν.prod (gaussianReal a v)`. -/
theorem integral_prod_gaussianReal_sub_smul_eq_smul_integral_deriv {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {ν : Measure α} [SFinite ν] (a : ℝ) (v : ℝ≥0) (g : α → ℝ → E)
    (hg : ∀ y, Differentiable ℝ (g y))
    (h₁ : Integrable (fun p ↦ (p.2 - a) • g p.1 p.2) (ν.prod (gaussianReal a v)))
    (h₂ : Integrable (fun p ↦ deriv (g p.1) p.2) (ν.prod (gaussianReal a v))) :
    ∫ p, (p.2 - a) • g p.1 p.2 ∂(ν.prod (gaussianReal a v)) =
      (v : ℝ) • ∫ p, deriv (g p.1) p.2 ∂(ν.prod (gaussianReal a v)) := by
  rw [integral_prod _ h₁, integral_prod _ h₂, ← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [h₁.prod_right_ae, h₂.prod_right_ae] with y hy₁ hy₂
  exact integral_sub_smul_eq_smul_integral_deriv_gaussianReal a v (g y) (hg y) hy₁ hy₂

/-- **Gaussian integration by parts** for real test functions. -/
theorem integral_sub_mul_eq_mul_integral_deriv_gaussianReal
    (μ : ℝ) (v : ℝ≥0) (f : ℝ → ℝ)
    (hf : Differentiable ℝ f)
    (hxf : Integrable (fun x => (x - μ) * f x) (gaussianReal μ v))
    (hdf : Integrable (deriv f) (gaussianReal μ v)) :
    ∫ x, (x - μ) * f x ∂(gaussianReal μ v) =
      (v : ℝ) * ∫ x, deriv f x ∂(gaussianReal μ v) :=
  integral_sub_smul_eq_smul_integral_deriv_gaussianReal μ v f hf hxf hdf

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
    (integral_sub_mul_eq_mul_integral_deriv_gaussianReal
      (μ := 0) (v := 1) f hf hxf' hdf)

/-- Gaussian integration by parts for `x * f (a + s * x)` under the standard law. -/
theorem integral_mul_comp_affine_gaussianReal {f : ℝ → ℝ} {A B : ℝ}
    (hf : ContDiff ℝ 1 f) (hA : ∀ x, |f x| ≤ A)
    (hB : ∀ x, |deriv f x| ≤ B) (a s : ℝ) :
    ∫ v, v * f (a + s * v) ∂(gaussianReal 0 1) =
      s * ∫ v, deriv f (a + s * v) ∂(gaussianReal 0 1) := by
  have hc : Continuous f := hf.continuous
  have hd : ∀ v, HasDerivAt (fun v => f (a + s * v)) (deriv f (a + s * v) * s) v := fun v => by
    have h1 : HasDerivAt (fun v : ℝ => a + s * v) s v := by
      simpa using ((hasDerivAt_id v).const_mul s).const_add a
    exact (hf.differentiable one_ne_zero (a + s * v)).hasDerivAt.comp v h1
  have hder : deriv (fun v => f (a + s * v)) = fun v => deriv f (a + s * v) * s :=
    funext fun v => (hd v).deriv
  have key := integral_mul_eq_integral_deriv_gaussianReal (fun v => f (a + s * v))
    (fun v => (hd v).differentiableAt)
    (by
      refine ((integrable_abs_gaussianReal 0 1).const_mul A).mono'
        (by fun_prop) (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hA _) (abs_nonneg _) |>.trans_eq (mul_comm _ _))
    (by
      rw [hder]
      refine (integrable_const (B * |s|)).mono' (by fun_prop) (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hB _) (abs_nonneg _))
  rw [key, hder]
  simp_rw [mul_comm (deriv f _) s]
  exact integral_const_mul s _

/-- **Gaussian integration by parts along the trigonometric coupling.** Under the standard planar
Gaussian law `γ ⊗ γ` (`γ = gaussianReal 0 1`), planar reflection symmetry and Gaussian integration
by parts rewrite the cross integral against the angular derivative of
`g (cos θ · p.1 + sin θ · p.2)` in terms of `deriv Φ` and `deriv g`. -/
theorem integral_mul_deriv_rot_gaussianReal {Φ g : ℝ → ℝ} {A₁ B₁ B₂ : ℝ}
    (hΦ : ContDiff ℝ 1 Φ) (hA₁ : ∀ x, |Φ x| ≤ A₁) (hB₁ : ∀ x, |deriv Φ x| ≤ B₁)
    (hg : ContDiff ℝ 1 g) (hB₂ : ∀ x, |deriv g x| ≤ B₂) (θ : ℝ) :
    ∫ p, Φ p.1 * (deriv g (Real.cos θ * p.1 + Real.sin θ * p.2) *
        (-Real.sin θ * p.1 + Real.cos θ * p.2))
        ∂(Measure.prod (gaussianReal 0 1) (gaussianReal 0 1)) =
      -Real.sin θ * ∫ p, deriv Φ p.1 * deriv g (Real.cos θ * p.1 + Real.sin θ * p.2)
        ∂(Measure.prod (gaussianReal 0 1) (gaussianReal 0 1)) := by
  have := hΦ.continuous
  have := hg.continuous_deriv le_rfl
  have := hΦ.continuous_deriv le_rfl
  have hB₂0 : 0 ≤ B₂ := (abs_nonneg _).trans (hB₂ 0)
  have hmp := measurePreserving_reflection_gaussianReal θ
  set c := Real.cos θ; set s := Real.sin θ
  have hrot (p : ℝ × ℝ) : c * (c * p.1 + s * p.2) + s * (s * p.1 - c * p.2) = p.1 := by
    linear_combination p.1 * Real.cos_sq_add_sin_sq θ
  -- Reflect `(p.1, p.2) ↦ (c * p.1 + s * p.2, s * p.1 - c * p.2)` and integrate by parts in `q.2`.
  let H : ℝ × ℝ → ℝ := fun q ↦ Φ (c * q.1 + s * q.2) * (deriv g q.1 * (-q.2))
  have hHc : Continuous H := by fun_prop
  have hHint : Integrable H (Measure.prod (gaussianReal 0 1) (gaussianReal 0 1)) :=
    ((integrable_abs_add_abs_gaussianReal 0 0 1 1).const_mul (A₁ * B₂)).mono'
      hHc.aestronglyMeasurable <| ae_of_all _ fun q ↦ by
        simp only [H, Real.norm_eq_abs, abs_mul, abs_neg, mul_assoc]
        exact mul_le_mul (hA₁ _) (mul_le_mul (hB₂ _) (le_add_of_nonneg_left (abs_nonneg _))
          (abs_nonneg _) hB₂0) (by positivity) ((abs_nonneg _).trans (hA₁ 0))
  have hch1 := hmp.hasLaw.integral_comp hHc.aestronglyMeasurable
  simp only [Function.comp_def] at hch1
  rw [show (fun p : ℝ × ℝ ↦ Φ p.1 * (deriv g (c * p.1 + s * p.2) * (-s * p.1 + c * p.2))) =
      fun p ↦ H (c * p.1 + s * p.2, s * p.1 - c * p.2) from
        funext fun p ↦ by simp only [H, hrot p]; ring, hch1, integral_prod _ hHint]
  have hinner (u : ℝ) :
      ∫ v, H (u, v) ∂(gaussianReal 0 1) =
        -s * (deriv g u * ∫ v, deriv Φ (c * u + s * v) ∂(gaussianReal 0 1)) := by
    simp_rw [show ∀ v, H (u, v) = -(deriv g u) * (v * Φ (c * u + s * v)) from
      fun _ ↦ by simp only [H]; ring]
    rw [integral_const_mul, integral_mul_comp_affine_gaussianReal hΦ hA₁ hB₁]; ring
  simp_rw [hinner, integral_const_mul]; congr 1
  -- Reflect back so `deriv Φ` is evaluated at `p.1` and `deriv g` at `c * p.1 + s * p.2`.
  let K : ℝ × ℝ → ℝ := fun q ↦ deriv g q.1 * deriv Φ (c * q.1 + s * q.2)
  have hKc : Continuous K := by fun_prop
  have hKint : Integrable K (Measure.prod (gaussianReal 0 1) (gaussianReal 0 1)) :=
    Integrable.of_bound hKc.aestronglyMeasurable (B₂ * B₁) <| ae_of_all _ fun _ ↦ by
      rw [Real.norm_eq_abs]
      simpa only [K, abs_mul] using mul_le_mul (hB₂ _) (hB₁ _) (abs_nonneg _) hB₂0
  have hch2 := hmp.hasLaw.integral_comp hKc.aestronglyMeasurable
  simp only [Function.comp_def, show (fun p : ℝ × ℝ ↦ K (c * p.1 + s * p.2, s * p.1 - c * p.2)) =
    fun p ↦ deriv Φ p.1 * deriv g (c * p.1 + s * p.2) from
      funext fun p ↦ by simp only [K, hrot p]; ring] at hch2
  rw [hch2, integral_prod _ hKint]
  exact (integral_congr_ae (.of_forall fun _ ↦ integral_const_mul _ _)).symm

end TauCeti.Probability
