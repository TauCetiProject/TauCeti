/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Mixtures of measures

This file identifies a mixture of jointly measurable densities with the measure whose density
is their pointwise integral. The result allows s-finite mixing and reference measures, so it
applies to probability mixtures and unnormalised integral representations.

## Main results

* `MeasureTheory.Measure.bind_withDensity` writes a mixture of `withDensity` measures as a single
  `withDensity` measure.
* `MeasureTheory.Measure.bind_eq_withDensity_of_ae_eq` allows the component-density presentation
  to hold only almost everywhere with respect to the mixing measure.
* `MeasureTheory.Measure.rnDeriv_bind_withDensity` identifies the Radon--Nikodym derivative of a
  mixture of densities.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace MeasureTheory.Measure

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- A mixture of measures with jointly measurable densities has density equal to the pointwise
integral of the component densities. -/
theorem bind_withDensity (rho : Measure A) (nu : Measure B) [SFinite rho] [SFinite nu]
    {f : A → B → ℝ≥0∞} (hf : Measurable f.uncurry) :
    rho.bind (fun a ↦ nu.withDensity (f a)) =
      nu.withDensity (fun b ↦ ∫⁻ a, f a b ∂rho) := by
  have hkernel : Measurable fun a ↦ nu.withDensity (f a) :=
    measurable_withDensity hf
  have hdensity : Measurable fun b ↦ ∫⁻ a, f a b ∂rho :=
    hf.lintegral_prod_left
  ext s hs
  rw [bind_apply hs hkernel.aemeasurable, withDensity_apply _ hs]
  simp_rw [withDensity_apply _ hs]
  exact lintegral_lintegral_swap (μ := rho) (ν := nu.restrict s) hf.aemeasurable

/-- If almost every component of a measurable family has a density with respect to the same
reference measure, then its mixture has the integrated density. -/
theorem bind_eq_withDensity_of_ae_eq (rho : Measure A) (nu : Measure B)
    [SFinite rho] [SFinite nu] {K : A → Measure B} {f : A → B → ℝ≥0∞}
    (hf : Measurable f.uncurry)
    (hKf : K =ᵐ[rho] fun a ↦ nu.withDensity (f a)) :
    rho.bind K = nu.withDensity (fun b ↦ ∫⁻ a, f a b ∂rho) := by
  rw [bind_congr_right hKf, bind_withDensity rho nu hf]

/-- The Radon--Nikodym derivative of a mixture of densities is the pointwise integral of the
component densities. -/
theorem rnDeriv_bind_withDensity {rho : Measure A} {nu : Measure B} {K : A → Measure B}
    {f : A → B → ℝ≥0∞} [SFinite rho] [SigmaFinite nu]
    (hf : Measurable f.uncurry) (hKf : K =ᵐ[rho] fun a ↦ nu.withDensity (f a)) :
    (rho.bind K).rnDeriv nu =ᵐ[nu] fun b ↦ ∫⁻ a, f a b ∂rho := by
  rw [bind_eq_withDensity_of_ae_eq rho nu hf hKf]
  exact rnDeriv_withDensity nu hf.lintegral_prod_left

end MeasureTheory.Measure
