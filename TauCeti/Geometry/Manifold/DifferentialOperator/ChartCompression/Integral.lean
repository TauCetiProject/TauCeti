/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import TauCeti.Geometry.Manifold.DifferentialOperator.ChartCompression.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.Analysis.Distribution.TestFunction.Basic

/-!
# Integrating a cutoff pullback against a measure read in a chart

Let `e` be a chart of the maximal smooth atlas of a manifold `M` modelled on a real normed space
`E`, and let `μ` be a measure on `M` that reads in the chart as `ρ(y) dy`: the integral against `μ`
of a continuous complex-valued function `f` with compact support in the chart source is
`∫_{e.target} ρ(y) f(e⁻¹ y) dy`. This holds for instance for a measure with a smooth positive
density (`TauCeti.HasSmoothPositiveDensity`). Pairing a function on `M` with the pullback
`(θ f) ∘ e` of a function on `E` by a cutoff `θ` in the chart target
(`OpenPartialHomeomorph.complexCutoffPullback`) is then a pairing in coordinates against `ρ θ dy`.

## Main results

* `OpenPartialHomeomorph.integral_inner_complexCutoffPullback`: pairing a continuous function on
  `M` with the pullback `(θ f) ∘ e` of a function on the chart target is pairing in coordinates
  against `ρ θ dy`.
* `OpenPartialHomeomorph.integral_inner_complexCutoffPullback_left`: the same with the pullback
  on the left of the pairing.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped ContDiff Manifold Distributions ComplexConjugate

namespace OpenPartialHomeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
  [OpensMeasurableSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [T2Space M] [MeasurableSpace M]
  {μ : Measure M} {e : OpenPartialHomeomorph M E} {ρ : E → ℝ}

/-- **Changing variables in a chart.** Let `ρ` be the density in the chart `e` of a measure `μ`
on `M`: integration against `μ` of a continuous complex-valued function with compact support in
the chart source is `∫_{e.target} ρ(y) f(e⁻¹ y) dy`. Pairing a continuous function `F` on `M` with
the pullback `(θ f) ∘ e` of a function `f` on `E` by a cutoff `θ` in the chart target is pairing
`F ∘ e⁻¹` with `f` against `ρ θ dy`. -/
theorem integral_inner_complexCutoffPullback (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hint : ∀ f : M → ℂ, Continuous f → HasCompactSupport f → tsupport f ⊆ e.source →
      ∫ x, f x ∂μ = ∫ y in e.target, (ρ y : ℂ) * f (e.symm y))
    (θ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (f : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, ℂ), ℂ⟯) {F : M → ℂ}
    (hF : Continuous F) :
    ∫ x, inner ℂ (F x) (e.complexCutoffPullback he θ f x) ∂μ =
      ∫ y, ((ρ y * θ y : ℝ) : ℂ) * inner ℂ (F (e.symm y)) (f y) := by
  have hsupp : tsupport (fun x ↦ inner ℂ (F x) (e.complexCutoffPullback he θ f x)) ⊆
      e.symm '' tsupport θ :=
    (closure_mono <| Function.support_subset_iff'.2 fun x hx ↦ by
      simp [Function.notMem_support.1 hx]).trans (e.tsupport_complexCutoffPullback_subset he θ f)
  rw [hint _ (hF.inner (e.complexCutoffPullback he θ f).contMDiff.continuous)
      ((e.isCompact_symm_image_tsupport θ).of_isClosed_subset (isClosed_tsupport _) hsupp)
      (hsupp.trans (e.symm_image_tsupport_subset_source θ)),
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) (s := e.target)
      (f := fun y ↦ ((ρ y * θ y : ℝ) : ℂ) * inner ℂ (F (e.symm y)) (f y)) fun y hy ↦ by
        simp [image_eq_zero_of_notMem_tsupport fun h ↦ hy (θ.tsupport_subset h)]]
  refine setIntegral_congr_fun e.open_target.measurableSet fun y hy ↦ ?_
  simp only [complexCutoffPullback_apply_of_mem he _ _ (e.map_target hy), e.right_inv hy,
    RCLike.inner_apply', Complex.real_smul]
  push_cast
  ring

/-- **Changing variables in a chart, the pullback on the left.** With `μ` and `ρ` as in
`OpenPartialHomeomorph.integral_inner_complexCutoffPullback`, pairing the pullback `(θ f) ∘ e`
with a continuous function `F` on `M` is pairing `f` with `F ∘ e⁻¹` against `ρ θ dy`. -/
theorem integral_inner_complexCutoffPullback_left
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hint : ∀ f : M → ℂ, Continuous f → HasCompactSupport f → tsupport f ⊆ e.source →
      ∫ x, f x ∂μ = ∫ y in e.target, (ρ y : ℂ) * f (e.symm y))
    (θ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (f : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, ℂ), ℂ⟯) {F : M → ℂ}
    (hF : Continuous F) :
    ∫ x, inner ℂ (e.complexCutoffPullback he θ f x) (F x) ∂μ =
      ∫ y, ((ρ y * θ y : ℝ) : ℂ) * inner ℂ (f y) (F (e.symm y)) := by
  have h := congrArg conj (e.integral_inner_complexCutoffPullback he hint θ f hF)
  rw [← integral_conj, ← integral_conj] at h
  simpa only [inner_conj_symm, map_mul, Complex.conj_ofReal] using h

end OpenPartialHomeomorph
