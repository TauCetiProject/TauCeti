/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import TauCeti.Geometry.Manifold.DifferentialOperator.ChartCompression.Basic

/-!
# Integrating pullbacks of cutoffs against a density in a chart

Let `M` be a manifold modelled on a real normed space `E`, `e` a chart of its maximal smooth atlas
and `μ` a measure on `M` that reads in `e` as `ρ(y) dy`: integration against `μ` of a continuous
complex-valued function `f` with compact support in the chart source is
`∫_{e.target} ρ(y) f(e⁻¹ y) dy`. This is the chart condition defining a smooth positive density
(`TauCeti.HasSmoothPositiveDensity`).

For a cutoff `θ` with compact support in the chart target and a smooth function `f` on `E`, the
pullback `(θ f) ∘ e` (`OpenPartialHomeomorph.complexCutoffPullback`) has compact support in the
chart source, so pairing it with a continuous function `F` on `M` changes variables to the chart:

`∫ ⟪F, (θ f) ∘ e⟫ dμ = ∫ ρ θ ⟪F ∘ e⁻¹, f⟫ dy`.

## Main results

* `TauCeti.integral_inner_complexCutoffPullback`: the change of variables, with the pullback on the
  right of the inner product.
* `TauCeti.integral_inner_complexCutoffPullback_left`: the same, with the pullback on the left.
-/

public section

noncomputable section

open Set MeasureTheory ComplexConjugate
open scoped ContDiff Manifold Distributions

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
  [OpensMeasurableSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [T2Space M] [MeasurableSpace M]
  {μ : Measure M} {e : OpenPartialHomeomorph M E}
  (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {ρ : E → ℝ}
  (hint : ∀ f : M → ℂ, Continuous f → HasCompactSupport f → tsupport f ⊆ e.source →
    ∫ x, f x ∂μ = ∫ y in e.target, (ρ y : ℂ) * f (e.symm y))

include he hint

/-- **Changing variables in a chart.** Let `ρ` be the density in the chart `e` of a measure `μ`
on `M`. Pairing a continuous function `F` on `M` with the pullback `(θ f) ∘ e` of a function `f`
on `E` by a cutoff `θ` in the chart target is pairing `F ∘ e⁻¹` with `f` against `ρ θ dy`. -/
theorem integral_inner_complexCutoffPullback (θ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (f : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, ℂ), ℂ⟯) {F : M → ℂ} (hF : Continuous F) :
    ∫ x, inner ℂ (F x) (e.complexCutoffPullback he θ f x) ∂μ =
      ∫ y, ((ρ y * θ y : ℝ) : ℂ) * inner ℂ (F (e.symm y)) (f y) := by
  have hsupp : tsupport (fun x ↦ inner ℂ (F x) (e.complexCutoffPullback he θ f x)) ⊆
      e.symm '' tsupport θ :=
    (closure_mono <| Function.support_subset_iff'.2 fun x hx ↦ by
      simp [Function.notMem_support.1 hx]).trans (e.tsupport_complexCutoffPullback_subset he θ f)
  obtain ⟨hc, hs⟩ := OpenPartialHomeomorph.hasCompactSupport_and_tsupport_subset_source_of_subset
    θ hsupp
  rw [hint _ (hF.inner (e.complexCutoffPullback he θ f).contMDiff.continuous) hc hs,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) (s := e.target)
      (f := fun y ↦ ((ρ y * θ y : ℝ) : ℂ) * inner ℂ (F (e.symm y)) (f y)) fun y hy ↦ by
        simp [image_eq_zero_of_notMem_tsupport fun h ↦ hy (θ.tsupport_subset h)]]
  refine setIntegral_congr_fun e.open_target.measurableSet fun y hy ↦ ?_
  simp only [OpenPartialHomeomorph.complexCutoffPullback_apply_of_mem he _ _ (e.map_target hy),
    e.right_inv hy, RCLike.inner_apply', Complex.real_smul]
  push_cast
  ring

/-- **Changing variables in a chart, with the pullback on the left.** Pairing the pullback
`(θ f) ∘ e` with a continuous function `F` on `M` is pairing `f` with `F ∘ e⁻¹` against
`ρ θ dy`. -/
theorem integral_inner_complexCutoffPullback_left (θ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (f : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, ℂ), ℂ⟯) {F : M → ℂ} (hF : Continuous F) :
    ∫ x, inner ℂ (e.complexCutoffPullback he θ f x) (F x) ∂μ =
      ∫ y, ((ρ y * θ y : ℝ) : ℂ) * inner ℂ (f y) (F (e.symm y)) := by
  have h := congrArg conj (integral_inner_complexCutoffPullback he hint θ f hF)
  rw [← integral_conj, ← integral_conj] at h
  simpa only [inner_conj_symm, map_mul, Complex.conj_ofReal] using h

end TauCeti
