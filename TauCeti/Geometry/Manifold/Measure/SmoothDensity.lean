/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.MeasureTheory.Function.Jacobian
import TauCeti.Analysis.Calculus.FDeriv.Equiv

/-!
# Measures with a smooth positive density on a manifold

A measure `μ` on a manifold `M` modelled on a real normed space `E` has a **smooth positive
density** when in every chart `e` of the maximal smooth atlas it is `ρ(y) dy` for a function `ρ`
smooth and positive on the chart target (`TauCeti.HasSmoothPositiveDensity`): the integral against
`μ` of a continuous complex-valued function `f` with compact support in the chart source is
`∫_{e.target} ρ(y) f(e⁻¹ y) dy`. Here `dy` is the measure `volume` of the `MeasureSpace E`
instance on the model space, which is Lebesgue measure for `CoordinateSpace n`. These are the
measures for which formal adjoints and transposes of differential and pseudodifferential operators
on `M` are taken; the Riemannian volume of a smooth metric is one, although that is not shown here.

The measure `volume` on `E` itself is one when it is an additive Haar measure, such as Lebesgue
measure (`TauCeti.hasSmoothPositiveDensity_volume`): in a chart `e` of the maximal atlas of `E`,
its density is the absolute Jacobian determinant `|det D(e⁻¹)(y)|`, by the change of variables
formula.

## Main definitions

* `TauCeti.HasSmoothPositiveDensity E μ`: the measure `μ` on a manifold modelled on `E` is given in
  every chart of the maximal atlas by a smooth positive density with respect to the measure
  `volume` of the `MeasureSpace E` instance (Lebesgue measure for `CoordinateSpace n`).

## Main results

* `TauCeti.hasSmoothPositiveDensity_iff`: unfolding the definition.
* `TauCeti.hasSmoothPositiveDensity_volume`: the measure `volume` on a finite-dimensional real
  normed space, when it is an additive Haar measure, has a smooth positive density for the maximal
  atlas.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 16,
  the section on densities.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MeasurableSpace M]

variable (E) in
/-- A measure `μ` on a manifold `M` modelled on a real normed space `E` **has a smooth positive
density** when in every chart `e` of the maximal smooth atlas it is `ρ(y) dy` for a function `ρ`
smooth and positive on the chart target: the integral against `μ` of every continuous
complex-valued function `f` with compact support in the chart source is
`∫_{e.target} ρ(y) f(e⁻¹ y) dy`, where `dy` is the measure `volume` of the `MeasureSpace E` instance
(Lebesgue measure for `CoordinateSpace n`). -/
def HasSmoothPositiveDensity (μ : Measure M) : Prop :=
  ∀ e : OpenPartialHomeomorph M E, e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M →
    ∃ ρ : E → ℝ, ContDiffOn ℝ ∞ ρ e.target ∧ (∀ y ∈ e.target, 0 < ρ y) ∧
      ∀ f : M → ℂ, Continuous f → HasCompactSupport f → tsupport f ⊆ e.source →
        ∫ x, f x ∂μ = ∫ y in e.target, (ρ y : ℂ) * f (e.symm y)

/-- Unfolding `TauCeti.HasSmoothPositiveDensity`: in every chart of the maximal atlas, integration
against `μ` is integration in coordinates against a smooth positive density. -/
theorem hasSmoothPositiveDensity_iff {μ : Measure M} :
    HasSmoothPositiveDensity E μ ↔
      ∀ e : OpenPartialHomeomorph M E, e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M →
        ∃ ρ : E → ℝ, ContDiffOn ℝ ∞ ρ e.target ∧ (∀ y ∈ e.target, 0 < ρ y) ∧
          ∀ f : M → ℂ, Continuous f → HasCompactSupport f → tsupport f ⊆ e.source →
            ∫ x, f x ∂μ = ∫ y in e.target, (ρ y : ℂ) * f (e.symm y) :=
  Iff.rfl

/-- **Lebesgue measure has a smooth positive density.** In a chart `e` of the maximal atlas of a
finite-dimensional real normed space `E`, the density of `volume` (assumed to be an additive Haar
measure) is the absolute Jacobian determinant `|det D(e⁻¹)(y)|`, by the change of variables
formula. -/
theorem hasSmoothPositiveDensity_volume [FiniteDimensional ℝ E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] :
    HasSmoothPositiveDensity E (volume : Measure E) := by
  refine hasSmoothPositiveDensity_iff.2 fun e he ↦ ?_
  have hs : ContDiffOn ℝ ∞ e e.source :=
    contMDiffOn_iff_contDiffOn.1 (contMDiffOn_of_mem_maximalAtlas he)
  have hs' : ContDiffOn ℝ ∞ e.symm e.target :=
    contMDiffOn_iff_contDiffOn.1 (contMDiffOn_symm_of_mem_maximalAtlas he)
  refine ⟨fun y ↦ |(fderiv ℝ e.symm y).det|,
    e.symm.contDiffOn_abs_det_fderiv_of_contDiffOn (by simp) hs' hs,
    fun y hy ↦ abs_pos.2 (e.symm.det_fderiv_ne_zero_of_contDiffOn hs' hs (by simp) hy),
    fun f _ _ hfs ↦ ?_⟩
  have hd : ∀ y ∈ e.symm.source, HasFDerivAt e.symm (fderiv ℝ e.symm y) y :=
    fun y hy ↦ ((hs'.differentiableOn (by simp)).differentiableAt
      (e.open_target.mem_nhds hy)).hasFDerivAt
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := e.source)
      fun x hx ↦ image_eq_zero_of_notMem_tsupport fun h ↦ hx (hfs h),
    ← e.symm_target, integral_target_eq_integral_abs_det_fderiv_smul volume hd]
  simp [Complex.real_smul]

end TauCeti
