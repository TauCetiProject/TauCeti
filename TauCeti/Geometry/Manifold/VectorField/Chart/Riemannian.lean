/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Riemannian
public import TauCeti.Geometry.Manifold.VectorField.Chart.Derivative
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.MFDeriv.ContinuousLinearMap
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The metric pairing of vector fields at a zero

Let `M` be a boundaryless manifold with a continuous Riemannian metric `g`. This file proves a
product rule at a zero (`MDifferentiableAt.mvfderiv_inner_bundle_apply_of_eq_zero`): if a vector
field `σ` is differentiable at `x` and vanishes there, and `τ` is continuous at `x`, then
`y ↦ g_y (σ y, τ y)` is differentiable at `x` with derivative `v ↦ g_x (τ x, D v)`, where
`D = TauCeti.vectorFieldChartDerivative I σ x` is the chart derivative of `σ`. Since `σ x = 0`,
the variation of the metric and of `τ` does not contribute, so only the continuity of the metric
and of `τ` is needed. Near `x`, the pairing is a continuous family of linear maps applied to the
coordinate field of `σ`, so both results follow from the zero-value derivative rule
`TauCeti.mvfderiv_eq_comp_of_eventuallyEq_clm_apply` and its differentiability companion
`TauCeti.mdifferentiableAt_of_eventuallyEq_clm_apply`.

## Main results

* `MDifferentiableAt.inner_bundle_of_eq_zero`,
  `MDifferentiableAt.mvfderiv_inner_bundle_apply_of_eq_zero`: the derivative of the metric
  pairing of a vector field with another at a zero of the first.
-/

public section

open Bundle Filter Set VectorField
open scoped ContDiff Manifold Topology InnerProductSpace

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

variable {σ τ : (x : M) → TangentSpace I x} {x : M}

omit [I.Boundaryless] in
/-- The pairing with a field `τ` continuous at `x`, read through the inverse trivialization at
`x`, is continuous at `x`: against each fixed `u` it pairs `τ` with the field of constant
coordinates `u`. -/
private theorem continuousAt_innerSL_comp_symmL_trivializationAt
    (hτ : ContinuousAt (fun y ↦ (τ y : TangentBundle I M)) x) :
    ContinuousAt (fun y ↦ (innerSL ℝ (τ y)) ∘L
      (trivializationAt E (TangentSpace I) x).symmL ℝ y) x := by
  set e := trivializationAt E (TangentSpace I) x
  rw [continuousAt_clm_apply]
  intro u
  let X := FiberBundle.extend E (e.symm x u)
  have hX : ∀ p, X p = e.symm p u := fun p ↦ by
    simp only [X, FiberBundle.extend, e]
    rw [Trivialization.apply_mk_symm _ (FiberBundle.mem_baseSet_trivializationAt' x)]
  have hXc : ContinuousAt (fun p ↦ (X p : TangentBundle I M)) x :=
    (FiberBundle.contMDiffAt_extend (k := 0) I E (e.symm x u)).continuousAt
  refine (ContinuousAt.inner_bundle hτ hXc).congr ?_
  filter_upwards [e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)]
    with y hy
  rw [hX, ContinuousLinearMap.comp_apply, innerSL_apply_apply, Trivialization.symmL_apply _ hy]

/-- Near a zero `x` of `σ`, the metric pairing of `σ` with a field `τ` continuous at `x` is
`y ↦ c y (u y)`, where `u` is the coordinate field of `σ` in the chart at `x`, read on `M`, and
`c y = g (τ y, ·)` is read through the inverse trivialization. Here `u` is differentiable and
vanishes at `x`, `c` is continuous at `x`, and `c x` applied to the derivative of `u` is
`g_x (τ x, D ·)`, where `D` is the chart derivative of `σ`. -/
private theorem exists_eventuallyEq_clm_apply_inner_of_eq_zero
    (hσ : MDifferentiableAt I I.tangent (fun y ↦ (σ y : TangentBundle I M)) x) (hσ₀ : σ x = 0)
    (hτ : ContinuousAt (fun y ↦ (τ y : TangentBundle I M)) x) :
    ∃ (c : M → E →L[ℝ] ℝ) (u : M → E),
      (fun y ↦ c y (u y)) =ᶠ[𝓝 x] (fun y ↦ inner ℝ (σ y) (τ y)) ∧ ContinuousAt c x ∧
        MDifferentiableAt I 𝓘(ℝ, E) u x ∧ u x = 0 ∧
        ∀ v, c x (mvfderiv I u x v) =
          inner ℝ (τ x) (vectorFieldChartDerivative I σ x v : TangentSpace I x) := by
  set φ := extChartAt I x
  set e := trivializationAt E (TangentSpace I) x
  let U : E → E := mpullback 𝓘(ℝ, E) I φ.symm σ
  -- The coordinate field of `σ` is differentiable at the chart point, where it vanishes.
  have hU : DifferentiableAt ℝ U (φ x) := by
    have h := MDifferentiableWithinAt.differentiableWithinAt_mpullbackWithin_extChartAt_symm
      (s := univ) hσ.mdifferentiableWithinAt
    rw [I.range_eq_univ, mpullbackWithin_univ, preimage_univ, inter_univ] at h
    exact h.differentiableAt univ_mem
  have hU₀ : U (φ x) = 0 := by
    simp only [U, φ, mpullback_extChartAt_symm_apply_eq_mfderiv σ (mem_extChartAt_source x), hσ₀,
      map_zero]
    -- The zero of the tangent space at the chart point is the zero of `E`.
    rfl
  let c : M → E →L[ℝ] ℝ := fun y ↦ (innerSL ℝ (τ y)) ∘L e.symmL ℝ y
  refine ⟨c, U ∘ φ, ?_, continuousAt_innerSL_comp_symmL_trivializationAt hτ,
    hU.comp_mdifferentiableAt (mdifferentiableAt_extChartAt (mem_chart_source H x)), hU₀,
    fun v ↦ ?_⟩
  · filter_upwards [extChartAt_source_mem_nhds (I := I) x] with y hy
    have hb : y ∈ e.baseSet := by
      simpa only [e, TangentBundle.trivializationAt_baseSet, φ, extChartAt_source] using hy
    -- In the chart, `σ` is recovered from its coordinate field by the inverse trivialization.
    have hσy : e.symmL ℝ y (U (φ y)) = σ y := by
      have h₁ : U (φ y) = e.continuousLinearMapAt ℝ y (σ y) :=
        (mpullback_extChartAt_symm_apply_eq_mfderiv σ hy).trans (DFunLike.congr_fun
          (TangentBundle.continuousLinearMapAt_trivializationAt (by simpa [φ] using hy))
            (σ y)).symm
      rw [h₁, Trivialization.symmL_continuousLinearMapAt _ hb]
    rw [Function.comp_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, hσy,
      real_inner_comm]
  · -- The derivative of the coordinate field read on `M` is its derivative at the chart point.
    have hD : mvfderiv I (U ∘ φ) x = fderiv ℝ U (φ x) := by
      rw [mvfderiv_eq_fderiv_comp_extChartAt_symm]
      refine Filter.EventuallyEq.fderiv_eq ?_
      filter_upwards [extChartAt_target_mem_nhds (I := I) x] with z hz
      rw [Function.comp_apply, Function.comp_apply, φ.right_inv hz]
    simp only [ContinuousLinearMap.comp_apply, c, innerSL_apply_apply]
    rw [hD, Manifold.symmL_trivializationAt_self, vectorFieldChartDerivative_def]
    -- The chart derivative is the derivative of the coordinate field `U` at the chart point.
    rfl

/-- **The metric pairing at a zero is differentiable.** If a vector field `σ` is differentiable at
a zero `x` and `τ` is continuous at `x`, then for a continuous metric the pairing
`y ↦ g_y (σ y, τ y)` is differentiable at `x`. -/
theorem _root_.MDifferentiableAt.inner_bundle_of_eq_zero
    (hσ : MDifferentiableAt I I.tangent (fun y ↦ (σ y : TangentBundle I M)) x) (hσ₀ : σ x = 0)
    (hτ : ContinuousAt (fun y ↦ (τ y : TangentBundle I M)) x) :
    MDifferentiableAt I 𝓘(ℝ) (fun y ↦ inner ℝ (σ y) (τ y)) x := by
  obtain ⟨c, u, hf, hc, hu, hu₀, -⟩ := exists_eventuallyEq_clm_apply_inner_of_eq_zero hσ hσ₀ hτ
  exact mdifferentiableAt_of_eventuallyEq_clm_apply hf hc hu hu₀

/-- **The product rule at a zero.** If a vector field `σ` is differentiable at a zero `x` and `τ`
is continuous at `x`, then for a continuous metric the derivative at `x` of the pairing
`y ↦ g_y (σ y, τ y)` in the direction `v` is `g_x (τ x, D v)`, where `D` is the chart derivative
of `σ` at `x`. Neither the metric nor `τ` needs to be differentiable. -/
theorem _root_.MDifferentiableAt.mvfderiv_inner_bundle_apply_of_eq_zero
    (hσ : MDifferentiableAt I I.tangent (fun y ↦ (σ y : TangentBundle I M)) x) (hσ₀ : σ x = 0)
    (hτ : ContinuousAt (fun y ↦ (τ y : TangentBundle I M)) x) (v : TangentSpace I x) :
    mvfderiv I (fun y ↦ inner ℝ (σ y) (τ y)) x v =
      inner ℝ (τ x) (vectorFieldChartDerivative I σ x v : TangentSpace I x) := by
  obtain ⟨c, u, hf, hc, hu, hu₀, hcu⟩ := exists_eventuallyEq_clm_apply_inner_of_eq_zero hσ hσ₀ hτ
  rw [mvfderiv_eq_comp_of_eventuallyEq_clm_apply hf hc hu hu₀]
  exact hcu v

end TauCeti
