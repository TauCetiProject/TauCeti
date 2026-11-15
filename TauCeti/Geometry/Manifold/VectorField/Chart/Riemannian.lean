/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Riemannian
public import TauCeti.Geometry.Manifold.VectorField.Chart.Derivative
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
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
and of `τ` is needed.

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

/-- In the chart at a zero `x` of `σ`, the metric pairing of `σ` with a field `τ` continuous at
`x` has a derivative which evaluates to `g_x (τ x, D v)`, where `D` is the chart derivative of
`σ`. In the chart, the pairing is `z ↦ c z (U z)` for the coordinate field `U` of `σ` and the
continuous family `c z = g (τ, ·)` read through the inverse trivialization; at a zero of `U` only
the continuity of `c` matters. -/
private theorem exists_hasFDerivAt_inner_comp_extChartAt_symm_of_eq_zero
    (hσ : MDifferentiableAt I I.tangent (fun y ↦ (σ y : TangentBundle I M)) x) (hσ₀ : σ x = 0)
    (hτ : ContinuousAt (fun y ↦ (τ y : TangentBundle I M)) x) :
    ∃ L : E →L[ℝ] ℝ, HasFDerivAt ((fun y ↦ inner ℝ (σ y) (τ y)) ∘ (extChartAt I x).symm) L
      (extChartAt I x x) ∧
        ∀ v, L v = inner ℝ (τ x) (vectorFieldChartDerivative I σ x v : TangentSpace I x) := by
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
  -- The pairing with `τ`, read through the inverse trivialization, is continuous at the chart
  -- point: against each fixed `u` it pairs `τ` with the field of constant coordinates `u`.
  let c : E → E →L[ℝ] ℝ := fun z ↦ (innerSL ℝ (τ (φ.symm z))) ∘L e.symmL ℝ (φ.symm z)
  have hc : ContinuousAt c (φ x) := by
    rw [continuousAt_clm_apply]
    intro u
    let X := FiberBundle.extend E (e.symm x u)
    have hX : ∀ p, X p = e.symm p u := fun p ↦ by
      simp only [X, FiberBundle.extend, e]
      rw [Trivialization.apply_mk_symm _ (FiberBundle.mem_baseSet_trivializationAt' x)]
    have hXc : ContinuousAt (fun p ↦ (X p : TangentBundle I M)) x :=
      (FiberBundle.contMDiffAt_extend (k := 0) I E (e.symm x u)).continuousAt
    have h := (ContinuousAt.inner_bundle hτ hXc).comp_of_eq
      (continuousAt_extChartAt_symm (I := I) x) (extChartAt_to_inv x)
    refine h.congr ?_
    filter_upwards [extChartAt_target_mem_nhds (I := I) x] with z hz
    rw [Function.comp_apply, hX, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      Trivialization.symmL_apply _ (TangentBundle.extChartAt_symm_mem_trivializationAt_baseSet hz)]
  refine ⟨c (φ x) ∘L fderiv ℝ U (φ x), ?_, fun v ↦ ?_⟩
  · have h₁ := (HasFDerivWithinAt.clm_apply_of_eq_zero hc.continuousWithinAt
      hU.hasFDerivAt.hasFDerivWithinAt hU₀).hasFDerivAt univ_mem
    refine h₁.congr_of_eventuallyEq ?_
    filter_upwards [extChartAt_target_mem_nhds (I := I) x] with z hz
    obtain ⟨y, hy, rfl⟩ : ∃ y ∈ φ.source, φ y = z := ⟨_, φ.map_target hz, φ.right_inv hz⟩
    have hb : y ∈ e.baseSet := by
      simpa only [e, TangentBundle.trivializationAt_baseSet, φ, extChartAt_source] using hy
    -- In the chart, `σ` is recovered from its coordinate field by the inverse trivialization.
    have hσy : e.symmL ℝ y (U (φ y)) = σ y := by
      have h₁ : U (φ y) = e.continuousLinearMapAt ℝ y (σ y) :=
        (mpullback_extChartAt_symm_apply_eq_mfderiv σ hy).trans (DFunLike.congr_fun
          (TangentBundle.continuousLinearMapAt_trivializationAt (by simpa [φ] using hy))
            (σ y)).symm
      rw [h₁, Trivialization.symmL_continuousLinearMapAt _ hb]
    simp only [Function.comp_apply, c]
    rw [φ.left_inv hy, ContinuousLinearMap.comp_apply, innerSL_apply_apply, hσy, real_inner_comm]
  · have hxx : φ.symm (φ x) = x := extChartAt_to_inv x
    simp only [ContinuousLinearMap.comp_apply, c, innerSL_apply_apply]
    rw [hxx, Manifold.symmL_trivializationAt_self, vectorFieldChartDerivative_def]
    -- The chart derivative is the derivative of the coordinate field `U` at the chart point.
    rfl

/-- **The metric pairing at a zero is differentiable.** If a vector field `σ` is differentiable at
a zero `x` and `τ` is continuous at `x`, then for a continuous metric the pairing
`y ↦ g_y (σ y, τ y)` is differentiable at `x`. -/
theorem _root_.MDifferentiableAt.inner_bundle_of_eq_zero
    (hσ : MDifferentiableAt I I.tangent (fun y ↦ (σ y : TangentBundle I M)) x) (hσ₀ : σ x = 0)
    (hτ : ContinuousAt (fun y ↦ (τ y : TangentBundle I M)) x) :
    MDifferentiableAt I 𝓘(ℝ) (fun y ↦ inner ℝ (σ y) (τ y)) x := by
  obtain ⟨L, hL, -⟩ := exists_hasFDerivAt_inner_comp_extChartAt_symm_of_eq_zero hσ hσ₀ hτ
  exact mdifferentiableAt_iff_differentiableAt_comp_extChartAt_symm.mpr hL.differentiableAt

/-- **The product rule at a zero.** If a vector field `σ` is differentiable at a zero `x` and `τ`
is continuous at `x`, then for a continuous metric the derivative at `x` of the pairing
`y ↦ g_y (σ y, τ y)` in the direction `v` is `g_x (τ x, D v)`, where `D` is the chart derivative
of `σ` at `x`. Neither the metric nor `τ` needs to be differentiable. -/
theorem _root_.MDifferentiableAt.mvfderiv_inner_bundle_apply_of_eq_zero
    (hσ : MDifferentiableAt I I.tangent (fun y ↦ (σ y : TangentBundle I M)) x) (hσ₀ : σ x = 0)
    (hτ : ContinuousAt (fun y ↦ (τ y : TangentBundle I M)) x) (v : TangentSpace I x) :
    mvfderiv I (fun y ↦ inner ℝ (σ y) (τ y)) x v =
      inner ℝ (τ x) (vectorFieldChartDerivative I σ x v : TangentSpace I x) := by
  obtain ⟨L, hL, hLv⟩ := exists_hasFDerivAt_inner_comp_extChartAt_symm_of_eq_zero hσ hσ₀ hτ
  rw [mvfderiv_eq_fderiv_comp_extChartAt_symm, hL.fderiv]
  exact hLv v

end TauCeti
