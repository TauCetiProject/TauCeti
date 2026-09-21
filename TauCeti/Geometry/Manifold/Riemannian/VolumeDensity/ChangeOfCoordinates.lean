/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Determinant

/-!
# Change of coordinates for Riemannian volume density

The Riemannian volume density in a chart transforms by the absolute Jacobian determinant of a
change of coordinates. This file identifies the frame-change matrix in
`TauCeti.chartVolumeDensity_changeFrame` with the matrix of Mathlib's tangent coordinate change,
then states the resulting coordinate formula and its coordinate-domain form.

These formulas are the compatibility needed to assemble the chart densities into a measure on a
manifold. They apply to manifolds with boundary and corners: derivatives are taken within the
range of the model with corners, exactly as in Mathlib's tangent-bundle construction.

The convention follows J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM
176 (2018), Proposition 2.44.

## Main results

* `TauCeti.chartVolumeDensity_changeChart`: the volume density transforms by the absolute
  determinant of the tangent coordinate change.
* `TauCeti.chartVolumeDensity_symm_apply_changeChart_fderivWithin`: the coordinate-domain form
  used by change-of-variables arguments.
-/

public section

open Bundle FiberBundle Riemannian.Tensor
open scoped Manifold

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- On the overlap of two charts, the Riemannian volume density in the source chart is the
density in the target chart multiplied by the absolute determinant of the tangent coordinate
change. -/
theorem chartVolumeDensity_changeChart (α β : M) {x : M}
    (hα : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hβ : x ∈ (trivializationAt E (TangentSpace I) β).baseSet) :
    chartVolumeDensity (I := I) α x =
      |(tangentCoordChange I α β x).det| *
        chartVolumeDensity (I := I) β x := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (Module.finBasis ℝ E),
    Manifold.tangentCoordChange_toMatrix α β (Module.finBasis ℝ E) hα hβ]
  exact chartVolumeDensity_changeFrame α β hα hβ

/-- The coordinate-domain form of the density transition law. At a point in the source of the
extended change from the `α` chart to the `β` chart, the source density pulled back by the
inverse `α` chart is the target density multiplied by the absolute Jacobian determinant. -/
theorem chartVolumeDensity_symm_apply_changeChart_fderivWithin (α β : M) {y : E}
    (hy : y ∈ ((extChartAt I α).symm ≫ extChartAt I β).source) :
    chartVolumeDensity (I := I) α ((extChartAt I α).symm y) =
      |(fderivWithin ℝ (extChartAt I β ∘ (extChartAt I α).symm) (Set.range I) y).det| *
        chartVolumeDensity (I := I) β ((extChartAt I α).symm y) := by
  rw [PartialEquiv.trans_source] at hy
  have hyα : y ∈ (extChartAt I α).target := by simpa only [PartialEquiv.symm_source] using hy.1
  have hxα : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
    (extChartAt I α).symm.map_source hyα
  have hxβ : (extChartAt I α).symm y ∈ (extChartAt I β).source := hy.2
  have hα : (extChartAt I α).symm y ∈
      (trivializationAt E (TangentSpace I) α).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet, extChartAt_source] using hxα
  have hβ : (extChartAt I α).symm y ∈
      (trivializationAt E (TangentSpace I) β).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet, extChartAt_source] using hxβ
  simpa only [tangentCoordChange_def, (extChartAt I α).right_inv hyα] using
    chartVolumeDensity_changeChart α β hα hβ

end TauCeti
