/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Charts
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback
public import TauCeti.Geometry.Manifold.Measure
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Boundary restriction and null sets on manifolds

This file supplies the measure-theoretic and differential-form interfaces needed at the boundary of
an oriented manifold with boundary.  A manifold null set is defined chartwise, without installing a
measurable structure on the manifold.  For the Euclidean half-space model, its boundary is null
because every extended chart sends boundary points into the coordinate hyperplane.  Rough forms on a
manifold with boundary restrict to the boundary manifold by pulling back along the subtype
inclusion.
-/

public section

open Set
open MeasureTheory
open scoped Manifold

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) 1 M]
  {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] {j : ℕ}

/-- Restrict a rough form on a half-space manifold to its boundary manifold by pulling it back
along the subtype inclusion. -/
noncomputable def boundaryRestriction (φ : RoughForm (𝓡∂ (n + 1)) M F j) :
    RoughForm 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((𝓡∂ (n + 1)).boundary M) F j :=
  mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)) Subtype.val φ

/-- Evaluation of boundary restriction is evaluation of the original form on the tangent map of the
boundary inclusion. -/
@[simp]
theorem boundaryRestriction_apply (φ : RoughForm (𝓡∂ (n + 1)) M F j)
    (x : (𝓡∂ (n + 1)).boundary M) (v : Fin j → TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :
    boundaryRestriction φ x v = φ x (fun i ↦ mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (𝓡∂ (n + 1)) Subtype.val x (v i)) := by
  simp [boundaryRestriction]

/-- The boundary of a finite-dimensional half-space manifold is a chartwise null set. -/
theorem isNullSet_boundary :
    IsNullSet (𝓡∂ (n + 1)) ((𝓡∂ (n + 1)).boundary M) := by
  rw [isNullSet_iff]
  intro x μ hμ
  let s : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1))) := euclideanHalfSpaceBoundary n
  have hs : s ≠ ⊤ := by
    intro h
    have hm : (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin (n + 1))) ∈ s := by
      rw [h]
      trivial
    -- Unfold the local abbreviation so the coordinate-hyperplane witness can be tested.
    change (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin (n + 1))) ∈
      euclideanHalfSpaceBoundary n at hm
    rw [mem_euclideanHalfSpaceBoundary] at hm
    norm_num [Pi.single_apply] at hm
  refine measure_mono_null ?_ (_root_.MeasureTheory.Measure.addHaar_submodule μ s hs)
  rintro y ⟨z, hz, rfl⟩
  -- The measure bound is stated for the local hyperplane abbreviation `s`.
  change (extChartAt (𝓡∂ (n + 1)) x z) ∈ euclideanHalfSpaceBoundary n
  rw [mem_euclideanHalfSpaceBoundary]
  have hzsource : z ∈ (chartAt (EuclideanHalfSpace (n + 1)) x).source := by
    simpa only [extChartAt_source] using hz.2
  have hboundary :=
    (ModelWithCorners.isBoundaryPoint_iff_mem_frontier_range (I := 𝓡∂ (n + 1))
      one_ne_zero (IsManifold.chart_mem_maximalAtlas x) hzsource).1 hz.1
  rw [frontier_range_modelWithCornersEuclideanHalfSpace,
    modelWithCornersEuclideanHalfSpace_toFun] at hboundary
  simpa [extChartAt, OpenPartialHomeomorph.extend_coe] using hboundary.symm

end TauCeti
