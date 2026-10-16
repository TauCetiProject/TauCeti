/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Integration
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import TauCeti.Geometry.Manifold.Boundary.Derivative

/-!
# Boundary restriction in coordinates

Boundary restriction is pullback along the actual coordinate-zero inclusion in each induced
chart. This description preserves C1 regularity on a C2 manifold.
-/

public section

noncomputable section

open Set Filter
open scoped Manifold Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

private theorem inChartAt_chart_apply [IsManifold I 1 M]
    (φ : RoughForm I M F k) (α : M) {x : M}
    (hx : x ∈ (extChartAt I α).source) (v : Fin k → E) :
    φ.inChartAt α (extChartAt I α x) v =
      φ x (fun i ↦ tangentCoordChange I α x x (v i)) := by
  rw [RoughForm.inChartAt_apply]
  have hx' : x ∈ (chartAt H α).source := by simpa only [extChartAt_source] using hx
  rw [← TangentBundle.symmL_trivializationAt hx', TangentBundle.symmL_trivializationAt_eq_core hx']
  rw [(extChartAt I α).left_inv hx]
  rfl

section Boundary

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 1 M]

local instance boundaryRestriction_isManifold : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1
    ((𝓡∂ (n + 1)).boundary M) := isManifold_boundary M one_ne_zero

/-- In a boundary-centered chart, boundary restriction is the actual flat pullback along the
coordinate-zero inclusion. -/
theorem inChartAt_boundaryRestriction (φ : RoughForm (𝓡∂ (n + 1)) M F k)
    (α : (𝓡∂ (n + 1)).boundary M) {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α).target) :
    (boundaryRestriction φ).inChartAt α y =
      (φ.inChartAt (α : M) (euclideanHalfSpaceBoundaryParam n y)).compContinuousLinearMap
        (euclideanHalfSpaceBoundaryParam n) := by
  let x := (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α).symm y
  have hx : x ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α).source :=
    (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α).map_target hy
  have hx' : (x : M) ∈ (extChartAt (𝓡∂ (n + 1)) (α : M)).source := by
    simpa only [extChartAt_source, boundaryChartedSpace_chartAt_source, mem_preimage] using hx
  have hxy : extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α x = y :=
    (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α).right_inv hy
  rw [← hxy, boundaryParam_extChartAt hx]
  ext v
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    inChartAt_chart_apply (boundaryRestriction φ) α hx,
    inChartAt_chart_apply φ (α : M) hx']
  have hbr := boundaryRestriction_apply φ x
    (fun i ↦ tangentCoordChange 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α x x (v i))
  rw [mfderiv_subtypeVal_boundary] at hbr
  apply hbr.trans
  congr 1
  funext i
  exact (congrArg (fun L ↦ L (v i))
    (tangentCoordChange_boundaryParam hx (mem_extChartAt_source x))).symm

/-- Extension by zero commutes with boundary restriction in a boundary-centered chart, including
all points outside the boundary chart target. -/
theorem indicator_inChartAt_boundaryRestriction (φ : RoughForm (𝓡∂ (n + 1)) M F k)
    (α : (𝓡∂ (n + 1)).boundary M) (y : EuclideanSpace ℝ (Fin n)) :
    ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α).target.indicator
      ((boundaryRestriction φ).inChartAt α)) y =
    (((extChartAt (𝓡∂ (n + 1)) (α : M)).target.indicator (φ.inChartAt (α : M)))
      (euclideanHalfSpaceBoundaryParam n y)).compContinuousLinearMap
        (euclideanHalfSpaceBoundaryParam n) := by
  classical
  by_cases hy : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α).target
  · rw [indicator_of_mem hy, indicator_of_mem
      ((boundaryParam_mem_extChartAt_target_iff α y).mpr hy)]
    exact inChartAt_boundaryRestriction φ α hy
  · rw [indicator_of_notMem hy, indicator_of_notMem
      (fun h ↦ hy ((boundaryParam_mem_extChartAt_target_iff α y).mp h))]
    rfl

/-- A `C¹` form on a `C²` manifold restricts to a `C¹` form on its actual boundary. -/
theorem IsSmoothForm.boundaryRestriction [IsManifold (𝓡∂ (n + 1)) 2 M]
    {φ : RoughForm (𝓡∂ (n + 1)) M F k} (hφ : IsSmoothForm (𝓡∂ (n + 1)) 1 φ) :
    IsSmoothForm 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 (TauCeti.boundaryRestriction φ) := by
  apply IsSmoothForm.of_contDiffWithinAt_inChartAt_self
  intro x
  let p := euclideanHalfSpaceBoundaryParam n
  let C := ContinuousAlternatingMap.compContinuousLinearMapCLM (F := F) (ι := Fin k) p
  have htarget := (boundaryParam_mem_extChartAt_target_iff x
    (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x x)).mpr (mem_extChartAt_target x)
  have hd := C.contDiff.contDiffWithinAt.comp _
    ((hφ.contDiffWithinAt_inChartAt (x : M) htarget).comp _ p.contDiff.contDiffWithinAt
      (s := range 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (fun y _ ↦ EuclideanHalfSpace.boundaryParam_mem_range y)) (mapsTo_univ _ _)
  have he : (TauCeti.boundaryRestriction φ).inChartAt x =ᶠ[
      𝓝[range 𝓘(ℝ, EuclideanSpace ℝ (Fin n))]
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x x)]
      fun y ↦ C (φ.inChartAt (x : M) (p y)) := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) x]
      with y hy
    exact inChartAt_boundaryRestriction φ x hy
  exact hd.congr_of_eventuallyEq he (he.self_of_nhdsWithin (by simp))

end Boundary

end TauCeti
