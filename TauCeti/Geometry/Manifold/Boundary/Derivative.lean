/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Charts
public import TauCeti.Geometry.Manifold.Boundary.LinearAlgebra
public import TauCeti.Geometry.Manifold.Boundary.TransitionNormal

/-!
# Tangent maps of boundary charts

The boundary inclusion is the coordinate hyperplane parametrization in the preferred charts.
Its manifold derivative is therefore the actual zero-insertion linear map.
-/

public section

noncomputable section

open Set Filter
open scoped Manifold Topology

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 1 M]

local instance : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1
    ((𝓡∂ (n + 1)).boundary M) := isManifold_boundary M one_ne_zero

/-- The boundary chart target is exactly the zero-coordinate slice of the ambient target. -/
theorem boundaryParam_mem_extChartAt_target_iff
    (α : (𝓡∂ (n + 1)).boundary M) (y : EuclideanSpace ℝ (Fin n)) :
    euclideanHalfSpaceBoundaryParam n y ∈
      (extChartAt (𝓡∂ (n + 1)) (α : M)).target ↔
    y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α).target := by
  simp only [extChartAt_target, mem_inter_iff, mem_preimage,
    EuclideanHalfSpace.boundaryParam_mem_range, and_true,
    EuclideanHalfSpace.modelWithCornersEuclideanHalfSpace_symm_boundaryParam,
    modelWithCornersSelf_coe_symm, modelWithCornersSelf_coe, range_id,
    mem_univ, boundaryChartedSpace_chartAt_target]
  rfl

/-- Inserting the missing zero coordinate of a boundary chart recovers its ambient chart. -/
theorem boundaryParam_extChartAt {α x : (𝓡∂ (n + 1)).boundary M}
    (hα : x ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α).source) :
    euclideanHalfSpaceBoundaryParam n (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α x) =
      extChartAt (𝓡∂ (n + 1)) (α : M) (x : M) := by
  have hx : (x : M) ∈ (chartAt (EuclideanHalfSpace (n + 1)) (α : M)).source := by
    simpa only [extChartAt_source, boundaryChartedSpace_chartAt_source, mem_preimage] using hα
  have hb := (ModelWithCorners.mem_boundary_euclideanHalfSpace_iff_of_mem_atlas
    one_ne_zero (chart_mem_atlas _ (α : M)) hx).mp x.property
  have hp := congrArg Subtype.val (EuclideanHalfSpace.boundaryParam_boundaryProj hb)
  simpa only [EuclideanHalfSpace.boundaryParam_coe, EuclideanHalfSpace.boundaryProj_coe,
    extChartAt, OpenPartialHomeomorph.extend_coe, Function.comp_apply,
    modelWithCornersSelf_coe, id_eq, boundaryChartedSpace_chartAt_apply,
    modelWithCornersEuclideanHalfSpace_toFun] using hp

/-- The inclusion of the boundary has the coordinate zero-insertion map as its manifold
derivative in the canonical preferred charts. -/
theorem mfderiv_subtypeVal_boundary (x : (𝓡∂ (n + 1)).boundary M) :
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
      (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x =
        euclideanHalfSpaceBoundaryParam n := by
  have heq : writtenInExtChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)) x
      (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) =ᶠ[
        𝓝 (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x x)]
        euclideanHalfSpaceBoundaryParam n := by
    have ht := (chartAt (EuclideanSpace ℝ (Fin n)) x).open_target.mem_nhds
      ((chartAt (EuclideanSpace ℝ (Fin n)) x).map_source (mem_chart_source _ x))
    filter_upwards [ht] with z hz
    have hz' : EuclideanHalfSpace.boundaryParam n z ∈
        (chartAt (EuclideanHalfSpace (n + 1)) (x : M)).target := by
      rwa [boundaryChartedSpace_chartAt_target M x] at hz
    simp only [writtenInExtChartAt, Function.comp_apply, mfld_simps]
    rw [boundaryChartedSpace_chartAt_symm_apply M x hz',
      (chartAt (EuclideanHalfSpace (n + 1)) (x : M)).right_inv hz',
      modelWithCornersEuclideanHalfSpace_toFun, EuclideanHalfSpace.boundaryParam_coe]
  apply HasMFDerivAt.mfderiv
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  have hd := (euclideanHalfSpaceBoundaryParam n).hasFDerivAt.congr_of_eventuallyEq heq
  convert hd.hasFDerivWithinAt (s := Set.range 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) using 1
  ext v
  rfl

/-- Boundary transition derivatives are the ambient transition derivatives restricted to the
coordinate hyperplane and then projected back to boundary coordinates. -/
theorem tangentCoordChange_boundary {α β x : (𝓡∂ (n + 1)).boundary M}
    (hα : x ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α).source)
    (hβ : x ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) β).source) :
    tangentCoordChange 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α β x =
      (euclideanHalfSpaceBoundaryProj n).comp
        ((tangentCoordChange (𝓡∂ (n + 1)) (α : M) (β : M) (x : M)).comp
          (euclideanHalfSpaceBoundaryParam n)) := by
  have hα' : (x : M) ∈ (chartAt (EuclideanHalfSpace (n + 1)) (α : M)).source := by
    simpa only [extChartAt_source, boundaryChartedSpace_chartAt_source, mem_preimage] using hα
  have hβ' : (x : M) ∈ (chartAt (EuclideanHalfSpace (n + 1)) (β : M)).source := by
    simpa only [extChartAt_source, boundaryChartedSpace_chartAt_source, mem_preimage] using hβ
  let z := extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α x
  let f := extChartAt (𝓡∂ (n + 1)) (β : M) ∘
    (extChartAt (𝓡∂ (n + 1)) (α : M)).symm
  have hd := ((𝓡∂ (n + 1)).contDiffWithinAt_extendCoordChange'
    (IsManifold.chart_mem_maximalAtlas (α : M))
    (IsManifold.chart_mem_maximalAtlas (β : M)) hα' hβ').differentiableWithinAt one_ne_zero
  -- The maximal-atlas theorem uses extendCoordChange and chart.extend. Identify
  -- their underlying functions with the named extended-chart composite f so that
  -- the following rewrite can match the boundary chart image.
  change DifferentiableWithinAt ℝ f (range (𝓡∂ (n + 1)))
    (extChartAt (𝓡∂ (n + 1)) (α : M) (x : M)) at hd
  have hd' := hd.hasFDerivWithinAt
  rw [← boundaryParam_extChartAt hα] at hd'
  have hc := hd'.comp z (euclideanHalfSpaceBoundaryParam n).hasFDerivAt.hasFDerivWithinAt
    (s := univ) (fun y _ ↦ EuclideanHalfSpace.boundaryParam_mem_range y)
  have hc' := (euclideanHalfSpaceBoundaryProj n).hasFDerivAt.comp_hasFDerivWithinAt z hc
  have heq : (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) β ∘
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α).symm) =ᶠ[𝓝 z]
      (euclideanHalfSpaceBoundaryProj n ∘ f ∘ euclideanHalfSpaceBoundaryParam n) := by
    have ht := (chartAt (EuclideanSpace ℝ (Fin n)) α).open_target.mem_nhds
      ((chartAt (EuclideanSpace ℝ (Fin n)) α).map_source
        (by simpa only [extChartAt_source] using hα))
    filter_upwards [ht] with y hy
    have hy' : EuclideanHalfSpace.boundaryParam n y ∈
        (chartAt (EuclideanHalfSpace (n + 1)) (α : M)).target := by
      rwa [boundaryChartedSpace_chartAt_target M α] at hy
    simp only [f, Function.comp_apply, mfld_simps, boundaryChartedSpace_chartAt_apply]
    rw [boundaryChartedSpace_chartAt_symm_apply M α hy']
    simp only [EuclideanHalfSpace.modelWithCornersEuclideanHalfSpace_symm_boundaryParam,
      EuclideanHalfSpace.boundaryProj_coe, modelWithCornersEuclideanHalfSpace_toFun]
  rw [tangentCoordChange_def, modelWithCornersSelf_coe, range_id, fderivWithin_univ]
  have hf := (hc'.hasFDerivAt (by simp)).congr_of_eventuallyEq heq
  simpa only [z, f, boundaryParam_extChartAt hα, tangentCoordChange_def] using hf.fderiv

/-- Boundary transition maps intertwine zero insertion with the ambient transition maps. -/
theorem tangentCoordChange_boundaryParam {α β x : (𝓡∂ (n + 1)).boundary M}
    (hα : x ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α).source)
    (hβ : x ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) β).source) :
    (tangentCoordChange (𝓡∂ (n + 1)) (α : M) (β : M) (x : M)).comp
        (euclideanHalfSpaceBoundaryParam n) =
      (euclideanHalfSpaceBoundaryParam n).comp
        (tangentCoordChange 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α β x) := by
  have hα' : (x : M) ∈ (extChartAt (𝓡∂ (n + 1)) (α : M)).source := by
    simpa only [extChartAt_source, boundaryChartedSpace_chartAt_source, mem_preimage] using hα
  have hβ' : (x : M) ∈ (extChartAt (𝓡∂ (n + 1)) (β : M)).source := by
    simpa only [extChartAt_source, boundaryChartedSpace_chartAt_source, mem_preimage] using hβ
  obtain ⟨a, -, ha⟩ := tangentCoordChange_normal_pos x.property hα' hβ'
  rw [tangentCoordChange_boundary hα hβ]
  apply ContinuousLinearMap.ext
  intro v
  apply euclideanHalfSpaceBoundaryParam_proj ?_ |>.symm
  rw [mem_euclideanHalfSpaceBoundary]
  -- Membership is the zeroth coordinate of the composed projection/transition map;
  -- unfold that dependent Euclidean-space application before using the normal factor.
  change (tangentCoordChange (𝓡∂ (n + 1)) (α : M) (β : M) (x : M)
    (euclideanHalfSpaceBoundaryParam n v)) 0 = 0
  rw [ha, euclideanHalfSpaceBoundaryParam_apply_zero, mul_zero]

/-- Ambient and boundary transition determinants differ by a strictly positive normal factor. -/
theorem exists_pos_det_tangentCoordChange_boundary {α β x : (𝓡∂ (n + 1)).boundary M}
    (hα : x ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α).source)
    (hβ : x ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) β).source) :
    ∃ a > 0, (tangentCoordChange (𝓡∂ (n + 1)) (α : M) (β : M) (x : M)).det =
      a * (tangentCoordChange 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α β x).det := by
  have hα' : (x : M) ∈ (extChartAt (𝓡∂ (n + 1)) (α : M)).source := by
    simpa only [extChartAt_source, boundaryChartedSpace_chartAt_source, mem_preimage] using hα
  have hβ' : (x : M) ∈ (extChartAt (𝓡∂ (n + 1)) (β : M)).source := by
    simpa only [extChartAt_source, boundaryChartedSpace_chartAt_source, mem_preimage] using hβ
  obtain ⟨a, ha, hA⟩ := tangentCoordChange_normal_pos x.property hα' hβ'
  refine ⟨a, ha, ?_⟩
  rw [tangentCoordChange_boundary hα hβ]
  exact ContinuousLinearMap.det_eq_normal_mul_boundary _ hA

end TauCeti
