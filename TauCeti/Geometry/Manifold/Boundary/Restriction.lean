/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Integration
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import TauCeti.Geometry.Manifold.Boundary.Derivative
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# Boundary restriction in coordinates

Boundary restriction is pullback along the actual coordinate-zero inclusion in each induced
chart. This description preserves arbitrary form regularity on a C1 manifold. Exterior
differentiation commutes with restriction under the C2/C1 naturality hypotheses.
-/

public section

noncomputable section

open Set Filter
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

section Boundary

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 1 M]

local instance boundaryRestriction_isManifold : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1
    ((𝓡∂ (n + 1)).boundary M) := isManifold_boundary M one_ne_zero

/-- Restricting a pulled-back form to the actual boundary is pullback along the restricted map. -/
theorem boundaryRestriction_mpullback {E' H' N : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
    {f : M → N} (hf : MDifferentiable (𝓡∂ (n + 1)) J f) (φ : RoughForm J N F k) :
    boundaryRestriction (mpullback (𝓡∂ (n + 1)) J f φ) =
      mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) J
        (fun x : (𝓡∂ (n + 1)).boundary M ↦ f x) φ := by
  rw [boundaryRestriction_eq_mpullback]
  have hinc := (isSmoothEmbedding_subtypeVal_boundary (n := n) (k := 1) M one_ne_zero).contMDiff
    |>.mdifferentiable one_ne_zero
  exact (mpullback_comp hinc hf φ).symm

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
    RoughForm.inChartAt_chart_apply (boundaryRestriction φ) α hx,
    RoughForm.inChartAt_chart_apply φ (α : M) hx']
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

/-- Boundary restriction preserves arbitrary regularity of forms on a `C¹` manifold. -/
theorem IsSmoothForm.boundaryRestriction {r : WithTop ℕ∞}
    {φ : RoughForm (𝓡∂ (n + 1)) M F k} (hφ : IsSmoothForm (𝓡∂ (n + 1)) r φ) :
    IsSmoothForm 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) r (TauCeti.boundaryRestriction φ) := by
  apply IsSmoothForm.of_contDiffWithinAt_inChartAt_self
  intro x
  let p := euclideanHalfSpaceBoundaryParam n
  let C := ContinuousAlternatingMap.compContinuousLinearMapCLM (F := F) (ι := Fin k) p
  have hcenter : p (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x x) =
      extChartAt (𝓡∂ (n + 1)) (x : M) (x : M) :=
    boundaryParam_extChartAt (mem_extChartAt_source x)
  have hcoord : ContDiffWithinAt ℝ r (φ.inChartAt (x : M))
      (range (𝓡∂ (n + 1))) (p (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x x)) := by
    rw [hcenter]
    exact hφ.contDiffWithinAt_inChartAt_self (x : M)
  have hd := C.contDiff.contDiffWithinAt.comp _
    (hcoord.comp _ p.contDiff.contDiffWithinAt
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

/-- Exterior differentiation commutes with restriction to the actual boundary. -/
theorem boundaryRestriction_mextDeriv [IsManifold (𝓡∂ (n + 1)) 2 M]
    {φ : RoughForm (𝓡∂ (n + 1)) M F k} (hφ : IsSmoothForm (𝓡∂ (n + 1)) 1 φ) :
    boundaryRestriction (mextDeriv φ) = mextDeriv (boundaryRestriction φ) := by
  have : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 2
      ((𝓡∂ (n + 1)).boundary M) := isManifold_boundary M (by norm_num : (2 : ℕ∞ω) ≠ 0)
  simpa only [boundaryRestriction_eq_mpullback] using mpullback_mextDeriv
    (isSmoothEmbedding_subtypeVal_boundary (n := n) (k := 2) M (by norm_num)).contMDiff
    ((isSmoothBundleForm_def 1 φ).mpr hφ.contMDiff)

end Boundary

end TauCeti
