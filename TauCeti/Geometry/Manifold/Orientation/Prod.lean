/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Orientability of product manifolds

The preferred transition derivative of a product is block diagonal. Products of source signs
therefore give an orientation lift of the product, including manifolds with boundary and corners.
-/

public section

noncomputable section

open Set
open scoped Manifold

variable {E H M E' H' M' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']
  [IsManifold I' 1 M']

/-- A product chart's within-range transition derivative is block diagonal. -/
theorem tangentCoordChange_prod {α β x : M × M'}
    (hα : x ∈ (extChartAt (I.prod I') α).source)
    (hβ : x ∈ (extChartAt (I.prod I') β).source) :
    tangentCoordChange (I.prod I') α β x =
      (tangentCoordChange I α.1 β.1 x.1).prodMap (tangentCoordChange I' α.2 β.2 x.2) := by
  rw [extChartAt_prod] at hα hβ
  have h₁ := (I.contDiffWithinAt_extendCoordChange'
    (IsManifold.chart_mem_maximalAtlas α.1) (IsManifold.chart_mem_maximalAtlas β.1)
    (by simpa only [extChartAt_source] using hα.1)
    (by simpa only [extChartAt_source] using hβ.1)).differentiableWithinAt one_ne_zero
  have h₂ := (I'.contDiffWithinAt_extendCoordChange'
    (IsManifold.chart_mem_maximalAtlas α.2) (IsManifold.chart_mem_maximalAtlas β.2)
    (by simpa only [extChartAt_source] using hα.2)
    (by simpa only [extChartAt_source] using hβ.2)).differentiableWithinAt one_ne_zero
  change DifferentiableWithinAt ℝ (extChartAt I β.1 ∘ (extChartAt I α.1).symm)
    (range I) (extChartAt I α.1 x.1) at h₁
  change DifferentiableWithinAt ℝ (extChartAt I' β.2 ∘ (extChartAt I' α.2).symm)
    (range I') (extChartAt I' α.2 x.2) at h₂
  have hu : UniqueDiffWithinAt ℝ (range I ×ˢ range I')
      (extChartAt I α.1 x.1, extChartAt I' α.2 x.2) := by
    rw [← ModelWithCorners.range_prod]
    apply (I.prod I').uniqueDiffOn
    exact ⟨(chartAt H α.1 x.1, chartAt H' α.2 x.2), rfl⟩
  have hderiv := HasFDerivWithinAt.prodMap (p := (extChartAt I α.1 x.1,
      extChartAt I' α.2 x.2))
    (h₁.hasFDerivWithinAt.mono (fst_image_prod_subset (range I) (range I')))
    (h₂.hasFDerivWithinAt.mono (snd_image_prod_subset (range I) (range I')))
  rw [tangentCoordChange_def, tangentCoordChange_def, tangentCoordChange_def]
  convert hderiv.fderivWithin hu using 1
  · simp only [extChartAt_prod, PartialEquiv.prod_coe, PartialEquiv.prod_coe_symm,
      ModelWithCorners.range_prod, Function.comp_def]
    rfl

namespace Manifold.OrientationLift

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
  {ι ι' : Type*} [Fintype ι] [Fintype ι']

/-- Two source-indexed lifts construct an orientation of their product. The arbitrary choice of
model orientation is sufficient for this existence result. -/
theorem nonempty_orientation_prod (o : OrientationLift I M ι) (o' : OrientationLift I' M' ι') :
    Nonempty (Orientation (I.prod I') (M × M') (Fin (Module.finrank ℝ (E × E')))) := by
  let left (α : M × M') (x : (extChartAt (I.prod I') α).source) :
      (extChartAt I α.1).source :=
    ⟨x.val.1, by exact (show x.val ∈ (extChartAt I α.1).source ×ˢ
      (extChartAt I' α.2).source from by
        simpa only [extChartAt_prod, PartialEquiv.prod_source] using x.property).1⟩
  let right (α : M × M') (x : (extChartAt (I.prod I') α).source) :
      (extChartAt I' α.2).source :=
    ⟨x.val.2, by exact (show x.val ∈ (extChartAt I α.1).source ×ˢ
      (extChartAt I' α.2).source from by
        simpa only [extChartAt_prod, PartialEquiv.prod_source] using x.property).2⟩
  refine ⟨Orientation.mk {
    modelOrientation := (Module.finBasis ℝ (E × E')).orientation
    card_eq := Fintype.card_fin _
    sign := fun α x ↦ o.sign α.1 (left α x) * o'.sign α.2 (right α x)
    locallyConstant_sign := ?_
    compatible := ?_ }⟩
  · intro α
    exact ((o.locallyConstant_sign α.1).comp_continuous
      ((continuous_fst.comp continuous_subtype_val).subtype_mk _)).mul
        ((o'.locallyConstant_sign α.2).comp_continuous
          ((continuous_snd.comp continuous_subtype_val).subtype_mk _))
  · intro α β x hα hβ
    have h₁ := o.compatible α.1 β.1 x.1 (left α ⟨x, hα⟩).property
      (left β ⟨x, hβ⟩).property
    have h₂ := o'.compatible α.2 β.2 x.2 (right α ⟨x, hα⟩).property
      (right β ⟨x, hβ⟩).property
    rw [tangentCoordChange_prod hα hβ, ContinuousLinearMap.det,
      ContinuousLinearMap.coe_prodMap, LinearMap.det_prodMap]
    simp only [Units.val_mul, Int.cast_mul]
    convert mul_pos h₁ h₂ using 1
    ring

end Manifold.OrientationLift
