/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent

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

namespace TauCeti.Manifold.OrientationLift

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
  {ι ι' : Type*} [Fintype ι] [Fintype ι']

/-- Two source-indexed lifts construct an orientation of their product. The arbitrary choice of
model orientation is sufficient for this existence result. -/
theorem nonempty_orientation_prod (o : OrientationLift I M ι) (o' : OrientationLift I' M' ι') :
    Nonempty (Orientation (I.prod I') (M × M') (Fin (Module.finrank ℝ (E × E')))) := by
  let left (α : M × M') (x : (chartAt (ModelProd H H') α).source) :
      (chartAt H α.1).source :=
    ⟨x.val.1, by exact (show x.val ∈ (chartAt H α.1).source ×ˢ
      (chartAt H' α.2).source from by
        simpa only [prodChartedSpace_chartAt,
          OpenPartialHomeomorph.prod_source] using x.property).1⟩
  let right (α : M × M') (x : (chartAt (ModelProd H H') α).source) :
      (chartAt H' α.2).source :=
    ⟨x.val.2, by exact (show x.val ∈ (chartAt H α.1).source ×ˢ
      (chartAt H' α.2).source from by
        simpa only [prodChartedSpace_chartAt,
          OpenPartialHomeomorph.prod_source] using x.property).2⟩
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
    rw [← tangentCoordChange_def, TauCeti.Manifold.tangentCoordChange_prod
      ⟨by simpa only [extChartAt_source] using hα,
        by simpa only [extChartAt_source] using hβ⟩, ContinuousLinearMap.det,
      ContinuousLinearMap.coe_prodMap, LinearMap.det_prodMap]
    rw [← tangentCoordChange_def] at h₁ h₂
    simp only [Units.val_mul, Int.cast_mul]
    convert mul_pos h₁ h₂ using 1
    ring

end TauCeti.Manifold.OrientationLift
