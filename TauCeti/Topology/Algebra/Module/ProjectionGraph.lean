/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
public import TauCeti.Topology.Homeomorph.SetCongr
public import Mathlib.Topology.OpenPartialHomeomorph.Defs

/-!
# Graphs over the range of a projection

A continuous map from the range of an idempotent continuous linear map into its kernel has an
embedded graph. The projection is a continuous left inverse of its graph parameterization.

## Main declarations

* `ContinuousLinearMap.isEmbedding_graph`: the graph parameterization over the range of a
  projection is an embedding.
* `ContinuousLinearMap.graphHomeomorph`: the part of the range of a projection lying in a set `s`
  is homeomorphic to the graph over it, with inverse given by the projection.
* `ContinuousLinearMap.projectionGraphChart`: the ambient coordinate change
  `z ↦ z - g (P z)` straightens the graph on an open cylinder over its parameter set.
-/

public section

open Set Topology

namespace ContinuousLinearMap

variable {R M : Type*} [Semiring R] [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  [ContinuousAdd M]

/-- A graph over the range of a continuous projection is embedded when its vertical component
lies in the kernel of the projection. -/
theorem isEmbedding_graph (P : M →L[R] M) (hP : IsIdempotentElem P) (g : M → M)
    (hPg : ∀ v ∈ range P, P (g v) = 0) (hg : ContinuousOn g (range P)) :
    IsEmbedding (fun v : range P ↦ (v : M) + g v) := by
  have hleft : Function.LeftInverse (rangeFactorization P) (fun v : range P ↦ (v : M) + g v) := by
    intro v
    apply Subtype.ext
    rw [rangeFactorization_coe, map_add, hPg v v.2, add_zero]
    exact (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap hP)).mp (LinearMap.mem_range.mpr v.2)
  exact hleft.isEmbedding P.continuous.rangeFactorization
    (continuous_subtype_val.add (hg.comp_continuous continuous_subtype_val Subtype.prop))

/-- The graph over the part of the range of a continuous projection lying in `s` is homeomorphic
to that part, when the vertical component of the graph lies in the kernel of the projection. -/
noncomputable def graphHomeomorph (P : M →L[R] M) (hP : IsIdempotentElem P) (g : M → M)
    (hPg : ∀ v ∈ range P, P (g v) = 0) (hg : ContinuousOn g (range P)) (s : Set M) :
    (Subtype.val ⁻¹' s : Set (range P)) ≃ₜ (fun v : M ↦ v + g v) '' (range P ∩ s) :=
  (Homeomorph.setCongr
    (Set.preimage_image_eq (Subtype.val ⁻¹' s)
      (isEmbedding_graph P hP g hPg hg).injective).symm).trans <|
    ((isEmbedding_graph P hP g hPg hg).homeomorphOfSubsetRange
      (Set.image_subset_range _ _)).trans <| .setCongr <| by
      rw [← Subtype.image_preimage_val, image_image]

/-- The graph homeomorphism sends `v` to `v + g v`. -/
@[simp]
theorem coe_graphHomeomorph_apply (P : M →L[R] M) (hP : IsIdempotentElem P) (g : M → M)
    (hPg : ∀ v ∈ range P, P (g v) = 0) (hg : ContinuousOn g (range P)) (s : Set M)
    (v : (Subtype.val ⁻¹' s : Set (range P))) :
    (graphHomeomorph P hP g hPg hg s v : M) = (v : M) + g v := by
  simp only [graphHomeomorph, Homeomorph.trans_apply, Homeomorph.setCongr_apply,
    IsEmbedding.homeomorphOfSubsetRange_apply_coe, Subtype.coe_mk]

/-- The inverse graph homeomorphism is given by the projection. -/
@[simp]
theorem coe_graphHomeomorph_symm_apply (P : M →L[R] M) (hP : IsIdempotentElem P) (g : M → M)
    (hPg : ∀ v ∈ range P, P (g v) = 0) (hg : ContinuousOn g (range P)) (s : Set M)
    (z : (fun v : M ↦ v + g v) '' (range P ∩ s)) :
    (((graphHomeomorph P hP g hPg hg s).symm z : range P) : M) = P z := by
  set v := (graphHomeomorph P hP g hPg hg s).symm z
  rw [← (graphHomeomorph P hP g hPg hg s).apply_symm_apply z, coe_graphHomeomorph_apply,
    map_add, hPg _ (v : range P).2, add_zero]
  exact ((LinearMap.IsIdempotentElem.mem_range_iff
    (ContinuousLinearMap.IsIdempotentElem.toLinearMap hP)).mp
      (LinearMap.mem_range.mpr (v : range P).2)).symm

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {R M : Type*} [Semiring R] [TopologicalSpace M] [AddCommGroup M] [Module R M]
  [IsTopologicalAddGroup M]

/-- The triangular ambient chart straightening a graph over the range of an idempotent
continuous linear map. Its source and target are the cylinder over `U`. The coordinate
change itself does not require idempotence. -/
def projectionGraphChart (P : M →L[R] M) (g : M → M)
    {U : Set M} (hU : IsOpen U) (hg : ContinuousOn g (P.range ∩ U))
    (hPg : ∀ v ∈ (P.range : Set M) ∩ U, P (g v) = 0) : OpenPartialHomeomorph M M where
  toFun z := z - g (P z)
  invFun z := z + g (P z)
  source := P ⁻¹' U
  target := P ⁻¹' U
  map_source' z hz := by simpa [hPg (P z) ⟨P.mem_range_self z, hz⟩] using hz
  map_target' z hz := by simpa [hPg (P z) ⟨P.mem_range_self z, hz⟩] using hz
  left_inv' z hz := by simp [hPg (P z) ⟨P.mem_range_self z, hz⟩]
  right_inv' z hz := by simp [hPg (P z) ⟨P.mem_range_self z, hz⟩]
  open_source := hU.preimage P.continuous
  open_target := hU.preimage P.continuous
  continuousOn_toFun := continuousOn_id.sub
    (hg.comp P.continuous.continuousOn fun z hz ↦ ⟨P.mem_range_self z, hz⟩)
  continuousOn_invFun := continuousOn_id.add
    (hg.comp P.continuous.continuousOn fun z hz ↦ ⟨P.mem_range_self z, hz⟩)

variable (P : M →L[R] M) (g : M → M)
  {U : Set M} (hU : IsOpen U) (hg : ContinuousOn g (P.range ∩ U))
  (hPg : ∀ v ∈ (P.range : Set M) ∩ U, P (g v) = 0)

@[simp]
theorem projectionGraphChart_source :
    (P.projectionGraphChart g hU hg hPg).source = P ⁻¹' U := (rfl)

@[simp]
theorem projectionGraphChart_target :
    (P.projectionGraphChart g hU hg hPg).target = P ⁻¹' U := (rfl)

@[simp]
theorem projectionGraphChart_apply (z : M) :
    P.projectionGraphChart g hU hg hPg z = z - g (P z) := (rfl)

@[simp]
theorem projectionGraphChart_symm_apply (z : M) :
    (P.projectionGraphChart g hU hg hPg).symm z = z + g (P z) := (rfl)

/-- On its source, the chart takes a graph precisely to the range of the projection.
The graph may be defined over a larger parameter set `S`, for example a closed disk whose
interior contains `U`. -/
theorem projectionGraphChart_mem_range_iff (hP : IsIdempotentElem P)
    {S : Set M} (hUS : U ⊆ S) (hPgS : ∀ v ∈ (P.range : Set M) ∩ S, P (g v) = 0)
    {z : M} (hz : P z ∈ U) :
    P.projectionGraphChart g hU hg hPg z ∈ P.range ↔
      z ∈ (fun v ↦ v + g v) '' ((P.range : Set M) ∩ S) := by
  have hfix (v : M) : v ∈ P.range ↔ P v = v :=
    LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap hP)
  constructor
  · intro h
    have heq : P z = z - g (P z) := by
      simpa only [projectionGraphChart_apply, map_sub,
        hPg (P z) ⟨P.mem_range_self z, hz⟩, sub_zero] using (hfix _).mp h
    exact ⟨P z, ⟨P.mem_range_self z, hUS hz⟩, (eq_sub_iff_add_eq).mp heq⟩
  · rintro ⟨v, ⟨hv, hvU⟩, rfl⟩
    have hvP := (hfix v).mp hv
    simp only [projectionGraphChart_apply, map_add, hvP, hPgS v ⟨hv, hvU⟩, add_zero,
      add_sub_cancel_right]
    exact hv

end ContinuousLinearMap
