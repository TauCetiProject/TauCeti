/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent

/-!
# Graphs over the range of a projection

A continuous map from the range of an idempotent continuous linear map into its kernel has an
embedded graph. The projection is a continuous left inverse of its graph parameterization.

## Main declarations

* `ContinuousLinearMap.isEmbedding_graph`: the graph parameterization over the range of a
  projection is an embedding.
* `ContinuousLinearMap.graphHomeomorph`: the part of the range of a projection lying in a set `s`
  is homeomorphic to the graph over it, with inverse given by the projection.
-/

public section

open Set Topology

namespace ContinuousLinearMap

private theorem coe_setCongr_apply {Y : Type*} [TopologicalSpace Y] {s t : Set Y}
    (h : s = t) (v : s) : ((Homeomorph.setCongr h) v : Y) = v := by
  -- `setCongr` has no application theorem; use the computation theorem for its public `toEquiv`.
  exact congrArg Subtype.val (Set.equivOfEq_apply h v)

private theorem coe_homeomorphImage_apply {Y Z : Type*} [TopologicalSpace Y]
    [TopologicalSpace Z] {f : Y → Z} (hf : IsEmbedding f) (s : Set Y) (v : s) :
    (hf.homeomorphImage s v : Z) = f v := by
  simp only [IsEmbedding.homeomorphImage, Homeomorph.trans_apply, coe_setCongr_apply,
    IsEmbedding.toHomeomorph_apply_coe, Function.comp_apply]

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
  ((isEmbedding_graph P hP g hPg hg).homeomorphImage _).trans <| .setCongr <| by
    rw [← Subtype.image_preimage_val, image_image]

/-- The graph homeomorphism sends `v` to `v + g v`. -/
@[simp]
theorem coe_graphHomeomorph_apply (P : M →L[R] M) (hP : IsIdempotentElem P) (g : M → M)
    (hPg : ∀ v ∈ range P, P (g v) = 0) (hg : ContinuousOn g (range P)) (s : Set M)
    (v : (Subtype.val ⁻¹' s : Set (range P))) :
    (graphHomeomorph P hP g hPg hg s v : M) = (v : M) + g v := by
  simp only [graphHomeomorph, Homeomorph.trans_apply, coe_setCongr_apply,
    coe_homeomorphImage_apply]

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
