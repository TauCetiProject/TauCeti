/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent

/-!
# Graphs over the range of a projection

A continuous map from the range of an idempotent continuous linear map into its kernel has an
embedded graph. The projection is a continuous left inverse of its graph parameterization.
-/

public section

open Metric Set Topology

namespace ContinuousLinearMap

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A graph over the range of a continuous projection is embedded when its vertical component
lies in the kernel of the projection. -/
theorem isEmbedding_graph (P : X →L[ℝ] X) (hP : IsIdempotentElem P) (g : X → X)
    (hPg : ∀ v, P (g v) = 0) (hg : Continuous g) :
    IsEmbedding (fun v : range P ↦ (v : X) + g v) := by
  let q : X → range P := fun z ↦ ⟨P z, z, rfl⟩
  have hleft : Function.LeftInverse q (fun v : range P ↦ (v : X) + g v) := by
    intro v
    apply Subtype.ext
    change P ((v : X) + g v) = v
    rw [map_add, hPg, add_zero]
    exact (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap hP)).mp (LinearMap.mem_range.mpr v.2)
  exact hleft.isEmbedding (P.continuous.subtype_mk _)
    (continuous_subtype_val.add (hg.comp continuous_subtype_val))

/-- The inverse graph homeomorphism is given by the projection. -/
@[simp]
theorem coe_isEmbedding_graph_toHomeomorph_symm_apply (P : X →L[ℝ] X)
    (hP : IsIdempotentElem P)
    (g : X → X) (hPg : ∀ v, P (g v) = 0) (hg : Continuous g)
    (z : range (fun v : range P ↦ (v : X) + g v)) :
    ↑((isEmbedding_graph P hP g hPg hg).toHomeomorph.symm z) = P z := by
  obtain ⟨v, hv⟩ := z.2
  have hz : z = (isEmbedding_graph P hP g hPg hg).toHomeomorph v := by
    apply Subtype.ext
    simpa using hv.symm
  rw [hz, Homeomorph.symm_apply_apply, IsEmbedding.toHomeomorph_apply_coe, map_add, hPg,
    add_zero]
  exact ((LinearMap.IsIdempotentElem.mem_range_iff
    (ContinuousLinearMap.IsIdempotentElem.toLinearMap hP)).mp
      (LinearMap.mem_range.mpr v.2)).symm

/-- The graph over a closed ball in the range subtype is the graph over the corresponding
intersection in the ambient space. -/
theorem image_graph_closedBall (P : X →L[ℝ] X) (g : X → X) (ρ : ℝ) :
    (fun v : range P ↦ (v : X) + g v) '' {v : range P | ‖(v : X)‖ ≤ ρ} =
      (fun v : X ↦ v + g v) '' (range P ∩ closedBall 0 ρ) := by
  have hset : {v : range P | ‖(v : X)‖ ≤ ρ} =
      Subtype.val ⁻¹' closedBall 0 ρ := by
    ext v
    simp only [mem_ofPred_eq, mem_preimage, mem_closedBall_zero_iff]
  rw [hset, show (fun v : range P ↦ (v : X) + g v) =
    (fun v : X ↦ v + g v) ∘ Subtype.val from rfl, Set.image_comp,
    Subtype.image_preimage_val]

end ContinuousLinearMap
