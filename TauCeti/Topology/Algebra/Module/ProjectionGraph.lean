/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.LinearAlgebra.Projection

/-!
# Graphs over the range of a projection

A continuous map from the range of an idempotent continuous linear map into its kernel has an
embedded graph. The projection is a continuous left inverse of its graph parameterization.
-/

public section

open Metric Set Topology

namespace ContinuousLinearMap

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A point in the range of an idempotent continuous linear map is fixed by that map. -/
theorem IsIdempotentElem.apply_eq_self_of_mem_range (P : X →L[ℝ] X)
    (hP : IsIdempotentElem P) {v : X} (hv : v ∈ range P) : P v = v := by
  obtain ⟨w, rfl⟩ := hv
  rw [← mul_apply_eq_comp, hP.eq]

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
    exact IsIdempotentElem.apply_eq_self_of_mem_range P hP v.2
  exact hleft.isEmbedding (P.continuous.subtype_mk _)
    (continuous_subtype_val.add (hg.comp continuous_subtype_val))

/-- The graph of a map into the kernel of a continuous projection is homeomorphic to the range
of that projection. -/
noncomputable def graphHomeomorphRange (P : X →L[ℝ] X) (hP : IsIdempotentElem P)
    (g : X → X) (hPg : ∀ v, P (g v) = 0) (hg : Continuous g) :
    range P ≃ₜ range (fun v : range P ↦ (v : X) + g v) :=
  (isEmbedding_graph P hP g hPg hg).toHomeomorph

/-- The graph homeomorphism evaluates to the graph map. -/
@[simp]
theorem coe_graphHomeomorphRange_apply (P : X →L[ℝ] X) (hP : IsIdempotentElem P)
    (g : X → X) (hPg : ∀ v, P (g v) = 0) (hg : Continuous g) (v : range P) :
    ↑(graphHomeomorphRange P hP g hPg hg v) = (v : X) + g v := by
  simp [graphHomeomorphRange]

/-- The inverse graph homeomorphism is given by the projection. -/
@[simp]
theorem coe_graphHomeomorphRange_symm_apply (P : X →L[ℝ] X) (hP : IsIdempotentElem P)
    (g : X → X) (hPg : ∀ v, P (g v) = 0) (hg : Continuous g)
    (z : range (fun v : range P ↦ (v : X) + g v)) :
    ↑((graphHomeomorphRange P hP g hPg hg).symm z) = P z := by
  obtain ⟨v, hv⟩ := z.2
  have hz : z = graphHomeomorphRange P hP g hPg hg v := by
    apply Subtype.ext
    exact hv.symm
  rw [hz, Homeomorph.symm_apply_apply, coe_graphHomeomorphRange_apply, map_add, hPg,
    add_zero]
  exact (IsIdempotentElem.apply_eq_self_of_mem_range P hP v.2).symm

/-- The graph over a closed ball in the range subtype is the graph over the corresponding
intersection in the ambient space. -/
theorem image_graph_closedBall (P : X →L[ℝ] X) (g : X → X) (ρ : ℝ) :
    (fun v : range P ↦ (v : X) + g v) '' {v : range P | ‖(v : X)‖ ≤ ρ} =
      (fun v : X ↦ v + g v) '' (range P ∩ closedBall 0 ρ) := by
  ext x
  simp only [mem_image, mem_ofPred_eq, mem_inter_iff, mem_closedBall_zero_iff]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, ⟨v.2, hv⟩, rfl⟩
  · rintro ⟨v, ⟨hv, hn⟩, rfl⟩
    exact ⟨⟨v, hv⟩, hn, rfl⟩

end ContinuousLinearMap
