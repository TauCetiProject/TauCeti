/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Isomorphism.PathFamily

/-!
# Mixed capacities under network isomorphisms

A network isomorphism transports an ordinary flow together with its vertex-capacity constraint.
The vertex capacities are relabelled by the vertex equivalence, just as arrow capacities are
transported by `TauCeti.Network.Iso.assignmentEquiv`. This gives an equivalence between flows
respecting corresponding vertex capacities and preserves their values.

The same relabelling transports a mixed separator by mapping its vertex and arrow finsets. Its
weight is unchanged: the vertex-capacity sum and the arrow-capacity sum are each reindexed along
an equivalence. Together with `TauCeti.Network.Iso.isMixedSeparator_map_iff`, this shows that the
mixed max-flow/min-cut data are independent of vertex and arrow labels.

## Main definitions

* `TauCeti.Network.Iso.mixedFlowEquiv`: transport of flows respecting vertex capacities.

## Main results

* `TauCeti.Network.Iso.respectsVertexCapacity_mapFlow_iff`: transport preserves and reflects
  the vertex-capacity constraint.
* `TauCeti.Network.Iso.val_mixedFlowEquiv`: mixed-flow transport preserves flow value.
* `TauCeti.Network.Iso.mixedSeparatorWeight_map`: relabelling preserves mixed-separator weight.
-/

public section

namespace TauCeti.Network.Iso

open Finset

universe u u' v v' w

variable {K : Type w} {V : Type u} {W : Type u'}

section Flow

variable [AddCommGroup K] [PartialOrder K]
  {N : Network.{u, v} K V} {N' : Network.{u', v'} K W}
  [Fintype V] [Fintype W] [∀ x y, Fintype (N.Hom x y)]
  [∀ x y, Fintype (N'.Hom x y)]

/-- Transporting a flow along a network isomorphism preserves and reflects whether it respects
the correspondingly relabelled vertex capacities. -/
@[simp]
theorem respectsVertexCapacity_mapFlow_iff (e : N ≃ₙ N') (cap : N.Assignment K)
    (c : V → K) (s t : V) (f : Flow cap s t) :
    (e.mapFlow f).RespectsVertexCapacity (c ∘ e.vertexEquiv.symm) ↔
      f.RespectsVertexCapacity c := by
  rw [Flow.respectsVertexCapacity_iff, Flow.respectsVertexCapacity_iff]
  constructor
  · intro hf x hxs hxt
    have h := hf (e.vertexEquiv x) (fun hxs' ↦ hxs (e.vertexEquiv.injective hxs'))
      (fun hxt' ↦ hxt (e.vertexEquiv.injective hxt'))
    have hsum : arrowSum (e.assignmentEquiv K f.toFun) univ {e.vertexEquiv x} =
        arrowSum f.toFun univ {x} := by
      simpa using e.arrowSum_assignmentEquiv f.toFun (univ : Finset V) ({x} : Finset V)
    rw [e.mapFlow_toFun, hsum] at h
    simpa using h
  · intro hf y hys hyt
    obtain ⟨x, rfl⟩ := e.vertexEquiv.surjective y
    have h := hf x (fun hxs ↦ hys (congrArg e.vertexEquiv hxs))
      (fun hxt ↦ hyt (congrArg e.vertexEquiv hxt))
    have hsum : arrowSum (e.assignmentEquiv K f.toFun) univ {e.vertexEquiv x} =
        arrowSum f.toFun univ {x} := by
      simpa using e.arrowSum_assignmentEquiv f.toFun (univ : Finset V) ({x} : Finset V)
    rw [e.mapFlow_toFun, hsum]
    simpa using h

/-- Transport of ordinary flows restricts to an equivalence on flows respecting corresponding
vertex capacities. -/
def mixedFlowEquiv (e : N ≃ₙ N') (cap : N.Assignment K) (c : V → K) (s t : V) :
    {f : Flow cap s t // f.RespectsVertexCapacity c} ≃
      {f : Flow (e.assignmentEquiv K cap) (e.vertexEquiv s) (e.vertexEquiv t) //
        f.RespectsVertexCapacity (c ∘ e.vertexEquiv.symm)} :=
  (e.flowEquiv cap s t).subtypeEquiv fun f ↦ by
    rw [flowEquiv_apply, respectsVertexCapacity_mapFlow_iff]

@[simp]
theorem mixedFlowEquiv_apply_val (e : N ≃ₙ N') (cap : N.Assignment K) (c : V → K)
    (s t : V) (f : {f : Flow cap s t // f.RespectsVertexCapacity c}) :
    (e.mixedFlowEquiv cap c s t f).val = e.flowEquiv cap s t f.val :=
  by rw [mixedFlowEquiv, Equiv.subtypeEquiv_apply]

@[simp]
theorem mixedFlowEquiv_symm_apply_val (e : N ≃ₙ N') (cap : N.Assignment K) (c : V → K)
    (s t : V)
    (f : {f : Flow (e.assignmentEquiv K cap) (e.vertexEquiv s) (e.vertexEquiv t) //
      f.RespectsVertexCapacity (c ∘ e.vertexEquiv.symm)}) :
    ((e.mixedFlowEquiv cap c s t).symm f).val = (e.flowEquiv cap s t).symm f.val :=
  by
    apply Flow.ext
    simp [mixedFlowEquiv]

/-- Transporting a flow respecting vertex capacities preserves its value. -/
theorem val_mixedFlowEquiv (e : N ≃ₙ N') (cap : N.Assignment K) (c : V → K)
    (s t : V) (f : {f : Flow cap s t // f.RespectsVertexCapacity c}) :
    (e.mixedFlowEquiv cap c s t f).val.val = f.val.val := by
  rw [mixedFlowEquiv_apply_val, e.flowEquiv_apply, e.val_mapFlow]

end Flow

section Separator

variable [AddCommMonoid K] [LE K]
  {N : Network.{u, v} K V} {N' : Network.{u', v'} K W}

/-- Relabelling the vertices and individual arrows of a mixed separator preserves its weight.
The statement does not require the separator property, so it also applies to arbitrary candidate
vertex and arrow sets. -/
theorem mixedSeparatorWeight_map (e : N ≃ₙ N') (cap : N.Assignment K) (c : V → K)
    (X : Finset V) (F : Finset (Σ x y, N.Hom x y)) :
    (∑ y ∈ X.map e.vertexEquiv.toEmbedding, (c ∘ e.vertexEquiv.symm) y) +
        ∑ a ∈ F.map e.totalHomEquiv.toEmbedding, (e.assignmentEquiv K cap) a.2.2 =
      (∑ x ∈ X, c x) + ∑ a ∈ F, cap a.2.2 := by
  simp only [Finset.sum_map, Equiv.coe_toEmbedding, Function.comp_apply,
    Equiv.symm_apply_apply, e.assignmentEquiv_apply_totalHomEquiv]

end Separator

end TauCeti.Network.Iso
