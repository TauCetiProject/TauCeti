/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Connectivity.BlockCut.Degree

/-!
# Degrees of cut vertices in the block--cut forest of a multigraph

This file transports the block--cut component-count formula from the underlying simple graph
to a multigraph.
-/

public section

open Set

universe u

namespace Graph

variable {α : Type u} {β : Type*} {G : Graph α β} {v : V(G)}

/-- **The multigraph block--cut degree formula.** For a cut vertex of a multigraph with finitely
many actual vertices, deleting that vertex adds its degree in the block--cut forest of the
underlying simple graph minus one to the number of components. -/
theorem IsCutVertex.componentCount_deleteVerts_add_one_eq_add_blockCutDegree
    [Finite V(G)] (hv : G.IsCutVertex v) :
    (G.deleteVerts {(v : α)}).componentCount + 1 = G.componentCount +
      (G.toSimpleGraph.blockCutGraph.neighborSet (.inr
        (⟨v, (G.isCutVertex_iff_toSimpleGraph_isCutVertex v.property).mp hv⟩ :
          G.toSimpleGraph.CutVertex))).ncard := by
  let c : G.toSimpleGraph.CutVertex :=
    ⟨v, (G.isCutVertex_iff_toSimpleGraph_isCutVertex v.property).mp hv⟩
  have hs : {x : V(G) | (x : α) ∉ ({(v : α)} : Set α)} = ({v}ᶜ : Set V(G)) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_compl_iff, Subtype.ext_iff]
  let e : (G.deleteVerts {(v : α)}).toSimpleGraph ≃g
      G.toSimpleGraph.induce ({v}ᶜ : Set V(G)) := by
    rw [← hs]
    exact G.toSimpleGraphDeleteVertsIso {(v : α)}
  have heq : Nat.card (G.deleteVerts {(v : α)}).toSimpleGraph.ConnectedComponent =
      Nat.card (G.toSimpleGraph.induce ({v}ᶜ : Set V(G))).ConnectedComponent :=
    Nat.card_congr e.connectedComponentEquiv
  rw [componentCount_eq_natCard_toSimpleGraph, componentCount_eq_natCard_toSimpleGraph, heq]
  exact c.natCard_connectedComponent_induce_compl_singleton_add_one

end Graph
