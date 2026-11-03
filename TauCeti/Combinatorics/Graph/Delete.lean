/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Graph.Delete
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# Deletion in standard multigraphs

This file computes edge deletion `Graph.deleteEdges` in two families of multigraphs: graphs
`Graph.ofSimpleGraph H` built from simple graphs, where deletion corresponds to
`SimpleGraph.deleteEdges`, and the graphs `Graph.banana u w F` on two vertices, where deletion
removes edges from `F`. These identities let deletion-based connectivity predicates be compared
with their simple-graph versions and evaluated on explicit examples. It also records that
deletion is antitone in the deleted set, `Graph.deleteEdges_anti_right`, complementing Mathlib's
`Graph.deleteEdges_mono_left`. Vertex deletion commutes with simplification up to the canonical
isomorphism `Graph.toSimpleGraphDeleteVertsIso`; its vertex map retains the original point.
-/

public section

open Set

namespace Graph

variable {α β : Type*}

/-- Deleting more edges gives a smaller graph. -/
@[gcongr]
theorem deleteEdges_anti_right (G : Graph α β) {F₁ F₂ : Set β} (h : F₁ ⊆ F₂) :
    G.deleteEdges F₂ ≤ G.deleteEdges F₁ := by
  simpa [union_eq_right.mpr h] using (G.deleteEdges F₁).deleteEdges_le (F := F₂)

/-- Deleting edges commutes with regarding a simple graph as a multigraph. -/
@[simp]
theorem ofSimpleGraph_deleteEdges (H : SimpleGraph α) (F : Set (Sym2 α)) :
    (Graph.ofSimpleGraph H).deleteEdges F = Graph.ofSimpleGraph (H.deleteEdges F) :=
  Graph.ext (by simp) fun e x y ↦ by simp [and_assoc]

/-- Deleting edges from a graph on two vertices removes them from its edge set. -/
@[simp]
theorem banana_deleteEdges (u w : α) (F D : Set β) :
    (banana u w F).deleteEdges D = banana u w (F \ D) :=
  Graph.ext (by simp) fun e x y ↦ by simp [and_assoc, and_comm (a := e ∉ D)]

/-- Simplifying after vertex deletion is the same as inducing the simplification on the
remaining actual vertices. -/
def toSimpleGraphDeleteVertsIso (G : Graph α β) (X : Set α) :
    (G.deleteVerts X).toSimpleGraph ≃g G.toSimpleGraph.induce {v : V(G) | (v : α) ∉ X} := by
  let e : V(G.deleteVerts X) ≃ {v : V(G) // (v : α) ∉ X} :=
    (Equiv.subtypeEquivRight fun _ ↦ by
      simp only [vertexSet_deleteVerts, mem_sdiff, mem_ofPred_eq]).trans
        (Equiv.Set.sep V(G) (· ∉ X))
  -- Both factors retain the underlying point: subtypeEquivRight changes only its proof,
  -- and Set.sep rearranges the two membership proofs into nested subtypes.
  have he (v : V(G.deleteVerts X)) : ((e v).val : α) = v := rfl
  refine { toEquiv := e, map_rel_iff' := ?_ }
  intro u v
  have hu := u.property
  have hv := v.property
  simp only [vertexSet_deleteVerts, mem_sdiff] at hu hv
  simp [toSimpleGraph_adj, Graph.Adj, deleteVerts_isLink, Subtype.ext_iff, he, hu.2, hv.2]

-- The forward and inverse coercions retain the original point through Equiv.trans,
-- subtypeEquivRight, and Set.sep; only the arrangement of membership proofs changes.
@[simp]
theorem coe_toSimpleGraphDeleteVertsIso_apply (G : Graph α β) (X : Set α)
    (v : V(G.deleteVerts X)) :
    (((G.toSimpleGraphDeleteVertsIso X) v).val : α) = v := (rfl)

@[simp]
theorem coe_toSimpleGraphDeleteVertsIso_symm_apply (G : Graph α β) (X : Set α)
    (v : {v : V(G) // (v : α) ∉ X}) :
    (((G.toSimpleGraphDeleteVertsIso X).symm v) : α) = v.val := (rfl)

end Graph
