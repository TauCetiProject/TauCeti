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
`Graph.deleteEdges_mono_left`, and that it gives a spanning subgraph,
`Graph.deleteEdges_isSpanningSubgraph`. Vertex deletion commutes with simplification up to the
canonical isomorphism `Graph.toSimpleGraphDeleteVertsIso`; more generally,
`Graph.toSimpleGraphInduceIso` identifies simplification after induction with induction after
simplification when the inducing set consists of actual vertices. Both vertex maps retain the
original point.
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

/-- Deleting edges keeps every vertex, so it gives a spanning subgraph. -/
theorem deleteEdges_isSpanningSubgraph (G : Graph α β) (F : Set β) : G.deleteEdges F ≤s G :=
  ⟨deleteEdges_le, vertexSet_deleteEdges ..⟩

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

/-- Deleting vertices induces the graph on the remaining actual vertices. -/
theorem deleteVerts_eq_induce (G : Graph α β) (X : Set α) :
    G.deleteVerts X = G.induce (V(G) \ X) := by
  refine Graph.ext (by simp) fun e x y ↦ ?_
  simp only [deleteVerts_isLink, induce_isLink, mem_sdiff, and_congr_right_iff]
  intro h
  simp only [h.left_mem, h.right_mem, true_and]

/-- Simplifying a multigraph induced on actual vertices gives the simple graph induced on the
corresponding vertices. The isomorphism retains the underlying ambient vertex. -/
def toSimpleGraphInduceIso (G : Graph α β) (X : Set α) (hX : X ⊆ V(G)) :
    (G.induce X).toSimpleGraph ≃g G.toSimpleGraph.induce {v : V(G) | (v : α) ∈ X} := by
  let e : V(G.induce X) ≃ {v : V(G) // (v : α) ∈ X} :=
    (Equiv.subtypeEquivRight fun _ ↦ by
      simp only [vertexSet_induce]).trans
        (Equiv.subtypeSubtypeEquivSubtype fun hx ↦ hX hx).symm
  -- Both canonical subtype equivalences only reorganize membership proofs.
  have he (v : V(G.induce X)) : ((e v).val : α) = v := by
    simp [e]
  refine { toEquiv := e, map_rel_iff' := ?_ }
  intro u v
  have hu := u.property
  have hv := v.property
  simp only [vertexSet_induce] at hu hv
  simp [toSimpleGraph_adj, Graph.Adj, induce_isLink, Subtype.ext_iff, he, hu, hv]

/-- The induced-simplification isomorphism keeps the underlying ambient vertex. -/
@[simp]
theorem coe_toSimpleGraphInduceIso_apply (G : Graph α β) (X : Set α) (hX : X ⊆ V(G))
    (v : V(G.induce X)) :
    (((G.toSimpleGraphInduceIso X hX) v).val : α) = v := by
  simp [toSimpleGraphInduceIso]

/-- The inverse induced-simplification isomorphism keeps the underlying ambient vertex. -/
@[simp]
theorem coe_toSimpleGraphInduceIso_symm_apply (G : Graph α β) (X : Set α)
    (hX : X ⊆ V(G)) (v : {v : V(G) // (v : α) ∈ X}) :
    (((G.toSimpleGraphInduceIso X hX).symm v) : α) = v.val := by
  symm
  simpa using G.coe_toSimpleGraphInduceIso_apply X hX
    ((G.toSimpleGraphInduceIso X hX).symm v)

private def toSimpleGraphDeleteVertsSourceIso (G : Graph α β) (X : Set α) :
    (G.deleteVerts X).toSimpleGraph ≃g (G.induce (V(G) \ X)).toSimpleGraph := by
  let source : V(G.deleteVerts X) ≃ V(G.induce (V(G) \ X)) :=
    Equiv.subtypeEquivRight fun _ ↦ by
      simp only [vertexSet_deleteVerts, vertexSet_induce]
  refine { toEquiv := source, map_rel_iff' := ?_ }
  intro u v
  have hu := u.property
  have hv := v.property
  simp only [vertexSet_deleteVerts, mem_sdiff] at hu hv
  simp [toSimpleGraph_adj, Graph.Adj, deleteVerts_isLink, induce_isLink, source, hu, hv]

private theorem coe_toSimpleGraphDeleteVertsSourceIso_apply (G : Graph α β) (X : Set α)
    (v : V(G.deleteVerts X)) :
    (((toSimpleGraphDeleteVertsSourceIso G X) v) : α) = v := by
  simp [toSimpleGraphDeleteVertsSourceIso]

private def toSimpleGraphDeleteVertsTargetIso (G : Graph α β) (X : Set α) :
    G.toSimpleGraph.induce {v : V(G) | (v : α) ∈ V(G) \ X} ≃g
      G.toSimpleGraph.induce {v : V(G) | (v : α) ∉ X} :=
  SimpleGraph.Iso.induce (SimpleGraph.Iso.refl (G := G.toSimpleGraph)) (by
    convert Set.bijOn_id {v : V(G) | (v : α) ∉ X} using 1 <;> ext v <;> simp)

private theorem coe_toSimpleGraphDeleteVertsTargetIso_apply (G : Graph α β) (X : Set α)
    (v : {v : V(G) // (v : α) ∈ V(G) \ X}) :
    (((toSimpleGraphDeleteVertsTargetIso G X) v).val : α) = v.val := by
  simp [toSimpleGraphDeleteVertsTargetIso]

/-- Simplifying after vertex deletion is the same as inducing the simplification on the
remaining actual vertices. -/
def toSimpleGraphDeleteVertsIso (G : Graph α β) (X : Set α) :
    (G.deleteVerts X).toSimpleGraph ≃g G.toSimpleGraph.induce {v : V(G) | (v : α) ∉ X} :=
  (toSimpleGraphDeleteVertsSourceIso G X).trans
    ((G.toSimpleGraphInduceIso (V(G) \ X) sdiff_subset).trans
      (toSimpleGraphDeleteVertsTargetIso G X))

@[simp]
theorem coe_toSimpleGraphDeleteVertsIso_apply (G : Graph α β) (X : Set α)
    (v : V(G.deleteVerts X)) :
    (((G.toSimpleGraphDeleteVertsIso X) v).val : α) = v := by
  simp only [toSimpleGraphDeleteVertsIso, RelIso.trans_apply,
    coe_toSimpleGraphDeleteVertsTargetIso_apply, G.coe_toSimpleGraphInduceIso_apply,
    coe_toSimpleGraphDeleteVertsSourceIso_apply]

@[simp]
theorem coe_toSimpleGraphDeleteVertsIso_symm_apply (G : Graph α β) (X : Set α)
    (v : {v : V(G) // (v : α) ∉ X}) :
    (((G.toSimpleGraphDeleteVertsIso X).symm v) : α) = v.val := by
  symm
  simpa using G.coe_toSimpleGraphDeleteVertsIso_apply X
    ((G.toSimpleGraphDeleteVertsIso X).symm v)

end Graph
