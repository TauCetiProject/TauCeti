/-
Copyright (c) 2026 Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Combinatorics.Graph.Delete
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Incidence counts for multigraphs

This file counts actual multigraph edge identities incident to vertices and vertex sets.  The two
vertex counts differ only in their treatment of loops: `Graph.incidenceCount` counts a loop once,
while `Graph.nonloopIncidenceCount` discards it.  Parallel edges are always counted separately.
Both definitions use `Set.ncard`, so they return zero when the set being counted is infinite.

For finite actual edge sets, `Graph.internalEdges` and `Graph.incidentEdges` provide the finite
sets of edges internal to, or incident with, a finite set of actual vertices.  These are the
counting objects used by degree arguments and by orientation constraints.  The comparison with
`SimpleGraph.degree` shows that the multigraph count specializes to the usual simple-graph degree.
The edge-deletion results record that surviving incident edges together with deleted incident
edges account for the original incidence count.
-/

public section

open Set

universe u v

namespace Graph

variable {α : Type u} {β : Type v} (G : Graph α β)

/-- The `Set.ncard` of the nonloop edge identities incident to a vertex of a multigraph.
Parallel edges are counted separately; the result is zero when this set is infinite. -/
noncomputable def nonloopIncidenceCount (x : α) : ℕ :=
  (G.incidenceSet x \ G.loopSet x).ncard

/-- The `Set.ncard` of the edge identities incident to a vertex of a multigraph, counting each
loop once and counting parallel edges separately. The result is zero when this set is infinite. -/
noncomputable def incidenceCount (x : α) : ℕ :=
  (G.incidenceSet x).ncard

/-- The incidence set of a vertex is finite when the graph has finitely many actual edges. -/
theorem finite_incidenceSet [Finite G.edgeSet] (x : α) : (G.incidenceSet x).Finite :=
  (Set.finite_coe_iff.mp inferInstance).subset (G.incidenceSet_subset_edgeSet x)

/-- The loop set of a vertex is finite when the graph has finitely many actual edges. -/
theorem finite_loopSet [Finite G.edgeSet] (x : α) : (G.loopSet x).Finite :=
  (G.finite_incidenceSet x).subset (G.loopSet_subset_incidenceSet x)

/-- When the incidence set is finite, the incident edges split into the nonloop incident edges and
the loops at the vertex. -/
theorem nonloopIncidenceCount_add_ncard_loopSet (x : α) (hfin : (G.incidenceSet x).Finite) :
    G.nonloopIncidenceCount x + (G.loopSet x).ncard = G.incidenceCount x := by
  exact Set.ncard_sdiff_add_ncard_of_subset (G.loopSet_subset_incidenceSet x) hfin

/-- A loopless multigraph has no loops at any vertex. -/
@[simp]
theorem loopSet_eq_empty [G.Loopless] (x : α) : G.loopSet x = ∅ := by
  ext e
  simp

/-- On a loopless multigraph, counting all incident edges is the same as counting nonloop
incident edges. -/
@[simp]
theorem nonloopIncidenceCount_eq_incidenceCount [G.Loopless] (x : α) :
    G.nonloopIncidenceCount x = G.incidenceCount x := by
  simp [nonloopIncidenceCount, incidenceCount]

/-- Deleting edges removes precisely the deleted members of a vertex's incidence set. -/
@[simp]
theorem incidenceSet_deleteEdges (F : Set β) (x : α) :
    (G.deleteEdges F).incidenceSet x = G.incidenceSet x \ F := by
  ext e
  simp [incidenceSet]

/-- Deleting edges removes precisely the deleted members of a vertex's loop set. -/
@[simp]
theorem loopSet_deleteEdges (F : Set β) (x : α) :
    (G.deleteEdges F).loopSet x = G.loopSet x \ F := by
  ext e
  simp

/-- The incidence count after edge deletion counts exactly the surviving incident edges. -/
theorem incidenceCount_deleteEdges (F : Set β) (x : α) :
    (G.deleteEdges F).incidenceCount x = (G.incidenceSet x \ F).ncard := by
  unfold incidenceCount
  rw [incidenceSet_deleteEdges]

/-- When the incidence set is finite, the surviving and deleted incident-edge counts add to the
original incidence count. -/
theorem incidenceCount_deleteEdges_add_ncard_inter (F : Set β) (x : α)
    (hfin : (G.incidenceSet x).Finite) :
    (G.deleteEdges F).incidenceCount x + (G.incidenceSet x ∩ F).ncard =
      G.incidenceCount x := by
  rw [incidenceCount_deleteEdges, incidenceCount]
  rw [add_comm]
  exact Set.ncard_inter_add_ncard_sdiff_eq_ncard (G.incidenceSet x) F hfin

/-- Deleting edges removes precisely the deleted members of a vertex's nonloop incidence set. -/
theorem nonloopIncidenceCount_deleteEdges (F : Set β) (x : α) :
    (G.deleteEdges F).nonloopIncidenceCount x =
      ((G.incidenceSet x \ G.loopSet x) \ F).ncard := by
  unfold nonloopIncidenceCount
  rw [incidenceSet_deleteEdges, loopSet_deleteEdges]
  congr 1
  ext e
  simp only [mem_sdiff]
  tauto

/-! ## Basic examples -/

/-- A graph with no edges has an empty incidence set at every vertex. -/
@[simp]
theorem incidenceSet_noEdge (X : Set α) (x : α) :
    (Graph.noEdge X β).incidenceSet x = ∅ := by
  ext e
  simp

/-- A graph with no edges has incidence count zero at every vertex. -/
@[simp]
theorem incidenceCount_noEdge (X : Set α) (x : α) :
    (Graph.noEdge X β).incidenceCount x = 0 := by
  simp [incidenceCount]

/-- Every edge identity of a banana graph is incident to its left endpoint. -/
@[simp]
theorem incidenceSet_banana_left (x y : α) (E : Set β) :
    (Graph.banana x y E).incidenceSet x = E := by
  ext e
  simp

/-- Every edge identity of a bouquet is incident to its unique vertex. -/
theorem incidenceSet_bouquet (x : α) (E : Set β) :
    (Graph.bouquet x E).incidenceSet x = E := by
  ext e
  simp

/-- Every edge identity of a bouquet is a loop at its unique vertex. -/
@[simp]
theorem loopSet_bouquet (x : α) (E : Set β) :
    (Graph.bouquet x E).loopSet x = E := by
  ext e
  simp

/-- A banana graph with distinct endpoints has no loops at its left endpoint. -/
@[simp]
theorem loopSet_banana_left (x y : α) (E : Set β) (hxy : x ≠ y) :
    (Graph.banana x y E).loopSet x = ∅ := by
  ext e
  simp [hxy]

/-- Every edge identity of a banana graph is incident to its left endpoint, so the incidence
count there is `E.ncard`, which is zero when `E` is infinite. -/
@[simp]
theorem incidenceCount_banana_left (x y : α) (E : Set β) :
    (Graph.banana x y E).incidenceCount x = E.ncard := by
  simp [incidenceCount]

/-- Every edge identity of a bouquet is a loop at its unique vertex, so its incidence count is
`E.ncard`, which is zero when `E` is infinite. -/
theorem incidenceCount_bouquet (x : α) (E : Set β) :
    (Graph.bouquet x E).incidenceCount x = E.ncard := by
  simp [incidenceCount]

/-- A bouquet has no nonloop incident edges, independently of how many loops it has. -/
@[simp]
theorem nonloopIncidenceCount_bouquet (x : α) (E : Set β) :
    (Graph.bouquet x E).nonloopIncidenceCount x = 0 := by
  simp [nonloopIncidenceCount]

/-- When the endpoints of a banana graph are distinct, every edge is nonloop and the count at the
left endpoint is `E.ncard`, which is zero when `E` is infinite. -/
@[simp]
theorem nonloopIncidenceCount_banana_left (x y : α) (E : Set β) (hxy : x ≠ y) :
    (Graph.banana x y E).nonloopIncidenceCount x = E.ncard := by
  simp [nonloopIncidenceCount, hxy]

section FiniteEdges

variable [Fintype G.edgeSet]

noncomputable section

/-- The actual edge identities whose two endpoints both lie in `S`. -/
def internalEdges (S : Finset G.vertexSet) : Finset G.edgeSet :=
  by
    classical
    exact Finset.univ.filter fun e ↦
      ∃ x ∈ S, ∃ y ∈ S, G.IsLink e.1 x.1 y.1

/-- The actual edge identities with at least one endpoint in `S`. -/
def incidentEdges (S : Finset G.vertexSet) : Finset G.edgeSet :=
  by
    classical
    exact Finset.univ.filter fun e ↦ ∃ x ∈ S, G.Inc e.1 x.1

@[simp]
theorem mem_internalEdges {S : Finset G.vertexSet} {e : G.edgeSet} :
    e ∈ G.internalEdges S ↔ ∃ x ∈ S, ∃ y ∈ S, G.IsLink e.1 x.1 y.1 := by
  classical
  simp [internalEdges]

@[simp]
theorem mem_incidentEdges {S : Finset G.vertexSet} {e : G.edgeSet} :
    e ∈ G.incidentEdges S ↔ ∃ x ∈ S, G.Inc e.1 x.1 := by
  classical
  simp [incidentEdges]

@[simp]
theorem internalEdges_empty : G.internalEdges ∅ = ∅ := by
  ext e
  simp

@[simp]
theorem incidentEdges_empty : G.incidentEdges ∅ = ∅ := by
  ext e
  simp

@[simp]
theorem incidentEdges_univ [Fintype G.vertexSet] :
    G.incidentEdges Finset.univ = Finset.univ := by
  ext e
  simp only [mem_incidentEdges, Finset.mem_univ, iff_true]
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet e.2
  exact ⟨⟨x, hxy.left_mem⟩, trivial, hxy.inc_left⟩

@[simp]
theorem internalEdges_univ [Fintype G.vertexSet] :
    G.internalEdges Finset.univ = Finset.univ := by
  ext e
  simp only [mem_internalEdges, Finset.mem_univ, iff_true]
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet e.2
  exact ⟨⟨x, hxy.left_mem⟩, trivial, ⟨y, hxy.right_mem⟩, trivial, hxy⟩

/-- Every edge internal to `S` is incident with `S`. -/
theorem internalEdges_subset_incidentEdges (S : Finset G.vertexSet) :
    G.internalEdges S ⊆ G.incidentEdges S := by
  intro e
  simp only [mem_internalEdges, mem_incidentEdges]
  rintro ⟨x, hx, y, hy, hxy⟩
  exact ⟨x, hx, hxy.inc_left⟩

/-- Enlarging a vertex set enlarges its set of internal edges. -/
theorem internalEdges_mono {S T : Finset G.vertexSet} (hST : S ⊆ T) :
    G.internalEdges S ⊆ G.internalEdges T := by
  intro e
  simp only [mem_internalEdges]
  rintro ⟨x, hx, y, hy, hxy⟩
  exact ⟨x, hST hx, y, hST hy, hxy⟩

/-- Enlarging a vertex set enlarges its set of incident edges. -/
theorem incidentEdges_mono {S T : Finset G.vertexSet} (hST : S ⊆ T) :
    G.incidentEdges S ⊆ G.incidentEdges T := by
  intro e
  simp only [mem_incidentEdges]
  rintro ⟨x, hx, hex⟩
  exact ⟨x, hST hx, hex⟩

/-- The cardinality of the finite incident-edge set of a singleton is its incidence count. -/
theorem card_incidentEdges_singleton (x : G.vertexSet) :
    (G.incidentEdges {x}).card = G.incidenceCount x.1 := by
  rw [incidenceCount]
  rw [← Set.ncard_coe_finset]
  calc
    (↑(G.incidentEdges {x}) : Set G.edgeSet).ncard =
        {e : G.edgeSet | e.1 ∈ G.incidenceSet x.1}.ncard := by
      congr 1
      ext e
      simp
    _ = (G.incidenceSet x.1 ∩ G.edgeSet).ncard :=
      Set.ncard_subtype (fun e ↦ e ∈ G.edgeSet) (G.incidenceSet x.1)
    _ = (G.incidenceSet x.1).ncard := by
      rw [inter_eq_left.mpr (G.incidenceSet_subset_edgeSet x.1)]

/-- The number of internal edges of a singleton is the number of loops at its vertex. -/
theorem card_internalEdges_singleton (x : G.vertexSet) :
    (G.internalEdges {x}).card = (G.loopSet x.1).ncard := by
  rw [← Set.ncard_coe_finset]
  calc
    (↑(G.internalEdges {x}) : Set G.edgeSet).ncard =
        {e : G.edgeSet | e.1 ∈ G.loopSet x.1}.ncard := by
      congr 1
      ext e
      simp
    _ = (G.loopSet x.1 ∩ G.edgeSet).ncard :=
      Set.ncard_subtype (fun e ↦ e ∈ G.edgeSet) (G.loopSet x.1)
    _ = (G.loopSet x.1).ncard := by
      rw [inter_eq_left.mpr <|
        (G.loopSet_subset_incidenceSet x.1).trans (G.incidenceSet_subset_edgeSet x.1)]

end

end FiniteEdges

section SimpleGraph

variable (H : SimpleGraph α)

/-- The multigraph associated to a simple graph is loopless. -/
instance : (Graph.ofSimpleGraph H).Loopless where
  not_isLoopAt e x := by
    intro he
    rw [Graph.IsLoopAt, Graph.ofSimpleGraph_isLink] at he
    rcases he with ⟨rfl, he⟩
    exact H.irrefl ((SimpleGraph.mem_edgeSet H).mp he)

/-- The multigraph incidence set of `Graph.ofSimpleGraph H` is the usual simple-graph incidence
set. -/
@[simp]
theorem incidenceSet_ofSimpleGraph (x : α) :
    (Graph.ofSimpleGraph H).incidenceSet x = H.incidenceSet x := by
  ext e
  simp only [Graph.mem_incidenceSet, Graph.Inc, Graph.ofSimpleGraph_isLink,
    SimpleGraph.incidenceSet, Set.mem_sep_iff, Sym2.mem_iff_exists]
  tauto

/-- The incidence count on `Graph.ofSimpleGraph H` is the degree in `H`. -/
@[simp]
theorem incidenceCount_ofSimpleGraph (x : α) [Fintype (H.neighborSet x)] :
    (Graph.ofSimpleGraph H).incidenceCount x = H.degree x := by
  rw [incidenceCount, incidenceSet_ofSimpleGraph, SimpleGraph.ncard_incidenceSet]

end SimpleGraph

end Graph
