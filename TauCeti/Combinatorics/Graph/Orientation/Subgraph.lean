/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Orientation.Indegree
public import TauCeti.Combinatorics.Graph.Union

/-!
# Orientations of subgraphs and unions

An orientation of a multigraph restricts to every subgraph: each edge of the subgraph keeps its
chosen tail and head, which are also its ends in the subgraph. Conversely, orientations of two
compatible graphs combine into an orientation of their union, taking the direction of a shared
edge from the first orientation. When the edge sets are disjoint, restricting the combined
orientation recovers both inputs, so orientations of the union are exactly pairs of orientations.

Restriction keeps the head of every remaining edge. Hence deleting a set of edges lowers the
indegree of a vertex by the number of deleted edges with their head there. In a union, a vertex
of only one of the two graphs has the same indegree as in that graph; in particular this holds
for every vertex of a vertex-disjoint union.

## Main declarations

* `Graph.Orientation.restrict`: the orientation of a subgraph induced by an orientation.
* `Graph.Orientation.union`: the orientation of a compatible union built from two orientations.
* `Graph.Orientation.unionEquiv`: orientations of an edge-disjoint union are pairs of
  orientations.
* `Graph.Orientation.indegree_restrict_deleteEdges_add`: the indegree change under edge deletion.
* `Graph.Orientation.indegree_union_left` and `Graph.Orientation.indegree_union_right`: indegrees
  in a union at vertices of only one of the two graphs, with outdegree analogues.
-/

public section

open Finset

namespace Graph.Orientation

universe u v

variable {V : Type u} {E : Type v} {G H K : Graph V E}

section Restrict

/-- The orientation of a subgraph that keeps the chosen tail and head of each of its edges. -/
def restrict (o : Orientation G) (h : H ≤ G) : Orientation H where
  tail e := ⟨o.tail (Set.inclusion h.edgeSet_mono e),
    ((h.isLink_iff e.2).2 (o.isLink (Set.inclusion h.edgeSet_mono e))).left_mem⟩
  head e := ⟨o.head (Set.inclusion h.edgeSet_mono e),
    ((h.isLink_iff e.2).2 (o.isLink (Set.inclusion h.edgeSet_mono e))).right_mem⟩
  isLink e := (h.isLink_iff e.2).2 (o.isLink (Set.inclusion h.edgeSet_mono e))

/-- A restricted orientation keeps the chosen tail of each edge. -/
@[simp]
theorem coe_restrict_tail (o : Orientation G) (h : H ≤ G) (e : H.edgeSet) :
    ((o.restrict h).tail e : V) = o.tail (Set.inclusion h.edgeSet_mono e) :=
  (rfl)

/-- A restricted orientation keeps the chosen head of each edge. -/
@[simp]
theorem coe_restrict_head (o : Orientation G) (h : H ≤ G) (e : H.edgeSet) :
    ((o.restrict h).head e : V) = o.head (Set.inclusion h.edgeSet_mono e) :=
  (rfl)

/-- Restricting to the whole graph changes nothing. -/
@[simp]
theorem restrict_rfl (o : Orientation G) : o.restrict le_rfl = o :=
  ext_of_head fun _ ↦ Subtype.ext (rfl)

/-- Restricting in two steps is restricting once. -/
@[simp]
theorem restrict_restrict (o : Orientation K) (hGK : G ≤ K) (hHG : H ≤ G) :
    (o.restrict hGK).restrict hHG = o.restrict (hHG.trans hGK) :=
  ext_of_head fun _ ↦ Subtype.ext (rfl)

/-- Restriction commutes with reversal. -/
@[simp]
theorem reverse_restrict (o : Orientation G) (h : H ≤ G) :
    (o.restrict h).reverse = o.reverse.restrict h :=
  ext_of_head fun _ ↦ Subtype.ext <| by simp

end Restrict

section Union

variable (o₁ : Orientation G) (o₂ : Orientation H) (h : G.Compatible H)

private theorem mem_right_of_notMem_left {e : h.union.edgeSet} (he : e.1 ∉ E(G)) : e.1 ∈ E(H) := by
  simpa [he] using e.2

open Classical in
/-- The orientation of a compatible union that directs the edges of `G` by `o₁` and the remaining
edges, which belong to `H`, by `o₂`. -/
noncomputable def union : Orientation h.union where
  tail e := if he : e.1 ∈ E(G) then Set.inclusion h.left_le_union.vertexSet_mono (o₁.tail ⟨e, he⟩)
    else Set.inclusion h.right_le_union.vertexSet_mono (o₂.tail ⟨e, mem_right_of_notMem_left h he⟩)
  head e := if he : e.1 ∈ E(G) then Set.inclusion h.left_le_union.vertexSet_mono (o₁.head ⟨e, he⟩)
    else Set.inclusion h.right_le_union.vertexSet_mono (o₂.head ⟨e, mem_right_of_notMem_left h he⟩)
  isLink e := by
    by_cases he : e.1 ∈ E(G)
    · simpa [he] using (o₁.isLink ⟨e, he⟩).mono h.left_le_union
    · simpa [he] using (o₂.isLink ⟨e, mem_right_of_notMem_left h he⟩).mono h.right_le_union

variable {o₁ o₂ h}

/-- An edge of `G` takes its tail from `o₁`. -/
@[simp]
theorem coe_union_tail_of_mem {e : h.union.edgeSet} (he : e.1 ∈ E(G)) :
    ((o₁.union o₂ h).tail e : V) = o₁.tail ⟨e, he⟩ := by
  simp [union, he]

/-- An edge of `G` takes its head from `o₁`. -/
@[simp]
theorem coe_union_head_of_mem {e : h.union.edgeSet} (he : e.1 ∈ E(G)) :
    ((o₁.union o₂ h).head e : V) = o₁.head ⟨e, he⟩ := by
  simp [union, he]

/-- An edge of `H` outside `G` takes its tail from `o₂`. -/
@[simp]
theorem coe_union_tail_of_notMem {e : h.union.edgeSet} (he : e.1 ∉ E(G)) (he' : e.1 ∈ E(H)) :
    ((o₁.union o₂ h).tail e : V) = o₂.tail ⟨e, he'⟩ := by
  simp [union, he]

/-- An edge of `H` outside `G` takes its head from `o₂`. -/
@[simp]
theorem coe_union_head_of_notMem {e : h.union.edgeSet} (he : e.1 ∉ E(G)) (he' : e.1 ∈ E(H)) :
    ((o₁.union o₂ h).head e : V) = o₂.head ⟨e, he'⟩ := by
  simp [union, he]

/-- Restricting a combined orientation to the first graph recovers the first orientation. -/
@[simp]
theorem restrict_union_left : (o₁.union o₂ h).restrict h.left_le_union = o₁ :=
  ext_of_head fun e ↦ Subtype.ext <| by
    simp

/-- Restricting a combined orientation to the second graph recovers the second orientation when
the two graphs share no edge. -/
@[simp]
theorem restrict_union_right (hE : Disjoint E(G) E(H)) :
    (o₁.union o₂ h).restrict h.right_le_union = o₂ :=
  ext_of_head fun e ↦ Subtype.ext <| by
    simp [hE.notMem_of_mem_right e.2]

/-- Every orientation of a compatible union is combined from its two restrictions. -/
@[simp]
theorem union_restrict (o : Orientation h.union) :
    (o.restrict h.left_le_union).union (o.restrict h.right_le_union) h = o := by
  refine ext_of_head fun e ↦ Subtype.ext ?_
  by_cases he : e.1 ∈ E(G)
  · simp [he]
  · have heH := mem_right_of_notMem_left h he
    simp [he, heH]

/-- Combining orientations commutes with reversal. -/
@[simp]
theorem reverse_union : (o₁.union o₂ h).reverse = o₁.reverse.union o₂.reverse h := by
  refine ext_of_head fun e ↦ Subtype.ext ?_
  by_cases he : e.1 ∈ E(G)
  · simp [he]
  · have heH := mem_right_of_notMem_left h he
    simp [he, heH]

variable (h) in
/-- Orientations of the union of two compatible graphs with disjoint edge sets are pairs of
orientations of the two graphs. -/
noncomputable def unionEquiv (hE : Disjoint E(G) E(H)) :
    Orientation G × Orientation H ≃ Orientation h.union where
  toFun o := o.1.union o.2 h
  invFun o := (o.restrict h.left_le_union, o.restrict h.right_le_union)
  left_inv _ := Prod.ext restrict_union_left (restrict_union_right hE)
  right_inv := union_restrict

@[simp]
theorem unionEquiv_apply (hE : Disjoint E(G) E(H)) (o : Orientation G × Orientation H) :
    unionEquiv h hE o = o.1.union o.2 h :=
  (rfl)

@[simp]
theorem unionEquiv_symm_apply (hE : Disjoint E(G) E(H)) (o : Orientation h.union) :
    (unionEquiv h hE).symm o = (o.restrict h.left_le_union, o.restrict h.right_le_union) :=
  (rfl)

end Union

section Indegree

variable [Fintype G.edgeSet] [Fintype H.edgeSet]

/-- The indegree of a vertex under a restricted orientation counts the edges of the subgraph
whose head is that vertex. -/
theorem indegree_restrict [DecidableEq G.vertexSet] [DecidablePred (· ∈ E(H))]
    (o : Orientation G) (h : H ≤ G) (v : H.vertexSet) :
    (o.restrict h).indegree v =
      #{e | e.1 ∈ E(H) ∧ o.head e = Set.inclusion h.vertexSet_mono v} := by
  classical
  rw [indegree_def]
  refine card_bij (fun e _ ↦ Set.inclusion h.edgeSet_mono e) (fun e he ↦ ?_)
    (fun _ _ _ _ he ↦ Set.inclusion_injective _ he) (fun e he ↦ ?_)
  · simp only [mem_filter, mem_univ, true_and] at he ⊢
    exact ⟨e.2, Subtype.ext (by simpa using congrArg Subtype.val he)⟩
  · simp only [mem_filter, mem_univ, true_and] at he
    exact ⟨⟨e, he.1⟩, by simpa [Subtype.ext_iff] using congrArg Subtype.val he.2, rfl⟩

/-- Restriction cannot increase indegrees. -/
theorem indegree_restrict_le (o : Orientation G) (h : H ≤ G) (v : H.vertexSet) :
    (o.restrict h).indegree v ≤ o.indegree (Set.inclusion h.vertexSet_mono v) := by
  classical
  rw [indegree_restrict, indegree_def]
  exact card_le_card fun e he ↦ mem_filter.2 ⟨(mem_filter.1 he).1, (mem_filter.1 he).2.2⟩

/-- If every edge with its head at `v` belongs to the subgraph, restriction does not change the
indegree of `v`. -/
theorem indegree_restrict_of_forall (o : Orientation G) (h : H ≤ G) (v : H.vertexSet)
    (hv : ∀ e, o.head e = Set.inclusion h.vertexSet_mono v → e.1 ∈ E(H)) :
    (o.restrict h).indegree v = o.indegree (Set.inclusion h.vertexSet_mono v) := by
  classical
  rw [indegree_restrict, indegree_def]
  exact congrArg card (filter_congr fun e _ ↦ ⟨And.right, fun he ↦ ⟨hv e he, he⟩⟩)

/-- The indegree of a vertex drops under restriction by the number of edges outside the subgraph
with their head there. -/
theorem indegree_restrict_add [DecidableEq G.vertexSet] [DecidablePred (· ∈ E(H))]
    (o : Orientation G) (h : H ≤ G) (v : H.vertexSet) :
    (o.restrict h).indegree v + #{e | e.1 ∉ E(H) ∧ o.head e = Set.inclusion h.vertexSet_mono v} =
      o.indegree (Set.inclusion h.vertexSet_mono v) := by
  rw [indegree_restrict, indegree_def, ← card_filter_add_card_filter_not
    (s := {e | o.head e = Set.inclusion h.vertexSet_mono v}) (·.1 ∈ E(H)), filter_filter,
    filter_filter]
  congr 2 <;> ext e <;> simp [and_comm]

/-- Deleting a set of edges lowers the indegree of a vertex by the number of deleted edges with
their head there. -/
theorem indegree_restrict_deleteEdges_add {F : Set E} [Fintype (G.deleteEdges F).edgeSet]
    [DecidableEq G.vertexSet] [DecidablePred (· ∈ F)] (o : Orientation G) (v : G.vertexSet) :
    (o.restrict (deleteEdges_le (F := F))).indegree v + #{e | e.1 ∈ F ∧ o.head e = v} =
      o.indegree v := by
  classical
  convert o.indegree_restrict_add (deleteEdges_le (F := F)) v using 3
  ext e
  simp [Subtype.ext_iff]

/-- Restriction cannot increase outdegrees. -/
theorem outdegree_restrict_le (o : Orientation G) (h : H ≤ G) (v : H.vertexSet) :
    (o.restrict h).outdegree v ≤ o.outdegree (Set.inclusion h.vertexSet_mono v) := by
  rw [← indegree_reverse, ← indegree_reverse, reverse_restrict]
  exact o.reverse.indegree_restrict_le h v

/-- The outdegree of a vertex drops under restriction by the number of edges outside the subgraph
with their tail there. -/
theorem outdegree_restrict_add [DecidableEq G.vertexSet] [DecidablePred (· ∈ E(H))]
    (o : Orientation G) (h : H ≤ G) (v : H.vertexSet) :
    (o.restrict h).outdegree v + #{e | e.1 ∉ E(H) ∧ o.tail e = Set.inclusion h.vertexSet_mono v} =
      o.outdegree (Set.inclusion h.vertexSet_mono v) := by
  rw [← indegree_reverse, ← indegree_reverse, reverse_restrict]
  simpa using o.reverse.indegree_restrict_add h v

/-- Deleting a set of edges lowers the outdegree of a vertex by the number of deleted edges with
their tail there. -/
theorem outdegree_restrict_deleteEdges_add {F : Set E} [Fintype (G.deleteEdges F).edgeSet]
    [DecidableEq G.vertexSet] [DecidablePred (· ∈ F)] (o : Orientation G) (v : G.vertexSet) :
    (o.restrict (deleteEdges_le (F := F))).outdegree v + #{e | e.1 ∈ F ∧ o.tail e = v} =
      o.outdegree v := by
  classical
  convert o.outdegree_restrict_add (deleteEdges_le (F := F)) v using 3
  ext e
  simp [Subtype.ext_iff]

variable {o₁ : Orientation G} {o₂ : Orientation H} {h : G.Compatible H} [Fintype h.union.edgeSet]

omit [Fintype H.edgeSet] in
/-- At a vertex of `G` outside `H`, the combined orientation has the indegree given by `o₁`. -/
theorem indegree_union_left (v : G.vertexSet) (hv : v.1 ∉ V(H)) :
    (o₁.union o₂ h).indegree (Set.inclusion h.left_le_union.vertexSet_mono v) = o₁.indegree v := by
  have hv' (e) (he : (o₁.union o₂ h).head e = Set.inclusion h.left_le_union.vertexSet_mono v) :
      e.1 ∈ E(G) := by
    by_contra heG
    have hval := congrArg Subtype.val he
    simp only [coe_union_head_of_notMem heG (mem_right_of_notMem_left h heG)] at hval
    exact hv (hval ▸ (o₂.head _).2)
  rw [← (o₁.union o₂ h).indegree_restrict_of_forall h.left_le_union v hv', restrict_union_left]

omit [Fintype G.edgeSet] in
/-- At a vertex of `H` outside `G`, the combined orientation has the indegree given by `o₂`. -/
theorem indegree_union_right (v : H.vertexSet) (hv : v.1 ∉ V(G)) :
    (o₁.union o₂ h).indegree (Set.inclusion h.right_le_union.vertexSet_mono v) =
      o₂.indegree v := by
  classical
  have hv' (e) (he : (o₁.union o₂ h).head e = Set.inclusion h.right_le_union.vertexSet_mono v) :
      e.1 ∈ E(H) := by
    by_contra heH
    have heG : e.1 ∈ E(G) := by simpa [heH] using e.2
    have hval := congrArg Subtype.val he
    simp only [coe_union_head_of_mem heG] at hval
    exact hv (hval ▸ (o₁.head _).2)
  rw [← (o₁.union o₂ h).indegree_restrict_of_forall h.right_le_union v hv', indegree_def,
    indegree_def]
  refine congrArg card (filter_congr fun e _ ↦ ?_)
  by_cases heG : e.1 ∈ E(G)
  · have hlink := (h.isLink_congr heG e.2).2 (o₂.isLink e)
    refine iff_of_false (fun he ↦ hv ?_) (fun he ↦ hv (he ▸ hlink.right_mem))
    have hval := congrArg Subtype.val he
    rw [coe_restrict_head, coe_union_head_of_mem heG] at hval
    exact hval ▸ (o₁.head _).2
  · simp [Subtype.ext_iff, heG]

omit [Fintype H.edgeSet] in
/-- At a vertex of `G` outside `H`, the combined orientation has the outdegree given by `o₁`. -/
theorem outdegree_union_left (v : G.vertexSet) (hv : v.1 ∉ V(H)) :
    (o₁.union o₂ h).outdegree (Set.inclusion h.left_le_union.vertexSet_mono v) =
      o₁.outdegree v := by
  rw [← indegree_reverse, ← indegree_reverse, reverse_union, indegree_union_left v hv]

omit [Fintype G.edgeSet] in
/-- At a vertex of `H` outside `G`, the combined orientation has the outdegree given by `o₂`. -/
theorem outdegree_union_right (v : H.vertexSet) (hv : v.1 ∉ V(G)) :
    (o₁.union o₂ h).outdegree (Set.inclusion h.right_le_union.vertexSet_mono v) =
      o₂.outdegree v := by
  rw [← indegree_reverse, ← indegree_reverse, reverse_union, indegree_union_right v hv]

end Indegree

end Graph.Orientation
