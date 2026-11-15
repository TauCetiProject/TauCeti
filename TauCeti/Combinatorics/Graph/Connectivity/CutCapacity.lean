/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.EdgeCut
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.PairCutCapacity
public import Mathlib.Data.Set.Card

/-!
# Capacities of undirected cuts

This file defines the capacity of a cut in a weighted multigraph. Parallel edges contribute
separately and loops never contribute. Aggregating the weights of all edges with the same unordered
pair of distinct ends therefore preserves every cut capacity.

For a simple graph, the multigraph cut capacity of `Graph.ofSimpleGraph G` agrees with
`TauCeti.pairCutCapacity` when pair capacities vanish away from the edges of `G`.

## Main definitions

* `Graph.edgeCutCapacity`: the capacity of a cut in a weighted multigraph.
* `Graph.pairCapacity`: aggregation of multigraph edge weights by their distinct ends.
* `SimpleGraph.ofSimpleGraphCapacity`: restriction of pair capacities to actual edges.

## Main result

* `Graph.edgeCutCapacity_one`: a unit-capacity cut has value equal to the number of crossing
  edge identities.
* `Graph.pairCutCapacity_pairCapacity`: aggregation preserves every cut capacity.
* `Graph.isSubmodular_edgeCutCapacity`: an edge-capacity function nonnegative on nonloop edges has
  a submodular cut function.
* `Graph.isSymmSubmodular_edgeCutCapacity`: the bundled symmetric-submodular result.
* `SimpleGraph.edgeCutCapacity_eq_pairCutCapacity`: the simple-graph and multigraph cut-capacity
  interfaces agree.
-/

public section

open Finset

namespace Graph

variable {V E K : Type*} (G : Graph V E)

open Classical in
/-- The capacity of a cut in a weighted multigraph. Each actual crossing edge is counted once. -/
noncomputable def edgeCutCapacity [Fintype G.edgeSet] [AddCommMonoid K]
    (c : G.edgeSet → K) (S : Finset G.vertexSet) : K :=
  ∑ e : G.edgeSet,
    if e.1 ∈ G.edgeCut (Subtype.val '' (S : Set G.vertexSet)) then c e else 0

/-- The defining finite-sum formula for `edgeCutCapacity`. -/
theorem edgeCutCapacity_def [Fintype G.edgeSet] [AddCommMonoid K]
    (c : G.edgeSet → K) (S : Finset G.vertexSet)
    [DecidablePred fun e : G.edgeSet ↦
      e.1 ∈ G.edgeCut (Subtype.val '' (S : Set G.vertexSet))] :
    G.edgeCutCapacity c S =
      ∑ e : G.edgeSet,
        if e.1 ∈ G.edgeCut (Subtype.val '' (S : Set G.vertexSet)) then c e else 0 := by
  classical
  apply sum_congr rfl
  intro e _
  by_cases he : e.1 ∈ G.edgeCut (Subtype.val '' (S : Set G.vertexSet)) <;>
    simp [he]

/-- Giving every actual edge capacity one makes the capacity of a cut equal to the number of
crossing edge identities. In particular, parallel edges are counted separately. -/
@[simp]
theorem edgeCutCapacity_one [Fintype G.edgeSet] (S : Finset G.vertexSet) :
    G.edgeCutCapacity (fun _ ↦ (1 : ℕ)) S =
      (G.edgeCut (Subtype.val '' (S : Set G.vertexSet))).ncard := by
  classical
  rw [edgeCutCapacity_def]
  let C : Set G.edgeSet :=
    Subtype.val ⁻¹' G.edgeCut (Subtype.val '' (S : Set G.vertexSet))
  calc
    (∑ e : G.edgeSet,
        if e.1 ∈ G.edgeCut (Subtype.val '' (S : Set G.vertexSet)) then 1 else 0) =
        #(univ.filter fun e : G.edgeSet ↦
          e.1 ∈ G.edgeCut (Subtype.val '' (S : Set G.vertexSet))) := by
      rw [card_filter]
    _ = C.ncard := by
      rw [Set.ncard_eq_toFinset_card C]
      congr 1
      ext e
      simp [C]
    _ = (G.edgeCut (Subtype.val '' (S : Set G.vertexSet))).ncard :=
      Set.ncard_preimage_of_injective_subset_range Subtype.val_injective
        (by simpa using G.edgeCut_subset_edgeSet)

open Classical in
/-- Aggregate edge weights by the unordered pair of their distinct ends. The capacity of every
diagonal pair is zero, so loops are discarded. -/
noncomputable def pairCapacity [Fintype G.edgeSet] [AddCommMonoid K]
    (c : G.edgeSet → K) (p : Sym2 G.vertexSet) : K :=
  ∑ e : G.edgeSet, if ¬p.IsDiag ∧ G.edgeEnds e = p then c e else 0

/-- The defining finite-sum formula for `pairCapacity`. -/
theorem pairCapacity_def [Fintype G.edgeSet] [AddCommMonoid K]
    (c : G.edgeSet → K) (p : Sym2 G.vertexSet)
    [DecidablePred fun e : G.edgeSet ↦ ¬p.IsDiag ∧ G.edgeEnds e = p] :
    G.pairCapacity c p =
      ∑ e : G.edgeSet, if ¬p.IsDiag ∧ G.edgeEnds e = p then c e else 0 := by
  classical
  apply sum_congr rfl
  intro e _
  by_cases he : ¬p.IsDiag ∧ G.edgeEnds e = p <;> simp [he]

/-- On a pair of distinct vertices, `pairCapacity` sums exactly the weights of edges linking
those vertices. -/
theorem pairCapacity_mk_of_ne [Fintype G.edgeSet] [AddCommMonoid K]
    (c : G.edgeSet → K) {x y : G.vertexSet} (hxy : x ≠ y)
    [DecidablePred fun e : G.edgeSet ↦ G.IsLink e.1 x.1 y.1] :
    G.pairCapacity c s(x, y) =
      ∑ e : G.edgeSet, if G.IsLink e.1 x.1 y.1 then c e else 0 := by
  classical
  simp [pairCapacity_def, hxy, G.edgeEnds_eq_iff_isLink]

/-- Aggregated pair capacity vanishes on a diagonal pair. -/
@[simp]
theorem pairCapacity_mk_self [Fintype G.edgeSet] [AddCommMonoid K]
    (c : G.edgeSet → K) (x : G.vertexSet) :
    G.pairCapacity c s(x, x) = 0 := by
  classical
  simp [pairCapacity_def]

/-- Aggregated pair capacity vanishes on diagonal pairs, independently of loop weights. -/
theorem pairCapacity_eq_zero_of_isDiag [Fintype G.edgeSet] [AddCommMonoid K]
    (c : G.edgeSet → K) {p : Sym2 G.vertexSet} (hp : p.IsDiag) :
    G.pairCapacity c p = 0 := by
  classical
  rw [pairCapacity_def]
  apply sum_eq_zero
  intro e _
  simp [hp]

/-- Aggregating parallel edge weights by their distinct ends preserves every cut capacity. -/
theorem pairCutCapacity_pairCapacity [Fintype G.vertexSet] [Fintype G.edgeSet]
    [AddCommMonoid K] (c : G.edgeSet → K) (S : Finset G.vertexSet) :
    TauCeti.pairCutCapacity (G.pairCapacity c) S = G.edgeCutCapacity c S := by
  classical
  rw [TauCeti.pairCutCapacity_def, edgeCutCapacity_def]
  simp only [pairCapacity_def]
  calc
    (∑ p : Sym2 G.vertexSet,
        if p.Crosses (S : Set G.vertexSet) then
          ∑ e : G.edgeSet, if ¬p.IsDiag ∧ G.edgeEnds e = p then c e else 0 else 0) =
        ∑ p : Sym2 G.vertexSet, ∑ e : G.edgeSet,
          if p.Crosses (S : Set G.vertexSet) ∧ G.edgeEnds e = p
            then c e else 0 := by
      apply sum_congr rfl
      intro p _
      by_cases hp : p.Crosses (S : Set G.vertexSet)
      · simp [hp, hp.not_isDiag]
      · simp [hp]
    _ = ∑ p : Sym2 G.vertexSet, ∑ e ∈ univ with G.edgeEnds e = p,
          if (G.edgeEnds e).Crosses (S : Set G.vertexSet) then c e else 0 := by
      apply sum_congr rfl
      intro p _
      rw [Finset.sum_filter]
      apply sum_congr rfl
      intro e _
      by_cases hep : G.edgeEnds e = p
      · subst p
        simp
      · simp [hep]
    _ = ∑ e : G.edgeSet,
          if (G.edgeEnds e).Crosses (S : Set G.vertexSet) then c e else 0 :=
      Finset.sum_fiberwise univ G.edgeEnds
        (fun e ↦ if (G.edgeEnds e).Crosses (S : Set G.vertexSet) then c e else 0)
    _ = ∑ e : G.edgeSet,
          if e.1 ∈ G.edgeCut (Subtype.val '' (S : Set G.vertexSet)) then c e else 0 := by
      apply sum_congr rfl
      intro e _
      simp only [G.edgeEnds_crosses_iff_mem_edgeCut e S]

/-- Multigraph cut capacity is unchanged when the two sides of the cut are exchanged. -/
@[simp]
theorem edgeCutCapacity_compl [Fintype G.vertexSet] [Fintype G.edgeSet]
    [DecidableEq G.vertexSet] [AddCommMonoid K] (c : G.edgeSet → K)
    (S : Finset G.vertexSet) :
    G.edgeCutCapacity c Sᶜ = G.edgeCutCapacity c S := by
  classical
  rw [edgeCutCapacity_def, edgeCutCapacity_def]
  apply sum_congr rfl
  intro e _
  rw [← G.edgeEnds_crosses_iff_mem_edgeCut e (Sᶜ : Finset G.vertexSet),
    ← G.edgeEnds_crosses_iff_mem_edgeCut e S]
  simp only [Finset.coe_compl, Sym2.crosses_compl]

/-- The cut function of edge weights nonnegative on nonloop edges is submodular. Together with
`edgeCutCapacity_compl`, this makes it a symmetric submodular set function. Parallel edges are
counted separately, and loop weights are unrestricted. -/
theorem isSubmodular_edgeCutCapacity [Fintype G.edgeSet] [DecidableEq G.vertexSet]
    [AddCommMonoid K] [Preorder K] [IsOrderedAddMonoid K]
    (c : G.edgeSet → K) (hc : ∀ e, ¬ (G.edgeEnds e).IsDiag → 0 ≤ c e) :
    TauCeti.IsSubmodular (G.edgeCutCapacity c) := by
  classical
  rw [TauCeti.isSubmodular_def]
  intro S T
  simp_rw [edgeCutCapacity_def]
  rw [← sum_add_distrib, ← sum_add_distrib]
  apply sum_le_sum
  intro e _
  simp_rw [← G.edgeEnds_crosses_iff_mem_edgeCut e]
  simp only [Finset.coe_union, Finset.coe_inter]
  exact (G.edgeEnds e).ite_crosses_union_add_ite_crosses_inter_le (c e) (hc e) S T

/-- The cut function of edge weights nonnegative on nonloop edges is symmetric submodular.
Loop weights are unrestricted. -/
theorem isSymmSubmodular_edgeCutCapacity [Fintype G.vertexSet] [Fintype G.edgeSet]
    [DecidableEq G.vertexSet] [AddCommMonoid K] [Preorder K] [IsOrderedAddMonoid K]
    (c : G.edgeSet → K) (hc : ∀ e, ¬ (G.edgeEnds e).IsDiag → 0 ≤ c e) :
    TauCeti.IsSymmSubmodular (G.edgeCutCapacity c) :=
  ⟨G.edgeCutCapacity_compl c, G.isSubmodular_edgeCutCapacity c hc⟩

end Graph

namespace SimpleGraph

variable {V K : Type*} (G : SimpleGraph V)

/-- The vertex set of the multigraph realization of a finite simple graph is finite. -/
noncomputable instance instFintypeOfSimpleGraphVertexSet [Fintype V] :
    Fintype (Graph.ofSimpleGraph G).vertexSet :=
  Fintype.ofFinite _

/-- The edge set of the multigraph realization of a finite simple graph is finite. -/
noncomputable instance instFintypeOfSimpleGraphEdgeSet [Fintype V] :
    Fintype (Graph.ofSimpleGraph G).edgeSet :=
  Fintype.ofFinite _

/-- Restrict capacities on unordered vertex pairs to the actual edges of
`Graph.ofSimpleGraph G`. -/
def ofSimpleGraphCapacity (c : Sym2 V → K) : (Graph.ofSimpleGraph G).edgeSet → K :=
  fun e ↦ c e.1

@[simp]
theorem ofSimpleGraphCapacity_apply (c : Sym2 V → K)
    (e : (Graph.ofSimpleGraph G).edgeSet) : G.ofSimpleGraphCapacity c e = c e.1 :=
  (rfl)

/-- Include a vertex of a simple graph in the full vertex set of `Graph.ofSimpleGraph G`. -/
def toOfSimpleGraphVertex (x : V) : (Graph.ofSimpleGraph G).vertexSet :=
  ⟨x, by rw [Graph.vertexSet_ofSimpleGraph]; exact Set.mem_univ x⟩

@[simp]
theorem toOfSimpleGraphVertex_val (x : V) : (G.toOfSimpleGraphVertex x).1 = x :=
  (rfl)

/-- Include a finite vertex set in the full vertex set of `Graph.ofSimpleGraph G`. -/
def toOfSimpleGraphFinset (S : Finset V) :
    Finset (Graph.ofSimpleGraph G).vertexSet :=
  S.map ⟨G.toOfSimpleGraphVertex,
    fun _ _ h ↦ congrArg Subtype.val h⟩

@[simp]
theorem mem_toOfSimpleGraphFinset {S : Finset V} {x : V} :
    G.toOfSimpleGraphVertex x ∈ G.toOfSimpleGraphFinset S ↔ x ∈ S := by
  rw [toOfSimpleGraphFinset]
  exact Finset.mem_map' _

@[simp]
theorem image_val_toOfSimpleGraphFinset (S : Finset V) :
    Subtype.val '' (G.toOfSimpleGraphFinset S : Set (Graph.ofSimpleGraph G).vertexSet) =
      (S : Set V) := by
  rw [toOfSimpleGraphFinset, Finset.coe_map, Set.image_image]
  trans id '' (S : Set V)
  · apply Set.image_congr
    intro x _
    exact G.toOfSimpleGraphVertex_val x
  · exact Set.image_id _

@[simp]
theorem toOfSimpleGraphFinset_map_val
    (S : Finset (Graph.ofSimpleGraph G).vertexSet) :
    G.toOfSimpleGraphFinset (S.map ⟨Subtype.val, Subtype.val_injective⟩) = S := by
  rw [toOfSimpleGraphFinset, Finset.map_map]
  have h :
      (⟨Subtype.val, Subtype.val_injective⟩ :
          (Graph.ofSimpleGraph G).vertexSet ↪ V).trans
        ⟨G.toOfSimpleGraphVertex, fun _ _ h ↦ congrArg Subtype.val h⟩ =
          Function.Embedding.refl _ := by
    ext x
    rfl
  rw [h, Finset.map_refl]

/-- The multigraph cut capacity of `Graph.ofSimpleGraph G` agrees with pair cut capacity when
capacities vanish away from the edges of `G`. -/
theorem edgeCutCapacity_eq_pairCutCapacity [Fintype V] [AddCommMonoid K]
    (c : Sym2 V → K) (hc : ∀ p, ¬p.IsDiag → p ∉ G.edgeSet → c p = 0)
    (S : Finset V) :
    (Graph.ofSimpleGraph G).edgeCutCapacity (G.ofSimpleGraphCapacity c)
        (G.toOfSimpleGraphFinset S) =
      TauCeti.pairCutCapacity c S := by
  classical
  rw [Graph.edgeCutCapacity_def, TauCeti.pairCutCapacity_def]
  rw [image_val_toOfSimpleGraphFinset]
  calc
    (∑ e : (Graph.ofSimpleGraph G).edgeSet,
        if e.1 ∈ (Graph.ofSimpleGraph G).edgeCut (S : Set V) then
          G.ofSimpleGraphCapacity c e else 0) =
        ∑ p ∈ Finset.univ.filter (· ∈ G.edgeSet), if p.Crosses (S : Set V) then c p else 0 := by
      simp only [ofSimpleGraphCapacity]
      rw [← Finset.sum_subtype
        (Finset.univ.filter (· ∈ (Graph.ofSimpleGraph G).edgeSet)) (by simp)
        (fun p ↦ if p ∈ (Graph.ofSimpleGraph G).edgeCut (S : Set V) then
            c p else 0)]
      rw [Graph.edgeSet_ofSimpleGraph]
      apply Finset.sum_congr (by ext p; simp)
      intro e heG
      rw [G.mem_edgeCut_ofSimpleGraph_iff_crosses (by simpa using heG)]
    _ = ∑ p : Sym2 V, if p.Crosses (S : Set V) then c p else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : p ∈ G.edgeSet
      · simp [hp]
      · by_cases hcross : p.Crosses (S : Set V)
        · simp [hp, hcross, hc p hcross.not_isDiag hp]
        · simp [hp, hcross]

end SimpleGraph
