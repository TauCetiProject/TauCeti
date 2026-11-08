/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Matching.Hall

/-!
# Perfect matchings of regular bipartite multigraphs

Let `G : Graph α β` be a multigraph with finitely many actual edges and a bipartition `L, R`, in
which every actual vertex is an end of exactly `k` edges; parallel edges count separately, and
there are no loops. This file proves the classical consequences of Hall's theorem for such
`k`-regular bipartite multigraphs:

* if `k ≠ 0`, the two sides have the same number of vertices and `G` has a perfect matching;
* for every `k`, the edge set of `G` is the disjoint union of `k` perfect matchings.

When `k = 0` the multigraph has no edges, and the family of perfect matchings is empty; no perfect
matching need exist, since an isolated vertex is an end of no edge. The empty graph is allowed.

## Main results

* `Graph.IsBipartition.card_left_eq_card_right`: a `k`-regular bipartite multigraph with `k ≠ 0`
  has sides of equal size.
* `Graph.IsBipartition.card_le_card_neighborsIn`: Hall's condition holds in a `k`-regular
  bipartite multigraph with `k ≠ 0`.
* `Graph.IsBipartition.exists_isPerfectMatching`: a `k`-regular bipartite multigraph with `k ≠ 0`
  has a perfect matching.
* `Graph.IsBipartition.exists_perfectMatching_decomposition`: the edge set of a `k`-regular
  bipartite multigraph is the disjoint union of `k` perfect matchings.

## Implementation notes

Every actual edge has exactly one end in `L`, so for `S ⊆ L` the `k * |S|` edges at `S` are among
the `k * |N(S)|` edges at the neighbourhood `N(S)` of `S`. Thus `|S| ≤ |N(S)|`, and with `S = L`
and `S = R` the two sides have equal size. Hall's theorem for multiset capacitated matchings
(`Graph.IsBipartition.exists_isCapacitatedMatching_saturating_iff`) at unit capacities then gives
a perfect matching. Deleting it leaves a `(k - 1)`-regular bipartite multigraph on the same actual
vertices (`Graph.IsPerfectMatching.incidenceCount_deleteEdges_add_one`), which gives the
decomposition by induction on `k`.

## References

* D. Kőnig, *Gráfok és alkalmazásuk a determinánsok és a halmazok elméletére*, Mat. Természett.
  Ért. 34 (1916).
* R. Diestel, *Graph Theory*, 5th ed., Springer, 2017, Section 2.1.
-/

public section

open Finset Function
open scoped Graph

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β} {L R : Finset V(G)} {k : ℕ}

namespace IsBipartition

/-- In a bipartite multigraph whose actual vertices are each an end of `k ≠ 0` edges, every set
`S` of vertices of one side has at least `|S|` neighbours on the other side. -/
theorem card_le_card_neighborsIn [Finite E(G)] (hLR : G.IsBipartition L R) (hk : k ≠ 0)
    (hreg : ∀ x ∈ V(G), G.incidenceCount x = k) {S : Finset V(G)} (hS : S ⊆ L) :
    #S ≤ #(G.neighborsIn S R) := by
  classical
  have := Fintype.ofFinite E(G)
  -- Count, for each set of vertices, the pairs of a vertex of the set and an edge at it.
  have hcount (T : Finset V(G)) :
      ∑ e : E(G), #{x ∈ T | G.Inc e.1 x.1} = #T * k := by
    have := G.sum_sum_incidentEdges_eq_sum_sum_filter_inc T fun _ ↦ 1
    simp only [sum_const, smul_eq_mul, mul_one, card_incidentEdges_singleton] at this
    rw [← this, sum_congr rfl fun x _ ↦ hreg x.1 x.2, sum_const, smul_eq_mul]
  -- An edge at `S` has a single end in `S`, and its other end is a neighbour of `S`.
  have hle (e : E(G)) : #{x ∈ S | G.Inc e.1 x.1} ≤ #{y ∈ G.neighborsIn S R | G.Inc e.1 y.1} := by
    obtain hS' | ⟨x, hx⟩ := eq_empty_or_nonempty {x ∈ S | G.Inc e.1 x.1}
    · simp [hS']
    obtain ⟨hxS, hex⟩ := mem_filter.1 hx
    have hlink := hex.isLink_other
    refine (card_le_one.2 fun a ha b hb ↦ ?_).trans (one_le_card.2 ⟨⟨_, hlink.right_mem⟩, ?_⟩)
    · exact (hLR.existsUnique_mem_left_inc e).unique ⟨hS (mem_filter.1 ha).1, (mem_filter.1 ha).2⟩
        ⟨hS (mem_filter.1 hb).1, (mem_filter.1 hb).2⟩
    · exact mem_filter.2 ⟨mem_neighborsIn.2 ⟨hLR.mem_right_of_isLink hlink (hS hxS),
        x, hxS, e, hlink⟩, hlink.inc_right⟩
  have := (hcount S).symm.trans_le ((sum_le_sum fun e _ ↦ hle e).trans_eq (hcount _))
  exact Nat.le_of_mul_le_mul_right this (Nat.pos_of_ne_zero hk)

/-- A bipartite multigraph whose actual vertices are each an end of `k ≠ 0` edges has sides of
equal size. -/
theorem card_left_eq_card_right [Finite E(G)] (hLR : G.IsBipartition L R) (hk : k ≠ 0)
    (hreg : ∀ x ∈ V(G), G.incidenceCount x = k) :
    #L = #R :=
  -- Every vertex of `L` has a neighbour, which lies in `R`, and symmetrically.
  ((hLR.card_le_card_neighborsIn hk hreg Subset.rfl).trans
      (card_le_card neighborsIn_subset)).antisymm
    ((hLR.symm.card_le_card_neighborsIn hk hreg Subset.rfl).trans
      (card_le_card neighborsIn_subset))

/-- A bipartite multigraph with finitely many actual edges, whose actual vertices are each an end
of `k ≠ 0` edges, has a perfect matching. -/
theorem exists_isPerfectMatching [Finite E(G)] (hLR : G.IsBipartition L R) (hk : k ≠ 0)
    (hreg : ∀ x ∈ V(G), G.incidenceCount x = k) :
    ∃ M : Set β, G.IsPerfectMatching M := by
  have := Fintype.ofFinite E(G)
  have := hLR.loopless
  -- Hall's theorem at unit capacities gives edge multiplicities using every vertex once.
  obtain ⟨x, -, hx⟩ := (hLR.exists_isCapacitatedMatching_saturating_iff 1).2
    ⟨by simpa using hLR.card_left_eq_card_right hk hreg,
      fun S hS ↦ by simpa using hLR.card_le_card_neighborsIn hk hreg hS⟩
  exact ⟨_, isPerfectMatching_of_sum_incidentEdges_eq_one fun v ↦ by simpa using hx v⟩

/-- **Perfect matching decomposition.** The edge set of a bipartite multigraph with finitely many
actual edges, whose actual vertices are each an end of `k` edges, is the disjoint union of `k`
perfect matchings. When `k = 0` the multigraph has no edges and the family is empty. -/
theorem exists_perfectMatching_decomposition [Finite E(G)] (hLR : G.IsBipartition L R)
    (hreg : ∀ x ∈ V(G), G.incidenceCount x = k) :
    ∃ M : Fin k → Set β, (∀ i, G.IsPerfectMatching (M i)) ∧ Pairwise (Disjoint on M) ∧
      ⋃ i, M i = E(G) := by
  induction k generalizing G with
  | zero =>
    -- Every edge has an actual end, which would then have a positive incidence count.
    refine ⟨Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, ?_⟩
    refine (Set.iUnion_of_empty _).trans (Set.eq_empty_of_forall_notMem fun e he ↦ ?_).symm
    obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
    have := hreg x hxy.left_mem
    rw [incidenceCount_def, Set.ncard_eq_zero (G.finite_incidenceSet x)] at this
    exact Set.eq_empty_iff_forall_notMem.1 this e ((G.mem_incidenceSet x e).2 hxy.inc_left)
  | succ k ih =>
    -- Delete a perfect matching, decompose the remaining `k`-regular multigraph, and add it back.
    obtain ⟨M₀, hM₀⟩ := hLR.exists_isPerfectMatching k.succ_ne_zero hreg
    have hE : E(G.deleteEdges M₀) = E(G) \ M₀ := edgeSet_deleteEdges ..
    have : Finite E(G.deleteEdges M₀) := (Set.toFinite E(G)).subset (hE ▸ Set.sdiff_subset)
    obtain ⟨M, hM, hdisj, hunion⟩ := ih (hLR.deleteEdges M₀) fun x hx ↦ by
      have := hM₀.incidenceCount_deleteEdges_add_one hx (G.finite_incidenceSet x)
      rw [hreg x hx] at this
      omega
    have hspan : G.deleteEdges M₀ ≤s G := ⟨deleteEdges_le, vertexSet_deleteEdges ..⟩
    have hdisj₀ (i : Fin k) : Disjoint M₀ (M i) :=
      Set.disjoint_left.2 fun e he₀ he ↦ (hE ▸ (hM i).subset_edgeSet he).2 he₀
    refine ⟨Fin.cons M₀ M, Fin.forall_fin_succ.2 ⟨by simpa using hM₀, fun i ↦ ?_⟩,
      pairwise_fin_succ_iff.2 ?_, ?_⟩
    · simpa using (hspan.isPerfectMatching_iff (hM i).subset_edgeSet).1 (hM i)
    · simp only [onFun, Fin.cons_zero, Fin.cons_succ]
      exact ⟨fun i ↦ (hdisj₀ i).symm, hdisj₀, fun i j hij ↦ hdisj hij⟩
    · -- The new union is `M₀ ∪ (E(G) \ M₀)`, which is `E(G)` since `M₀ ⊆ E(G)`.
      rw [← Set.union_sdiff_cancel hM₀.subset_edgeSet, ← hE, ← hunion]
      ext e
      simp

end IsBipartition

end Graph
