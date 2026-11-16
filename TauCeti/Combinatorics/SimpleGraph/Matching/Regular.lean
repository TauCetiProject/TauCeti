/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Hall

/-!
# Perfect matchings of regular bipartite simple graphs

This file proves the classical consequences of Hall's theorem for `k`-regular bipartite simple
graphs:

* if `k ≠ 0`, there is a perfect matching, and the two sides of any bipartition are in bijection;
* for every `k`, the edge set is the disjoint union of `k` perfect matchings.

When `k = 0` the graph has no edges and the family of perfect matchings is empty; no perfect
matching need exist, since an isolated vertex is matched by none. The vertex type may be
infinite: the graph only needs to be locally finite, as in Mathlib's Hall theorem for bipartite
graphs.

## Main results

* `SimpleGraph.IsRegularOfDegree.ncard_le_ncard_iUnion_neighborSet`: Hall's condition in a
  `k`-regular graph with `k ≠ 0`.
* `SimpleGraph.IsRegularOfDegree.exists_isPerfectMatching`: a `k`-regular bipartite graph with
  `k ≠ 0` has a perfect matching.
* `SimpleGraph.IsRegularOfDegree.nonempty_equiv_of_isBipartiteWith`: the two sides of a
  `k`-regular bipartite graph with `k ≠ 0` are in bijection.
* `SimpleGraph.Subgraph.IsPerfectMatching.isRegularOfDegree_deleteEdges`: deleting a perfect
  matching from a `(k + 1)`-regular graph leaves a `k`-regular graph.
* `SimpleGraph.IsRegularOfDegree.exists_perfectMatching_decomposition`: the edge set of a
  `k`-regular bipartite graph is the disjoint union of `k` perfect matchings.

## Implementation notes

In a locally finite graph in which every vertex has degree `k ≠ 0`, a finite vertex set `S` has at
least `|S|` neighbours: the `k * |S|` adjacent pairs with first vertex in `S` are among the
`k * |N(S)|` adjacent pairs with second vertex in the neighbourhood `N(S)`. Mathlib's
`SimpleGraph.exists_isPerfectMatching_of_forall_ncard_le` then gives a perfect matching. Deleting
it lowers every degree by one, which gives the decomposition by induction on `k`.

## References

* D. Kőnig, *Gráfok és alkalmazásuk a determinánsok és a halmazok elméletére*, Mat. Természett.
  Ért. 34 (1916).
* R. Diestel, *Graph Theory*, 5th ed., Springer, 2017, Section 2.1.
-/

public section

open Finset Function

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

/-- **Hall's condition in a regular graph.** In a locally finite graph in which every vertex has
degree `k ≠ 0`, every vertex set `s` has at least as many neighbours as elements. Infinite sets
satisfy this trivially, since their `ncard` is zero. -/
theorem IsRegularOfDegree.ncard_le_ncard_iUnion_neighborSet [G.LocallyFinite]
    (hG : G.IsRegularOfDegree k) (hk : k ≠ 0) (s : Set V) :
    s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard := by
  classical
  obtain hs | hs := s.finite_or_infinite
  swap
  · simp [hs.ncard]
  have hN : (⋃ x ∈ s, G.neighborSet x).Finite := hs.biUnion fun x _ ↦ (G.neighborSet x).toFinite
  rw [Set.ncard_eq_toFinset_card s hs, Set.ncard_eq_toFinset_card _ hN]
  -- Count adjacent pairs with first vertex in `s`: each such vertex contributes all `k` of its
  -- neighbours, while each neighbour receives at most its `k` neighbours.
  refine Nat.le_of_mul_le_mul_right (card_mul_le_card_mul G.Adj (m := k) (n := k)
    (fun a ha ↦ ?_) fun b _ ↦ ?_) (Nat.pos_of_ne_zero hk)
  · rw [← hG.degree_eq a, ← card_neighborFinset_eq_degree]
    refine card_le_card fun y hy ↦ (mem_bipartiteAbove G.Adj).2 ⟨?_, (mem_neighborFinset ..).1 hy⟩
    exact hN.mem_toFinset.2 <| Set.mem_biUnion (hs.mem_toFinset.1 ha) ((mem_neighborFinset ..).1 hy)
  · rw [← hG.degree_eq b, ← card_neighborFinset_eq_degree]
    exact card_le_card fun x hx ↦ (mem_neighborFinset ..).2 ((mem_bipartiteBelow G.Adj).1 hx).2.symm

/-- A locally finite `k`-regular bipartite graph with `k ≠ 0` has a perfect matching. -/
theorem IsRegularOfDegree.exists_isPerfectMatching [G.LocallyFinite]
    (hG : G.IsRegularOfDegree k) (hk : k ≠ 0) (hbip : G.IsBipartite) :
    ∃ M : G.Subgraph, M.IsPerfectMatching :=
  let ⟨_, _, hst⟩ := hbip.exists_isBipartiteWith
  exists_isPerfectMatching_of_forall_ncard_le hst (hG.ncard_le_ncard_iUnion_neighborSet hk)

/-- The two sides of a bipartition of a locally finite `k`-regular graph with `k ≠ 0` are in
bijection. -/
theorem IsRegularOfDegree.nonempty_equiv_of_isBipartiteWith [G.LocallyFinite]
    (hG : G.IsRegularOfDegree k) (hk : k ≠ 0) {s t : Set V} (hst : G.IsBipartiteWith s t) :
    Nonempty (s ≃ t) :=
  let ⟨f, hf, _⟩ :=
    exists_bijective_of_forall_ncard_le hst (hG.ncard_le_ncard_iUnion_neighborSet hk)
  ⟨.ofBijective f hf⟩

/-- The two sides of a bipartition of a locally finite `k`-regular graph with `k ≠ 0` have the
same number of elements. -/
theorem IsRegularOfDegree.ncard_eq_of_isBipartiteWith [G.LocallyFinite]
    (hG : G.IsRegularOfDegree k) (hk : k ≠ 0) {s t : Set V} (hst : G.IsBipartiteWith s t) :
    s.ncard = t.ncard := by
  obtain ⟨e⟩ := hG.nonempty_equiv_of_isBipartiteWith hk hst
  simpa using Nat.card_congr e

namespace Subgraph.IsPerfectMatching

variable {M : G.Subgraph}

/-- Deleting the edges of a perfect matching lowers the degree of every vertex by one. -/
theorem degree_deleteEdges_add_one [G.LocallyFinite] [(G.deleteEdges M.edgeSet).LocallyFinite]
    (hM : M.IsPerfectMatching) (v : V) :
    (G.deleteEdges M.edgeSet).degree v + 1 = G.degree v := by
  obtain ⟨w, hw, -⟩ := isPerfectMatching_iff.1 hM v
  have : (G.deleteEdges M.edgeSet).neighborSet v = G.neighborSet v \ {w} := by
    ext x
    rw [SimpleGraph.mem_neighborSet, SimpleGraph.deleteEdges_adj, Subgraph.mem_edgeSet,
      Set.mem_sdiff, SimpleGraph.mem_neighborSet, Set.mem_singleton_iff]
    exact and_congr_right fun _ ↦ not_congr ⟨fun h ↦ hM.1.eq_of_adj_left h hw, (· ▸ hw)⟩
  rw [← ncard_neighborSet, ← ncard_neighborSet, this,
    Set.ncard_sdiff_singleton_add_one (M.adj_sub hw)]

/-- Deleting the edges of a perfect matching from a `(k + 1)`-regular graph leaves a `k`-regular
graph. -/
theorem isRegularOfDegree_deleteEdges [G.LocallyFinite]
    [(G.deleteEdges M.edgeSet).LocallyFinite] (hG : G.IsRegularOfDegree (k + 1))
    (hM : M.IsPerfectMatching) :
    (G.deleteEdges M.edgeSet).IsRegularOfDegree k :=
  fun v ↦ Nat.add_right_cancel <| (hM.degree_deleteEdges_add_one v).trans (hG.degree_eq v)

end Subgraph.IsPerfectMatching

/-- **Perfect matching decomposition.** The edge set of a locally finite `k`-regular bipartite
graph is the disjoint union of the edge sets of `k` perfect matchings. When `k = 0` the graph has
no edges and the family is empty. -/
theorem IsRegularOfDegree.exists_perfectMatching_decomposition [G.LocallyFinite]
    (hG : G.IsRegularOfDegree k) (hbip : G.IsBipartite) :
    ∃ M : Fin k → G.Subgraph, (∀ i, (M i).IsPerfectMatching) ∧
      Pairwise (Disjoint on fun i ↦ (M i).edgeSet) ∧ ⋃ i, (M i).edgeSet = G.edgeSet := by
  induction k generalizing G with
  | zero =>
    -- Every vertex is isolated, so there are no edges.
    refine ⟨Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, ?_⟩
    rw [Set.iUnion_of_empty, eq_comm, Set.eq_empty_iff_forall_notMem]
    intro e he
    induction e using Sym2.ind with
    | _ v w => exact (degree_eq_zero G v).1 (hG.degree_eq v) w he
  | succ k ih =>
    -- Delete a perfect matching, decompose the remaining `k`-regular graph, and add it back.
    obtain ⟨M₀, hM₀⟩ := hG.exists_isPerfectMatching k.succ_ne_zero hbip
    have hle := G.deleteEdges_le M₀.edgeSet
    let _ : (G.deleteEdges M₀.edgeSet).LocallyFinite := fun v ↦
      ((G.neighborSet v).toFinite.subset fun _ hx ↦ hle hx).fintype
    obtain ⟨M, hM, hdisj, hunion⟩ :=
      ih (hM₀.isRegularOfDegree_deleteEdges hG) (hbip.mono_left hle)
    have hE (i : Fin k) : ((M i).map (Hom.ofLE hle)).edgeSet = (M i).edgeSet := by
      simp
    have hdisj₀ (i : Fin k) : Disjoint M₀.edgeSet (M i).edgeSet := by
      refine Set.disjoint_right.2 fun e he ↦ ?_
      have := (M i).edgeSet_subset he
      rw [edgeSet_deleteEdges] at this
      exact this.2
    refine ⟨Fin.cons M₀ fun i ↦ (M i).map (Hom.ofLE hle),
      Fin.forall_fin_succ.2 ⟨hM₀, fun i ↦ ⟨(hM i).1.map_ofLE hle, fun v ↦ ?_⟩⟩,
      pairwise_fin_succ_iff.2 ⟨fun i ↦ ?_, fun i ↦ ?_, fun i j hij ↦ ?_⟩, ?_⟩
    · simpa using (hM i).2 v
    · simpa [onFun, hE] using (hdisj₀ i).symm
    · simpa [onFun, hE] using hdisj₀ i
    · simpa [onFun, hE] using hdisj hij
    · -- An edge outside `M₀` survives the deletion, so it lies in one of the `M i`.
      refine (Set.iUnion_subset fun i ↦ Subgraph.edgeSet_subset _).antisymm fun e he ↦ ?_
      by_cases he₀ : e ∈ M₀.edgeSet
      · exact Set.mem_iUnion.2 ⟨0, by simpa using he₀⟩
      have : e ∈ ⋃ i, (M i).edgeSet := hunion ▸ (edgeSet_deleteEdges _ ▸ ⟨he, he₀⟩)
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 this
      exact Set.mem_iUnion.2 ⟨i.succ, by simpa [hE] using hi⟩

end SimpleGraph
