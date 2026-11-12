/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Cycle.Forest
public import TauCeti.Combinatorics.Graph.Serre.SpanningTree

/-!
# Spanning trees as spanning forests, and the edge count of a finite tree

Let `T` be a spanning tree and `O` an orientation of `Γ`. Deleting a dart of `T` together with
its reverse separates its endpoints, so the simple support of `T` is a tree, and the positive
darts of `T` form a spanning forest of `O`. Counting gives the edge count of a finite tree: a
spanning tree of a graph with finitely many vertices has one positive dart fewer than there are
vertices. Hence a connected graph with finitely many positive darts, which then has finitely
many vertices, has `#O + 1 - #V` positive darts outside a spanning tree.

## Main results

* `TauCeti.SerreGraph.SpanningTree.isTree_supportGraph`: the simple support of a spanning tree
  is a tree.
* `TauCeti.SerreGraph.SpanningTree.isSpanningForest`: the positive darts of a spanning tree
  form a spanning forest of the orientation.
* `TauCeti.SerreGraph.SpanningTree.card_inter_add_one`: a spanning tree has `#V - 1` positive
  darts.
* `TauCeti.SerreGraph.SpanningTree.card_diff_add_card`: the number of positive darts outside a
  spanning tree, plus the number of vertices, is the number of positive darts plus one.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.3.
* I. Kapovich, A. Myasnikov, *Stallings foldings and subgroups of free groups*, §8, Lemma 8.2.
-/

public section

namespace TauCeti.SerreGraph.SpanningTree

universe u v

variable {Γ : SerreGraph.{u, v}} (T : Γ.SpanningTree)

/-! ### The simple support of a spanning tree -/

/-- Any two vertices are joined in the simple support of a spanning tree. -/
theorem reachable_supportGraph (a b : Γ.V) : (Γ.supportGraph T.darts).Reachable a b :=
  (T.path a b).reachable_supportGraph fun _ => T.mem_of_mem_darts_path

/-- Deleting a dart of a spanning tree together with its reverse separates its endpoints. -/
theorem not_reachable_supportGraph_diff {e : Γ.E} (he : e ∈ T.darts) :
    ¬(Γ.supportGraph (T.darts \ {e, Γ.rev e})).Reachable (Γ.src e) (Γ.tgt e) := by
  have hrev : ∀ d ∈ T.darts \ {e, Γ.rev e}, Γ.rev d ∈ T.darts \ {e, Γ.rev e} := by
    rintro d ⟨hd, hde⟩
    refine ⟨T.rev_mem d hd, fun h => hde ?_⟩
    rcases h with h | h
    · exact .inr (by simp [← h])
    · exact .inl (Γ.rev_injective h)
  intro h
  obtain ⟨p, hp⟩ := (reachable_supportGraph_iff hrev).mp h
  have hsub : ∀ d ∈ Path.darts Γ (Path.reduce Γ p), d ∈ T.darts \ {e, Γ.rev e} :=
    fun d hd => hp d ((Path.darts_reduce_sublist Γ p).subset hd)
  have hpath := T.eq_path (Path.isReduced_reduce Γ p) fun d hd => (hsub d hd).1
  rw [T.path_src_tgt he] at hpath
  exact (hsub e (by simp [hpath])).2 (.inl rfl)

/-- The simple support of a spanning tree is a tree. -/
theorem isTree_supportGraph : (Γ.supportGraph T.darts).IsTree := by
  have : Nonempty Γ.V := (Γ.connected_iff.mp ((nonempty_spanningTree_iff Γ).mp ⟨T⟩)).1
  refine ⟨⟨T.reachable_supportGraph⟩, SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mpr ?_⟩
  -- By symmetry of bridges, it suffices to treat the endpoints of a tree dart in its direction.
  have key : ∀ e ∈ T.darts, (Γ.supportGraph T.darts).IsBridge s(Γ.src e, Γ.tgt e) := by
    intro e he
    refine SimpleGraph.isBridge_iff.mpr fun h => T.not_reachable_supportGraph_diff he (h.mono ?_)
    intro x y hxy
    obtain ⟨hadj, hne⟩ := SimpleGraph.deleteEdges_adj.mp hxy
    obtain ⟨hxy', h⟩ := (Γ.supportGraph_adj _ x y).mp hadj
    refine (Γ.supportGraph_adj _ x y).mpr ⟨hxy', h.imp ?_ ?_⟩ <;>
    · rintro ⟨d, hd, rfl, rfl⟩
      refine ⟨d, ⟨hd, ?_⟩, rfl, rfl⟩
      rintro (rfl | rfl) <;> simp [Sym2.eq_swap] at hne
  intro x y hxy
  obtain ⟨-, ⟨e, he, rfl, rfl⟩ | ⟨e, he, rfl, rfl⟩⟩ := (Γ.supportGraph_adj _ x y).mp hxy
  · exact key e he
  · exact Sym2.eq_swap ▸ key e he

/-! ### The positive darts of a spanning tree -/

variable {O : Set Γ.E} (hO : Γ.IsOrientation O)

include hO

/-- The positive darts of a spanning tree form a spanning forest of the orientation. -/
theorem isSpanningForest : Γ.IsSpanningForest O (T.darts ∩ O) where
  subset := Set.inter_subset_right
  src_ne_tgt _ he := T.src_ne_tgt he.1
  endpoints_injOn := by
    intro e he f hf h
    rcases Sym2.eq_iff.mp h with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · exact T.eq_of_src_eq_of_tgt_eq he.1 hf.1 hs ht
    · have h := T.eq_of_src_eq_of_tgt_eq he.1 (T.rev_mem f hf.1) (by simpa using hs)
        (by simpa using ht)
      exact absurd (h ▸ he.2) (hO.rev_notMem_of_mem Γ f hf.2)
  isAcyclic := by
    rw [hO.supportGraph_inter T.rev_mem]
    exact T.isTree_supportGraph.isAcyclic
  reachable_eq := by
    rw [hO.supportGraph_inter T.rev_mem]
    ext a b
    exact iff_of_true (T.reachable_supportGraph a b)
      (hO.reachable_supportGraph_iff_nonempty_path.mpr ⟨T.path a b⟩)

/-- A spanning tree of a graph with finitely many vertices has one positive dart fewer than
there are vertices. -/
theorem card_inter_add_one [Finite Γ.V] : Nat.card ↥(T.darts ∩ O) + 1 = Nat.card Γ.V := by
  have h := (T.isSpanningForest hO).card_add_card_connectedComponent
  rwa [SimpleGraph.card_connectedComponent_eq_one_iff.mpr
    (hO.connected_supportGraph_iff.mpr ((nonempty_spanningTree_iff Γ).mp ⟨T⟩))] at h

/-- For finitely many positive darts, the number of positive darts outside a spanning tree, plus
the number of vertices, is the number of positive darts plus one. -/
theorem card_diff_add_card [Finite O] :
    Nat.card ↥(O \ T.darts) + Nat.card Γ.V = Nat.card O + 1 := by
  -- Every dart lies in `O` or reverses a dart of `O`, and every vertex other than a base vertex
  -- `v` is the target of the last dart of the tree path from `v`.
  have : Finite Γ.E := Set.finite_univ_iff.mp <|
    ((Set.toFinite O).union ((Set.toFinite O).preimage Γ.rev_injective.injOn)).subset
      fun e _ => (em (e ∈ O)).imp id (hO.mem_rev_iff Γ e).mpr
  obtain ⟨v⟩ := (Γ.connected_iff.mp ((nonempty_spanningTree_iff Γ).mp ⟨T⟩)).1
  have : Finite Γ.V := Set.finite_univ_iff.mp <|
    ((Set.finite_range Γ.tgt).insert v).subset fun w _ => by
      cases T.path v w with
      | nil => exact .inl rfl
      | cons _ e => exact .inr ⟨e.1, e.2.2⟩
  have h := Set.ncard_inter_add_ncard_sdiff_eq_ncard O T.darts (Set.toFinite O)
  have h' := T.card_inter_add_one hO
  rw [Set.inter_comm] at h'
  simp only [Nat.card_coe_set_eq] at h' ⊢
  omega

end TauCeti.SerreGraph.SpanningTree
