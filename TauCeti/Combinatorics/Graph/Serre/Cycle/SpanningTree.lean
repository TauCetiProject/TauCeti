/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Cycle.Coefficients
public import TauCeti.Combinatorics.Graph.Serre.SpanningTree

/-!
# Spanning trees as spanning forests: fundamental cycles and the edge count of a finite tree

Let `T` be a spanning tree and `O` an orientation of `Γ`. Deleting a dart of `T` together with
its reverse separates its endpoints, so the simple support of `T` is a tree, and the positive
darts of `T` form a spanning forest of `O`. Its fundamental cycles, indexed by the positive darts
outside `T`, form a basis of the cycle module over any ring: the cycle of such a dart has
coordinate one at that dart and zero at the other positive darts outside `T`, and it is the unit
chain of the dart when the dart is a loop. Extension of scalars carries `r ⊗` an integral
fundamental cycle to `r` times the fundamental cycle of the same dart. Counting gives the
edge count of a finite tree: a spanning tree of a graph with finitely many vertices has one
positive dart fewer than there are vertices. Hence a connected graph with finitely many positive
darts, which then has finitely many vertices, has `#O + 1 - #V` positive darts outside a spanning
tree.

## Main results

* `TauCeti.SerreGraph.SpanningTree.isTree_supportGraph`: the simple support of a spanning tree
  is a tree.
* `TauCeti.SerreGraph.SpanningTree.isSpanningForest`: the positive darts of a spanning tree
  form a spanning forest of the orientation.
* `TauCeti.SerreGraph.SpanningTree.cycleBasis`: the fundamental cycle basis of a spanning tree,
  indexed by the positive darts outside the tree.
* `TauCeti.SerreGraph.SpanningTree.card_inter_add_one`: a spanning tree has `#V - 1` positive
  darts.
* `TauCeti.SerreGraph.SpanningTree.card_diff_add_card`: the number of positive darts outside a
  spanning tree, plus the number of vertices, is the number of positive darts plus one.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.3.
* I. Kapovich, A. Myasnikov, *Stallings foldings and subgroups of free groups*, §8, Lemma 8.2.
* R. Diestel, *Graph Theory*, §1.9 (fundamental cycle bases).
-/

public section

open scoped TensorProduct

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

section CycleBasis

variable (R : Type*) [Ring R]

/-- The fundamental cycle basis of a spanning tree: the basis of the cycle module over `R` indexed
by the positive darts outside the tree, whose cycle through such a dart has coordinate one at that
dart and zero at the other positive darts outside the tree. -/
noncomputable def cycleBasis : Module.Basis ↥(O \ T.darts) R (Γ.incidenceBoundary O R).ker :=
  ((T.isSpanningForest hO).cycleBasis R).reindex (Set.equivOfEq Set.sdiff_inter_self_eq_sdiff)

/-- The fundamental cycle of a positive dart outside the tree is its fundamental cycle for the
spanning forest of positive tree darts. -/
theorem cycleBasis_apply (e : ↥(O \ T.darts)) :
    T.cycleBasis hO R e =
      (T.isSpanningForest hO).cycleBasis R ⟨e.1, e.2.1, fun h => e.2.2 h.1⟩ := by
  simp [cycleBasis]

/-- The coefficient of the fundamental cycle of a positive dart outside the tree in a cycle is the
coordinate of the cycle at that dart. -/
@[simp] theorem cycleBasis_repr (c : (Γ.incidenceBoundary O R).ker) (e : ↥(O \ T.darts)) :
    (T.cycleBasis hO R).repr c e = c.val ⟨e.1, e.2.1⟩ := by
  simp [cycleBasis]

/-- The fundamental cycles of the tree have unit coordinates at the positive darts outside the
tree. -/
@[simp] theorem cycleBasis_apply_chord (e f : ↥(O \ T.darts)) :
    (T.cycleBasis hO R e).val ⟨f.1, f.2.1⟩ = Finsupp.single e (1 : R) f := by
  rw [← T.cycleBasis_repr hO]
  simp

/-- The coordinates of a fundamental cycle of the tree at the positive darts outside the tree form
the unit vector of its dart. -/
@[simp] theorem cycleChordCoordinates_cycleBasis (e : ↥(O \ T.darts)) :
    Γ.cycleChordCoordinates O T.darts R (T.cycleBasis hO R e) = Finsupp.single e 1 := by
  ext f
  simp

/-- The fundamental cycle of a positive loop dart outside the tree is the unit chain on that
loop. -/
theorem cycleBasis_of_loop (e : ↥(O \ T.darts)) (he : Γ.src e.1 = Γ.tgt e.1) :
    (T.cycleBasis hO R e).val = Finsupp.single ⟨e.1, e.2.1⟩ 1 := by
  simp [cycleBasis_apply, IsSpanningForest.cycleBasis_of_loop, he]

/-- Extension of scalars sends `r ⊗` an integral fundamental cycle of a spanning tree to `r` times
its fundamental cycle over `R`. -/
@[simp] theorem cycleBaseChangeEquiv_tmul_cycleBasis (r : R) (e : ↥(O \ T.darts)) :
    Γ.cycleBaseChangeEquiv O R (r ⊗ₜ[ℤ] T.cycleBasis hO ℤ e) = r • T.cycleBasis hO R e := by
  simp [cycleBasis_apply]

/-- The coordinates of a fundamental cycle of the tree over any ring are the casts of the
coordinates of the integral fundamental cycle of the same dart. -/
@[simp] theorem intCast_cycleBasis_apply (e : ↥(O \ T.darts)) (d : O) :
    ((T.cycleBasis hO ℤ e).val d : R) = (T.cycleBasis hO R e).val d := by
  simp [cycleBasis_apply]

end CycleBasis

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
