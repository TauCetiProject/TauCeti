/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Tree

/-!
# Convex sets of vertices

A set of vertices of a Serre graph is convex when it contains every vertex crossed by a reduced
path between two of its vertices. In a tree, the nonempty convex sets are the vertex sets of the
subtrees, since reduced paths are the geodesics. Convex sets are closed under arbitrary
intersections. In an acyclic graph, the following sets are convex: a set of vertices in which no
two distinct vertices are joined by a path (for instance a singleton), and the set of vertices of
a path.

In a tree, a union of convex sets with a common vertex is convex, and a dart between two convex
sets with a common vertex has both endpoints in one of them: subtrees through a common vertex
glue to a subtree, without creating new edges. Here the edges of the subgraph on a set of vertices
are its induced darts, `SerreGraph.inducedDarts`.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.2 and §6.1.
-/

public section

namespace TauCeti
namespace SerreGraph

variable (Γ : SerreGraph)

/-- A set of vertices is convex when every reduced path between two of its vertices only starts
darts at vertices of the set. -/
def IsConvex (S : Set Γ.V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ p : Γ.Path a b, Path.IsReduced Γ p → ∀ e ∈ Path.darts Γ p, Γ.src e ∈ S

variable {Γ}

/-- Unfold convexity. -/
theorem isConvex_iff {S : Set Γ.V} : Γ.IsConvex S ↔
    ∀ a ∈ S, ∀ b ∈ S, ∀ p : Γ.Path a b, Path.IsReduced Γ p →
      ∀ e ∈ Path.darts Γ p, Γ.src e ∈ S := Iff.rfl

/-- A reduced path between vertices of a convex set starts its darts in the set. -/
theorem IsConvex.src_mem {S : Set Γ.V} (hS : Γ.IsConvex S) {a b : Γ.V} (ha : a ∈ S)
    (hb : b ∈ S) {p : Γ.Path a b} (hp : Path.IsReduced Γ p) {e : Γ.E}
    (he : e ∈ Path.darts Γ p) : Γ.src e ∈ S :=
  hS a ha b hb p hp e he

/-- A reduced path between vertices of a convex set also ends its darts in the set. -/
theorem IsConvex.tgt_mem {S : Set Γ.V} (hS : Γ.IsConvex S) {a b : Γ.V} (ha : a ∈ S)
    (hb : b ∈ S) {p : Γ.Path a b} (hp : Path.IsReduced Γ p) {e : Γ.E}
    (he : e ∈ Path.darts Γ p) : Γ.tgt e ∈ S := by
  have hp' : Path.IsReduced Γ p.reverse := (Path.isReduced_reverse Γ p).mpr hp
  have he' : Γ.rev e ∈ Path.darts Γ p.reverse := by
    simpa only [Path.darts_reverse, List.mem_map, List.mem_reverse] using ⟨e, he, rfl⟩
  simpa only [src_rev] using hS.src_mem hb ha hp' he'

/-- A reduced path ending at a vertex `b` of a convex set `C`, whose last dart starts outside `C`,
can be continued by any reduced path from `b` to a vertex of `C` without backtracking. -/
theorem IsConvex.isReduced_comp {C : Set Γ.V} (hC : Γ.IsConvex C) {a b c : Γ.V}
    (hb : b ∈ C) (hc : c ∈ C) {p : Γ.Path a b} (hp : Path.IsReduced Γ p)
    (hpC : ∀ e ∈ (Path.darts Γ p).getLast?, Γ.src e ∉ C) {q : Γ.Path b c}
    (hq : Path.IsReduced Γ q) :
    Path.IsReduced Γ (p.comp q) := by
  refine (Path.isReduced_comp_iff Γ p q).mpr ⟨hp, hq, fun e he f hf hfe => ?_⟩
  -- The darts of `q` end in `C`, while the reverse of a dart of `p` ends outside it.
  have hfC : Γ.tgt f ∈ C := hC.tgt_mem hb hc hq (List.mem_of_mem_head? hf)
  rw [hfe, tgt_rev] at hfC
  exact hpC e he hfC

theorem isConvex_univ : Γ.IsConvex Set.univ := fun _ _ _ _ _ _ _ _ => Set.mem_univ _

theorem isConvex_empty : Γ.IsConvex ∅ := fun _ ha => ha.elim

/-- Intersections of convex sets are convex. -/
theorem isConvex_sInter {𝒮 : Set (Set Γ.V)} (h : ∀ S ∈ 𝒮, Γ.IsConvex S) :
    Γ.IsConvex (⋂₀ 𝒮) := fun a ha b hb p hp e he =>
  Set.mem_sInter.mpr fun S hS => h S hS a (ha S hS) b (hb S hS) p hp e he

/-- Intersections of indexed families of convex sets are convex. -/
theorem isConvex_iInter {ι : Sort*} {S : ι → Set Γ.V} (h : ∀ i, Γ.IsConvex (S i)) :
    Γ.IsConvex (⋂ i, S i) :=
  isConvex_sInter (Set.forall_mem_range.mpr h)

theorem IsConvex.inter {S T : Set Γ.V} (hS : Γ.IsConvex S) (hT : Γ.IsConvex T) :
    Γ.IsConvex (S ∩ T) := fun a ha b hb p hp e he =>
  ⟨hS a ha.1 b hb.1 p hp e he, hT a ha.2 b hb.2 p hp e he⟩

/-- In an acyclic graph, a set of vertices in which no two distinct vertices are joined by a path
is convex. -/
theorem IsAcyclic.isConvex_of_pairwise (h : Γ.IsAcyclic) {S : Set Γ.V}
    (hS : S.Pairwise fun a b => IsEmpty (Γ.Path a b)) : Γ.IsConvex S := by
  intro a ha b hb p hp e he
  obtain rfl | hab := eq_or_ne a b
  · rw [(isAcyclic_iff Γ).mp h a p hp, Path.darts_nil] at he
    exact absurd he List.not_mem_nil
  · exact (hS ha hb hab).elim p

/-- In an acyclic graph every singleton is convex. -/
theorem IsAcyclic.isConvex_singleton (h : Γ.IsAcyclic) (v : Γ.V) : Γ.IsConvex {v} :=
  h.isConvex_of_pairwise (Set.pairwise_singleton v _)

/-- In an acyclic graph, the vertices of a path form a convex set. -/
theorem IsAcyclic.isConvex_setOf_mem_vertices (h : Γ.IsAcyclic) {a b : Γ.V} (p : Γ.Path a b) :
    Γ.IsConvex {v | v ∈ p.vertices} := by
  intro u hu v hv r hr e he
  obtain ⟨p₁, p₂, hp⟩ := p.exists_eq_comp_of_mem_vertices hu
  obtain ⟨q₁, q₂, hq⟩ := p.exists_eq_comp_of_mem_vertices hv
  -- The reduced path `r` only crosses darts of the path from `u` back to `a` and on to `v`.
  have he' := (h.darts_sublist hr (p₁.reverse.comp q₁)).subset he
  simp only [Path.darts_comp, Path.darts_reverse, List.mem_append, List.mem_map,
    List.mem_reverse] at he'
  rcases he' with ⟨f, hf, rfl⟩ | he'
  · rw [src_rev, Set.mem_ofPred_eq]
    exact Path.tgt_mem_vertices_of_mem_darts Γ p (by simp [hp, hf])
  · exact Path.src_mem_vertices_of_mem_darts Γ p (by simp [hq, he'])

/-! ### Unions of convex sets in a tree -/

/-- In a tree, the union of two convex sets with a common vertex is convex. -/
theorem IsTree.isConvex_union (h : Γ.IsTree) {A B : Set Γ.V} (hA : Γ.IsConvex A)
    (hB : Γ.IsConvex B) (hAB : (A ∩ B).Nonempty) : Γ.IsConvex (A ∪ B) := by
  obtain ⟨c, hcA, hcB⟩ := hAB
  -- A reduced path from one set to the other only crosses darts of the reduced paths from its
  -- endpoints to the common vertex `c`.
  have key : ∀ {A B : Set Γ.V}, Γ.IsConvex A → Γ.IsConvex B → c ∈ A → c ∈ B → ∀ a ∈ A, ∀ b ∈ B,
      ∀ p : Γ.Path a b, Path.IsReduced Γ p → ∀ e ∈ Path.darts Γ p, Γ.src e ∈ A ∨ Γ.src e ∈ B := by
    intro A B hA hB hcA hcB a ha b hb p hp e he
    obtain ⟨q, hq, -⟩ := h.existsUnique_isReduced a c
    obtain ⟨r, hr, -⟩ := h.existsUnique_isReduced c b
    have he' := (h.isAcyclic.darts_sublist hp (q.comp r)).subset he
    rw [Path.darts_comp, List.mem_append] at he'
    exact he'.imp (hA.src_mem ha hcA hq) (hB.src_mem hcB hb hr)
  rintro a (ha | ha) b (hb | hb) p hp e he
  · exact Or.inl (hA a ha b hb p hp e he)
  · exact key hA hB hcA hcB a ha b hb p hp e he
  · exact (key hB hA hcB hcA a ha b hb p hp e he).symm
  · exact Or.inr (hB a ha b hb p hp e he)

/-- In a tree, a union of convex sets with a common vertex is convex. -/
theorem IsTree.isConvex_iUnion (h : Γ.IsTree) {ι : Sort*} {A : ι → Set Γ.V} {x : Γ.V}
    (hA : ∀ i, Γ.IsConvex (A i)) (hx : ∀ i, x ∈ A i) : Γ.IsConvex (⋃ i, A i) := by
  intro a ha b hb p hp e he
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hb
  exact (h.isConvex_union (hA i) (hA j) ⟨x, hx i, hx j⟩ a (Or.inl hi) b (Or.inr hj) p hp e he).elim
    (fun h => Set.mem_iUnion.mpr ⟨i, h⟩) fun h => Set.mem_iUnion.mpr ⟨j, h⟩

/-- In a tree, a dart from a convex set to a convex set meeting it has both endpoints in one of
the two sets. -/
theorem IsTree.tgt_mem_or_src_mem (h : Γ.IsTree) {A B : Set Γ.V} (hA : Γ.IsConvex A)
    (hB : Γ.IsConvex B) (hAB : (A ∩ B).Nonempty) {e : Γ.E} (hs : Γ.src e ∈ A)
    (ht : Γ.tgt e ∈ B) : Γ.tgt e ∈ A ∨ Γ.src e ∈ B := by
  obtain ⟨c, hcA, hcB⟩ := hAB
  obtain ⟨q, hq, -⟩ := h.existsUnique_isReduced (Γ.src e) c
  obtain ⟨r, hr, -⟩ := h.existsUnique_isReduced c (Γ.tgt e)
  -- The dart is the reduced path between its endpoints, so it lies on one of `q` and `r`.
  have he := (h.isAcyclic.darts_sublist (Path.isReduced_toPath Γ (Γ.dart e)) (q.comp r)).subset
    (by rw [Path.darts_toPath, dart_val]; exact List.mem_singleton_self e)
  rw [Path.darts_comp, List.mem_append] at he
  exact he.imp (hA.tgt_mem hs hcA hq) (hB.src_mem hcB ht hr)

/-! ### Induced darts of unions of convex sets in a tree -/

/-- In a tree, the union of two convex sets with a common vertex induces no dart beyond those
induced by each of them. -/
theorem IsTree.inducedDarts_union (h : Γ.IsTree) {A B : Set Γ.V} (hA : Γ.IsConvex A)
    (hB : Γ.IsConvex B) (hAB : (A ∩ B).Nonempty) :
    Γ.inducedDarts (A ∪ B) = Γ.inducedDarts A ∪ Γ.inducedDarts B := by
  refine (Set.union_subset (inducedDarts_mono Set.subset_union_left)
    (inducedDarts_mono Set.subset_union_right)).antisymm' fun e he => ?_
  simp only [Set.mem_union, mem_inducedDarts_iff] at he ⊢
  obtain ⟨hs | hs, ht | ht⟩ := he
  · exact Or.inl ⟨hs, ht⟩
  · exact (h.tgt_mem_or_src_mem hA hB hAB hs ht).imp (fun h => ⟨hs, h⟩) fun h => ⟨h, ht⟩
  · exact ((h.tgt_mem_or_src_mem hB hA (Set.inter_comm A B ▸ hAB) hs ht).imp
      (fun h => ⟨hs, h⟩) fun h => ⟨h, ht⟩).symm
  · exact Or.inr ⟨hs, ht⟩

/-- In a tree, a union of convex sets with a common vertex induces no dart beyond those induced
by each of them. -/
theorem IsTree.inducedDarts_iUnion (h : Γ.IsTree) {ι : Sort*} {A : ι → Set Γ.V} {x : Γ.V}
    (hA : ∀ i, Γ.IsConvex (A i)) (hx : ∀ i, x ∈ A i) :
    Γ.inducedDarts (⋃ i, A i) = ⋃ i, Γ.inducedDarts (A i) := by
  refine Set.Subset.antisymm ?_
    (Set.iUnion_subset fun i => inducedDarts_mono (Set.subset_iUnion A i))
  intro e he
  simp only [Set.mem_iUnion, mem_inducedDarts_iff] at he ⊢
  obtain ⟨⟨i, hi⟩, j, hj⟩ := he
  exact (h.tgt_mem_or_src_mem (hA i) (hA j) ⟨x, hx i, hx j⟩ hi hj).elim
    (fun h => ⟨i, hi, h⟩) fun h => ⟨j, h, hj⟩

end SerreGraph
end TauCeti
