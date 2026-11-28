/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Chordal.Separator

import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Simplicial vertices of chordal graphs

A vertex of a simple graph is *simplicial* (`SimpleGraph.IsSimplicial`) when its neighbours are
pairwise adjacent, that is, when its neighbourhood is a clique. Every vertex of a complete graph is
simplicial, and so is every vertex with at most one neighbour.

The main result is Dirac's theorem that a finite chordal graph which is not complete has two
nonadjacent simplicial vertices (`SimpleGraph.IsChordal.exists_isSimplicial_not_adj`). In
particular every chordal graph on a finite nonempty vertex type has a simplicial vertex; removing
such vertices one at a time is what produces perfect elimination orderings of chordal graphs.
Finiteness is needed: the two-way infinite path on `ℤ` is chordal, not complete, and has no
simplicial vertex.

The proof is by induction on the number of vertices (Vandenberghe–Andersen, proof of
Theorem 3.3). Given two nonadjacent vertices `a` and `b`, take a minimal `a`–`b` separator `S`,
which is a clique by Dirac's separator theorem, and let `A` be the set of vertices reachable from
`a` once `S` is deleted. The graph induced on `A ∪ S` is chordal and misses `b`, so it is complete
or, by induction, has two nonadjacent simplicial vertices. As `S` is a clique, in either case some
vertex of `A` is simplicial in the induced graph, and since every neighbour of a vertex of `A` lies
in `A ∪ S`, it is simplicial in `G`. The same argument on the side of `b` gives a second simplicial
vertex, which is neither equal nor adjacent to the first because `S` separates them.

## Main definitions

* `SimpleGraph.IsSimplicial G v`: the neighbours of `v` form a clique in `G`.

## Main results

* `SimpleGraph.IsSimplicial.of_embedding`, `SimpleGraph.Iso.isSimplicial_iff`,
  `SimpleGraph.IsSimplicial.induce`: simpliciality is reflected by graph embeddings, invariant under
  isomorphisms, and passes to induced subgraphs.
* `SimpleGraph.isSimplicial_induce_iff`: a vertex of `s` whose neighbours all lie in `s` is
  simplicial in `G` exactly when it is simplicial in the subgraph induced on `s`.
* `SimpleGraph.IsChordal.exists_isSimplicial_not_adj`: **Dirac's theorem**, a finite chordal graph
  that is not complete has two distinct nonadjacent simplicial vertices.
* `SimpleGraph.IsChordal.exists_isSimplicial`: a chordal graph on a finite nonempty vertex type has
  a simplicial vertex.

## References

* G. A. Dirac, *On rigid circuit graphs*, Abh. Math. Sem. Univ. Hamburg 25 (1961).
* L. Vandenberghe and M. S. Andersen, *Chordal Graphs and Semidefinite Optimization*, Foundations
  and Trends in Optimization 1 (4), 2014, Section 3.4, Theorem 3.3.
-/

public section

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {s : Set V} {v : V}

/-- A vertex is *simplicial* when its neighbours are pairwise adjacent, that is, when its
neighbourhood is a clique. -/
def IsSimplicial (G : SimpleGraph V) (v : V) : Prop :=
  G.IsClique (G.neighborSet v)

theorem isSimplicial_def : G.IsSimplicial v ↔ G.IsClique (G.neighborSet v) :=
  Iff.rfl

/-- A vertex is simplicial exactly when any two distinct neighbours of it are adjacent. -/
theorem isSimplicial_iff :
    G.IsSimplicial v ↔ ∀ ⦃x⦄, G.Adj v x → ∀ ⦃y⦄, G.Adj v y → x ≠ y → G.Adj x y := by
  simp [isSimplicial_def, IsClique, Set.Pairwise]

/-- Two distinct neighbours of a simplicial vertex are adjacent. -/
theorem IsSimplicial.adj (h : G.IsSimplicial v) {x y : V} (hx : G.Adj v x) (hy : G.Adj v y)
    (hxy : x ≠ y) : G.Adj x y :=
  isSimplicial_iff.1 h hx hy hxy

/-- A vertex is simplicial exactly when it forms a clique together with its neighbours. -/
theorem isSimplicial_iff_isClique_insert :
    G.IsSimplicial v ↔ G.IsClique (insert v (G.neighborSet v)) := by
  simp +contextual [isSimplicial_def]

/-- Every vertex of a complete graph is simplicial. -/
@[simp]
theorem isSimplicial_top : (⊤ : SimpleGraph V).IsSimplicial v :=
  IsClique.top _

/-- A vertex with at most one neighbour is simplicial. -/
theorem IsSimplicial.of_subsingleton (h : (G.neighborSet v).Subsingleton) : G.IsSimplicial v :=
  IsClique.of_subsingleton h

/-- Simpliciality is reflected by graph embeddings: if the image of `v` under an embedding is
simplicial, then so is `v`. -/
theorem IsSimplicial.of_embedding (f : G ↪g H) (h : H.IsSimplicial (f v)) : G.IsSimplicial v :=
  isSimplicial_iff.2 fun _ hx _ hy hxy ↦
    f.map_adj_iff.1 (h.adj (f.map_adj_iff.2 hx) (f.map_adj_iff.2 hy) (f.injective.ne hxy))

/-- Simpliciality is invariant under graph isomorphism. -/
theorem Iso.isSimplicial_iff (e : G ≃g H) : G.IsSimplicial v ↔ H.IsSimplicial (e v) :=
  ⟨fun h ↦ .of_embedding e.symm.toEmbedding (by simpa using h),
    .of_embedding e.toEmbedding⟩

/-- A simplicial vertex stays simplicial in every induced subgraph containing it. -/
theorem IsSimplicial.induce (h : G.IsSimplicial v) (hv : v ∈ s) :
    (G.induce s).IsSimplicial ⟨v, hv⟩ :=
  .of_embedding (Embedding.induce s) h

/-- A vertex of `s` all of whose neighbours lie in `s` is simplicial exactly when it is simplicial
in the subgraph induced on `s`. -/
theorem isSimplicial_induce_iff (hv : v ∈ s) (hs : G.neighborSet v ⊆ s) :
    (G.induce s).IsSimplicial ⟨v, hv⟩ ↔ G.IsSimplicial v := by
  refine ⟨fun h ↦ isSimplicial_iff.2 fun x hx y hy hxy ↦ ?_, fun h ↦ h.induce hv⟩
  have hxs : x ∈ s := hs ((G.mem_neighborSet v x).2 hx)
  have hys : y ∈ s := hs ((G.mem_neighborSet v y).2 hy)
  exact induce_adj.1 (h.adj (x := ⟨x, hxs⟩) (y := ⟨y, hys⟩) (induce_adj.2 hx) (induce_adj.2 hy)
    (Subtype.coe_ne_coe.1 hxy))

/-- Let `S` be a clique and `A` a set of vertices containing `a` such that every neighbour of a
vertex of `A` lies in `A ∪ S`. If the subgraph induced on `A ∪ S` is complete or has two
nonadjacent simplicial vertices, then some vertex of `A` is simplicial in `G`. -/
private theorem exists_mem_isSimplicial_of_induce {A S : Set V} {a : V} (ha : a ∈ A)
    (hS : G.IsClique S) (hA : ∀ v ∈ A, G.neighborSet v ⊆ A ∪ S)
    (h : G.induce (A ∪ S) = ⊤ ∨ ∃ u w, u ≠ w ∧ ¬(G.induce (A ∪ S)).Adj u w ∧
      (G.induce (A ∪ S)).IsSimplicial u ∧ (G.induce (A ∪ S)).IsSimplicial w) :
    ∃ u ∈ A, G.IsSimplicial u := by
  rcases h with h | ⟨⟨u, hu⟩, ⟨w, hw⟩, huw, hadj, hsu, hsw⟩
  · exact ⟨a, ha, (isSimplicial_induce_iff (Set.mem_union_left S ha) (hA a ha)).1
      (h ▸ isSimplicial_top)⟩
  -- the two vertices are nonadjacent, so they do not both lie in the clique `S`
  by_cases huA : u ∈ A
  · exact ⟨u, huA, (isSimplicial_induce_iff hu (hA u huA)).1 hsu⟩
  by_cases hwA : w ∈ A
  · exact ⟨w, hwA, (isSimplicial_induce_iff hw (hA w hwA)).1 hsw⟩
  have huS : u ∈ S := (Set.mem_union u A S).1 hu |>.resolve_left huA
  have hwS : w ∈ S := (Set.mem_union w A S).1 hw |>.resolve_left hwA
  exact absurd (induce_adj.2 (hS huS hwS (Subtype.coe_ne_coe.2 huw))) hadj

/-- **Dirac's simplicial vertex theorem.** A finite chordal graph that is not complete has two
distinct nonadjacent simplicial vertices. -/
theorem IsChordal.exists_isSimplicial_not_adj [Finite V] (hG : G.IsChordal) (hG' : G ≠ ⊤) :
    ∃ u v, u ≠ v ∧ ¬G.Adj u v ∧ G.IsSimplicial u ∧ G.IsSimplicial v := by
  induction hn : Nat.card V using Nat.strong_induction_on generalizing V with
  | _ n ih =>
  obtain ⟨a, b, hab, hnadj⟩ := ne_top_iff_exists_not_adj.1 hG'
  obtain ⟨S, -, hS⟩ := exists_isMinimalSeparator_subset_neighborSet hab hnadj
  have hSc := hG.isClique_of_isMinimalSeparator hS
  -- on the side of each of the two separated vertices there is a vertex simplicial in `G`
  have key {a b : V} (hsep : G.IsSeparator a b S) : ∃ (u : V) (hu : u ∉ S),
      (G.induce Sᶜ).Reachable ⟨a, hsep.left_notMem⟩ ⟨u, hu⟩ ∧ G.IsSimplicial u := by
    let A : Set V := {v | ∃ hv : v ∉ S, (G.induce Sᶜ).Reachable ⟨a, hsep.left_notMem⟩ ⟨v, hv⟩}
    have hbA : b ∉ A ∪ S := by
      rintro (⟨_, hr⟩ | hbS)
      exacts [hsep.not_reachable hr, hsep.right_notMem hbS]
    -- a neighbour of a vertex of `A` lies in `S` or is again reachable from `a`
    have hA : ∀ v ∈ A, G.neighborSet v ⊆ A ∪ S := by
      rintro v ⟨hv, hr⟩ w hw
      by_cases hwS : w ∈ S
      · exact Set.mem_union_right A hwS
      · exact Set.mem_union_left S
          ⟨hwS, hr.trans (induce_adj.2 ((G.mem_neighborSet v w).1 hw)).reachable⟩
    -- the graph induced on `A ∪ S` misses `b`, so the induction hypothesis applies to it
    have hind : G.induce (A ∪ S) = ⊤ ∨ ∃ u w, u ≠ w ∧ ¬(G.induce (A ∪ S)).Adj u w ∧
        (G.induce (A ∪ S)).IsSimplicial u ∧ (G.induce (A ∪ S)).IsSimplicial w := by
      by_cases htop : G.induce (A ∪ S) = ⊤
      · exact .inl htop
      · exact .inr (ih _ (hn ▸ Finite.card_subtype_lt hbA) (hG.induce _) htop rfl)
    obtain ⟨u, ⟨hu, hr⟩, hsu⟩ :=
      exists_mem_isSimplicial_of_induce (A := A) ⟨hsep.left_notMem, .rfl⟩ hSc hA hind
    exact ⟨u, hu, hr, hsu⟩
  obtain ⟨u, hu, hau, hsu⟩ := key hS.isSeparator
  obtain ⟨w, hw, hbw, hsw⟩ := key hS.isSeparator.symm
  refine ⟨u, w, ?_, hS.isSeparator.not_adj_of_reachable hu hw hau hbw, hsu, hsw⟩
  rintro rfl
  exact hS.isSeparator.not_reachable_of_reachable hu hau hbw

/-- A chordal graph on a finite nonempty vertex type has a simplicial vertex. -/
theorem IsChordal.exists_isSimplicial [Finite V] [Nonempty V] (hG : G.IsChordal) :
    ∃ v, G.IsSimplicial v := by
  by_cases h : G = ⊤
  · exact ⟨Classical.arbitrary V, h ▸ isSimplicial_top⟩
  · obtain ⟨u, -, -, -, hu, -⟩ := hG.exists_isSimplicial_not_adj h
    exact ⟨u, hu⟩

end SimpleGraph
