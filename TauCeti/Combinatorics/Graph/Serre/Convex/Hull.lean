/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Aut
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Set.Finite.List

/-!
# Convex hulls of sets of vertices

The convex hull of a set of vertices of a Serre graph is the smallest convex set containing it.
In a tree, where the nonempty convex sets are the vertex sets of the subtrees, it is the subtree
spanned by the set. The hull `Γ.convexHull {a, b}` of two vertices of a tree is the geodesic
segment `[a, b]`: the set of vertices of the reduced path from `a` to `b`.

Hulls in a tree are computed from segments through a base vertex: the hull of `{x} ∪ S` is the
union of `{x}` and the segments `[x, s]` for `s ∈ S`, because subtrees through a common vertex
glue to a subtree. In particular `[a, c] ⊆ [a, b] ∪ [b, c]`, and the hull of a finite set is
finite. Automorphisms commute with convex hulls.

## Main declarations

* `TauCeti.SerreGraph.convexHull`: the convex hull of a set of vertices.
* `TauCeti.SerreGraph.IsTree.convexHull_pair`: in a tree, the hull of two vertices is the set of
  vertices of the reduced path joining them.
* `TauCeti.SerreGraph.IsTree.convexHull_insert`: in a tree, the hull of `{x} ∪ S` is the union of
  `{x}` and the segments from `x` to the vertices of `S`.
* `TauCeti.SerreGraph.IsTree.finite_convexHull`: in a tree, the hull of a finite set is finite.
* `TauCeti.SerreGraph.Aut.convexHull_smul_set`: automorphisms commute with convex hulls.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.2 and §6.1.
-/

public section

namespace TauCeti
namespace SerreGraph

variable (Γ : SerreGraph)

/-- The convex hull of a set of vertices: the intersection of the convex sets containing it. -/
def convexHull (S : Set Γ.V) : Set Γ.V :=
  ⋂₀ {C | Γ.IsConvex C ∧ S ⊆ C}

variable {Γ} {S C : Set Γ.V}

theorem mem_convexHull_iff {v : Γ.V} :
    v ∈ Γ.convexHull S ↔ ∀ C : Set Γ.V, Γ.IsConvex C → S ⊆ C → v ∈ C := by
  simp only [convexHull, Set.mem_sInter, Set.mem_ofPred_eq, and_imp]

variable (S) in
theorem subset_convexHull : S ⊆ Γ.convexHull S :=
  fun _ hv => mem_convexHull_iff.mpr fun _ _ hSC => hSC hv

variable (S) in
/-- The convex hull of a set is convex. -/
theorem isConvex_convexHull : Γ.IsConvex (Γ.convexHull S) :=
  isConvex_sInter fun _ hC => hC.1

/-- The convex hull of a set is contained in every convex set containing it. -/
theorem IsConvex.convexHull_subset (hC : Γ.IsConvex C) (hSC : S ⊆ C) : Γ.convexHull S ⊆ C :=
  fun _ hv => mem_convexHull_iff.mp hv C hC hSC

theorem IsConvex.convexHull_subset_iff (hC : Γ.IsConvex C) : Γ.convexHull S ⊆ C ↔ S ⊆ C :=
  ⟨(subset_convexHull S).trans, hC.convexHull_subset⟩

/-- A convex set is its own convex hull. -/
theorem IsConvex.convexHull_eq (hC : Γ.IsConvex C) : Γ.convexHull C = C :=
  (hC.convexHull_subset subset_rfl).antisymm (subset_convexHull C)

theorem convexHull_mono {S T : Set Γ.V} (h : S ⊆ T) : Γ.convexHull S ⊆ Γ.convexHull T :=
  (isConvex_convexHull T).convexHull_subset (h.trans (subset_convexHull T))

@[simp] theorem convexHull_convexHull (S : Set Γ.V) :
    Γ.convexHull (Γ.convexHull S) = Γ.convexHull S :=
  (isConvex_convexHull S).convexHull_eq

@[simp] theorem convexHull_empty : Γ.convexHull ∅ = ∅ :=
  isConvex_empty.convexHull_eq

@[simp] theorem convexHull_univ : Γ.convexHull Set.univ = Set.univ :=
  isConvex_univ.convexHull_eq

/-- In an acyclic graph, the convex hull of a vertex is that vertex. -/
@[simp] theorem IsAcyclic.convexHull_singleton (h : Γ.IsAcyclic) (v : Γ.V) :
    Γ.convexHull {v} = {v} :=
  (h.isConvex_singleton v).convexHull_eq

@[simp] theorem left_mem_convexHull_pair (a b : Γ.V) : a ∈ Γ.convexHull {a, b} :=
  subset_convexHull _ (Set.mem_insert a _)

@[simp] theorem right_mem_convexHull_pair (a b : Γ.V) : b ∈ Γ.convexHull {a, b} :=
  subset_convexHull _ (Set.mem_insert_of_mem a rfl)

/-! ### Convex hulls in a tree -/

/-- In a tree, the convex hull of `{x} ∪ S` is the union of `{x}` and the segments from `x` to the
vertices of `S`. -/
theorem IsTree.convexHull_insert (h : Γ.IsTree) (x : Γ.V) (S : Set Γ.V) :
    Γ.convexHull (insert x S) = insert x (⋃ s ∈ S, Γ.convexHull {x, s}) := by
  -- The right-hand side is the union of the segments from `x` to the vertices of `{x} ∪ S`.
  have hconv : Γ.IsConvex (insert x (⋃ s ∈ S, Γ.convexHull {x, s})) := by
    have hU : insert x (⋃ s ∈ S, Γ.convexHull {x, s}) =
        ⋃ s : ↥(insert x S), Γ.convexHull {x, s.1} := by
      rw [← Set.biUnion_eq_iUnion (s := insert x S) (t := fun s _ => Γ.convexHull {x, s}),
        Set.biUnion_insert, Set.pair_eq_singleton, h.isAcyclic.convexHull_singleton,
        Set.singleton_union]
    rw [hU]
    exact h.isConvex_iUnion (x := x) (fun _ => isConvex_convexHull _)
      fun s => left_mem_convexHull_pair x s.1
  refine (hconv.convexHull_subset ?_).antisymm ?_
  · rintro s (rfl | hs)
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_biUnion hs (right_mem_convexHull_pair x s))
  · refine Set.insert_subset (subset_convexHull _ (Set.mem_insert x S))
      (Set.iUnion₂_subset fun s hs => convexHull_mono ?_)
    exact Set.insert_subset_insert (Set.singleton_subset_iff.mpr hs)

/-- In a tree, the segment from `a` to `c` is contained in the union of the segments from `a` to
`b` and from `b` to `c`. -/
theorem IsTree.convexHull_pair_subset_union (h : Γ.IsTree) (a b c : Γ.V) :
    Γ.convexHull {a, c} ⊆ Γ.convexHull {a, b} ∪ Γ.convexHull {b, c} :=
  (h.isConvex_union (isConvex_convexHull _) (isConvex_convexHull _)
    ⟨b, right_mem_convexHull_pair a b, left_mem_convexHull_pair b c⟩).convexHull_subset
      (Set.pair_subset (Or.inl (left_mem_convexHull_pair a b))
        (Or.inr (right_mem_convexHull_pair b c)))

/-- In a tree, the convex hull of two vertices is the set of vertices of the reduced path joining
them. -/
theorem IsTree.convexHull_pair (h : Γ.IsTree) {a b : Γ.V} {p : Γ.Path a b}
    (hp : Path.IsReduced Γ p) : Γ.convexHull {a, b} = {v | v ∈ p.vertices} := by
  refine ((h.isConvex_setOf_mem_vertices p).convexHull_subset
    (Set.pair_subset p.start_mem_vertices p.end_mem_vertices)).antisymm fun v hv => ?_
  rcases Path.eq_or_exists_tgt_eq_of_mem_vertices Γ p hv with rfl | ⟨e, he, rfl⟩
  · exact left_mem_convexHull_pair v b
  · exact (isConvex_convexHull _).tgt_mem (left_mem_convexHull_pair a b)
      (right_mem_convexHull_pair a b) hp he

/-- In a tree, the convex hull of a finite set of vertices is finite. -/
theorem IsTree.finite_convexHull (h : Γ.IsTree) (hS : S.Finite) : (Γ.convexHull S).Finite := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  rw [← Set.insert_eq_of_mem hx, h.convexHull_insert]
  refine (hS.biUnion fun s _ => ?_).insert x
  obtain ⟨p, hp, -⟩ := h.existsUnique_isReduced x s
  rw [h.convexHull_pair hp]
  exact p.vertices.finite_toSet

/-! ### Automorphisms -/

open scoped Pointwise in
/-- Automorphisms commute with convex hulls. -/
theorem Aut.convexHull_smul_set (φ : Γ.Aut) (S : Set Γ.V) :
    Γ.convexHull (φ • S) = φ • Γ.convexHull S := by
  refine ((φ.isConvex_smul_set_iff.mpr (isConvex_convexHull S)).convexHull_subset
    (Set.smul_set_mono (subset_convexHull S))).antisymm ?_
  rw [Set.smul_set_subset_iff_subset_inv_smul_set]
  exact (φ⁻¹.isConvex_smul_set_iff.mpr (isConvex_convexHull _)).convexHull_subset
    (by rw [← Set.smul_set_subset_iff_subset_inv_smul_set]; exact subset_convexHull _)

end SerreGraph
end TauCeti
