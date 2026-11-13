/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Aut
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Set.Finite.List
public import Mathlib.Order.Closure

/-!
# Convex hulls of sets of vertices

The convex hull of a set of vertices of a Serre graph is the smallest convex set containing it;
it is a closure operator, whose closed sets are the convex sets, and each of its vertices is
joined to the set by a path. In a tree, where the nonempty convex sets are the vertex sets of the
subtrees, it is the subtree spanned by the set. The hull `Γ.convexHull {a, b}` of two vertices
of an acyclic graph joined by a path is the geodesic segment `[a, b]`: the set of vertices of the
reduced path from `a` to `b`. In an acyclic graph the hull of a set is the union of the hulls of
its pairs of vertices, so the hull of a finite set is finite.

Hulls in a tree are computed from segments through a base vertex: the hull of `{x} ∪ S` is the
union of `{x}` and the segments `[x, s]` for `s ∈ S`, because subtrees through a common vertex
glue to a subtree. In particular `[a, c] ⊆ [a, b] ∪ [b, c]`. Automorphisms commute with convex
hulls.

## Main declarations

* `TauCeti.SerreGraph.convexHull`: the convex hull of a set of vertices, as a closure operator.
* `TauCeti.SerreGraph.IsAcyclic.convexHull_pair`: in an acyclic graph, the hull of two vertices is
  the set of vertices of a reduced path joining them.
* `TauCeti.SerreGraph.IsAcyclic.convexHull_eq_biUnion_convexHull_pair`: in an acyclic graph, the
  hull of a set is the union of the hulls of its pairs of vertices.
* `TauCeti.SerreGraph.IsAcyclic.finite_convexHull`: in an acyclic graph, the hull of a finite set
  is finite.
* `TauCeti.SerreGraph.IsTree.convexHull_insert`: in a tree, the hull of `{x} ∪ S` is the union of
  `{x}` and the segments from `x` to the vertices of `S`.
* `TauCeti.SerreGraph.Aut.convexHull_smul_set`: automorphisms commute with convex hulls.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.2 and §6.1.
-/

public section

namespace TauCeti
namespace SerreGraph

variable (Γ : SerreGraph)

/-- The convex hull of a set of vertices: the smallest convex set containing it. It is the
closure operator whose closed sets are the convex sets. -/
def convexHull : ClosureOperator (Set Γ.V) :=
  .ofCompletePred Γ.IsConvex fun _ => isConvex_sInter

/-- The sets closed under the convex hull are the convex sets. -/
@[simp] theorem convexHull_isClosed (S : Set Γ.V) : Γ.convexHull.IsClosed S ↔ Γ.IsConvex S :=
  Iff.rfl

variable {Γ} {S C : Set Γ.V}

variable (S) in
theorem subset_convexHull : S ⊆ Γ.convexHull S :=
  Γ.convexHull.le_closure S

variable (S) in
/-- The convex hull of a set is convex. -/
theorem isConvex_convexHull : Γ.IsConvex (Γ.convexHull S) :=
  (Γ.convexHull_isClosed _).mp (Γ.convexHull.isClosed_closure S)

/-- The convex hull of a set is contained in every convex set containing it. -/
theorem IsConvex.convexHull_subset (hC : Γ.IsConvex C) (hSC : S ⊆ C) : Γ.convexHull S ⊆ C :=
  Γ.convexHull.closure_min hSC ((Γ.convexHull_isClosed C).mpr hC)

theorem mem_convexHull_iff {v : Γ.V} :
    v ∈ Γ.convexHull S ↔ ∀ C : Set Γ.V, Γ.IsConvex C → S ⊆ C → v ∈ C :=
  ⟨fun hv _ hC hSC => hC.convexHull_subset hSC hv,
    fun h => h _ (isConvex_convexHull S) (subset_convexHull S)⟩

theorem IsConvex.convexHull_subset_iff (hC : Γ.IsConvex C) : Γ.convexHull S ⊆ C ↔ S ⊆ C :=
  ((Γ.convexHull_isClosed C).mpr hC).closure_le_iff

/-- A convex set is its own convex hull. -/
theorem IsConvex.convexHull_eq (hC : Γ.IsConvex C) : Γ.convexHull C = C :=
  ((Γ.convexHull_isClosed C).mpr hC).closure_eq

theorem convexHull_mono {S T : Set Γ.V} (h : S ⊆ T) : Γ.convexHull S ⊆ Γ.convexHull T :=
  Γ.convexHull.monotone h

@[simp] theorem convexHull_empty : Γ.convexHull ∅ = ∅ :=
  isConvex_empty.convexHull_eq

@[simp] theorem convexHull_univ : Γ.convexHull Set.univ = Set.univ :=
  Γ.convexHull.closure_top

/-- In an acyclic graph, the convex hull of a vertex is that vertex. -/
@[simp] theorem IsAcyclic.convexHull_singleton (h : Γ.IsAcyclic) (v : Γ.V) :
    Γ.convexHull {v} = {v} :=
  (h.isConvex_singleton v).convexHull_eq

@[simp] theorem left_mem_convexHull_pair (a b : Γ.V) : a ∈ Γ.convexHull {a, b} :=
  subset_convexHull _ (Set.mem_insert a _)

@[simp] theorem right_mem_convexHull_pair (a b : Γ.V) : b ∈ Γ.convexHull {a, b} :=
  subset_convexHull _ (Set.mem_insert_of_mem a rfl)

/-- Every vertex of the convex hull of a set is joined to the set by a path. -/
theorem exists_path_of_mem_convexHull {v : Γ.V} (hv : v ∈ Γ.convexHull S) :
    ∃ s ∈ S, Nonempty (Γ.Path s v) := by
  -- The vertices joined to `S` by a path form a convex set.
  refine (?_ : Γ.IsConvex {v | ∃ s ∈ S, Nonempty (Γ.Path s v)}).convexHull_subset
    (fun s hs => ⟨s, hs, ⟨.nil⟩⟩) hv
  refine isConvex_iff.mpr ?_
  rintro a ⟨s, hs, ⟨q⟩⟩ b - p - e he
  obtain ⟨p₁, -, -⟩ := Path.exists_eq_cons_comp_of_mem_darts Γ p he
  exact ⟨s, hs, ⟨q.comp p₁⟩⟩

/-! ### Convex hulls in an acyclic graph -/

/-- In an acyclic graph, the convex hull of two vertices is the set of vertices of a reduced path
joining them. -/
theorem IsAcyclic.convexHull_pair (h : Γ.IsAcyclic) {a b : Γ.V} {p : Γ.Path a b}
    (hp : Path.IsReduced Γ p) : Γ.convexHull {a, b} = {v | v ∈ p.vertices} := by
  refine ((h.isConvex_setOf_mem_vertices p).convexHull_subset
    (Set.pair_subset p.start_mem_vertices p.end_mem_vertices)).antisymm fun v hv => ?_
  rcases Path.eq_or_exists_tgt_eq_of_mem_vertices Γ p hv with rfl | ⟨e, he, rfl⟩
  · exact left_mem_convexHull_pair v b
  · exact (isConvex_convexHull _).tgt_mem (left_mem_convexHull_pair a b)
      (right_mem_convexHull_pair a b) hp he

/-- In an acyclic graph, the convex hull of two vertices is finite. -/
theorem IsAcyclic.finite_convexHull_pair (h : Γ.IsAcyclic) (a b : Γ.V) :
    (Γ.convexHull {a, b}).Finite := by
  rcases isEmpty_or_nonempty (Γ.Path a b) with hab | ⟨⟨p⟩⟩
  · -- Two vertices that are not joined by a path form a convex set.
    rw [(h.isConvex_of_pairwise (Set.pairwise_pair.mpr fun _ =>
      ⟨hab, ⟨fun p => hab.elim p.reverse⟩⟩)).convexHull_eq]
    exact Set.toFinite _
  · rw [h.convexHull_pair (Path.isReduced_reduce Γ p)]
    exact (Path.reduce Γ p).vertices.finite_toSet

/-- In an acyclic graph, the convex hull of a set is the union of the convex hulls of the pairs of
its vertices. -/
theorem IsAcyclic.convexHull_eq_biUnion_convexHull_pair (h : Γ.IsAcyclic) (S : Set Γ.V) :
    Γ.convexHull S = ⋃ a ∈ S, ⋃ b ∈ S, Γ.convexHull {a, b} := by
  -- Every vertex of the union lies in the hull of a pair `{a, b}` and is joined to `a` by a path.
  have reach : ∀ u ∈ ⋃ a ∈ S, ⋃ b ∈ S, Γ.convexHull {a, b},
      ∃ a ∈ S, ∃ b ∈ S, u ∈ Γ.convexHull {a, b} ∧ Nonempty (Γ.Path a u) := by
    simp only [Set.mem_iUnion]
    rintro u ⟨a, ha, b, hb, hu⟩
    obtain ⟨s, rfl | rfl, hs⟩ := exists_path_of_mem_convexHull hu
    · exact ⟨s, ha, b, hb, hu, hs⟩
    · exact ⟨s, hb, a, ha, Set.pair_comm a s ▸ hu, hs⟩
  refine ((?_ : Γ.IsConvex _).convexHull_subset fun a ha => Set.mem_biUnion ha
    (Set.mem_biUnion ha (left_mem_convexHull_pair a a))).antisymm
    (Set.iUnion₂_subset fun a ha => Set.iUnion₂_subset fun b hb =>
      convexHull_mono (Set.pair_subset ha hb))
  refine isConvex_iff.mpr fun u hu v hv r hr e he => ?_
  obtain ⟨a, ha, b, hb, hu, ⟨qa⟩⟩ := reach u hu
  obtain ⟨c, hc, d, hd, hv, ⟨qc⟩⟩ := reach v hv
  -- The reduced path `r` only crosses darts of the reduced paths from `u` to `a`, from `a` to
  -- `c` and from `c` to `v`, which lie in the hulls of `{a, b}`, `{a, c}` and `{c, d}`.
  have he' := (h.darts_sublist hr ((Path.reduce Γ qa.reverse).comp
    ((Path.reduce Γ (qa.comp (r.comp qc.reverse))).comp (Path.reduce Γ qc)))).subset he
  simp only [Path.darts_comp, List.mem_append] at he'
  rcases he' with he' | he' | he'
  · exact Set.mem_biUnion ha (Set.mem_biUnion hb (isConvex_iff.mp (isConvex_convexHull _) u hu a
      (left_mem_convexHull_pair a b) _ (Path.isReduced_reduce Γ _) e he'))
  · exact Set.mem_biUnion ha (Set.mem_biUnion hc (isConvex_iff.mp (isConvex_convexHull _) a
      (left_mem_convexHull_pair a c) c (right_mem_convexHull_pair a c) _
      (Path.isReduced_reduce Γ _) e he'))
  · exact Set.mem_biUnion hc (Set.mem_biUnion hd (isConvex_iff.mp (isConvex_convexHull _) c
      (left_mem_convexHull_pair c d) v hv _ (Path.isReduced_reduce Γ _) e he'))

/-- In an acyclic graph, the convex hull of a finite set of vertices is finite. -/
theorem IsAcyclic.finite_convexHull (h : Γ.IsAcyclic) (hS : S.Finite) :
    (Γ.convexHull S).Finite := by
  rw [h.convexHull_eq_biUnion_convexHull_pair]
  exact hS.biUnion fun a _ => hS.biUnion fun b _ => h.finite_convexHull_pair a b

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
