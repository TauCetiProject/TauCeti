/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Data.Set.Finite.Lemmas
public import TauCeti.Combinatorics.SimpleGraph.SpanningForest

/-!
# Minimum spanning forests, the cut property and the cycle property

Let `w : Sym2 V → R` be a weight on unordered pairs of vertices, with values in an ordered
commutative monoid. The weight of a graph `F` is the sum of `w` over the edges of `F`
(`SimpleGraph.totalWeight`), and a minimum spanning forest of `G` is a spanning forest of `G` of
least weight among all spanning forests of `G` (`SimpleGraph.IsMinSpanningForest`). Only the values
of `w` on edges of the graphs in question matter. Disconnected graphs are not excluded: on a
connected graph the minimum spanning forests are the spanning trees of least weight.

Every graph on a finite vertex type has a minimum spanning forest. The two classical criteria for
an edge to belong to one are proved here.

* *The cut property.* An edge of least weight among the edges of `G` leaving a set `S` of vertices
  lies in some minimum spanning forest; if it is strictly lighter than every other edge leaving
  `S` and the weights are cancellative, it lies in every minimum spanning forest.
* *The cycle property.* An edge of greatest weight on a cycle of `G` is missing from some minimum
  spanning forest; if it is strictly heavier than every other edge of the cycle and the weights
  are cancellative, it is missing from every minimum spanning forest.

Both rest on exchanging one edge of a minimum spanning forest for another
(`SimpleGraph.IsSpanningForest.exists_cut_exchange`,
`SimpleGraph.IsSpanningForest.exists_cycle_exchange`) and on the change of weight under adding or
deleting a single edge. Cancellation cannot be dropped from the statements about every minimum
spanning forest: with weights in `WithTop ℕ`, take a triangle with weights `1, 2, 3` and a pendant
edge of weight `⊤`. Every spanning tree has weight `⊤`, so all three are minimum, and the one
through the edges of weights `2` and `3` omits the strictly lightest edge leaving one of its ends.

## Main definitions

* `SimpleGraph.totalWeight w F`: the sum of `w` over the edges of `F`.
* `SimpleGraph.IsMinSpanningForest w F G`: `F` is a spanning forest of `G` of least weight.

## Main results

* `SimpleGraph.totalWeight_deleteEdges_add`, `SimpleGraph.totalWeight_sup_edge`: the weight after
  deleting or adding a single edge.
* `SimpleGraph.exists_isMinSpanningForest`: every graph on a finite vertex type has a minimum
  spanning forest.
* `SimpleGraph.exists_isMinSpanningForest_adj_of_cut`, `SimpleGraph.IsMinSpanningForest.adj_of_cut`:
  the cut property.
* `SimpleGraph.exists_isMinSpanningForest_notMem_of_cycle`,
  `SimpleGraph.IsMinSpanningForest.notMem_of_cycle`: the cycle property.

## References

* Jeff Erickson, *Algorithms*, first edition, 2019, Chapter 7, Lemma 7.2, for the cut property on
  connected graphs with distinct real weights.
* Robert E. Tarjan, *Data Structures and Network Algorithms*, SIAM, 1983, Chapter 6, for the cut
  and cycle properties as the blue and red rules.
-/

public section

namespace SimpleGraph

variable {V R : Type*} {F F' G H : SimpleGraph V} {u v : V}

section Weight

variable [AddCommMonoid R] (w : Sym2 V → R)

/-- The weight of a graph `F` for an edge weight `w`: the sum of `w` over the edges of `F`. The sum
is a `finsum`, so it says something only when `F` has finitely many edges, for instance when the
vertex type is finite. -/
noncomputable def totalWeight (F : SimpleGraph V) : R :=
  ∑ᶠ e ∈ F.edgeSet, w e

theorem totalWeight_def (F : SimpleGraph V) : totalWeight w F = ∑ᶠ e ∈ F.edgeSet, w e := (rfl)

/-- The weight of a graph with finitely many edges is the sum of the weights of its edges. -/
theorem totalWeight_eq_sum_edgeFinset (F : SimpleGraph V) [Fintype F.edgeSet] :
    totalWeight w F = ∑ e ∈ F.edgeFinset, w e :=
  finsum_mem_eq_toFinset_sum w F.edgeSet

/-- The graph without edges has weight `0`. -/
@[simp]
theorem totalWeight_bot : totalWeight w (⊥ : SimpleGraph V) = 0 := by
  simp [totalWeight_def]

variable [Finite V]

/-- Deleting an edge `f` of `F` lowers the weight of `F` by `w f`. -/
theorem totalWeight_deleteEdges_add {f : Sym2 V} (hf : f ∈ F.edgeSet) :
    totalWeight w (F.deleteEdges {f}) + w f = totalWeight w F := by
  rw [totalWeight_def, totalWeight_def, edgeSet_deleteEdges, add_comm,
    ← finsum_mem_insert w (s := F.edgeSet \ {f}) (fun h ↦ h.2 rfl) (Set.toFinite _),
    Set.insert_sdiff_singleton, Set.insert_eq_of_mem hf]

/-- Adding the edge `uv` to a graph `H` that does not contain it raises the weight of `H` by
`w s(u, v)`. -/
theorem totalWeight_sup_edge (huv : u ≠ v) (h : ¬H.Adj u v) :
    totalWeight w (H ⊔ edge u v) = totalWeight w H + w s(u, v) := by
  rw [totalWeight_def, totalWeight_def, edgeSet_sup, edgeSet_edge_of_ne huv, Set.union_singleton,
    finsum_mem_insert w ((mem_edgeSet H).not.mpr h) (Set.toFinite _), add_comm]

end Weight

/-- A minimum spanning forest of `G` for the edge weight `w`: a spanning forest of `G` whose weight
is at most the weight of every spanning forest of `G`. On a connected graph these are the spanning
trees of least weight. -/
structure IsMinSpanningForest [AddCommMonoid R] [LE R] (w : Sym2 V → R) (F G : SimpleGraph V) :
    Prop where
  /-- A minimum spanning forest is a spanning forest. -/
  isSpanningForest : F.IsSpanningForest G
  /-- A minimum spanning forest weighs at most as much as every spanning forest. -/
  totalWeight_le ⦃F' : SimpleGraph V⦄ : F'.IsSpanningForest G → totalWeight w F ≤ totalWeight w F'

namespace IsMinSpanningForest

variable [AddCommMonoid R] {w : Sym2 V → R}

/-- Two minimum spanning forests of `G` have the same weight. -/
theorem totalWeight_eq [PartialOrder R] (hF : IsMinSpanningForest w F G)
    (hF' : IsMinSpanningForest w F' G) : totalWeight w F = totalWeight w F' :=
  (hF.totalWeight_le hF'.isSpanningForest).antisymm (hF'.totalWeight_le hF.isSpanningForest)

/-- A spanning forest of `G` weighing at most as much as a minimum spanning forest of `G` is a
minimum spanning forest of `G`. -/
theorem of_totalWeight_le [Preorder R] (hF : IsMinSpanningForest w F G)
    (hF' : F'.IsSpanningForest G) (h : totalWeight w F' ≤ totalWeight w F) :
    IsMinSpanningForest w F' G :=
  ⟨hF', fun _ hF'' ↦ h.trans (hF.totalWeight_le hF'')⟩

end IsMinSpanningForest

/-- Every graph on a finite vertex type has a minimum spanning forest, for weights in a linearly
ordered commutative monoid. -/
theorem exists_isMinSpanningForest [Finite V] [AddCommMonoid R] [LinearOrder R]
    (w : Sym2 V → R) (G : SimpleGraph V) : ∃ F, IsMinSpanningForest w F G := by
  obtain ⟨F, hF, hmin⟩ := Set.exists_min_image {F : SimpleGraph V | F.IsSpanningForest G}
    (totalWeight w) (Set.toFinite _) G.exists_isSpanningForest
  exact ⟨F, hF, fun F' hF' ↦ hmin F' hF'⟩

/-! ### The cut property and the cycle property -/

section Exchange

variable [Finite V] [AddCommMonoid R] {w : Sym2 V → R} {f : Sym2 V}

variable [LinearOrder R]

/-- **The cut property.** If `uv` is an edge of `G` of least weight among the edges of `G` leaving
a set `S` of vertices, some minimum spanning forest of `G` contains `uv`. -/
theorem exists_isMinSpanningForest_adj_of_cut [IsOrderedAddMonoid R] (w : Sym2 V → R)
    {S : Set V} (huv : G.Adj u v) (hu : u ∈ S) (hv : v ∉ S)
    (hmin : ∀ ⦃x y : V⦄, G.Adj x y → x ∈ S → y ∉ S → w s(u, v) ≤ w s(x, y)) :
    ∃ F, IsMinSpanningForest w F G ∧ F.Adj u v := by
  obtain ⟨T, hT⟩ := exists_isMinSpanningForest w G
  by_cases hTuv : T.Adj u v
  · exact ⟨T, hT, hTuv⟩
  -- Exchange an edge `xy` of `T` leaving `S` for `uv`; the weight does not go up.
  obtain ⟨x, y, hxy, hx, hy, hT'⟩ := hT.isSpanningForest.exists_cut_exchange huv hu hv
  have h₁ := totalWeight_sup_edge w huv.ne fun h ↦ hTuv (deleteEdges_le {s(x, y)} h)
  have h₂ := totalWeight_deleteEdges_add w ((mem_edgeSet _).mpr hxy)
  refine ⟨_, hT.of_totalWeight_le hT' ?_, .inr ((edge_adj ..).mpr ⟨.inl ⟨rfl, rfl⟩, huv.ne⟩)⟩
  rw [h₁, ← h₂]
  exact add_le_add_right (hmin (hT.isSpanningForest.le hxy) hx hy) _

/-- **The cycle property.** If `e` is an edge of greatest weight on a cycle `c` of `G`, some
minimum spanning forest of `G` does not contain `e`. -/
theorem exists_isMinSpanningForest_notMem_of_cycle [IsOrderedAddMonoid R] (w : Sym2 V → R)
    {a : V} {c : G.Walk a a} (hc : c.IsCycle) {e : Sym2 V} (he : e ∈ c.edges)
    (hmax : ∀ e' ∈ c.edges, w e' ≤ w e) :
    ∃ F, IsMinSpanningForest w F G ∧ e ∉ F.edgeSet := by
  obtain ⟨T, hT⟩ := exists_isMinSpanningForest w G
  by_cases heT : e ∉ T.edgeSet
  · exact ⟨T, hT, heT⟩
  rw [not_not] at heT
  -- Exchange `e` for an edge `xy` of `c` outside `T`; the weight does not go up.
  obtain ⟨x, y, hxyc, hxy, hT'⟩ := hT.isSpanningForest.exists_cycle_exchange hc he heT
  have h₁ := totalWeight_sup_edge w (c.adj_of_mem_edges hxyc).ne fun h ↦ hxy (deleteEdges_le {e} h)
  have h₂ := totalWeight_deleteEdges_add w heT
  refine ⟨_, hT.of_totalWeight_le hT' ?_, ?_⟩
  · rw [h₁, ← h₂]
    exact add_le_add_right (hmax _ hxyc) _
  · -- `e` is deleted, and it is not `xy`, which is not an edge of `T`.
    rw [edgeSet_sup, edgeSet_deleteEdges, edgeSet_edge_of_ne (c.adj_of_mem_edges hxyc).ne]
    rintro (⟨-, h⟩ | rfl)
    · exact h rfl
    · exact hxy heT

end Exchange

section Cancel

variable [Finite V] [AddCommMonoid R] [PartialOrder R] [IsOrderedCancelAddMonoid R]
  {w : Sym2 V → R}

/-- **The cut property, strict form.** If `uv` is an edge of `G` leaving a set `S` of vertices and
strictly lighter than every other edge of `G` leaving `S`, every minimum spanning forest of `G`
contains `uv`. -/
theorem IsMinSpanningForest.adj_of_cut (hF : IsMinSpanningForest w F G) {S : Set V}
    (huv : G.Adj u v) (hu : u ∈ S) (hv : v ∉ S)
    (hlt : ∀ ⦃x y : V⦄, G.Adj x y → x ∈ S → y ∉ S → s(x, y) ≠ s(u, v) → w s(u, v) < w s(x, y)) :
    F.Adj u v := by
  by_contra hFuv
  -- Exchanging an edge `xy` of `F` leaving `S` for `uv` would give a lighter spanning forest.
  obtain ⟨x, y, hxy, hx, hy, hF'⟩ := hF.isSpanningForest.exists_cut_exchange huv hu hv
  have h₁ := totalWeight_sup_edge w huv.ne fun h ↦ hFuv (deleteEdges_le {s(x, y)} h)
  have h₂ := totalWeight_deleteEdges_add w ((mem_edgeSet _).mpr hxy)
  have hne : s(x, y) ≠ s(u, v) := fun h ↦ hFuv ((mem_edgeSet _).mp (h ▸ (mem_edgeSet _).mpr hxy))
  refine (hF.totalWeight_le hF').not_gt ?_
  rw [h₁, ← h₂]
  exact add_lt_add_right (hlt (hF.isSpanningForest.le hxy) hx hy hne) _

/-- **The cycle property, strict form.** If `e` is an edge of a cycle `c` of `G` strictly heavier
than every other edge of `c`, no minimum spanning forest of `G` contains `e`. -/
theorem IsMinSpanningForest.notMem_of_cycle (hF : IsMinSpanningForest w F G) {a : V}
    {c : G.Walk a a} (hc : c.IsCycle) {e : Sym2 V} (he : e ∈ c.edges)
    (hlt : ∀ e' ∈ c.edges, e' ≠ e → w e' < w e) : e ∉ F.edgeSet := by
  intro heF
  -- Exchanging `e` for an edge `xy` of `c` outside `F` would give a lighter spanning forest.
  obtain ⟨x, y, hxyc, hxy, hF'⟩ := hF.isSpanningForest.exists_cycle_exchange hc he heF
  have h₁ := totalWeight_sup_edge w (c.adj_of_mem_edges hxyc).ne fun h ↦ hxy (deleteEdges_le {e} h)
  have h₂ := totalWeight_deleteEdges_add w heF
  have hne : s(x, y) ≠ e := fun h ↦ hxy ((mem_edgeSet _).mp (h ▸ heF))
  refine (hF.totalWeight_le hF').not_gt ?_
  rw [h₁, ← h₂]
  exact add_lt_add_right (hlt _ hxyc hne) _

end Cancel

end SimpleGraph
