/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Matching.Capacitated

/-!
# The capacitated Kőnig–Ore formula and Hall's theorem

Let `G : Graph α β` be a multigraph with finitely many actual edges and a bipartition `L, R`, and
let `b v : ℕ` be a capacity on every actual vertex. For a set `S` of actual vertices, `N(S)` is the
set of vertices of `R` joined by an edge to a vertex of `S`; parallel edges contribute a neighbour
only once. Write `b(S)` for `∑ v ∈ S, b v`.

This file proves the capacitated Kőnig–Ore formula in witness form: some multiset capacitated
matching `x` and some `S ⊆ L` satisfy `∑ e, x e + b(S) = b(L) + b(N(S))`, while every multiset
capacitated matching `x` and every `S ⊆ L` satisfy `∑ e, x e + b(S) ≤ b(L) + b(N(S))`. The largest
size of a multiset capacitated matching is therefore `b(L) - max_{S ⊆ L} (b(S) - b(N(S)))`, with
truncated subtraction. Specializations are:

* **capacitated Hall**: some multiset capacitated matching saturates every vertex of `L`, that is,
  uses `v` exactly `b v` times for every `v ∈ L`, if and only if `b(S) ≤ b(N(S))` for every
  `S ⊆ L`;
* some multiset capacitated matching saturates every actual vertex if and only if moreover
  `b(L) = b(R)`.

Since `IsBipartition` is symmetric in its two sides, applying these results to the exchanged
bipartition `Graph.IsBipartition.symm` gives the versions saturating `R`. At `b = 1` a multiset
capacitated matching is an ordinary matching, and these become the Kőnig–Ore deficiency formula
`|M| + |S| = |L| + |N(S)|` and Hall's marriage theorem.

## Main results

* `Graph.IsCapacitatedMatching.sum_add_sum_le`: the capacitated Kőnig–Ore inequality.
* `Graph.IsBipartition.exists_isCapacitatedMatching_sum_add_sum_eq`: the capacitated Kőnig–Ore
  formula in witness form.
* `Graph.IsBipartition.isGreatest_sum_isCapacitatedMatching`: the largest size of a multiset
  capacitated matching.
* `Graph.IsBipartition.exists_isCapacitatedMatching_saturating_left_iff`: **Hall's theorem** for
  multiset capacitated matchings.
* `Graph.IsBipartition.exists_isCapacitatedMatching_saturating_iff`: the condition for a multiset
  capacitated matching saturating every actual vertex.

## Implementation notes

The formula follows from Kőnig's theorem
`Graph.IsBipartition.exists_isCapacitatedMatching_isVertexCover_sum_eq`. For `S ⊆ L`, the set
`(L ∖ S) ∪ N(S)` is a vertex cover of weight `b(L) - b(S) + b(N(S))`, which gives the inequality.
Conversely, for a vertex cover `C` of least weight, the set `S = L ∖ C` has all its neighbours in
`C ∩ R`, so `b(L) - b(S) + b(N(S)) ≤ b(C ∩ L) + b(C ∩ R) = b(C)`.

## References

* P. Hall, *On representatives of subsets*, J. London Math. Soc. 10 (1935).
* Ø. Ore, *Graphs and matching theorems*, Duke Math. J. 22 (1955).
* A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Springer, 2003,
  Chapters 16 and 21.
-/

public section

open Finset
open scoped Graph

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β}

/-! ### The capacitated Kőnig–Ore formula -/

variable [Fintype E(G)] {L R : Finset V(G)} {b : V(G) → ℕ} {x : E(G) → ℕ}

namespace IsCapacitatedMatching

/-- **The capacitated Kőnig–Ore inequality.** In a bipartite multigraph with sides `L` and `R`,
every multiset capacitated matching `x` and every `S ⊆ L` satisfy
`∑ e, x e + b(S) ≤ b(L) + b(N(S))`, where `N(S)` is the set of neighbours of `S`. -/
theorem sum_add_sum_le (hx : G.IsCapacitatedMatching b x) (hLR : G.IsBipartition L R)
    {S : Finset V(G)} (hS : S ⊆ L) :
    ∑ e, x e + ∑ v ∈ S, b v ≤ ∑ v ∈ L, b v + ∑ v ∈ G.neighborsIn S R, b v := by
  classical
  -- The vertices of `L` outside `S` together with the neighbours of `S` cover every edge.
  have hC : G.IsVertexCover ((L \ S ∪ G.neighborsIn S R : Finset V(G)) : Set V(G)) := by
    refine isVertexCover_def.2 fun e y z he ↦ ?_
    wlog hy : y ∈ L generalizing y z
    · exact (this z y he.symm (hLR.notMem_left_iff.1 hy |> hLR.mem_left_of_isLink he)).symm
    by_cases hyS : y ∈ S
    · exact .inr <| mem_coe.2 <| mem_union_right _ <|
        mem_neighborsIn.2 ⟨hLR.mem_right_of_isLink he hy, y, hyS, e, he⟩
    · exact .inl <| mem_coe.2 <| mem_union_left _ <| mem_sdiff.2 ⟨hy, hyS⟩
  have := (hx.sum_le_sum_of_isVertexCover hC).trans (le_self_add.trans_eq sum_union_inter)
  have := sum_sdiff (f := b) hS
  omega

end IsCapacitatedMatching

namespace IsBipartition

/-- **The capacitated Kőnig–Ore formula.** In a bipartite multigraph with sides `L` and `R`, some
multiset capacitated matching `x` and some `S ⊆ L` satisfy `∑ e, x e + b(S) = b(L) + b(N(S))`,
where `N(S)` is the set of neighbours of `S`. By
`Graph.IsCapacitatedMatching.sum_add_sum_le`, this matching is then largest and `S` maximizes
`b(S) - b(N(S))`. -/
theorem exists_isCapacitatedMatching_sum_add_sum_eq (hLR : G.IsBipartition L R)
    (b : V(G) → ℕ) :
    ∃ (x : E(G) → ℕ) (S : Finset V(G)), G.IsCapacitatedMatching b x ∧ S ⊆ L ∧
      ∑ e, x e + ∑ v ∈ S, b v = ∑ v ∈ L, b v + ∑ v ∈ G.neighborsIn S R, b v := by
  classical
  obtain ⟨x, C, hx, hC, hxC⟩ := hLR.exists_isCapacitatedMatching_isVertexCover_sum_eq b
  refine ⟨x, L \ C, hx, sdiff_subset, le_antisymm (hx.sum_add_sum_le hLR sdiff_subset) ?_⟩
  -- Every neighbour of `L ∖ C` lies in `C`, since the edge to it is covered by `C`.
  have hN : G.neighborsIn (L \ C) R ⊆ C := by
    intro y hy
    obtain ⟨-, z, hz, e, he⟩ := mem_neighborsIn.1 hy
    exact (isVertexCover_def.1 hC he).resolve_left (mem_sdiff.1 hz).2
  -- The vertices of `L ∩ C` and the neighbours of `L ∖ C` are disjoint parts of `C`.
  have hdisj : Disjoint (L ∩ C) (G.neighborsIn (L \ C) R) :=
    hLR.disjoint.mono inter_subset_left neighborsIn_subset
  have hle := sum_le_sum_of_subset (f := b) (union_subset (inter_subset_right (s₁ := L)) hN)
  rw [sum_union hdisj] at hle
  have := sum_sdiff (f := b) (sdiff_subset : L \ C ⊆ L)
  rw [sdiff_sdiff_right_self] at this
  omega

/-- **The largest multiset capacitated matching.** In a bipartite multigraph with sides `L` and
`R`, the largest size of a multiset capacitated matching is `b(L) - max_{S ⊆ L} (b(S) - b(N(S)))`,
with truncated subtraction, where `N(S)` is the set of neighbours of `S`. -/
theorem isGreatest_sum_isCapacitatedMatching (hLR : G.IsBipartition L R) (b : V(G) → ℕ) :
    IsGreatest {n | ∃ x : E(G) → ℕ, G.IsCapacitatedMatching b x ∧ ∑ e, x e = n}
      (∑ v ∈ L, b v -
        L.powerset.sup fun S ↦ ∑ v ∈ S, b v - ∑ v ∈ G.neighborsIn S R, b v) := by
  obtain ⟨T, hT, hTmax⟩ := exists_mem_eq_sup L.powerset ⟨∅, empty_mem_powerset L⟩
    fun S ↦ ∑ v ∈ S, b v - ∑ v ∈ G.neighborsIn S R, b v
  rw [hTmax]
  -- Every multiset capacitated matching has size at most `b(L)` and satisfies the Kőnig–Ore
  -- inequality for the maximizing set `T`.
  have hub {x : E(G) → ℕ} (hx : G.IsCapacitatedMatching b x) :
      ∑ e, x e ≤ ∑ v ∈ L, b v - (∑ v ∈ T, b v - ∑ v ∈ G.neighborsIn T R, b v) := by
    have := hx.sum_le_sum_of_isVertexCover hLR.isVertexCover_left
    have := hx.sum_add_sum_le hLR (mem_powerset.1 hT)
    omega
  refine ⟨?_, fun n ⟨x, hx, hxn⟩ ↦ hxn ▸ hub hx⟩
  obtain ⟨x, S, hx, hS, hxS⟩ := hLR.exists_isCapacitatedMatching_sum_add_sum_eq b
  have := le_sup (f := fun S ↦ ∑ v ∈ S, b v - ∑ v ∈ G.neighborsIn S R, b v)
    (mem_powerset.2 hS)
  have := hub hx
  exact ⟨x, hx, by omega⟩

/-- **Hall's theorem for multiset capacitated matchings.** In a bipartite multigraph with sides
`L` and `R`, some multiset capacitated matching saturates every vertex of `L` if and only if
`b(S) ≤ b(N(S))` for every `S ⊆ L`, where `N(S)` is the set of neighbours of `S`. -/
theorem exists_isCapacitatedMatching_saturating_left_iff (hLR : G.IsBipartition L R)
    (b : V(G) → ℕ) :
    (∃ x : E(G) → ℕ, G.IsCapacitatedMatching b x ∧
        ∀ v ∈ L, ∑ e ∈ G.incidentEdges {v}, x e = b v) ↔
      ∀ S ⊆ L, ∑ v ∈ S, b v ≤ ∑ v ∈ G.neighborsIn S R, b v := by
  constructor
  · rintro ⟨x, hx, hsat⟩ S hS
    have := (hx.sum_eq_sum_left_iff hLR).2 hsat
    have := hx.sum_add_sum_le hLR hS
    omega
  · intro hHall
    obtain ⟨x, S, hx, hS, hxS⟩ := hLR.exists_isCapacitatedMatching_sum_add_sum_eq b
    refine ⟨x, hx, (hx.sum_eq_sum_left_iff hLR).1 ?_⟩
    have := hx.sum_le_sum_of_isVertexCover hLR.isVertexCover_left
    have := hHall S hS
    omega

/-- In a bipartite multigraph with sides `L` and `R`, some multiset capacitated matching saturates
every actual vertex if and only if `b(L) = b(R)` and `b(S) ≤ b(N(S))` for every `S ⊆ L`, where
`N(S)` is the set of neighbours of `S`. -/
theorem exists_isCapacitatedMatching_saturating_iff (hLR : G.IsBipartition L R)
    (b : V(G) → ℕ) :
    (∃ x : E(G) → ℕ, G.IsCapacitatedMatching b x ∧
        ∀ v, ∑ e ∈ G.incidentEdges {v}, x e = b v) ↔
      ∑ v ∈ L, b v = ∑ v ∈ R, b v ∧ ∀ S ⊆ L, ∑ v ∈ S, b v ≤ ∑ v ∈ G.neighborsIn S R, b v := by
  constructor
  · rintro ⟨x, hx, hsat⟩
    exact ⟨((hx.sum_eq_sum_left_iff hLR).2 fun v _ ↦ hsat v).symm.trans
        ((hx.sum_eq_sum_left_iff hLR.symm).2 fun v _ ↦ hsat v),
      (hLR.exists_isCapacitatedMatching_saturating_left_iff b).1 ⟨x, hx, fun v _ ↦ hsat v⟩⟩
  · rintro ⟨hLR_eq, hHall⟩
    obtain ⟨x, hx, hsat⟩ := (hLR.exists_isCapacitatedMatching_saturating_left_iff b).2 hHall
    have hsatR := (hx.sum_eq_sum_left_iff hLR.symm).1 <|
      ((hx.sum_eq_sum_left_iff hLR).2 hsat).trans hLR_eq
    exact ⟨x, hx, fun v ↦ (hLR.mem_or_mem v).elim (hsat v) (hsatR v)⟩

end IsBipartition

end Graph
