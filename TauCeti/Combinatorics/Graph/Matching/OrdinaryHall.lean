/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Matching.Hall

import TauCeti.Combinatorics.Graph.Matching.VertexCover

/-!
# Hall's theorem for finite bipartite multigraphs

This file specializes capacitated matching to unit vertex capacities. Using the lower-level
correspondence between ordinary matchings and unit-capacitated matchings, it transfers the
capacitated Kőnig–Ore formula and Hall theorem to ordinary matchings while retaining parallel edge
identities.

For a bipartition with sides `L` and `R`, the resulting Kőnig–Ore formula gives a matching `M`
and `S ⊆ L` such that `|M| + |S| = |L| + |N(S)|`. Hall's theorem says that a matching saturating
`L` exists exactly when `|S| ≤ |N(S)|` for every `S ⊆ L`.

## Main results

* `Graph.IsMatching.card_add_card_le` and `Graph.IsMatching.card_add_card_right_le`: the Kőnig–Ore
  inequality on each side, without edge-finiteness assumptions.
* `Graph.IsBipartition.exists_isMatching_card_add_card_eq` and
  `Graph.IsBipartition.exists_isMatching_card_add_card_right_eq`: the ordinary Kőnig–Ore formula
  on each side.
* `Graph.IsBipartition.isGreatest_card_isMatching` and
  `Graph.IsBipartition.isGreatest_card_isMatching_right`: the numerical deficiency formula.
* `Graph.IsBipartition.exists_isMatching_saturating_left_iff` and
  `Graph.IsBipartition.exists_isMatching_saturating_right_iff`: Hall's theorem for finite
  bipartite multigraphs.
* `Graph.IsBipartition.exists_isPerfectMatching_iff` and
  `Graph.IsBipartition.exists_isPerfectMatching_iff_right`: Hall's condition for a perfect
  matching in a finite bipartite multigraph.

## References

* P. Hall, *On representatives of subsets*, J. London Math. Soc. 10 (1935).
* Ø. Ore, *Graphs and matching theorems*, Duke Math. J. 22 (1955).
-/

public section

open Finset Set
open scoped Graph

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β}
variable {L R : Finset V(G)}

namespace IsMatching

/-- The Kőnig–Ore inequality for ordinary matchings. If `M` is a matching and `S ⊆ L`, then
`|M| + |S| ≤ |L| + |N(S)|`. -/
theorem card_add_card_le {M : Finset E(G)} (hM : G.IsMatching (M : Set E(G)))
    (hLR : G.IsBipartition L R) {S : Finset V(G)} (hS : S ⊆ L) :
    M.card + S.card ≤ L.card + (G.neighborsIn S R).card := by
  classical
  have hcov :=
    (hM.card_le_card_of_isVertexCover (hLR.isVertexCover_sdiff_union_neighborsIn S)).trans
      (card_union_le _ _)
  have hsdiff := card_sdiff_add_card_eq_card hS
  omega

/-- The Kőnig–Ore inequality for subsets of the right side: if `M` is a matching and `T ⊆ R`,
then `|M| + |T| ≤ |R| + |N(T)|`, where `N(T)` is the set of neighbours of `T` in `L`. -/
theorem card_add_card_right_le {M : Finset E(G)} (hM : G.IsMatching (M : Set E(G)))
    (hLR : G.IsBipartition L R) {T : Finset V(G)} (hT : T ⊆ R) :
    M.card + T.card ≤ R.card + (G.neighborsIn T L).card :=
  hM.card_add_card_le hLR.symm hT

end IsMatching

namespace IsBipartition

/-- In a loopless graph with finitely many actual edges, if a matching `M` has an edge incident to
`y`, then the indicator of `M` sums to `1` over the edges incident to `y`. -/
private theorem sum_incidentEdges_indicator_eq_one [Fintype E(G)] [G.Loopless]
    {M : Set E(G)} (hM : G.IsMatching M) {y : V(G)} (hy : ∃ e ∈ M, G.Inc e y) :
    ∑ e ∈ G.incidentEdges {y}, M.indicator (1 : E(G) → ℕ) e = 1 := by
  have hx := (G.isMatching_iff_isCapacitatedMatching_indicator M).1 hM
  refine le_antisymm (isCapacitatedMatching_def.1 hx y) ?_
  obtain ⟨e, heM, hey⟩ := hy
  have he : e ∈ G.incidentEdges {y} := (mem_incidentEdges G).2 ⟨y, by simp, hey⟩
  have hxe : M.indicator (1 : E(G) → ℕ) e = 1 := Set.indicator_of_mem heM _
  exact hxe ▸ single_le_sum (fun _ _ ↦ Nat.zero_le _) he

variable [Finite E(G)]

/-- The ordinary Kőnig–Ore formula for finite bipartite multigraphs. There are a matching `M`
and a set `S ⊆ L` attaining `|M| + |S| = |L| + |N(S)|`. -/
theorem exists_isMatching_card_add_card_eq (hLR : G.IsBipartition L R) :
    ∃ (M : Finset E(G)) (S : Finset V(G)), G.IsMatching (M : Set E(G)) ∧ S ⊆ L ∧
      M.card + S.card = L.card + (G.neighborsIn S R).card := by
  classical
  let _ := Fintype.ofFinite E(G)
  obtain ⟨x, S, hx, hS, hxS⟩ :=
    hLR.exists_isCapacitatedMatching_sum_add_sum_eq (fun _ ↦ 1)
  refine ⟨Finset.univ.filter (fun e ↦ x e ≠ 0), S,
    hx.supportFinset_isMatching hLR.loopless, hS, ?_⟩
  simpa [hx.sum_eq_card_support] using hxS

/-- The ordinary Kőnig–Ore formula for subsets of the right side `R`: there are a matching `M`
and a set `T ⊆ R` attaining `|M| + |T| = |R| + |N(T)|`. -/
theorem exists_isMatching_card_add_card_right_eq (hLR : G.IsBipartition L R) :
    ∃ (M : Finset E(G)) (T : Finset V(G)), G.IsMatching (M : Set E(G)) ∧ T ⊆ R ∧
      M.card + T.card = R.card + (G.neighborsIn T L).card :=
  hLR.symm.exists_isMatching_card_add_card_eq

/-- The numerical Kőnig–Ore deficiency formula. The greatest size of an ordinary matching is
`|L| - max_{S ⊆ L} (|S| - |N(S)|)`. -/
theorem isGreatest_card_isMatching (hLR : G.IsBipartition L R) :
    IsGreatest {n | ∃ M : Finset E(G), G.IsMatching (M : Set E(G)) ∧ M.card = n}
      (L.card - L.powerset.sup fun S ↦ S.card - (G.neighborsIn S R).card) := by
  classical
  let _ := Fintype.ofFinite E(G)
  have hvalues :
      {n | ∃ x : E(G) → ℕ, G.IsCapacitatedMatching (fun _ ↦ 1) x ∧ ∑ e, x e = n} =
        {n | ∃ M : Finset E(G), G.IsMatching (M : Set E(G)) ∧ M.card = n} := by
    ext n
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Finset.univ.filter (fun e ↦ x e ≠ 0),
        hx.supportFinset_isMatching hLR.loopless, hx.sum_eq_card_support.symm⟩
    · rintro ⟨M, hM, rfl⟩
      refine ⟨(M : Set E(G)).indicator (fun _ ↦ 1),
        hM.isCapacitatedMatching_indicator, ?_⟩
      simp [Set.indicator_apply]
  rw [← hvalues]
  simpa using hLR.isGreatest_sum_isCapacitatedMatching (fun _ ↦ 1)

/-- The numerical Kőnig–Ore deficiency formula in terms of subsets of the right side `R`:
the greatest size of an ordinary matching is `|R| - max_{T ⊆ R} (|T| - |N(T)|)`. -/
theorem isGreatest_card_isMatching_right (hLR : G.IsBipartition L R) :
    IsGreatest {n | ∃ M : Finset E(G), G.IsMatching (M : Set E(G)) ∧ M.card = n}
      (R.card - R.powerset.sup fun T ↦ T.card - (G.neighborsIn T L).card) :=
  hLR.symm.isGreatest_card_isMatching

/-- **Hall's theorem for finite bipartite multigraphs.** There is an ordinary matching incident
to every vertex of `L` if and only if every `S ⊆ L` has at least `|S|` neighbours in `R`. -/
theorem exists_isMatching_saturating_left_iff (hLR : G.IsBipartition L R) :
    (∃ M : Finset E(G), G.IsMatching (M : Set E(G)) ∧
        ∀ y ∈ L, ∃ e ∈ M, G.Inc e y) ↔
      ∀ S ⊆ L, S.card ≤ (G.neighborsIn S R).card := by
  classical
  let _ := Fintype.ofFinite E(G)
  let _ : G.Loopless := hLR.loopless
  constructor
  · rintro ⟨M, hM, hsat⟩
    have hx := (G.isMatching_iff_isCapacitatedMatching_indicator (M : Set E(G))).1 hM
    have hcap := (hLR.exists_isCapacitatedMatching_saturating_left_iff 1).1
      ⟨(M : Set E(G)).indicator 1, hx, fun y hy ↦
        sum_incidentEdges_indicator_eq_one hM <|
          let ⟨e, heM, hey⟩ := hsat y hy; ⟨e, mem_coe.2 heM, hey⟩⟩
    simpa using hcap
  · intro hHall
    have hHall' : ∀ S ⊆ L, ∑ _ ∈ S, 1 ≤ ∑ _ ∈ G.neighborsIn S R, 1 := by
      simpa using hHall
    obtain ⟨x, hx, hsat⟩ :=
      (hLR.exists_isCapacitatedMatching_saturating_left_iff (fun _ ↦ 1)).2 hHall'
    refine ⟨Finset.univ.filter (fun e ↦ x e ≠ 0),
      hx.supportFinset_isMatching hLR.loopless, fun y hy ↦ ?_⟩
    have hpos : 0 < ∑ e ∈ G.incidentEdges {y}, x e := by simp [hsat y hy]
    obtain ⟨e, he, hxe⟩ := Finset.sum_pos_iff.1 hpos
    obtain ⟨z, hz, hez⟩ := (mem_incidentEdges G).1 he
    have hzy : z = y := by simpa using hz
    exact ⟨e, by simpa using hxe.ne', hzy ▸ hez⟩

/-- **Hall's theorem for finite bipartite multigraphs** saturating the right side `R`: there is
an ordinary matching incident to every vertex of `R` if and only if every `T ⊆ R` has at least
`|T|` neighbours in `L`. -/
theorem exists_isMatching_saturating_right_iff (hLR : G.IsBipartition L R) :
    (∃ M : Finset E(G), G.IsMatching (M : Set E(G)) ∧
        ∀ y ∈ R, ∃ e ∈ M, G.Inc e y) ↔
      ∀ T ⊆ R, T.card ≤ (G.neighborsIn T L).card :=
  hLR.symm.exists_isMatching_saturating_left_iff

/-- **Hall's condition for a perfect matching in a finite bipartite multigraph.** A perfect
matching exists if and only if the two sides have equal cardinality and every `S ⊆ L` has at least
`|S|` neighbours in `R`. -/
theorem exists_isPerfectMatching_iff (hLR : G.IsBipartition L R) :
    (∃ M : Set E(G), G.IsPerfectMatching M) ↔
      L.card = R.card ∧ ∀ S ⊆ L, S.card ≤ (G.neighborsIn S R).card := by
  classical
  let _ := Fintype.ofFinite E(G)
  let _ : G.Loopless := hLR.loopless
  constructor
  · rintro ⟨M, hM⟩
    obtain ⟨hM, hsat⟩ := isPerfectMatching_def.1 hM
    have hx := (G.isMatching_iff_isCapacitatedMatching_indicator M).1 hM
    have hcap := (hLR.exists_isCapacitatedMatching_saturating_iff 1).1
      ⟨M.indicator 1, hx, fun y ↦ sum_incidentEdges_indicator_eq_one hM (hsat y)⟩
    simpa using hcap
  · rintro ⟨hcard, hHall⟩
    have hcap : ∑ _ ∈ L, 1 = ∑ _ ∈ R, 1 ∧ ∀ S ⊆ L, ∑ _ ∈ S, 1 ≤ ∑ _ ∈ G.neighborsIn S R, 1 := by
      simpa using ⟨hcard, hHall⟩
    obtain ⟨x, -, hsat⟩ := (hLR.exists_isCapacitatedMatching_saturating_iff (fun _ ↦ 1)).2 hcap
    exact ⟨{e | x e ≠ 0}, isPerfectMatching_of_sum_incidentEdges_eq_one hsat⟩

/-- **Hall's condition for a perfect matching in a finite bipartite multigraph**, stated via
subsets of the right side `R`. -/
theorem exists_isPerfectMatching_iff_right (hLR : G.IsBipartition L R) :
    (∃ M : Set E(G), G.IsPerfectMatching M) ↔
      L.card = R.card ∧ ∀ T ⊆ R, T.card ≤ (G.neighborsIn T L).card := by
  rw [hLR.symm.exists_isPerfectMatching_iff, eq_comm]

end IsBipartition

end Graph
