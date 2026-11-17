/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Matching.Hall

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

* `Graph.IsBipartition.exists_isMatching_card_add_card_eq`: the ordinary Kőnig–Ore formula.
* `Graph.IsBipartition.isGreatest_card_isMatching`: the numerical deficiency formula.
* `Graph.IsBipartition.exists_isMatching_saturating_left_iff`: Hall's theorem for finite
  bipartite multigraphs.

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

variable [Finite E(G)]

namespace IsMatching

/-- The Kőnig–Ore inequality for ordinary matchings. If `M` is a matching and `S ⊆ L`, then
`|M| + |S| ≤ |L| + |N(S)|`. -/
theorem card_add_card_le {M : Finset E(G)} (hM : G.IsMatching (M : Set E(G)))
    (hLR : G.IsBipartition L R) {S : Finset V(G)} (hS : S ⊆ L) :
    M.card + S.card ≤ L.card + (G.neighborsIn S R).card := by
  classical
  let _ := Fintype.ofFinite E(G)
  have hx := hM.isCapacitatedMatching_indicator
  simpa [Set.indicator_apply] using hx.sum_add_sum_le hLR hS

end IsMatching

namespace IsBipartition

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

/-- **Hall's theorem for finite bipartite multigraphs.** There is an ordinary matching incident
to every vertex of `L` if and only if every `S ⊆ L` has at least `|S|` neighbours in `R`. -/
theorem exists_isMatching_saturating_left_iff (hLR : G.IsBipartition L R) :
    (∃ M : Finset E(G), G.IsMatching (M : Set E(G)) ∧
        ∀ y ∈ L, ∃ e ∈ M, G.Inc e y) ↔
      ∀ S ⊆ L, S.card ≤ (G.neighborsIn S R).card := by
  classical
  let _ := Fintype.ofFinite E(G)
  constructor
  · rintro ⟨M, hM, hsat⟩
    let x : E(G) → ℕ := (M : Set E(G)).indicator fun _ ↦ 1
    have hx : G.IsCapacitatedMatching (fun _ ↦ 1) x := hM.isCapacitatedMatching_indicator
    have hcap := (hLR.exists_isCapacitatedMatching_saturating_left_iff (fun _ ↦ 1)).1
      ⟨x, hx, fun y hy ↦ le_antisymm (isCapacitatedMatching_def.1 hx y) (by
        obtain ⟨e, heM, hey⟩ := hsat y hy
        have he : e ∈ G.incidentEdges {y} :=
          (mem_incidentEdges G).2 ⟨y, by simp, hey⟩
        have hxe : x e = 1 := Set.indicator_of_mem heM _
        exact hxe ▸ single_le_sum (fun _ _ ↦ Nat.zero_le _) he)⟩
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

end IsBipartition

end Graph
