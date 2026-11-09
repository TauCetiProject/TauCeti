/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Matching.Basic
public import TauCeti.Combinatorics.Graph.Matching.Hall

/-!
# Hall's theorem for finite bipartite multigraphs

This file specializes capacitated matching to unit vertex capacities. It first identifies an
ordinary matching with its zero-one edge multiplicity function, and conversely identifies a
unit-capacitated matching with the finite set of edges used positively. This transfers the
capacitated Kőnig–Ore formula and Hall theorem to ordinary matchings while retaining parallel edge
identities.

For a bipartition with sides `L` and `R`, the resulting Kőnig–Ore formula gives a matching `M`
and `S ⊆ L` such that `|M| + |S| = |L| + |N(S)|`. Hall's theorem says that a matching saturating
`L` exists exactly when `|S| ≤ |N(S)|` for every `S ⊆ L`.

## Main results

* `Graph.IsMatching.isCapacitatedMatching_indicator`: a matching gives a unit-capacitated
  matching by assigning multiplicity one to its selected edges.
* `Graph.IsCapacitatedMatching.support_isMatching`: the positive support of a unit-capacitated
  matching in a loopless graph is an ordinary matching.
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

section FiniteEdges

variable [Fintype E(G)]

namespace IsMatching

/-- An ordinary matching, represented by a finite set of actual edges, is a multiset
capacitated matching for unit vertex capacities when its selected edges have multiplicity one. -/
theorem isCapacitatedMatching_indicator {M : Finset E(G)} (hM : G.IsMatching (M : Set E(G))) :
    G.IsCapacitatedMatching (fun _ ↦ 1) ((M : Set E(G)).indicator fun _ ↦ 1) := by
  classical
  rw [isCapacitatedMatching_def]
  intro x
  calc
    ∑ e ∈ G.incidentEdges {x}, (M : Set E(G)).indicator (fun _ ↦ 1) e =
        ∑ e ∈ G.incidentEdges {x}, if e ∈ M then 1 else 0 :=
      sum_congr rfl fun e _ ↦ Set.indicator_apply _ _ _
    _ = ((G.incidentEdges {x}).filter (· ∈ M)).card :=
      sum_boole (R := ℕ) (· ∈ M) (G.incidentEdges {x})
    _ ≤ 1 := card_le_one.mpr fun e he f hf ↦ by
      obtain ⟨heinc, heM⟩ := mem_filter.1 he
      obtain ⟨hfinc, hfM⟩ := mem_filter.1 hf
      obtain ⟨y, hy, hey⟩ := (mem_incidentEdges G).1 heinc
      obtain ⟨z, hz, hfz⟩ := (mem_incidentEdges G).1 hfinc
      exact hM.eq_of_inc heM hfM (Finset.mem_singleton.mp hy ▸ hey)
        (Finset.mem_singleton.mp hz ▸ hfz)

end IsMatching

namespace IsCapacitatedMatching

/-- Every edge multiplicity in a unit-capacitated matching is at most one. -/
theorem apply_le_one {x : E(G) → ℕ} (hx : G.IsCapacitatedMatching (fun _ ↦ 1) x)
    (e : E(G)) : x e ≤ 1 := by
  obtain ⟨y, z, he⟩ := G.exists_isLink_of_mem_edgeSet e.2
  have hey : e ∈ G.incidentEdges {⟨y, he.left_mem⟩} :=
    (mem_incidentEdges G).2 ⟨⟨y, he.left_mem⟩, mem_singleton_self _, he.inc_left⟩
  exact (single_le_sum (fun _ _ ↦ Nat.zero_le _) hey).trans
    (isCapacitatedMatching_def.1 hx ⟨y, he.left_mem⟩)

/-- The sum of the multiplicities in a unit-capacitated matching is the cardinality of its
positive support. -/
theorem sum_eq_card_support {x : E(G) → ℕ} (hx : G.IsCapacitatedMatching (fun _ ↦ 1) x) :
    ∑ e, x e = (Finset.univ.filter fun e ↦ x e ≠ 0).card := by
  classical
  calc
    ∑ e, x e = ∑ e, if x e ≠ 0 then 1 else 0 := sum_congr rfl fun e _ ↦ by
      have hle := hx.apply_le_one e
      split_ifs with he
      · omega
      · simpa using he
    _ = (Finset.univ.filter fun e ↦ x e ≠ 0).card := by
      exact sum_boole (R := ℕ) (fun e ↦ x e ≠ 0) univ

/-- In a loopless graph, the positive support of a unit-capacitated matching is an ordinary
matching. -/
theorem support_isMatching {x : E(G) → ℕ} (hx : G.IsCapacitatedMatching (fun _ ↦ 1) x)
    (hG : G.Loopless) : G.IsMatching ({e | x e ≠ 0} : Set E(G)) := by
  classical
  rw [isMatching_def]
  refine ⟨fun e _ y ↦ hG.not_isLoopAt e y, fun e he f hf hef y hinc ↦ ?_⟩
  have hey : e ∈ G.incidentEdges {⟨y, hinc.1.vertex_mem⟩} :=
    (mem_incidentEdges G).2 ⟨⟨y, hinc.1.vertex_mem⟩, mem_singleton_self _, hinc.1⟩
  have hfy : f ∈ G.incidentEdges {⟨y, hinc.1.vertex_mem⟩} :=
    (mem_incidentEdges G).2 ⟨⟨y, hinc.1.vertex_mem⟩, mem_singleton_self _, hinc.2⟩
  have hpair : ∑ a ∈ {e, f}, x a ≤ 1 :=
    (sum_le_sum_of_subset (insert_subset_iff.2 ⟨hey, singleton_subset_iff.2 hfy⟩)).trans
      (isCapacitatedMatching_def.1 hx ⟨y, hinc.1.vertex_mem⟩)
  rw [sum_pair hef] at hpair
  change x e ≠ 0 at he
  change x f ≠ 0 at hf
  omega

/-- The finite positive support of a unit-capacitated matching in a loopless graph is an
ordinary matching. -/
theorem supportFinset_isMatching {x : E(G) → ℕ}
    (hx : G.IsCapacitatedMatching (fun _ ↦ 1) x) (hG : G.Loopless) :
    G.IsMatching (↑(Finset.univ.filter fun e ↦ x e ≠ 0) : Set E(G)) := by
  have hset : (↑(Finset.univ.filter fun e ↦ x e ≠ 0) : Set E(G)) = {e | x e ≠ 0} := by
    ext
    simp
  rw [hset]
  exact hx.support_isMatching hG

end IsCapacitatedMatching

end FiniteEdges

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
