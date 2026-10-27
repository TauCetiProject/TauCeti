/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Decomposition
public import TauCeti.Combinatorics.Network.ShortestAugmentation

/-!
# Menger's theorem for arrow-disjoint directed paths

Let `Q` be an arrow family on a vertex type `V`, and let `s ≠ t`. A family of directed `s`–`t`
paths is *arrow-disjoint* when no arrow identity is traversed by two of its members; parallel
arrows are distinct arrows. A set `F` of arrows *separates* `t` from `s` when every walk from `s`
to `t` traverses an arrow of `F`, that is, when `t` is not reachable from `s` without the arrows
of `F`.

This file proves the local edge form of Menger's theorem for directed networks with finitely many
vertices and arrows: the largest number of arrow-disjoint `s`–`t` paths equals the least number of
arrows separating `t` from `s`. Weak duality, that every arrow-disjoint family of `s`–`t` walks has
at most as many members as every separating set of arrows, needs no finiteness at all: each member
traverses an arrow of the separating set, and different members traverse different arrows.

Attainment is reduced to the max-flow/min-cut theorem over `ℤ` with capacity one on every arrow. A
maximum flow has the value of a cut `S`, which is the number of arrows leaving `S`; those arrows
separate `t` from `s`. A path–cycle decomposition of the flow has paths from `s` to `t` whose
weights add up to the value. Every arrow carries at most one unit, so every path has weight one
and no two paths share an arrow.

## Main results

* `TauCeti.card_le_card_of_not_reachableWithout`: **weak duality**, an arrow-disjoint family of
  `s`–`t` walks has at most as many members as any set of arrows separating `t` from `s`.
* `TauCeti.exists_paths_arrowSeparator_card_eq`: **Menger's theorem** for arrow-disjoint directed
  paths, in witness form: there are a family of arrow-disjoint `s`–`t` paths and a set of arrows
  separating `t` from `s` of the same size.
* `TauCeti.forall_reachableWithout_iff_exists_paths`: the predicate form, `t` stays reachable from
  `s` after deleting any fewer than `k` arrows exactly when there are `k` arrow-disjoint `s`–`t`
  paths.

## References

* K. Menger, *Zur allgemeinen Kurventheorie*, Fund. Math. 10 (1927).
* L. R. Ford, D. R. Fulkerson, *Maximal flow through a network*, Canad. J. Math. 8 (1956).
* A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Springer, 2003,
  Section 9.1.
-/

public section

namespace TauCeti

open Finset

universe u v

variable {V : Type u} {Q : V → V → Type v} {s t : V}

/-- **Weak duality for arrow-disjoint walks.** A family of `s`–`t` walks of which no two traverse a
common arrow has at most as many members as any set of arrows whose deletion leaves `t`
unreachable from `s`. -/
theorem card_le_card_of_not_reachableWithout {ι : Type*} [Fintype ι] {P : ι → ArrowWalk Q s t}
    (hP : Pairwise fun i j ↦ (P i).arrows.Disjoint (P j).arrows) {F : Finset (Σ x y, Q x y)}
    (hF : ¬ReachableWithout (F : Set (Σ x y, Q x y)) s t) : Fintype.card ι ≤ #F := by
  have h (i : ι) : ∃ a ∈ (P i).arrows, a ∈ F := by
    by_contra! h
    exact hF (reachableWithout_def.2 ⟨P i, fun a ha haF ↦ h a ha haF⟩)
  choose g hg hgF using h
  rw [← card_univ]
  refine card_le_card_of_injOn g (fun i _ ↦ hgF i) fun i _ j _ hij ↦ ?_
  by_contra hne
  exact hP hne (hg i) (hij ▸ hg j)

/-- **Menger's theorem for arrow-disjoint directed paths.** For distinct vertices `s` and `t` of a
finite arrow family, some family of directed `s`–`t` paths, no two of which traverse a common
arrow, has as many members as some set of arrows whose deletion leaves `t` unreachable from `s`.
By `TauCeti.card_le_card_of_not_reachableWithout`, the family is then largest and the set of
arrows smallest. -/
theorem exists_paths_arrowSeparator_card_eq [Finite V] [∀ x y, Finite (Q x y)] (hst : s ≠ t) :
    ∃ (k : ℕ) (P : Fin k → ArrowWalk Q s t) (F : Finset (Σ x y, Q x y)),
      (∀ i, (P i).IsPath) ∧ (Pairwise fun i j ↦ (P i).arrows.Disjoint (P j).arrows) ∧
      ¬ReachableWithout (F : Set (Σ x y, Q x y)) s t ∧ #F = k := by
  classical
  have := Fintype.ofFinite V
  have (x y : V) : Fintype (Q x y) := Fintype.ofFinite _
  -- A maximum flow for unit capacities has the value of a cut `S`: the number of arrows leaving
  -- `S`, which separate `t` from `s`.
  obtain ⟨f, S, hs, ht, hval⟩ :=
    Flow.exists_val_eq_arrowSum hst (cap := (1 : Assignment Q ℤ)) fun _ _ _ ↦ zero_le_one
  obtain ⟨k, P, hk, hP, -, hdisj⟩ := f.exists_paths_card_eq_val hst fun _ _ e ↦ f.le_upper e
  refine ⟨k, P, ({a : Σ x y, Q x y | a.1 ∈ S ∧ a.2.1 ∈ Sᶜ} : Finset _), hP, hdisj,
    fun h ↦ ht ?_, ?_⟩
  · refine h.mem_of_mem (C := (S : Set V)) hs fun v w e hv he ↦ ?_
    by_contra hw
    exact he (by simpa using ⟨hv, hw⟩)
  · rw [← Nat.cast_inj (R := ℤ), hk, hval, arrowSum_one]

/-- **Menger's theorem for arrow-disjoint directed paths, predicate form.** For distinct vertices
`s` and `t` of a finite arrow family, `t` stays reachable from `s` after deleting any fewer than
`k` arrows exactly when there are `k` directed `s`–`t` paths, no two of which traverse a common
arrow. -/
theorem forall_reachableWithout_iff_exists_paths [Finite V] [∀ x y, Finite (Q x y)] (hst : s ≠ t)
    (k : ℕ) :
    (∀ F : Finset (Σ x y, Q x y), #F < k → ReachableWithout (F : Set (Σ x y, Q x y)) s t) ↔
      ∃ P : Fin k → ArrowWalk Q s t, (∀ i, (P i).IsPath) ∧
        Pairwise fun i j ↦ (P i).arrows.Disjoint (P j).arrows := by
  refine ⟨fun h ↦ ?_, fun ⟨P, _, hP⟩ F hF ↦ ?_⟩
  · obtain ⟨m, P, F, hP, hdisj, hF, hFm⟩ := exists_paths_arrowSeparator_card_eq (Q := Q) hst
    have hkm : k ≤ m := hFm ▸ not_lt.1 fun hlt ↦ hF (h F hlt)
    exact ⟨fun i ↦ P (Fin.castLE hkm i), fun i ↦ hP _,
      fun i j hij ↦ hdisj fun h ↦ hij (Fin.castLE_injective hkm h)⟩
  · by_contra h
    exact hF.not_ge (by simpa using card_le_card_of_not_reachableWithout hP h)

end TauCeti
