/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.Combinatorics.Network.Decomposition
public import TauCeti.Combinatorics.Network.SetFlow
import Mathlib.Tactic.Linarith

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

It also proves the set-to-set form for disjoint vertex sets `A` and `B`. An *`A`–`B` path* runs from
a vertex of `A` to a vertex of `B` and has no other vertex in `A` or `B`; arrow-disjoint `A`–`B`
paths may share their endpoints. A set of arrows *separates* `B` from `A` when after deleting it no
vertex of `B` is reachable from a vertex of `A`. The largest number of arrow-disjoint `A`–`B` paths
equals the least number of arrows separating `B` from `A`; weak duality again needs neither
finiteness nor disjointness.

Attainment is reduced to the max-flow/min-cut theorem over `ℤ` with capacity one on every arrow,
between the terminals `s` and `t` or between the vertex sets `A` and `B`
(`TauCeti.SetFlow.exists_val_eq_arrowSum`). A maximum flow has the value of a cut `S`, which is the
number of arrows leaving `S`; those arrows separate the sink side from the source side. A
path–cycle decomposition of the flow has paths from supply to demand vertices whose weights add
up to the value. Every arrow carries at most one unit, so every path has weight one and no two
paths share an arrow (`TauCeti.PathCycleDecomposition.pairwise_disjoint_arrows`). In the
set-to-set case each path is finally trimmed to an `A`–`B` path, which traverses only arrows of
the original path (`TauCeti.ArrowWalk.exists_isPath_interior_notMem`).

## Main results

* `TauCeti.natCard_sub_one_le_card_of_completeCut`: a finite set of arrows containing every
  arrow across a nontrivial complete directed cut has at least one fewer member than the number
  of vertices.
* `TauCeti.card_le_card_of_not_reachableWithout`: **weak duality**, an arrow-disjoint family of
  `s`–`t` walks has at most as many members as any set of arrows separating `t` from `s`.
* `TauCeti.exists_paths_arrowSeparator_card_eq`: **Menger's theorem** for arrow-disjoint directed
  paths, in witness form: there are a family of arrow-disjoint `s`–`t` paths and a set of arrows
  separating `t` from `s` of the same size.
* `TauCeti.forall_reachableWithout_iff_exists_paths`: the predicate form, `t` stays reachable from
  `s` after deleting any fewer than `k` arrows exactly when there are `k` arrow-disjoint `s`–`t`
  paths.
* `TauCeti.SetFlow.exists_paths_card_eq_val`: an integer `A`–`B` flow carrying at most one unit on
  every arrow carries as many arrow-disjoint paths from `A` to `B` as its value.
* `TauCeti.card_le_card_of_forall_not_reachableWithout`: weak duality for arrow-disjoint walks from
  `A` to `B` and sets of arrows separating `B` from `A`.
* `TauCeti.exists_paths_setArrowSeparator_card_eq`: **Menger's theorem** for arrow-disjoint
  directed paths between disjoint vertex sets, in witness form.
* `TauCeti.forall_exists_reachableWithout_iff_exists_paths`: its predicate form.

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

/-- If every vertex of `C` has an arrow to every vertex outside `C`, then any finite set containing
all arrows leaving `C` has at least `Nat.card V - 1` members, provided `C` and its complement are
nonempty. -/
theorem natCard_sub_one_le_card_of_completeCut [Finite V] {C : Set V} (hs : s ∈ C) (ht : t ∉ C)
    (hC : ∀ u ∈ C, ∀ w ∉ C, Nonempty (Q u w)) {F : Finset (Σ x y, Q x y)}
    (hF : ∀ ⦃v w : V⦄ (e : Q v w), v ∈ C → w ∉ C → ⟨v, w, e⟩ ∈ F) :
    Nat.card V - 1 ≤ #F := by
  classical
  let _ := Fintype.ofFinite V
  set D : Finset V := {v | v ∈ C}
  have hsub : D ×ˢ Dᶜ ⊆ ({a ∈ F | a.1 ∈ C ∧ a.2.1 ∉ C}).image fun a ↦ (a.1, a.2.1) := by
    rintro ⟨v, w⟩ hvw
    simp only [D, mem_product, mem_compl, mem_filter, mem_univ, true_and] at hvw
    obtain ⟨e⟩ := hC v hvw.1 w hvw.2
    exact mem_image.2 ⟨⟨v, w, e⟩, mem_filter.2 ⟨hF e hvw.1 hvw.2, hvw.1, hvw.2⟩, rfl⟩
  have hcard := (card_le_card hsub).trans (card_image_le.trans (card_filter_le _ _))
  rw [card_product] at hcard
  have hD : 1 ≤ #D := card_pos.2 ⟨s, by simpa [D] using hs⟩
  have hDc : 1 ≤ #Dᶜ := card_pos.2 ⟨t, by simpa [D] using ht⟩
  rw [Nat.sub_le_iff_le_add, Nat.card_eq_fintype_card, ← card_add_card_compl D]
  nlinarith

/-- **Weak duality for arrow-disjoint set-to-set walks.** A family of walks, each from a vertex of
`A` to a vertex of `B`, of which no two traverse a common arrow, has at most as many members as any
set of arrows whose deletion leaves no vertex of `B` reachable from a vertex of `A`. -/
theorem card_le_card_of_forall_not_reachableWithout {A B : Set V} {ι : Type*} [Fintype ι]
    {a b : ι → V} {P : ∀ i, ArrowWalk Q (a i) (b i)} (ha : ∀ i, a i ∈ A) (hb : ∀ i, b i ∈ B)
    (hP : Pairwise fun i j ↦ (P i).arrows.Disjoint (P j).arrows) {F : Finset (Σ x y, Q x y)}
    (hF : ∀ a ∈ A, ∀ b ∈ B, ¬ReachableWithout (F : Set (Σ x y, Q x y)) a b) :
    Fintype.card ι ≤ #F := by
  -- Each member traverses an arrow of `F`, and different members traverse different arrows.
  have h (i : ι) : ∃ e ∈ (P i).arrows, e ∈ F := by
    by_contra! h
    exact hF _ (ha i) _ (hb i) (reachableWithout_def.2 ⟨P i, fun e he heF ↦ h e he heF⟩)
  choose g hg hgF using h
  rw [← card_univ]
  refine card_le_card_of_injOn g (fun i _ ↦ hgF i) fun i _ j _ hij ↦ ?_
  by_contra hne
  exact hP hne (hg i) (hij ▸ hg j)

/-- **Weak duality for arrow-disjoint walks.** A family of `s`–`t` walks of which no two traverse a
common arrow has at most as many members as any set of arrows whose deletion leaves `t`
unreachable from `s`. -/
theorem card_le_card_of_not_reachableWithout {ι : Type*} [Fintype ι] {P : ι → ArrowWalk Q s t}
    (hP : Pairwise fun i j ↦ (P i).arrows.Disjoint (P j).arrows) {F : Finset (Σ x y, Q x y)}
    (hF : ¬ReachableWithout (F : Set (Σ x y, Q x y)) s t) : Fintype.card ι ≤ #F :=
  card_le_card_of_forall_not_reachableWithout (A := {s}) (B := {t}) (a := fun _ ↦ s)
    (b := fun _ ↦ t) (P := P) (fun _ ↦ Set.mem_singleton s) (fun _ ↦ Set.mem_singleton t) hP
    (by simpa using hF)

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

/-- **Menger's theorem for arrow-disjoint directed paths, predicate form.** For vertices `s` and
`t` of a finite arrow family, `t` stays reachable from `s` after deleting any fewer than `k` arrows
exactly when there are `k` directed `s`–`t` paths, no two of which traverse a common arrow. -/
theorem forall_reachableWithout_iff_exists_paths [Finite V] [∀ x y, Finite (Q x y)] (k : ℕ) :
    (∀ F : Finset (Σ x y, Q x y), #F < k → ReachableWithout (F : Set (Σ x y, Q x y)) s t) ↔
      ∃ P : Fin k → ArrowWalk Q s t, (∀ i, (P i).IsPath) ∧
        Pairwise fun i j ↦ (P i).arrows.Disjoint (P j).arrows := by
  refine ⟨fun h ↦ ?_, fun ⟨P, _, hP⟩ F hF ↦ ?_⟩
  · -- At `s = t`, take `k` copies of the trivial path.
    rcases eq_or_ne s t with rfl | hst
    · exact ⟨fun _ ↦ .nil s, fun _ ↦ ArrowWalk.isPath_nil s, fun _ _ _ ↦ by simp⟩
    obtain ⟨m, P, F, hP, hdisj, hF, hFm⟩ := exists_paths_arrowSeparator_card_eq (Q := Q) hst
    have hkm : k ≤ m := hFm ▸ not_lt.1 fun hlt ↦ hF (h F hlt)
    exact ⟨fun i ↦ P (Fin.castLE hkm i), fun i ↦ hP _,
      fun i j hij ↦ hdisj fun h ↦ hij (Fin.castLE_injective hkm h)⟩
  · by_contra h
    exact hF.not_ge (by simpa using card_le_card_of_not_reachableWithout hP h)

/-! ### Arrow-disjoint paths between vertex sets -/

/-- An integer `A`–`B` flow carrying at most one unit on every arrow carries as many directed paths
as its value, each from a vertex of `A` to a vertex of `B`, no two of which traverse a common
arrow. -/
theorem SetFlow.exists_paths_card_eq_val [Fintype V] [∀ x y, Fintype (Q x y)]
    {cap : Assignment Q ℤ} {A B : Finset V} (f : SetFlow cap A B)
    (hf : ∀ ⦃x y : V⦄ (e : Q x y), f.toFun e ≤ 1) :
    ∃ (k : ℕ) (a b : Fin k → V) (P : ∀ i, ArrowWalk Q (a i) (b i)), (k : ℤ) = f.val ∧
      (∀ i, a i ∈ A) ∧ (∀ i, b i ∈ B) ∧ (∀ i, (P i).IsPath) ∧
      Pairwise fun i j ↦ (P i).arrows.Disjoint (P j).arrows := by
  classical
  obtain ⟨D⟩ := nonempty_pathCycleDecomposition (f := f.toFun) fun _ _ e ↦ f.nonneg e
  -- Every path of the decomposition starts at a supply vertex, which lies in `A` but not in `B`,
  -- and ends at a demand vertex, which lies in `B`.
  have hsource (p : WeightedWalk Q ℤ) (hp : p ∈ D.paths) : p.source ∈ A ∧ p.source ∉ B := by
    refine ⟨by_contra fun hA ↦ D.source_ne_of_mem_paths hp ?_ rfl,
      fun hB ↦ D.source_ne_of_mem_paths hp (f.excessAt_nonneg _ hB) rfl⟩
    by_cases hB : p.source ∈ B
    · exact f.excessAt_nonneg _ hB
    · exact (f.conserve _ hA hB).ge
  have htarget (p : WeightedWalk Q ℤ) (hp : p ∈ D.paths) : p.target ∈ B := by
    by_contra hB
    refine D.target_ne_of_mem_paths hp ?_ rfl
    by_cases hA : p.target ∈ A
    · exact f.excessAt_nonpos _ hA
    · exact (f.conserve _ hA hB).le
  refine ⟨D.paths.length, fun i ↦ D.paths[(i : ℕ)].source, fun i ↦ D.paths[(i : ℕ)].target,
    fun i ↦ D.paths[(i : ℕ)].walk, ?_, fun i ↦ (hsource _ (List.getElem_mem _)).1,
    fun i ↦ htarget _ (List.getElem_mem _), fun i ↦ D.isPath_walk _ (List.getElem_mem _),
    D.pairwise_disjoint_arrows hf⟩
  -- The value is the total weight of the paths ending in `B`, each of weight one.
  have hval := WeightedWalk.sum_excessAt_sum_map_assignment D.paths B
  rw [← D.pathAssignment_def, List.filter_eq_self.2 fun p hp ↦ decide_eq_true (htarget p hp),
    List.filter_eq_nil_iff.2 fun p hp ↦ by simpa using (hsource p hp).2] at hval
  simp only [D.excessAt_pathAssignment, List.map_nil, List.sum_nil, sub_zero] at hval
  rw [f.val_def, hval, List.map_congr_left fun p hp ↦ D.weight_eq_one_of_mem_paths hf hp,
    List.map_const', List.sum_replicate, nsmul_one]

/-- **Menger's theorem for arrow-disjoint directed paths between vertex sets.** Let `A` and `B` be
disjoint sets of vertices of a finite arrow family. Some family of `k` directed paths, the `i`-th
from `a i ∈ A` to `b i ∈ B` with its other vertices in neither `A` nor `B`, no two of which
traverse a common arrow, and some set of `k` arrows whose deletion leaves no vertex of `B` reachable
from a vertex of `A` exist. By `TauCeti.card_le_card_of_forall_not_reachableWithout`, the family
is then largest and the set of arrows smallest. -/
theorem exists_paths_setArrowSeparator_card_eq [Finite V] [∀ x y, Finite (Q x y)]
    {A B : Finset V} (hAB : Disjoint A B) :
    ∃ (k : ℕ) (a b : Fin k → V) (P : ∀ i, ArrowWalk Q (a i) (b i)) (F : Finset (Σ x y, Q x y)),
      (∀ i, a i ∈ A) ∧ (∀ i, b i ∈ B) ∧ (∀ i, (P i).IsPath) ∧
      (∀ i, ∀ v ∈ (P i).vertices, v ≠ a i → v ≠ b i → v ∉ A ∧ v ∉ B) ∧
      (Pairwise fun i j ↦ (P i).arrows.Disjoint (P j).arrows) ∧
      (∀ a ∈ A, ∀ b ∈ B, ¬ReachableWithout (F : Set (Σ x y, Q x y)) a b) ∧ #F = k := by
  classical
  have := Fintype.ofFinite V
  have (x y : V) : Fintype (Q x y) := Fintype.ofFinite _
  -- A maximum `A`–`B` flow for unit capacities has the value of an `A`–`B` cut `S`: the number of
  -- arrows leaving `S`, which separate `B` from `A`.
  obtain ⟨f, S, hS, hval⟩ :=
    SetFlow.exists_val_eq_arrowSum hAB (cap := (1 : Assignment Q ℤ)) fun _ _ _ ↦ zero_le_one
  obtain ⟨k, a, b, P, hk, ha, hb, -, hdisj⟩ := f.exists_paths_card_eq_val fun _ _ e ↦ f.le_cap e
  -- Trim every path to an `A`–`B` path, which traverses only arrows of the original path.
  have h (i : Fin k) : ∃ a' ∈ A, ∃ b' ∈ B, ∃ q : ArrowWalk Q a' b', q.IsPath ∧
      q.arrows ⊆ (P i).arrows ∧ ∀ v ∈ q.vertices, v ≠ a' → v ≠ b' → v ∉ A ∧ v ∉ B := by
    obtain ⟨a', ha', b', hb', q, hq, -, hsub, hint⟩ :=
      ArrowWalk.exists_isPath_interior_notMem (A := (A : Set V)) (B := (B : Set V)) (P i) (ha i)
        (hb i)
    exact ⟨a', ha', b', hb', q, hq, hsub, by simpa using hint⟩
  choose a' ha' b' hb' P' hP' hsub hint using h
  refine ⟨k, a', b', P', ({e : Σ x y, Q x y | e.1 ∈ S ∧ e.2.1 ∈ Sᶜ} : Finset _), ha', hb', hP',
    hint, fun i j hij e hei hej ↦ hdisj hij (hsub i hei) (hsub j hej), fun a ha b hb h ↦ ?_, ?_⟩
  · refine disjoint_left.1 hS.disjoint
      (h.mem_of_mem (C := (S : Set V)) (hS.subset ha) fun v w e hv he ↦ ?_) hb
    by_contra hw
    exact he (by simpa using ⟨hv, hw⟩)
  · rw [← Nat.cast_inj (R := ℤ), hk, hval, arrowSum_one]

/-- **Menger's theorem for arrow-disjoint directed paths between vertex sets, predicate form.** Let
`A` and `B` be sets of vertices of a finite arrow family. After deleting any fewer than
`k` arrows, some vertex of `B` stays reachable from some vertex of `A` exactly when there are `k`
directed paths, each from a vertex of `A` to a vertex of `B` with its other vertices in neither `A`
nor `B`, no two of which traverse a common arrow. -/
theorem forall_exists_reachableWithout_iff_exists_paths [Finite V] [∀ x y, Finite (Q x y)]
    {A B : Finset V} (k : ℕ) :
    (∀ F : Finset (Σ x y, Q x y), #F < k →
        ∃ a ∈ A, ∃ b ∈ B, ReachableWithout (F : Set (Σ x y, Q x y)) a b) ↔
      ∃ (a b : Fin k → V) (P : ∀ i, ArrowWalk Q (a i) (b i)), (∀ i, a i ∈ A) ∧
        (∀ i, b i ∈ B) ∧ (∀ i, (P i).IsPath) ∧
        (∀ i, ∀ v ∈ (P i).vertices, v ≠ a i → v ≠ b i → v ∉ A ∧ v ∉ B) ∧
        Pairwise fun i j ↦ (P i).arrows.Disjoint (P j).arrows := by
  refine ⟨fun h ↦ ?_, fun ⟨a, b, P, ha, hb, _, _, hP⟩ F hF ↦ ?_⟩
  · -- If `A` and `B` share a vertex `v`, take `k` copies of the trivial path at `v`.
    rcases em' (Disjoint A B) with hAB | hAB
    · obtain ⟨v, hvA, hvB⟩ := not_disjoint_iff.1 hAB
      exact ⟨fun _ ↦ v, fun _ ↦ v, fun _ ↦ .nil v, fun _ ↦ hvA, fun _ ↦ hvB,
        fun _ ↦ ArrowWalk.isPath_nil v, fun _ w hw h _ ↦ absurd (by simpa using hw) h,
        fun _ _ _ ↦ by simp⟩
    obtain ⟨m, a, b, P, F, ha, hb, hP, hint, hdisj, hF, hFm⟩ :=
      exists_paths_setArrowSeparator_card_eq (Q := Q) hAB
    have hkm : k ≤ m := hFm ▸ not_lt.1 fun hlt ↦
      let ⟨a, ha, b, hb, hab⟩ := h F hlt
      hF a ha b hb hab
    exact ⟨fun i ↦ a (Fin.castLE hkm i), fun i ↦ b (Fin.castLE hkm i),
      fun i ↦ P (Fin.castLE hkm i), fun i ↦ ha _, fun i ↦ hb _, fun i ↦ hP _,
      fun i ↦ hint _, fun i j hij ↦ hdisj fun h ↦ hij (Fin.castLE_injective hkm h)⟩
  · by_contra h
    push Not at h
    exact hF.not_ge (by simpa using card_le_card_of_forall_not_reachableWithout ha hb hP h)

end TauCeti
