/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.ClassEquation
public import TauCeti.Algebra.Group.Conj

/-!
# The class equation for a list of nonconjugate elements

The class equation `Group.sum_card_conj_classes_eq_card` says that the conjugacy classes of a
finite group `G` partition it. Combined with the orbit-stabilizer theorem
`ConjClasses.ncard_carrier_mk`, which identifies the size of the class of `x` with the index of
its centralizer, it gives a **mass criterion** for a candidate list of class representatives.

Let `l` be a list of pairwise nonconjugate elements of `G`. Their classes are distinct, hence
disjoint, so the centralizer indices `[G : C_G(x)]` for `x ∈ l` sum to at most `|G|`; and the sum
equals `|G|` exactly when the classes of the entries of `l` cover `G`.

This is how a complete list of conjugacy-class representatives of a large finite group is
certified in practice: the group order and the order of each centralizer are computed
separately, and the identity `∑ x ∈ l, |G| / |C_G(x)| = |G|` then proves that no class was
missed, without enumerating the group. `Subgroup.index_mul_card` converts centralizer orders into
the indices used here.

## Main statements

* `List.sum_index_centralizer_le_card`: the centralizer indices of a pairwise nonconjugate list
  sum to at most the order of the group.
* `List.sum_index_centralizer_eq_card_iff`: they sum to exactly the order of the group if and only
  if every element of the group is conjugate to an entry of the list.
-/

public section

open scoped BigOperators

variable {G : Type*} [Group G]

namespace List

/-- For a pairwise nonconjugate list, the sum of the centralizer indices of its entries is the
sum of the sizes of the distinct conjugacy classes those entries represent. -/
private theorem sum_index_centralizer_eq_sum_card_carrier [DecidableEq (ConjClasses G)]
    (l : List G) (hl : l.Pairwise fun x y => ¬ IsConj x y) :
    (l.map fun x => (Subgroup.centralizer {x}).index).sum =
      ∑ C ∈ (l.map ConjClasses.mk).toFinset, C.carrier.ncard := by
  have hnodup : (l.map ConjClasses.mk).Nodup :=
    List.Pairwise.map ConjClasses.mk
      (fun x y hxy hmk => hxy (ConjClasses.mk_eq_mk_iff_isConj.mp hmk)) hl
  rw [List.sum_toFinset _ hnodup, List.map_map]
  simp only [Function.comp_def, ConjClasses.ncard_carrier_mk]

/-- **The centralizer indices of pairwise nonconjugate elements sum to at most `|G|`.** Their
conjugacy classes are distinct, hence disjoint, and the class of `x` has `[G : C_G(x)]`
elements. -/
theorem sum_index_centralizer_le_card [Finite G] (l : List G)
    (hl : l.Pairwise fun x y => ¬ IsConj x y) :
    (l.map fun x => (Subgroup.centralizer {x}).index).sum ≤ Nat.card G := by
  classical
  have := Fintype.ofFinite (ConjClasses G)
  rw [sum_index_centralizer_eq_sum_card_carrier l hl, ← Group.sum_card_conj_classes_eq_card,
    finsum_eq_sum_of_fintype]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- **The mass criterion for conjugacy-class representatives.** A list of pairwise nonconjugate
elements of a finite group meets every conjugacy class if and only if the centralizer indices
of its entries sum to the order of the group. -/
theorem sum_index_centralizer_eq_card_iff [Finite G] (l : List G)
    (hl : l.Pairwise fun x y => ¬ IsConj x y) :
    (l.map fun x => (Subgroup.centralizer {x}).index).sum = Nat.card G ↔
      ∀ g : G, ∃ x ∈ l, IsConj x g := by
  classical
  have := Fintype.ofFinite (ConjClasses G)
  set S := (l.map ConjClasses.mk).toFinset
  have hcover : (∀ g : G, ∃ x ∈ l, IsConj x g) ↔ ∀ C, C ∈ S := by
    rw [ConjClasses.forall_isConj]
    refine forall_congr' fun g => ?_
    simp only [S, List.mem_toFinset, List.mem_map, ConjClasses.mk_eq_mk_iff_isConj]
  rw [hcover, sum_index_centralizer_eq_sum_card_carrier l hl,
    ← Group.sum_card_conj_classes_eq_card, finsum_eq_sum_of_fintype,
    ← Finset.sum_sdiff (Finset.subset_univ S), right_eq_add, Finset.sum_eq_zero_iff]
  -- Every class has positive size, so the classes missed by `l` contribute zero only when there
  -- are none.
  refine ⟨fun h => ConjClasses.forall_isConj.mpr fun g => by_contra fun hg => ?_,
    fun h C hC => absurd (h C) (Finset.mem_sdiff.mp hC).2⟩
  have hg' := h _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hg⟩)
  rw [ConjClasses.ncard_carrier_mk] at hg'
  exact Subgroup.index_ne_zero_of_finite hg'

end List
