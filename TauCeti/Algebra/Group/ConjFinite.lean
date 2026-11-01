/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.GroupTheory.ClassEquation

/-!
# Sizes of conjugacy classes

Two elementary facts about the carrier of a conjugacy class: the class of the identity is the
singleton `{1}`, and every class of a finite monoid is nonempty. The class equation then counts the
conjugacy classes of a finite group whose noncentral classes all have two elements, as happens for
groups `G` with a central element `ε` of order two such that every noncentral `x` is conjugate to
`ε * x` and to nothing else: there are `(|G| + |Z(G)|) / 2` classes.

## Main results

* `TauCeti.ConjClasses.carrier_mk_one`: the class of `1` is `{1}`, with its counting form
  `TauCeti.ConjClasses.card_carrier_mk_one`.
* `TauCeti.ConjClasses.card_carrier_pos`: a conjugacy class of a finite monoid has positive size.
* `TauCeti.ConjClasses.natCard_eq_natCard_center_add_ncard_noncenter`: the classes of a finite
  group are its central elements and its nontrivial classes.
* `TauCeti.ConjClasses.two_mul_natCard_eq_of_forall_noncenter`: if every nontrivial class has two
  elements, then twice the number of classes is `|G| + |Z(G)|`.
-/

public section

namespace TauCeti

namespace ConjClasses

variable {G : Type*} [Monoid G]

/-- **The conjugacy class of the identity is the singleton `{1}`**: an element conjugate to `1` is
`1`. -/
@[simp]
theorem carrier_mk_one : (_root_.ConjClasses.mk (1 : G)).carrier = {1} := by
  ext g
  rw [_root_.ConjClasses.mem_carrier_iff_mk_eq, _root_.ConjClasses.mk_eq_mk_iff_isConj,
    isConj_one_left, Set.mem_singleton_iff]

/-- **The identity conjugacy class has exactly one element.** This is the weight that normalizes the
identity column of a character table.

This is not a `@[simp]` lemma: `Nat.card` of a coerced set is not in simp normal form, `Set.ncard`
being what `Nat.card_coe_set_eq` rewrites it to. -/
theorem card_carrier_mk_one : Nat.card (_root_.ConjClasses.mk (1 : G)).carrier = 1 := by
  rw [carrier_mk_one]
  simp

/-- **A conjugacy class of a finite monoid has positive size.** -/
theorem card_carrier_pos [Finite G] (C : _root_.ConjClasses G) : 0 < Nat.card C.carrier := by
  obtain ⟨g, rfl⟩ := C.exists_rep
  have : Nonempty (_root_.ConjClasses.mk g).carrier := ⟨⟨g, _root_.ConjClasses.mem_carrier_mk⟩⟩
  exact Nat.card_pos

section Group

variable {G : Type*} [Group G]

/-- **The conjugacy classes of a finite group are its central elements and its nontrivial
classes**: a class is a singleton exactly when its element is central. -/
theorem natCard_eq_natCard_center_add_ncard_noncenter [Finite G] :
    Nat.card (_root_.ConjClasses G) =
      Nat.card (Subgroup.center G) + (_root_.ConjClasses.noncenter G).ncard := by
  rw [← Set.ncard_add_ncard_compl (_root_.ConjClasses.noncenter G), add_comm,
    ← (_root_.ConjClasses.mk_bijOn G).ncard_eq, ← SetLike.coe_sort_coe, Nat.card_coe_set_eq]

/-- **Counting conjugacy classes when every nontrivial class has two elements.** If every
noncentral conjugacy class of a finite group `G` has exactly two elements, then twice the number of
conjugacy classes is `|G| + |Z(G)|`. -/
theorem two_mul_natCard_eq_of_forall_noncenter [Finite G]
    (h : ∀ C ∈ _root_.ConjClasses.noncenter G, Nat.card C.carrier = 2) :
    2 * Nat.card (_root_.ConjClasses G) = Nat.card G + Nat.card (Subgroup.center G) := by
  have hfin := (_root_.ConjClasses.noncenter G).toFinite
  have hclass := Group.nat_card_center_add_sum_card_noncenter_eq_card G
  rw [finsum_mem_congr rfl h, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_const,
    smul_eq_mul, ← Set.ncard_eq_toFinset_card _ hfin] at hclass
  rw [natCard_eq_natCard_center_add_ncard_noncenter, ← hclass]
  omega

end Group

end ConjClasses

end TauCeti
