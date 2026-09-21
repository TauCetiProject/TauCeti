/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.DoubleCoset

/-!
# Maps between double-coset quotients

Enlarging the left subgroup coarsens the double-coset relation.  This file packages the resulting
surjection `H \ G / K → H' \ G / K` for `H ≤ H'`, records its value on representatives, and
proves its identity and composition laws.

This is the double-coset analogue of `Subgroup.quotientMapOfLE` for ordinary coset spaces.
-/

public section

namespace DoubleCoset

variable {G : Type*} [Group G]

/-- The map `H \ G / K → H' \ G / K` induced by an inclusion `H ≤ H'`. -/
def quotientMapOfLELeft {H H' : Subgroup G} (h : H ≤ H') (K : Subgroup G) :
    Quotient (H : Set G) K → Quotient (H' : Set G) K :=
  Quotient.map' id fun _ _ hab ↦ by
    rw [rel_iff] at hab ⊢
    obtain ⟨a, ha, b, hb, hab⟩ := hab
    exact ⟨a, h ha, b, hb, hab⟩

/-- The map induced by `H ≤ H'` sends the double coset of `g` to the double coset of `g`. -/
@[simp]
theorem quotientMapOfLELeft_apply_mk {H H' : Subgroup G} (h : H ≤ H')
    (K : Subgroup G) (g : G) :
    quotientMapOfLELeft h K (mk H K g) = mk H' K g :=
  (rfl)

/-- The double-coset quotient map induced by reflexivity is the identity. -/
@[simp]
theorem quotientMapOfLELeft_refl (H K : Subgroup G) :
    quotientMapOfLELeft (le_refl H) K = id := by
  funext q
  induction q using Quotient.inductionOn' with
  | h g => rw [quotientMapOfLELeft_apply_mk]; rfl

private theorem quotientMapOfLELeft_trans_apply {H H' H'' : Subgroup G} (h : H ≤ H')
    (h' : H' ≤ H'') (K : Subgroup G) (q : Quotient (H : Set G) K) :
    quotientMapOfLELeft (h.trans h') K q =
      quotientMapOfLELeft h' K (quotientMapOfLELeft h K q) := by
  induction q using Quotient.inductionOn' with
  | h g => simp only [quotientMapOfLELeft_apply_mk]

/-- Double-coset quotient maps compose along inclusions of left subgroups. -/
theorem quotientMapOfLELeft_trans {H H' H'' : Subgroup G} (h : H ≤ H') (h' : H' ≤ H'')
    (K : Subgroup G) :
    quotientMapOfLELeft (h.trans h') K =
      quotientMapOfLELeft h' K ∘ quotientMapOfLELeft h K := by
  funext q
  exact quotientMapOfLELeft_trans_apply h h' K q

/-- Enlarging the left subgroup gives a surjection on double-coset quotients. -/
theorem quotientMapOfLELeft_surjective {H H' : Subgroup G} (h : H ≤ H') (K : Subgroup G) :
    Function.Surjective (quotientMapOfLELeft h K) := by
  intro q
  induction q using Quotient.inductionOn' with
  | h g => exact ⟨mk H K g, quotientMapOfLELeft_apply_mk h K g⟩

end DoubleCoset
