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
proves its identity and composition laws.  It also transports a double-coset space along a group
isomorphism `e : G ≃* G'`, onto the double-coset space of the image subgroups.

These are the double-coset analogues of `Subgroup.quotientMapOfLE` and `QuotientGroup.congr` for
ordinary coset spaces.
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

variable {G' : Type*} [Group G']

/-- Transport of a double-coset space along a group isomorphism `e : G ≃* G'`: the equivalence
`H \ G / K ≃ H' \ G' / K'` when `H'` and `K'` are the images of `H` and `K` under `e`. -/
def quotientCongr (H K : Subgroup G) {H' K' : Subgroup G'} (e : G ≃* G')
    (hH : H.map e = H') (hK : K.map e = K') :
    Quotient (H : Set G) K ≃ Quotient (H' : Set G') K' :=
  Quotient.congr e.toEquiv fun a b ↦ by
    subst hH hK
    rw [rel_iff, rel_iff]
    constructor
    · rintro ⟨h, hh, k, hk, rfl⟩
      exact ⟨e h, Subgroup.mem_map_of_mem _ hh, e k, Subgroup.mem_map_of_mem _ hk, by simp⟩
    · rintro ⟨h', hh', k', hk', hb⟩
      obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hh'
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hk'
      exact ⟨h, hh, k, hk, e.injective (by simpa using hb)⟩

/-- The transported double-coset space sends the double coset of `g` to that of `e g`. -/
@[simp]
theorem quotientCongr_apply_mk (H K : Subgroup G) {H' K' : Subgroup G'} (e : G ≃* G')
    (hH : H.map e = H') (hK : K.map e = K') (g : G) :
    quotientCongr H K e hH hK (mk H K g) = mk H' K' (e g) :=
  (rfl)

/-- The inverse of the transported double-coset space sends the double coset of `g` to that of
`e.symm g`. -/
@[simp]
theorem quotientCongr_symm_apply_mk (H K : Subgroup G) {H' K' : Subgroup G'} (e : G ≃* G')
    (hH : H.map e = H') (hK : K.map e = K') (g : G') :
    (quotientCongr H K e hH hK).symm (mk H' K' g) = mk H K (e.symm g) := by
  rw [Equiv.symm_apply_eq, quotientCongr_apply_mk, MulEquiv.apply_symm_apply]

end DoubleCoset
