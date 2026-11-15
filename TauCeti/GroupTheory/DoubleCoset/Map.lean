/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.DoubleCoset

import Mathlib.Tactic.Group

/-!
# Maps between double-coset quotients

Enlarging either subgroup coarsens the double-coset relation.  This file packages the resulting
surjections, records their values on representatives, and proves their identity and composition
laws.  It also transports a double-coset space along a group isomorphism, identifies the
quotients by conjugate right subgroups by right translation, and carries a single double coset
along a multiplicative map: `DoubleCoset.image_doubleCoset` computes the image, and
`DoubleCoset.mem_doubleCoset_image_iff` transports membership along an injective multiplicative
map.

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
    quotientMapOfLELeft (le_refl H) K = id :=
  funext fun q ↦ q.inductionOn' fun _ ↦ rfl

/-- Double-coset quotient maps compose along inclusions of left subgroups. -/
theorem quotientMapOfLELeft_trans {H H' H'' : Subgroup G} (h : H ≤ H') (h' : H' ≤ H'')
    (K : Subgroup G) :
    quotientMapOfLELeft (h.trans h') K =
      quotientMapOfLELeft h' K ∘ quotientMapOfLELeft h K :=
  funext fun q ↦ q.inductionOn' fun _ ↦ rfl

/-- Enlarging the left subgroup gives a surjection on double-coset quotients. -/
theorem quotientMapOfLELeft_surjective {H H' : Subgroup G} (h : H ≤ H') (K : Subgroup G) :
    Function.Surjective (quotientMapOfLELeft h K) :=
  fun q ↦ q.inductionOn' fun g ↦ ⟨mk H K g, rfl⟩

/-- The map `H \ G / K → H \ G / K'` induced by an inclusion `K ≤ K'`. -/
def quotientMapOfLERight (H : Subgroup G) {K K' : Subgroup G} (h : K ≤ K') :
    Quotient (H : Set G) K → Quotient (H : Set G) K' :=
  Quotient.map' id fun _ _ hab ↦ by
    rw [rel_iff] at hab ⊢
    obtain ⟨a, ha, b, hb, hab⟩ := hab
    exact ⟨a, ha, b, h hb, hab⟩

/-- The map induced by `K ≤ K'` sends the double coset of `g` to the double coset of `g`. -/
@[simp]
theorem quotientMapOfLERight_apply_mk (H : Subgroup G) {K K' : Subgroup G} (h : K ≤ K')
    (g : G) : quotientMapOfLERight H h (mk H K g) = mk H K' g :=
  (rfl)

/-- The right double-coset quotient map induced by reflexivity is the identity. -/
@[simp]
theorem quotientMapOfLERight_refl (H K : Subgroup G) :
    quotientMapOfLERight H (le_refl K) = id :=
  funext fun q ↦ q.inductionOn' fun _ ↦ rfl

/-- Double-coset quotient maps compose along inclusions of right subgroups. -/
theorem quotientMapOfLERight_trans {K K' K'' : Subgroup G} (H : Subgroup G)
    (h : K ≤ K') (h' : K' ≤ K'') :
    quotientMapOfLERight H (h.trans h') =
      quotientMapOfLERight H h' ∘ quotientMapOfLERight H h :=
  funext fun q ↦ q.inductionOn' fun _ ↦ rfl

/-- Enlarging the right subgroup gives a surjection on double-coset quotients. -/
theorem quotientMapOfLERight_surjective (H : Subgroup G) {K K' : Subgroup G} (h : K ≤ K') :
    Function.Surjective (quotientMapOfLERight H h) :=
  fun q ↦ q.inductionOn' fun g ↦ ⟨mk H K g, rfl⟩

/-- Right translation by `g` identifies quotients by `K` and by the conjugate `g⁻¹Kg`. -/
def quotientConjRight (H K : Subgroup G) (g : G) :
    Quotient (H : Set G) K ≃
      Quotient (H : Set G)
        (↑(K.map ((MulAut.conj g).symm : G →* G)) : Set G) :=
  Quotient.congr (Equiv.mulRight g) fun x y ↦ by
    rw [rel_iff, rel_iff]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      refine ⟨a, ha, (MulAut.conj g).symm b, Subgroup.mem_map_of_mem _ hb, ?_⟩
      simp only [Equiv.coe_mulRight, MulAut.conj_symm_apply]
      group
    · rintro ⟨a, ha, b, hb, hxy⟩
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hb
      refine ⟨a, ha, c, hc, ?_⟩
      simp only [Equiv.coe_mulRight, MonoidHom.coe_ofClass, MulAut.conj_symm_apply] at hxy
      rw [← mul_left_inj g, hxy]
      group

/-- Right translation sends the double coset of `x` to the double coset of `x * g`.

Not a `simp` lemma: the codomain contains a coerced mapped subgroup, which `simp` rewrites to a
set image in the dependent type. -/
theorem quotientConjRight_apply_mk (H K : Subgroup G) (g x : G) :
    quotientConjRight H K g (mk H K x) =
      mk H (K.map (MulAut.conj g).symm) (x * g) :=
  (rfl)

/-- The inverse conjugation equivalence sends the double coset of `y` to that of `y * g⁻¹`.

Not a `simp` lemma, for the same dependent-type reason as `quotientConjRight_apply_mk`. -/
theorem quotientConjRight_symm_apply_mk (H K : Subgroup G) (g y : G) :
    (quotientConjRight H K g).symm
        (mk H (K.map (MulAut.conj g).symm) y) = mk H K (y * g⁻¹) :=
  (rfl)

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
    (quotientCongr H K e hH hK).symm (mk H' K' g) = mk H K (e.symm g) :=
  (rfl)

variable {α β F : Type*} [Mul α] [Mul β] [FunLike F α β] [MulHomClass F α β]

/-- A multiplicative map sends the double coset of `a` by `s` and `t` onto the double coset of
`f a` by the images of `s` and `t`. -/
theorem image_doubleCoset (f : F) (a : α) (s t : Set α) :
    f '' doubleCoset a s t = doubleCoset (f a) (f '' s) (f '' t) := by
  simp only [doubleCoset, Set.image_mul, Set.image_singleton]

/-- An injective multiplicative map transports membership in a double coset. -/
theorem mem_doubleCoset_image_iff {f : F} (hf : Function.Injective f) (a : α) (s t : Set α)
    (x : α) :
    f x ∈ doubleCoset (f a) (f '' s) (f '' t) ↔ x ∈ doubleCoset a s t := by
  rw [← image_doubleCoset, hf.mem_set_image]

end DoubleCoset
