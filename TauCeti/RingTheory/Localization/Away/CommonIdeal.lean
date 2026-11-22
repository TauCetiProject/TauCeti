/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Localization.Away.Basic

/-!
# Localizing away from an element of a common ideal

Let `f : A →+* B` be a ring homomorphism and `I` an ideal of `A` that `f` maps bijectively onto
an ideal of `B`: the image `f(I)` is already the ideal `I.map f`, and `ker f ∩ I = 0`. Then for
every `t ∈ I` the induced map `A_t → B_{f t}` of localizations away from `t` and `f t` is a ring
isomorphism. Geometrically, `Spec B → Spec A` is an isomorphism over the basic open `D(t)`.

The typical example is a subring `A` of `B` and an ideal of `B` contained in `A`, such as the
conductor of `A` in `B`. Then `A` and `B` agree away from that ideal. This is the step in
Ferrand's construction of pinched schemes showing that a pinching does not change the scheme
away from the pinched locus.

Neither `f` nor `t` need be injective or regular: `t` may be a zero divisor or nilpotent, in
which case the localizations are zero rings, and `f` may have a kernel as long as it meets `I`
trivially.

## Main definitions

* `IsLocalization.Away.mapRingEquivOfMemIdeal`: the ring isomorphism `A_t ≃+* B_{f t}` whose
  underlying map is `IsLocalization.Away.map`.

## Main results

* `TauCeti.mul_eq_zero_of_ker_inf_eq_bot`: if `ker f ∩ I = 0`, every element of `I` kills
  every element of `ker f`.
* `IsLocalization.Away.map_injective_of_ker_inf_eq_bot`: the map `A_t → B_{f t}` is injective
  when `ker f ∩ I = 0`.
* `IsLocalization.Away.map_surjective_of_coe_map_subset_range`: it is surjective when every
  element of the ideal `I.map f` lies in the image of `f`.
* `IsLocalization.Away.map_bijective_of_mem_ideal`: under both conditions it is bijective.
* `IsLocalization.Away.mapRingEquivOfMemIdeal_symm_algebraMap_eq_mk'`: the inverse sends `b`
  to `a / t` for any `a : A` with `f a = f t * b`.

## References

* D. Ferrand, *Conducteur, descente et pincement*, Bull. Soc. Math. France 131 (2003),
  Lemme 1.3 and the proof of Théorème 5.1.
-/

public section

namespace TauCeti

variable {A B : Type*} [CommRing A] [CommRing B] {f : A →+* B} {I : Ideal A}

/-- If `f` is injective on the ideal `I`, that is `ker f ∩ I = 0`, then every element of `I`
kills every element of `ker f`: the product lies in both. -/
theorem mul_eq_zero_of_ker_inf_eq_bot (hker : RingHom.ker f ⊓ I = ⊥) {t a : A} (ht : t ∈ I)
    (ha : f a = 0) : t * a = 0 := by
  have h : t * a ∈ RingHom.ker f ⊓ I := ⟨by simp [RingHom.mem_ker, ha], I.mul_mem_right a ht⟩
  rwa [hker, Ideal.mem_bot] at h

end TauCeti

namespace IsLocalization.Away

section Semiring

variable {A B : Type*} [CommSemiring A] [CommSemiring B] {f : A →+* B} {t : A} {I : Ideal A}
variable (S Q : Type*) [CommSemiring S] [CommSemiring Q] [Algebra A S] [Algebra B Q]
  [IsLocalization.Away t S] [IsLocalization.Away (f t) Q]

/-- If every element of the ideal `I.map f` lies in the image of `f` and `t ∈ I`, then
`A_t → B_{f t}` is surjective. This holds in particular when `f(I)` is already the ideal
`I.map f`. -/
theorem map_surjective_of_coe_map_subset_range (hrange : (I.map f : Set B) ⊆ Set.range f)
    (ht : t ∈ I) : Function.Surjective (map S Q f t) := by
  refine (map_surjective_iff S Q f t).mpr fun b ↦ ?_
  -- `f t * b` lies in the ideal `I.map f`, hence is the image of some `a`
  obtain ⟨a, ha⟩ := hrange ((I.map f).mul_mem_right b (Ideal.mem_map_of_mem f ht))
  exact ⟨a, 1, by rw [ha, pow_one]⟩

end Semiring

variable {A B : Type*} [CommRing A] [CommRing B] {f : A →+* B} {I : Ideal A} {t : A}
variable (S Q : Type*) [CommRing S] [CommRing Q] [Algebra A S] [Algebra B Q]
  [IsLocalization.Away t S] [IsLocalization.Away (f t) Q]

/-- If `ker f ∩ I = 0` and `t ∈ I`, then `A_t → B_{f t}` is injective. -/
theorem map_injective_of_ker_inf_eq_bot (hker : RingHom.ker f ⊓ I = ⊥) (ht : t ∈ I) :
    Function.Injective (map S Q f t) :=
  (map_injective_iff (S := S) Q f t).mpr fun _ ha ↦
    ⟨1, by simpa using TauCeti.mul_eq_zero_of_ker_inf_eq_bot hker ht ha⟩

/-- **Ferrand's localization of a common ideal.** If `f` is injective on the ideal `I` and every
element of the ideal `I.map f` lies in the image of `f`, then for `t ∈ I` the induced map
`A_t → B_{f t}` is bijective. This holds in particular when `f` maps `I` bijectively onto the
ideal `I.map f`. -/
theorem map_bijective_of_mem_ideal (hker : RingHom.ker f ⊓ I = ⊥)
    (hrange : (I.map f : Set B) ⊆ Set.range f) (ht : t ∈ I) : Function.Bijective (map S Q f t) :=
  ⟨map_injective_of_ker_inf_eq_bot S Q hker ht,
    map_surjective_of_coe_map_subset_range S Q hrange ht⟩

/-- The ring isomorphism `A_t ≃+* B_{f t}` of `IsLocalization.Away.map_bijective_of_mem_ideal`,
for `f` injective on the ideal `I` with `I.map f` contained in the image of `f`, and `t ∈ I`. -/
noncomputable def mapRingEquivOfMemIdeal (hker : RingHom.ker f ⊓ I = ⊥)
    (hrange : (I.map f : Set B) ⊆ Set.range f) (ht : t ∈ I) : S ≃+* Q :=
  RingEquiv.ofBijective (map S Q f t) (map_bijective_of_mem_ideal S Q hker hrange ht)

variable {S Q} (hker : RingHom.ker f ⊓ I = ⊥) (hrange : (I.map f : Set B) ⊆ Set.range f)
  (ht : t ∈ I)

@[simp]
theorem coe_mapRingEquivOfMemIdeal :
    ⇑(mapRingEquivOfMemIdeal S Q hker hrange ht) = map S Q f t :=
  RingEquiv.coe_ofBijective _ _

@[simp]
theorem mapRingEquivOfMemIdeal_algebraMap (a : A) :
    mapRingEquivOfMemIdeal S Q hker hrange ht (algebraMap A S a) = algebraMap B Q (f a) := by
  simp

@[simp]
theorem mapRingEquivOfMemIdeal_symm_algebraMap (a : A) :
    (mapRingEquivOfMemIdeal S Q hker hrange ht).symm (algebraMap B Q (f a)) =
      algebraMap A S a := by
  rw [RingEquiv.symm_apply_eq, mapRingEquivOfMemIdeal_algebraMap]

/-- The inverse of `A_t ≃+* B_{f t}` sends `b` to the fraction `a / t` for any `a : A` with
`f a = f t * b`. Such an `a` exists by the range condition, but it need not lie in `I` or be
unique; the fraction `a / t` does not depend on the choice. -/
theorem mapRingEquivOfMemIdeal_symm_algebraMap_eq_mk' {a : A} {b : B} (hab : f a = f t * b) :
    (mapRingEquivOfMemIdeal S Q hker hrange ht).symm (algebraMap B Q b) =
      IsLocalization.mk' S a (⟨t, Submonoid.mem_powers t⟩ : Submonoid.powers t) := by
  rw [RingEquiv.symm_apply_eq]
  simp [map_mk', IsLocalization.eq_mk'_iff_mul_eq, ← map_mul, hab, mul_comm]

end IsLocalization.Away
