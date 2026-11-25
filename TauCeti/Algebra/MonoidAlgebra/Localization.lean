/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra

/-!
# Localizations of monoid algebras

Let `f : M →* N` be an injective homomorphism of commutative monoids and let `x : M` be an element
whose image is a unit of `N`. When every element of `N` becomes an element of the image of `f`
after multiplying by a sufficiently large power of `f x`, the induced map of monoid algebras
`R[M] → R[N]` is the localization away from the monomial of `x`.

This is the algebraic form of an open immersion of affine monoid schemes: in toric geometry, the
coordinate ring of the affine chart of a face `σ ∩ m^⊥` of a cone `σ` is obtained from the
coordinate ring of `σ` by inverting the monomial of `m`.

Localizing the coefficient ring also localizes the monoid algebra, at the corresponding
constant monomials, for arbitrary commutative monoids and commutative coefficient semirings.

## Main declarations

* `MonoidAlgebra.isLocalization_coefficients`: localization of the coefficient ring.

* `TauCeti.MonoidAlgebra.isLocalization_away_mapDomainRingHom`: the induced map of monoid
  algebras is a localization away from the monomial of `x`.
* `TauCeti.AddMonoidAlgebra.isLocalization_away_mapDomainRingHom`: the same statement for
  additive monoid algebras, where `x` maps to an additive unit and powers become multiples.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.2–1.3.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §1.3.
-/

public section

namespace TauCeti

open MonoidAlgebra

variable (R : Type*) [CommSemiring R] {M N : Type*} [CommMonoid M] [CommMonoid N]

/-- Let `f : M →* N` be an injective homomorphism of commutative monoids, and let `x : M` map to
a unit of `N` such that every element of `N` lands in the image of `f` after multiplication by a
power of `f x`. Then the induced map of monoid algebras `R[M] → R[N]` is the localization away
from the monomial of `x`. -/
theorem MonoidAlgebra.isLocalization_away_mapDomainRingHom (f : M →* N)
    (hf : Function.Injective f) (x : M) (hx : IsUnit (f x))
    (hsurj : ∀ y : N, ∃ n : ℕ, y * f x ^ n ∈ Set.range f) :
    letI := (mapDomainRingHom R f).toAlgebra
    IsLocalization.Away (single x (1 : R)) (MonoidAlgebra R N) := by
  let := (mapDomainRingHom R f).toAlgebra
  have halg (a : MonoidAlgebra R M) :
      algebraMap (MonoidAlgebra R M) (MonoidAlgebra R N) a = mapDomain f a := by
    rw [RingHom.algebraMap_toAlgebra, mapDomainRingHom_apply]
  refine IsLocalization.Away.mk _ ?_ (fun s ↦ ?_) fun a b hab ↦ ?_
  · simpa [halg] using hx.map (of R N)
  · induction s using MonoidAlgebra.induction_linear with
    | zero => exact ⟨0, 0, by simp⟩
    | add s t hs ht =>
      obtain ⟨n, a, ha⟩ := hs
      obtain ⟨k, b, hb⟩ := ht
      refine ⟨n + k, a * single x 1 ^ k + b * single x 1 ^ n, ?_⟩
      simp only [map_add, map_mul, map_pow, ← ha, ← hb]
      ring
    | single y r =>
      obtain ⟨n, z, hz⟩ := hsurj y
      exact ⟨n, single z r, by simp [halg, hz]⟩
  · rw [halg, halg] at hab
    exact ⟨0, by rw [mapDomain_injective hf hab]⟩

section Additive

variable {A B : Type*} [AddCommMonoid A] [AddCommMonoid B]

/-- Let `f : A →+ B` be an injective homomorphism of commutative additive monoids, and let `x : A`
map to an additive unit of `B` such that every element of `B` lands in the image of `f` after
adding a multiple of `f x`. Then the induced map of additive monoid algebras `R[A] → R[B]` is the
localization away from the monomial of `x`. -/
theorem AddMonoidAlgebra.isLocalization_away_mapDomainRingHom (f : A →+ B)
    (hf : Function.Injective f) (x : A) (hx : IsAddUnit (f x))
    (hsurj : ∀ y : B, ∃ n : ℕ, y + n • f x ∈ Set.range f) :
    letI := (AddMonoidAlgebra.mapDomainRingHom R f).toAlgebra
    IsLocalization.Away (AddMonoidAlgebra.single x (1 : R)) (AddMonoidAlgebra R B) := by
  let := (AddMonoidAlgebra.mapDomainRingHom R f).toAlgebra
  have halg (a : AddMonoidAlgebra R A) :
      algebraMap (AddMonoidAlgebra R A) (AddMonoidAlgebra R B) a =
        AddMonoidAlgebra.mapDomain f a := by
    rw [RingHom.algebraMap_toAlgebra, AddMonoidAlgebra.mapDomainRingHom_apply]
  refine IsLocalization.Away.mk _ ?_ (fun s ↦ ?_) fun a b hab ↦ ?_
  · obtain ⟨u, hu⟩ := hx
    refine IsUnit.of_mul_eq_one (AddMonoidAlgebra.single (↑(-u) : B) 1) ?_
    simp [halg, AddMonoidAlgebra.single_mul_single, ← hu, AddMonoidAlgebra.one_def]
  · induction s using AddMonoidAlgebra.induction_linear with
    | zero => exact ⟨0, 0, by simp⟩
    | add s t hs ht =>
      obtain ⟨n, a, ha⟩ := hs
      obtain ⟨k, b, hb⟩ := ht
      refine ⟨n + k, a * AddMonoidAlgebra.single x 1 ^ k + b * AddMonoidAlgebra.single x 1 ^ n, ?_⟩
      simp only [map_add, map_mul, map_pow, ← ha, ← hb]
      ring
    | single y r =>
      obtain ⟨n, z, hz⟩ := hsurj y
      exact ⟨n, AddMonoidAlgebra.single z r, by
        simp [halg, hz, AddMonoidAlgebra.single_pow, AddMonoidAlgebra.single_mul_single]⟩
  · rw [halg, halg] at hab
    exact ⟨0, by rw [AddMonoidAlgebra.mapDomain_injective hf hab]⟩

end Additive

end TauCeti

open scoped AlgebraMonoidAlgebra

variable (R : Type*) [CommSemiring R] {M : Type*} [CommMonoid M]

/-- Localizing the coefficients localizes a commutative monoid algebra at the constant
monomials of the denominators. -/
@[to_additive (dont_translate := R S U)
/-- Localizing the coefficients localizes a commutative additive monoid algebra
at the constant monomials of the denominators. -/]
theorem MonoidAlgebra.isLocalization_coefficients {S : Type*} [CommSemiring S]
    [Algebra R S] (U : Submonoid R) [IsLocalization U S] :
    IsLocalization (Algebra.algebraMapSubmonoid (MonoidAlgebra R M) U)
      (MonoidAlgebra S M) :=
  (Algebra.isLocalization_iff_isPushout U S).mpr inferInstance
