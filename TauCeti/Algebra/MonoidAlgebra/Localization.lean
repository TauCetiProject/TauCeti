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
