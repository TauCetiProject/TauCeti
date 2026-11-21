/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
import TauCeti.Algebra.Group.Submonoid.Finiteness

/-!
# Localizations of monoid algebras

Let `f : M →* N` be an injective homomorphism of commutative monoids and let `x : M` be an element
whose image is a unit of `N`. When every element of `N` becomes an element of the image of `f`
after multiplying by a sufficiently large power of `f x`, the induced map of monoid algebras
`R[M] → R[N]` is the localization away from the monomial of `x`.

Additively, for an injective homomorphism `f : M →+ H` into an abelian group `H`,
`AddMonoidAlgebra.isLocalization_mapDomain_of_single` gives a general criterion for `R[H]` to be a
localization of `R[M]` at a submonoid `T`, and
`AddMonoidAlgebra.exists_isLocalization_away_of_exists_add_eq` specializes to principal
localizations when `M` is finitely generated.

This is the algebraic form of an open immersion of affine monoid schemes: in toric geometry, the
coordinate ring of the affine chart of a face `σ ∩ m^⊥` of a cone `σ` is obtained from the
coordinate ring of `σ` by inverting the monomial of `m`.

Localizing the coefficient ring also localizes the monoid algebra, at the corresponding
constant monomials, for arbitrary commutative monoids and commutative coefficient semirings.

## Main declarations

* `MonoidAlgebra.isLocalization_coefficients`: localization of the coefficient ring.

* `TauCeti.MonoidAlgebra.isLocalization_away_mapDomainRingHom`: the induced map of monoid
  algebras is a localization away from the monomial of `x`.

* `AddMonoidAlgebra.isLocalization_mapDomain_of_single` and
  `AddMonoidAlgebra.exists_isLocalization_away_of_exists_add_eq`: localization criteria for
  additive monoid algebras into an abelian group.

## References

* W. Bruns and J. Gubeladze, *Polytopes, Rings, and K-Theory*, Chapter 2.
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

namespace AddMonoidAlgebra

/-- Let `f : M →+ H` be an injective homomorphism from an additive commutative monoid into an
abelian group, and `T` a submonoid of `R[M]` sent to units of `R[H]`. If every monomial `single g 1`
in `R[H]` clears into the image of `f` by multiplying with `mapDomain f s.1` for some `s : T`, then
`R[H]` is the localization of `R[M]` at `T`. -/
theorem isLocalization_mapDomain_of_single {M H R : Type*} [AddCommMonoid M]
    [AddCommGroup H] [CommSemiring R] {f : M →+ H} (hf : Function.Injective f)
    {T : Submonoid (AddMonoidAlgebra R M)}
    (hunits : ∀ s : T, IsUnit (mapDomain f s.1))
    (hsurj : ∀ g : H, ∃ (a : M) (s : T), single g (1 : R) * mapDomain f s.1 = single (f a) 1) :
    letI := (mapDomainRingHom R f).toAlgebra
    IsLocalization T (AddMonoidAlgebra R H) := by
  let := (mapDomainRingHom R f).toAlgebra
  have halg (p : AddMonoidAlgebra R M) :
      algebraMap _ (AddMonoidAlgebra R H) p = mapDomain f p := by
    rw [RingHom.algebraMap_toAlgebra, mapDomainRingHom_apply]
  refine ⟨⟨fun s ↦ halg s.1 ▸ hunits s, fun p ↦ ?_, fun {_ _} hab ↦ ?_⟩⟩
  · induction p using AddMonoidAlgebra.induction_on with
    | of g =>
      obtain ⟨a, s, hs⟩ := hsurj g
      exact ⟨⟨single a 1, s⟩, by simpa [halg, mapDomain_single] using hs⟩
    | add p q hp hq =>
      obtain ⟨⟨a, s⟩, ha⟩ := hp
      obtain ⟨⟨b, t⟩, hb⟩ := hq
      refine ⟨⟨a * t + b * s, s * t⟩, ?_⟩
      simp only [map_add, map_mul, Submonoid.coe_mul]
      rw [← ha, ← hb]; ring
    | smul r p hp =>
      obtain ⟨⟨a, s⟩, ha⟩ := hp
      exact ⟨⟨r • a, s⟩, by
        rw [smul_mul_assoc, ha]
        exact ((mapDomainAlgHom R R f).toLinearMap.map_smul r a).symm⟩
  · rw [halg, halg] at hab
    exact ⟨1, by simp [mapDomain_injective hf hab]⟩

/-- If `f : M →+ H` is an injective additive homomorphism from a finitely generated additive monoid
`M` into an abelian group `H` such that every element of `H` can be shifted into `f '' M`, then
`R[H]` is a localization of `R[M]` away from a single coefficient-one monomial. -/
theorem exists_isLocalization_away_of_exists_add_eq {M H : Type*}
    [AddCommMonoid M] [AddMonoid.FG M] [AddCommGroup H] {f : M →+ H} (hf : Function.Injective f)
    (hshift : ∀ g : H, ∃ a b : M, g + f b = f a) (R : Type*) [CommSemiring R] :
    ∃ u : M,
      letI := (mapDomainRingHom R f).toAlgebra
      IsLocalization.Away (single u (1 : R)) (AddMonoidAlgebra R H) := by
  have htop : (⊤ : AddSubmonoid M).FG := (AddMonoid.fg_iff_addSubmonoid_fg ⊤).1 inferInstance
  obtain ⟨u, hu⟩ := htop.exists_forall_exists_add_eq_nsmul
  refine ⟨u.1, isLocalization_mapDomain_of_single hf (fun s ↦ ?_) (fun g ↦ ?_)⟩
  · obtain ⟨n, hn⟩ := s.2
    dsimp only at hn
    rw [← hn, single_pow, one_pow, mapDomain_single]
    exact (Group.isUnit (Multiplicative.ofAdd (f (n • u.1)))).map (of R H)
  · obtain ⟨a, b, hab⟩ := hshift g
    obtain ⟨n, c, hbc⟩ := hu ⟨b, trivial⟩
    have hnu : g + n • f u.1 = f (a + c.1) := by
      have hbc' : b + c.1 = n • u.1 := congrArg Subtype.val hbc
      rw [← map_nsmul, ← hbc', map_add, ← add_assoc, hab, ← map_add]
    exact ⟨a + c.1, ⟨single u.1 (1 : R) ^ n, n, rfl⟩, by
      simp [single_pow, single_mul_single, hnu]⟩

end AddMonoidAlgebra
