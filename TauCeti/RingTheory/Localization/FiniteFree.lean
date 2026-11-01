/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Localization.FractionRing
import TauCeti.RingTheory.Flat.NonZeroDivisors
import TauCeti.RingTheory.Norm.NonZeroDivisors

/-!
# Total rings of fractions of finite free algebras

Let `S` be a commutative `R`-algebra that is free of finite rank as an `R`-module, where neither
`R` nor `S` need be a domain. Every non-zero-divisor of `R` stays a non-zero-divisor in `S`, and
every non-zero-divisor `x` of `S` divides the image of its norm, which is a non-zero-divisor of
`R` (`TauCeti.RingTheory.Norm.NonZeroDivisors`). So inverting the non-zero-divisors of `R` already
inverts every non-zero-divisor of `S`: a ring `T` is a total ring of fractions of `S` exactly when
it is the localization of `S` at the image of the non-zero-divisors of `R`
(`IsFractionRing.isLocalization_algebraMapSubmonoid_iff`). In particular the total ring of
fractions of `S` is finite free over that of `R`, and it is an Artinian ring whenever the total
ring of fractions of `R` is (`IsFractionRing.isArtinianRing_of_free`), for instance when `R` is a
domain.

This is how the total ring of fractions of a group ring, or of a ring of Novikov series, over an
abelian group with torsion is reduced to the fraction field of a torsion-free subgroup of finite
index.

## Main results

* `IsFractionRing.isLocalization_algebraMapSubmonoid_iff`: the total rings of fractions of `S` are
  its localizations at the non-zero-divisors of `R`.
* `IsFractionRing.isArtinianRing_of_free`: if the total ring of fractions of `R` is Artinian, so is
  that of `S`.
-/

public section

open scoped nonZeroDivisors

namespace IsFractionRing

variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Free R S]
  [Module.Finite R S] (T : Type*) [CommRing T] [Algebra S T]

/-- A localization of an algebra `S`, finite free over `R`, at the non-zero-divisors of `R` is a
total ring of fractions of `S`. -/
theorem of_isLocalization_algebraMapSubmonoid
    [IsLocalization (Algebra.algebraMapSubmonoid S R⁰) T] : IsFractionRing S T := by
  refine IsLocalization.of_le_of_exists_dvd (Algebra.algebraMapSubmonoid S R⁰) S⁰ ?_ ?_
  · rintro _ ⟨r, hr, rfl⟩
    exact Module.Flat.algebraMap_mem_nonZeroDivisors hr
  · exact fun x hx ↦ ⟨_, Algebra.mem_algebraMapSubmonoid_of_mem
      ⟨_, Algebra.norm_mem_nonZeroDivisors_iff.mpr hx⟩, Algebra.dvd_algebraMap_norm x⟩

/-- For an algebra `S`, finite free over `R`, a ring is a total ring of fractions of `S` exactly
when it is the localization of `S` at the non-zero-divisors of `R`. -/
theorem isLocalization_algebraMapSubmonoid_iff :
    IsLocalization (Algebra.algebraMapSubmonoid S R⁰) T ↔ IsFractionRing S T := by
  refine ⟨fun _ ↦ of_isLocalization_algebraMapSubmonoid R T, fun _ ↦ ?_⟩
  let Sₘ := Localization (Algebra.algebraMapSubmonoid S R⁰)
  have := of_isLocalization_algebraMapSubmonoid R (S := S) Sₘ
  exact IsLocalization.isLocalization_of_algEquiv _ (IsLocalization.algEquiv S⁰ Sₘ T)

/-- If the total ring of fractions of `R` is Artinian, then so is every total ring of fractions
of an algebra `S` that is finite free over `R`. -/
theorem isArtinianRing_of_free [IsArtinianRing (FractionRing R)] [IsFractionRing S T] :
    IsArtinianRing T := by
  -- The localization `Sₘ` of `S` at the non-zero-divisors of `R` is a total ring of fractions of
  -- `S`, and a basis of `S` over `R` is a basis of `Sₘ` over the total ring of fractions of `R`.
  let Sₘ := Localization (Algebra.algebraMapSubmonoid S R⁰)
  have := of_isLocalization_algebraMapSubmonoid R (S := S) Sₘ
  have := Module.Finite.of_basis
    ((Module.Free.chooseBasis R S).localizationLocalization (FractionRing R) R⁰ Sₘ)
  have := IsArtinianRing.of_finite (FractionRing R) Sₘ
  exact (IsLocalization.algEquiv S⁰ Sₘ T).toRingEquiv.isArtinianRing

end IsFractionRing
