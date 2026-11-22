/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Squarefreeness and relative primality in localizations

In a decomposition monoid, relatively prime elements stay relatively prime in every
localization, and with cancellation squarefree elements stay squarefree
(`Submonoid.LocalizationMap.map_isRelPrime`, `Submonoid.LocalizationMap.map_squarefree`).
Since polynomials over a GCD domain `R` form a GCD monoid (Mathlib's form of Gauss's lemma) and
`S[X]` is a localization of `R[X]` whenever `S` is a localization of `R`, squarefreeness and
relative primality pass from `R[X]` to `S[X]` (`Squarefree.map_localization_map`,
`IsRelPrime.map_localization_map`); the fraction field is the main case. No primitivity is
assumed: a constant factor of a polynomial over `R` may become a unit over `S`, so these
implications only lose information. Over `K[X]` for a field `K`, a principal ideal domain,
relative primality is the same as `IsCoprime`, which makes resultants of the images nonzero; this
is how the members of a squarefree basis are shown to have nonzero pairwise resultants
(`Finset.IsSquarefreeBasis.resultant_ne_zero`).

These facts complement Mathlib's
`Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map` and
`Polynomial.IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map`.
-/

public section

open Polynomial

namespace Submonoid.LocalizationMap

variable {M N : Type*} [CommMonoidWithZero M] {S : Submonoid M} [CommMonoid N]
  (f : LocalizationMap S N)

/-- In a decomposition monoid, relatively prime elements stay relatively prime in every
localization. -/
theorem map_isRelPrime [DecompositionMonoid M] {x y : M} (h : IsRelPrime x y) :
    IsRelPrime (f x) (f y) := by
  intro d hx hy
  obtain ⟨⟨a, s⟩, hd⟩ := f.surj d
  have hs := f.map_units s
  refine isUnit_of_mul_isUnit_left (hd ▸ f.map_isUnit_iff.2 ?_)
  obtain ⟨m₁, hm₁, ha₁⟩ := f.map_dvd_map.1 (hd ▸ hs.mul_right_dvd.2 hx)
  obtain ⟨m₂, hm₂, ha₂⟩ := f.map_dvd_map.1 (hd ▸ hs.mul_right_dvd.2 hy)
  obtain ⟨a₁, a₂, h₁, h₂, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul ha₁
  exact ⟨m₁ * m₂, mul_mem hm₁ hm₂, mul_dvd_mul h₁
    ((h.of_dvd_left h₂).dvd_of_dvd_mul_right ((dvd_mul_left a₂ a₁).trans ha₂))⟩

/-- In a cancellative decomposition monoid, squarefree elements stay squarefree in every
localization. -/
theorem map_squarefree [IsCancelMulZero M] [DecompositionMonoid M] {x : M} (hx : Squarefree x) :
    Squarefree (f x) := by
  intro d hd
  obtain ⟨⟨a, s⟩, hda⟩ := f.surj d
  have hs := f.map_units s
  refine isUnit_of_mul_isUnit_left (hda ▸ f.map_isUnit_iff.2 ?_)
  obtain ⟨m, hm, ham⟩ := f.map_dvd_map.1 (show f (a * a) ∣ f x by
    rwa [map_mul, ← hda, mul_mul_mul_comm, (hs.mul hs).mul_right_dvd])
  exact ⟨m, hm, hx.dvd_of_squarefree_of_mul_dvd_mul_left ham⟩

end Submonoid.LocalizationMap

variable {R S : Type*} [CommRing R] [IsGCDMonoid R] [CommSemiring S] [Algebra R S]

attribute [local instance] Polynomial.algebra Polynomial.isLocalization in
/-- A squarefree polynomial over a GCD domain stays squarefree over every localization, in
particular over the fraction field. -/
theorem Squarefree.map_localization_map (M : Submonoid R) [IsLocalization M S] {p : R[X]}
    (hp : Squarefree p) :
    Squarefree (p.map (algebraMap R S)) :=
  have := IsGCDMonoid.isCancelMulZero R[X]
  (IsLocalization.toLocalizationMap (M.map C) S[X]).map_squarefree hp

attribute [local instance] Polynomial.algebra Polynomial.isLocalization in
/-- Relatively prime polynomials over a GCD domain stay relatively prime over every
localization, in particular over the fraction field. -/
theorem IsRelPrime.map_localization_map (M : Submonoid R) [IsLocalization M S] {p q : R[X]}
    (h : IsRelPrime p q) :
    IsRelPrime (p.map (algebraMap R S)) (q.map (algebraMap R S)) :=
  (IsLocalization.toLocalizationMap (M.map C) S[X]).map_isRelPrime h
