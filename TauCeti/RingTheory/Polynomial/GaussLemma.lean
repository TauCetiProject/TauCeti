/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Squarefreeness and relative primality in localizations

Let `φ : R →+* S` be a homomorphism from a commutative semiring into a semiring. A polynomial
over `S` that, if nonzero, is associated to the image of a primitive polynomial over `R` is a
unit as soon as every primitive polynomial whose image divides it is a unit
(`TauCeti.isUnit_of_forall_isPrimitive_map_dvd`). For injective `φ` into a semiring without
zero divisors the converse holds too (`TauCeti.isUnit_iff_forall_isPrimitive_map_dvd`).

Over a GCD domain (by Mathlib's `Polynomial.eq_C_content_mul_primPart`) and over a domain with
well-founded divisibility such as a Noetherian domain (`TauCeti.exists_isPrimitive_eq_C_mul`),
every polynomial is a constant times a primitive polynomial. If `R` is a domain with fraction
field `K` and the integer normalization of a nonzero polynomial over `K` is a constant times a
primitive polynomial, then that polynomial is associated to the image of a primitive polynomial
over `R` (`TauCeti.exists_isPrimitive_associated_map`).

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

open scoped nonZeroDivisors

namespace TauCeti

/-- Let `φ : R →+* S` be a homomorphism from a commutative semiring into a semiring, and let `q`
be a polynomial over `S` that, if nonzero, is associated to the image of a primitive polynomial
over `R`. If every primitive polynomial whose image divides `q` is a unit, then so is `q`. -/
theorem isUnit_of_forall_isPrimitive_map_dvd {R S : Type*} [CommSemiring R] [Semiring S]
    {φ : R →+* S} {q : S[X]}
    (hq : q ≠ 0 → ∃ p : R[X], p.IsPrimitive ∧ Associated (p.map φ) q)
    (h : ∀ q₀ : R[X], q₀.IsPrimitive → q₀.map φ ∣ q → IsUnit q₀) : IsUnit q := by
  rcases subsingleton_or_nontrivial S with _ | _
  · exact isUnit_of_subsingleton _
  have := φ.domain_nontrivial
  obtain ⟨p, hp, hpq⟩ := hq fun h0 ↦ not_isUnit_X (h X monic_X.isPrimitive (h0 ▸ dvd_zero _))
  exact hpq.isUnit_iff.1 ((h p hp hpq.dvd).map (mapRingHom φ))

/-- Let `φ : R →+* S` be an injective homomorphism from a commutative semiring into a semiring
without zero divisors, and let `q` be a polynomial over `S` that, if nonzero, is associated to
the image of a primitive polynomial over `R`. Then `q` is a unit if and only if every primitive
polynomial whose image divides it is a unit. The forward direction is the degree argument of
Mathlib's `Polynomial.IsPrimitive.isUnit_iff_isUnit_map_of_injective`, which is stated for
commutative rings. -/
theorem isUnit_iff_forall_isPrimitive_map_dvd {R S : Type*} [CommSemiring R] [Semiring S]
    [NoZeroDivisors S] {φ : R →+* S} (hφ : Function.Injective φ) {q : S[X]}
    (hq : q ≠ 0 → ∃ p : R[X], p.IsPrimitive ∧ Associated (p.map φ) q) :
    IsUnit q ↔ ∀ q₀ : R[X], q₀.IsPrimitive → q₀.map φ ∣ q → IsUnit q₀ := by
  rcases subsingleton_or_nontrivial S with _ | _
  · have := hφ.subsingleton
    exact iff_of_true (isUnit_of_subsingleton _) fun _ _ _ ↦ isUnit_of_subsingleton _
  refine ⟨fun hu q₀ hq₀ ⟨c, hc⟩ ↦ ?_, isUnit_of_forall_isPrimitive_map_dvd hq⟩
  subst hc
  obtain ⟨hm, hc⟩ := mul_ne_zero_iff.1 hu.ne_zero
  have hdeg := natDegree_mul hm hc
  rw [natDegree_eq_zero_of_isUnit hu, natDegree_map_eq_of_injective hφ] at hdeg
  rw [eq_C_of_natDegree_eq_zero (by omega : q₀.natDegree = 0)] at hq₀ ⊢
  exact isUnit_C.2 (isPrimitive_iff_isUnit_of_C_dvd.1 hq₀ _ dvd_rfl)

/-- Over a commutative semiring in which divisibility is well-founded (for instance a Noetherian
domain), every polynomial is a constant times a primitive polynomial. Over a GCD domain the
same holds by Mathlib's `Polynomial.eq_C_content_mul_primPart`. -/
theorem exists_isPrimitive_eq_C_mul {R : Type*} [CommSemiring R] [WfDvdMonoid R] (g : R[X]) :
    ∃ (c : R) (p : R[X]), p.IsPrimitive ∧ g = C c * p := by
  rcases eq_or_ne g 0 with rfl | hg
  · exact ⟨0, 1, isPrimitive_one, by simp⟩
  obtain ⟨n, hn⟩ : ∃ n, g.coeff n ≠ 0 := ⟨_, mt leadingCoeff_eq_zero.1 hg⟩
  -- Divide out constants as long as possible: a minimal coefficient at `n` is reached.
  obtain ⟨_, ⟨c, p, rfl, rfl⟩, hmin⟩ := WellFounded.has_min ‹WfDvdMonoid R›
    {a | ∃ (c : R) (p : R[X]), g = C c * p ∧ a = p.coeff n} ⟨_, 1, g, by simp, rfl⟩
  refine ⟨c, p, isPrimitive_iff_isUnit_of_C_dvd.2 fun r ⟨q, hq⟩ ↦ ?_, rfl⟩
  by_contra hr
  subst hq
  rw [← mul_assoc, ← C_mul, coeff_C_mul] at hn
  exact hmin _ ⟨c * r, q, by rw [← mul_assoc, ← C_mul], rfl⟩
    ⟨right_ne_zero_of_mul hn, r, hr, by rw [coeff_C_mul, mul_comm]⟩

/-- Let `K` be the fraction field of a domain `R`, and let `f` be a nonzero polynomial over `K`
whose integer normalization is a constant times a primitive polynomial (always the case over a
GCD domain, by `Polynomial.eq_C_content_mul_primPart`, or a domain with well-founded
divisibility, by `TauCeti.exists_isPrimitive_eq_C_mul`). Then `f` is associated to the image of
a primitive polynomial over `R`. -/
theorem exists_isPrimitive_associated_map {R K : Type*} [CommRing R] [IsDomain R] [CommRing K]
    [Algebra R K] [IsFractionRing R K] {f : K[X]} (hf : f ≠ 0)
    (hR : ∃ (c : R) (p : R[X]), p.IsPrimitive ∧
      IsLocalization.integerNormalization R⁰ f = C c * p) :
    ∃ p : R[X], p.IsPrimitive ∧ Associated (p.map (algebraMap R K)) f := by
  obtain ⟨b, hb, hbf⟩ := IsLocalization.integerNormalization_spec R⁰ f
  obtain ⟨c, p, hp, hgp⟩ := hR
  have hc : c ≠ 0 := by
    rintro rfl
    exact hf ((IsLocalization.integerNormalization_eq_zero_iff le_rfl f).1 (by simpa using hgp))
  have hcu : IsUnit (C (algebraMap R K c)) :=
    isUnit_C.2 (IsLocalization.map_units K (⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩ : R⁰))
  refine ⟨p, hp, (associated_unit_mul_left _ _ hcu).symm.trans ?_⟩
  rw [← map_C, ← Polynomial.map_mul, ← hgp, hbf, ← algebraMap_smul K, smul_eq_C_mul]
  exact associated_unit_mul_left _ _ (isUnit_C.2 (IsLocalization.map_units K ⟨b, hb⟩))

end TauCeti

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
