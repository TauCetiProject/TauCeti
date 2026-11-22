/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Squarefreeness and relative primality over the fraction field

Let `φ : R →+* S` be an injective homomorphism from a commutative semiring into a semiring
without zero divisors. A nonzero polynomial over `S` that is associated to the image of a
primitive polynomial over `R` is a unit exactly when every primitive polynomial whose image
divides it is a unit (`TauCeti.isUnit_iff_forall_isPrimitive_map_dvd`).

Over a GCD domain (by Mathlib's `Polynomial.eq_C_content_mul_primPart`) and over a domain with
well-founded divisibility such as a Noetherian domain (`TauCeti.exists_isPrimitive_eq_C_mul`),
every polynomial is a constant times a primitive polynomial. For such a domain `R` with
fraction field `K`, every nonzero polynomial over `K` is therefore associated to the image of a
primitive polynomial over `R` (`TauCeti.exists_isPrimitive_associated_map`).

Over a GCD domain, Gauss's lemma also says that a primitive polynomial divides a polynomial
over `R` as soon as it does so over `K`. Consequently squarefreeness and relative primality pass
from `R[X]` to `K[X]` (`Squarefree.map_fraction_map`,
`IsRelPrime.map_fraction_map`). No primitivity is assumed: a constant factor of a polynomial
over `R` becomes a unit over `K`, so these implications only lose information. Over `K[X]`, a
principal ideal domain, relative primality is the same as `IsCoprime`, which makes resultants
of the images nonzero; this is how the members of a squarefree basis are shown to have nonzero
pairwise resultants (`Finset.IsSquarefreeBasis.resultant_ne_zero`).

These facts complement Mathlib's
`Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map` and
`Polynomial.IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map`.
-/

public section

open Polynomial

open scoped nonZeroDivisors

namespace TauCeti

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
  refine ⟨fun hu q₀ hq₀ ⟨c, hc⟩ ↦ ?_, fun h ↦ ?_⟩
  · subst hc
    obtain ⟨hm, hc⟩ := mul_ne_zero_iff.1 hu.ne_zero
    have hdeg := natDegree_mul hm hc
    rw [natDegree_eq_zero_of_isUnit hu, natDegree_map_eq_of_injective hφ] at hdeg
    rw [eq_C_of_natDegree_eq_zero (by omega : q₀.natDegree = 0)] at hq₀ ⊢
    exact isUnit_C.2 (isPrimitive_iff_isUnit_of_C_dvd.1 hq₀ _ dvd_rfl)
  · have := φ.domain_nontrivial
    obtain ⟨p, hp, hpq⟩ :=
      hq fun h0 ↦ not_isUnit_X (h X monic_X.isPrimitive (h0 ▸ dvd_zero _))
    exact hpq.isUnit_iff.1 ((h p hp hpq.dvd).map (mapRingHom φ))

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

end TauCeti

variable {R K : Type*} [CommRing R] [CommRing K] [Algebra R K] [IsFractionRing R K]

/-- Let `K` be the fraction field of a domain `R` in which every polynomial is a constant times a
primitive polynomial (a GCD domain, by `Polynomial.eq_C_content_mul_primPart`, or a domain with
well-founded divisibility, by `TauCeti.exists_isPrimitive_eq_C_mul`). Then every nonzero
polynomial over `K` is associated to the image of a primitive polynomial over `R`. -/
theorem TauCeti.exists_isPrimitive_associated_map [IsDomain R]
    (hR : ∀ g : R[X], ∃ (c : R) (p : R[X]), p.IsPrimitive ∧ g = C c * p) {f : K[X]}
    (hf : f ≠ 0) : ∃ p : R[X], p.IsPrimitive ∧ Associated (p.map (algebraMap R K)) f := by
  obtain ⟨b, hb, hbf⟩ := IsLocalization.integerNormalization_spec R⁰ f
  obtain ⟨c, p, hp, hgp⟩ := hR (IsLocalization.integerNormalization R⁰ f)
  have hc : c ≠ 0 := by
    rintro rfl
    exact hf ((IsLocalization.integerNormalization_eq_zero_iff le_rfl f).1 (by simpa using hgp))
  have hcu : IsUnit (C (algebraMap R K c)) :=
    isUnit_C.2 (IsLocalization.map_units K (⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩ : R⁰))
  refine ⟨p, hp, (associated_unit_mul_left _ _ hcu).symm.trans ?_⟩
  rw [← map_C, ← Polynomial.map_mul, ← hgp, hbf, ← algebraMap_smul K, smul_eq_C_mul]
  exact associated_unit_mul_left _ _ (isUnit_C.2 (IsLocalization.map_units K ⟨b, hb⟩))

variable [IsGCDMonoid R]

/-- A squarefree polynomial over a GCD domain stays squarefree over the fraction field. -/
theorem Squarefree.map_fraction_map {p : R[X]} (hp : Squarefree p) :
    Squarefree (p.map (algebraMap R K)) := by
  obtain _ | _ := (isCancelMulZero_iff_isDomain_or_subsingleton R).1 (IsGCDMonoid.isCancelMulZero R)
  swap
  · have := (algebraMap R K).codomain_trivial
    exact fun _ _ ↦ isUnit_of_subsingleton _
  let := Classical.arbitrary (NormalizedGCDMonoid R)
  let : Field K := IsFractionRing.toField R
  intro q hq
  refine (TauCeti.isUnit_iff_forall_isPrimitive_map_dvd (IsFractionRing.injective R K)
    (TauCeti.exists_isPrimitive_associated_map fun g ↦
      ⟨_, _, g.isPrimitive_primPart, g.eq_C_content_mul_primPart⟩)).2
    fun q₀ hq₀ hdvd ↦ hp q₀ ?_
  refine (hq₀.mul hq₀).dvd_of_fraction_map_dvd_fraction_map (K := K) ?_
  rw [Polynomial.map_mul]
  exact (mul_dvd_mul hdvd hdvd).trans hq

/-- Relatively prime polynomials over a GCD domain stay relatively prime over the fraction
field. -/
theorem IsRelPrime.map_fraction_map {p q : R[X]} (h : IsRelPrime p q) :
    IsRelPrime (p.map (algebraMap R K)) (q.map (algebraMap R K)) := by
  obtain _ | _ := (isCancelMulZero_iff_isDomain_or_subsingleton R).1 (IsGCDMonoid.isCancelMulZero R)
  swap
  · have := (algebraMap R K).codomain_trivial
    exact fun _ _ _ ↦ isUnit_of_subsingleton _
  let := Classical.arbitrary (NormalizedGCDMonoid R)
  let : Field K := IsFractionRing.toField R
  intro d hdp hdq
  exact (TauCeti.isUnit_iff_forall_isPrimitive_map_dvd (IsFractionRing.injective R K)
    (TauCeti.exists_isPrimitive_associated_map fun g ↦
      ⟨_, _, g.isPrimitive_primPart, g.eq_C_content_mul_primPart⟩)).2 fun d₀ hd₀ hdvd ↦
      h (hd₀.dvd_of_fraction_map_dvd_fraction_map (hdvd.trans hdp))
        (hd₀.dvd_of_fraction_map_dvd_fraction_map (hdvd.trans hdq))
