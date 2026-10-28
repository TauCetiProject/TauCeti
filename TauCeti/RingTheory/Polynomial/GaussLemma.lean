/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Squarefreeness and relative primality over the fraction field

Let `R` be a GCD domain with fraction field `K`. Every nonzero polynomial over `K` is, up to
a unit, the image of a primitive polynomial over `R`, and by Gauss's lemma a primitive
polynomial divides a polynomial over `R` as soon as it does so over `K`. Hence a polynomial
over `K` is a unit as soon as every primitive polynomial whose image divides it is a unit
(`Polynomial.isUnit_of_forall_isPrimitive_map_dvd`).

Consequently squarefreeness and relative primality pass from `R[X]` to `K[X]`
(`Squarefree.map_fraction_map`, `IsRelPrime.map_fraction_map`). No primitivity is assumed:
a constant factor of a polynomial over `R` becomes a unit over `K`, so these implications
only lose information. Over `K[X]`, a principal ideal domain, relative primality is the same
as `IsCoprime`, which makes resultants of the images nonzero; this is how the members of a
squarefree basis are shown to have nonzero pairwise resultants
(`Finset.IsSquarefreeBasis.resultant_ne_zero`).

These facts complement Mathlib's
`Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map` and
`Polynomial.IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map`.
-/

public section

open Polynomial

open scoped nonZeroDivisors

variable {R K : Type*} [CommRing R] [IsDomain R] [IsGCDMonoid R] [Field K] [Algebra R K]
  [IsFractionRing R K]

namespace Polynomial

/-- A nonzero polynomial over the fraction field of a GCD domain is a unit as soon as every
primitive polynomial whose image divides it is a unit. -/
theorem isUnit_of_forall_isPrimitive_map_dvd {q : K[X]} (hq : q ≠ 0)
    (h : ∀ q₀ : R[X], q₀.IsPrimitive → q₀.map (algebraMap R K) ∣ q → IsUnit q₀) :
    IsUnit q := by
  let := Classical.arbitrary (NormalizedGCDMonoid R)
  obtain ⟨b, hb, hbq⟩ := IsLocalization.integerNormalization_spec R⁰ q
  apply isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart (R := R) hq
  refine h _ (isPrimitive_primPart _) ?_
  have hb0 : IsUnit (C (algebraMap R K b)) :=
    isUnit_C.2 (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb).isUnit
  rw [← hb0.dvd_mul_left, ← smul_eq_C_mul, algebraMap_smul, ← hbq]
  exact Polynomial.map_dvd _ (primPart_dvd _)

end Polynomial

/-- A squarefree polynomial over a GCD domain stays squarefree over the fraction field. -/
theorem Squarefree.map_fraction_map {p : R[X]} (hp : Squarefree p) :
    Squarefree (p.map (algebraMap R K)) := by
  let := Classical.arbitrary (NormalizedGCDMonoid R)
  have hinj := IsFractionRing.injective R K
  intro q hq
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hp.ne_zero ((Polynomial.map_eq_zero_iff hinj).1 (zero_dvd_iff.1 (by simpa using hq)))
  refine isUnit_of_forall_isPrimitive_map_dvd hq0 fun q₀ hq₀ hdvd ↦ hp q₀ ?_
  refine (hq₀.mul hq₀).dvd_of_fraction_map_dvd_fraction_map (K := K) ?_
  rw [Polynomial.map_mul]
  exact (mul_dvd_mul hdvd hdvd).trans hq

/-- Relatively prime polynomials over a GCD domain stay relatively prime over the fraction
field. -/
theorem IsRelPrime.map_fraction_map {p q : R[X]} (h : IsRelPrime p q) :
    IsRelPrime (p.map (algebraMap R K)) (q.map (algebraMap R K)) := by
  have hinj := IsFractionRing.injective R K
  intro d hdp hdq
  have hd0 : d ≠ 0 := by
    rintro rfl
    have hp := (Polynomial.map_eq_zero_iff hinj).1 (zero_dvd_iff.1 hdp)
    have hq := (Polynomial.map_eq_zero_iff hinj).1 (zero_dvd_iff.1 hdq)
    exact not_isRelPrime_zero_zero (hp ▸ hq ▸ h)
  exact isUnit_of_forall_isPrimitive_map_dvd hd0 fun d₀ hd₀ hdvd ↦
    h (hd₀.dvd_of_fraction_map_dvd_fraction_map (hdvd.trans hdp))
      (hd₀.dvd_of_fraction_map_dvd_fraction_map (hdvd.trans hdq))
