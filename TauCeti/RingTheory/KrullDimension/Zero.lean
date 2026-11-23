/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Units and injective homomorphisms out of zero-dimensional rings

In a commutative ring `R` of Krull dimension at most zero, such as an Artinian ring, every prime
ideal is maximal and hence minimal. An element of a minimal prime is a zero divisor, so a
non-zero-divisor of `R` lies in no maximal ideal: the units of `R` are exactly its
non-zero-divisors (`TauCeti.isUnit_iff_mem_nonZeroDivisors_of_krullDimLE_zero`). This generalizes
Mathlib's `IsArtinianRing.isUnit_iff_mem_nonZeroDivisors`.

Let `g : R →+* S` be an injective ring homomorphism. An injective homomorphism reflects
non-zero-divisors, so when `R` is zero-dimensional it reflects units
(`TauCeti.isUnit_map_iff_of_injective_of_krullDimLE_zero`). A minimal prime of the source of an
injective homomorphism is the preimage of a prime of the target (Stacks 00FK), so when `R` is
zero-dimensional the induced map of prime spectra is surjective
(`PrimeSpectrum.comap_surjective_of_injective_of_krullDimLE_zero`). For a reduced Artinian ring
`R`, the finite product of its residue fields, this says that each of these fields embeds into a
residue field of `S`. No hypothesis on `S` is needed in either statement.

These apply to the induced map of total rings of fractions along an injective ring homomorphism,
when the source total ring of fractions is Artinian.
-/

public section

open scoped nonZeroDivisors

variable {R S : Type*} [CommRing R] [CommRing S] [Ring.KrullDimLE 0 R]

namespace TauCeti

/-- In a ring of Krull dimension at most zero, an element is a unit exactly when it is a
non-zero-divisor. -/
theorem isUnit_iff_mem_nonZeroDivisors_of_krullDimLE_zero {x : R} : IsUnit x ↔ x ∈ R⁰ := by
  refine ⟨IsUnit.mem_nonZeroDivisors, fun hx ↦ by_contra fun hu ↦ ?_⟩
  obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits hu
  have := hm.isPrime
  exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hxm
    (Ideal.mem_minimalPrimes_of_krullDimLE_zero m) hx

/-- An injective ring homomorphism out of a ring of Krull dimension at most zero reflects units. -/
theorem isUnit_map_iff_of_injective_of_krullDimLE_zero {g : R →+* S}
    (hg : Function.Injective g) {x : R} : IsUnit (g x) ↔ IsUnit x :=
  ⟨fun hx ↦ isUnit_iff_mem_nonZeroDivisors_of_krullDimLE_zero.2 <|
    mem_nonZeroDivisors_of_injective hg hx.mem_nonZeroDivisors, fun hx ↦ hx.map g⟩

end TauCeti

/-- An injective ring homomorphism out of a ring of Krull dimension at most zero induces a
surjective map of prime spectra: every prime ideal of the source is the preimage of a prime ideal
of the target. -/
theorem PrimeSpectrum.comap_surjective_of_injective_of_krullDimLE_zero {g : R →+* S}
    (hg : Function.Injective g) : Function.Surjective (PrimeSpectrum.comap g) := fun p ↦ by
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective hg p.asIdeal
    (Ideal.mem_minimalPrimes_of_krullDimLE_zero p.asIdeal)
  exact ⟨⟨q, hq⟩, PrimeSpectrum.ext hqp⟩
