/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Support

import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.Tactic.ENatToNat

/-!
# Primes of small height in the support of a torsion module

A finitely generated torsion module `M` over a noetherian ring `A` vanishes at every minimal prime
of `A`, so every prime of height at most one in its support is minimal over the annihilator of
`M`. Hence there are only finitely many such primes
(`Module.IsTorsion.finite_setOf_mem_support_height_le_one`). Over a noetherian normal domain these
are the height-one primes at which the characteristic divisor of `M` is supported, and the
finiteness is what makes prime avoidance available for them.
-/

public section

namespace Module.IsTorsion

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- A torsion module vanishes at every minimal prime of the ring: elements of a minimal prime are
zero divisors. -/
theorem notMem_support_of_mem_minimalPrimes (hM : Module.IsTorsion A M) {𝔭 : PrimeSpectrum A}
    (h𝔭 : 𝔭.asIdeal ∈ minimalPrimes A) : 𝔭 ∉ Module.support A M := by
  refine Module.notMem_support_iff'.mpr fun m ↦ ?_
  obtain ⟨⟨s, hs⟩, hsm⟩ := @hM m
  exact ⟨s, fun h ↦ notMem_nonZeroDivisors_of_mem_mem_minimalPrimes h h𝔭 hs, hsm⟩

/-- A finitely generated torsion module over a noetherian ring has only finitely many primes of
height at most one in its support. -/
theorem finite_setOf_mem_support_height_le_one [IsNoetherianRing A] [Module.Finite A M]
    (hM : Module.IsTorsion A M) :
    {𝔭 ∈ Module.support A M | 𝔭.asIdeal.height ≤ 1}.Finite := by
  -- Every such prime is minimal over the annihilator of `M`: a prime strictly below it has
  -- height zero, so it is a minimal prime of `A`, where `M` vanishes.
  have hinj : Function.Injective (PrimeSpectrum.asIdeal (R := A)) := fun _ _ h ↦ PrimeSpectrum.ext h
  refine ((Ideal.finite_minimalPrimes_of_isNoetherianRing A (Module.annihilator A M)).preimage
    hinj.injOn).subset ?_
  rintro 𝔭 ⟨hmem, hht⟩
  refine ⟨⟨𝔭.isPrime, Module.mem_support_iff_of_finite.mp hmem⟩, fun 𝔮 ⟨h𝔮, hann⟩ hle ↦ ?_⟩
  by_contra hne
  have hlt : 𝔮 < 𝔭.asIdeal := lt_of_le_of_ne hle fun h ↦ hne (h ▸ le_rfl)
  have h0 : 𝔮.height = 0 := by
    have := (Ideal.height_add_one_le_of_lt_of_isPrime hlt).trans hht
    generalize 𝔮.height = n at this ⊢
    enat_to_nat
    omega
  exact hM.notMem_support_of_mem_minimalPrimes (𝔭 := ⟨𝔮, h𝔮⟩) (Ideal.height_eq_zero_iff.mp h0)
    (Module.mem_support_iff_of_finite.mpr hann)

end Module.IsTorsion
