/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.LocalProperties.Reduced
public import TauCeti.RingTheory.Ideal.MinimalPrime.Finite

/-!
# Localizations and total quotient rings of reduced rings

Every localization of a reduced ring is reduced (`IsLocalization.isReduced`).

A prime ideal of a reduced Noetherian ring consists of zero divisors exactly when it is minimal
(`Ideal.mem_minimalPrimes_iff_disjoint_nonZeroDivisors`). Consequently the total quotient ring
`K` of a reduced Noetherian ring `A` has Krull dimension zero. Being Noetherian too, `K` is
Artinian (`IsFractionRing.isArtinianRing_of_isReduced`), and it is reduced. Mathlib's
`IsArtinianRing.equivPi` then decomposes `K` as the finite product of its residue fields `K ⧸ m`
over its maximal ideals `m`.

## References

* The Stacks Project, Algebra, section *Zerodivisors and total rings of fractions*.
-/

public section

open scoped nonZeroDivisors

variable {A : Type*} [CommRing A]

/-- Every localization of a reduced ring is reduced. -/
theorem IsLocalization.isReduced [IsReduced A] (M : Submonoid A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization M S] : IsReduced S :=
  let e := IsLocalization.algEquiv M S (Localization M)
  isReduced_of_injective e e.injective

namespace IsFractionRing

variable (A) (K : Type*) [CommRing K] [Algebra A K] [IsFractionRing A K]

/-- The total quotient ring of a reduced Noetherian ring is Artinian. -/
theorem isArtinianRing_of_isReduced [IsNoetherianRing A] [IsReduced A] : IsArtinianRing K := by
  have : IsNoetherianRing K := IsLocalization.isNoetherianRing A⁰ K inferInstance
  refine isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mpr ⟨inferInstance, ?_⟩
  -- Every prime of `K` contracts to a minimal prime of `A`, so every prime of `K` is minimal.
  have hmin (P : Ideal K) [P.IsPrime] : P ∈ minimalPrimes K := by
    have hP : P.comap (algebraMap A K) ∈ minimalPrimes A :=
      (Ideal.mem_minimalPrimes_iff_disjoint_nonZeroDivisors
        (minimalPrimes.finite_of_isNoetherianRing A)).mpr
        ((IsLocalization.isPrime_iff_isPrime_disjoint A⁰ K P).mp ‹_›).2.symm
    have h := IsLocalization.minimalPrimes_map A⁰ K (⊥ : Ideal A)
    rw [Ideal.map_bot] at h
    exact (Set.ext_iff.mp h P).mpr hP
  refine Ring.KrullDimLE.mk₀ fun P hP ↦ ?_
  obtain ⟨M, hM, hPM⟩ := P.exists_le_maximal hP.ne_top
  rwa [le_antisymm hPM ((hmin M).2 ⟨hP, bot_le⟩ hPM)]

end IsFractionRing
