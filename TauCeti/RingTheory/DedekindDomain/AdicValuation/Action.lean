/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import TauCeti.RingTheory.DedekindDomain.HeightOneSpectrumAction
-- Proof-only: the general localization `Ideal.valuationSubringAtPrime`, its equivariance and
-- stabilizer, and its identification with `valuationSubringAtPrime` at a place.
import TauCeti.RingTheory.DedekindDomain.Prufer

/-!
# Group actions on the valuation subrings at the places of a Dedekind domain

Let `R` be a Dedekind domain with fraction field `L`, and let a group `G` act on `R` and `L` by
ring automorphisms, compatibly (`SMulDistribClass G R L`). Then `G` acts on the places
`HeightOneSpectrum R` through `IsDedekindDomain.HeightOneSpectrum.pointwiseMulAction`, with
`(σ • w).asIdeal = σ • w.asIdeal`. This file compares that action with Mathlib's pointwise action
on valuation subrings of `L`: the localization of `R` at `σ • w`, as a valuation subring of `L`,
is the image under `σ` of the localization at `w`, and the stabilizer of `w` under
`Gal(L/K) = L ≃ₐ[K] L` is Mathlib's decomposition subgroup
`ValuationSubring.decompositionSubgroup` of the valuation subring `valuationSubringAtPrime L w`.
These are the Dedekind case of the general `Ideal.smul_valuationSubringAtPrime` and
`ValuationSubring.IsCenteredAt.stabilizer_eq` (a valuation subring is determined by its centre),
through `IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_asIdeal`.

For an extension of number fields `L/K` and `R = 𝓞 L`, this is the Galois action on the finite
places of `L`, and the stabilizer of a finite place is its decomposition group.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.smul_valuationSubringAtPrime`:
  `σ • valuationSubringAtPrime L w = valuationSubringAtPrime L (σ • w)`.
* `IsDedekindDomain.HeightOneSpectrum.stabilizer_valuationSubringAtPrime`: for any group acting
  compatibly, the stabilizer of a place is the stabilizer of its valuation subring.
* `IsDedekindDomain.HeightOneSpectrum.stabilizer_eq_decompositionSubgroup`: the stabilizer of a
  place is the decomposition subgroup of its valuation subring.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9 and Chapter II, §9.
-/

public section

open scoped Pointwise

namespace IsDedekindDomain.HeightOneSpectrum

section DedekindDomain

variable {L R : Type*} [Field L] [CommRing R] [IsDedekindDomain R] [Algebra R L]
  [IsFractionRing R L]

section Group

variable {G : Type*} [Group G] [MulSemiringAction G L] [MulSemiringAction G R]
  [SMulDistribClass G R L]

/-- The localization of a Dedekind domain `R` at `σ • w`, as a valuation subring of its fraction
field `L`, is the image under `σ` of the localization at `w`, for a group acting compatibly on `R`
and `L` by ring automorphisms. -/
@[simp]
theorem smul_valuationSubringAtPrime (σ : G) (w : HeightOneSpectrum R) :
    σ • valuationSubringAtPrime L w = valuationSubringAtPrime L (σ • w) := by
  simp [← valuationSubringAtPrime_asIdeal, Ideal.smul_valuationSubringAtPrime]

/-- The stabilizer of a place `w` is the stabilizer of its valuation subring
`valuationSubringAtPrime L w`. -/
theorem stabilizer_valuationSubringAtPrime (w : HeightOneSpectrum R) :
    MulAction.stabilizer G (valuationSubringAtPrime L w) = MulAction.stabilizer G w := by
  rw [stabilizer_eq_stabilizer_asIdeal, ← valuationSubringAtPrime_asIdeal (L := L)]
  exact Ideal.isCenteredAt_valuationSubringAtPrime.stabilizer_eq

end Group

variable {K : Type*} [Field K] [Algebra K L] [MulSemiringAction (L ≃ₐ[K] L) R]
  [SMulDistribClass (L ≃ₐ[K] L) R L]

/-- The stabilizer of a place `w` of a Dedekind domain `R` with fraction field `L`, under an
action of `Gal(L/K)` on `R` compatible with its action on `L`, is Mathlib's decomposition subgroup
of the valuation subring `valuationSubringAtPrime L w`. For `R = 𝓞 L` this is the stabilizer of
a finite place of the number field `L`. -/
theorem stabilizer_eq_decompositionSubgroup (w : HeightOneSpectrum R) :
    MulAction.stabilizer (L ≃ₐ[K] L) w =
      (valuationSubringAtPrime L w).decompositionSubgroup K :=
  (stabilizer_valuationSubringAtPrime w).symm

end DedekindDomain

end IsDedekindDomain.HeightOneSpectrum
