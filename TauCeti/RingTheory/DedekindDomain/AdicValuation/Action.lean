/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import TauCeti.RingTheory.DedekindDomain.HeightOneSpectrumAction

/-!
# Group actions on the valuation subrings at the places of a Dedekind domain

Let `R` be a Dedekind domain with fraction field `L`, and let a group `G` act on `R` and `L` by
ring automorphisms, compatibly (`SMulDistribClass G R L`). Then `G` acts on the places
`HeightOneSpectrum R` through `IsDedekindDomain.HeightOneSpectrum.pointwiseMulAction`, with
`(σ • w).asIdeal = σ • w.asIdeal`. This file compares that action with Mathlib's pointwise action
on valuation subrings of `L`: the localization of `R` at `σ • w`, as a valuation subring of `L`,
is the image under `σ` of the localization at `w`. Since the localization is the valuation subring
of the `w`-adic valuation, which determines the place (Mathlib's
`valuationSubringAtPrime_eq_valuationSubring` and `valuationSubring_valuation_injective`), the
stabilizer of `w` under `Gal(L/K) = L ≃ₐ[K] L` is Mathlib's decomposition subgroup
`ValuationSubring.decompositionSubgroup` of the valuation subring `valuationSubringAtPrime L w`.

For an extension of number fields `L/K` and `R = 𝓞 L`, this is the Galois action on the finite
places of `L`, and the stabilizer of a finite place is its decomposition group.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.smul_valuationSubringAtPrime`:
  `σ • valuationSubringAtPrime L w = valuationSubringAtPrime L (σ • w)`.
* `IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_injective`: a place is determined
  by its localization.
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

/-- The elements of the localization of `R` at `w`, as a valuation subring of `L`, are the
fractions `a / s` with `s ∉ w.asIdeal`. -/
private theorem mem_valuationSubringAtPrime_iff {w : HeightOneSpectrum R} {x : L} :
    x ∈ valuationSubringAtPrime L w ↔
      ∃ a s, s ∈ w.asIdeal.primeCompl ∧ x = algebraMap R L a * (algebraMap R L s)⁻¹ := by
  rw [← ValuationSubring.mem_toSubring, valuationSubringAtPrime_toSubring,
    Subalgebra.mem_toSubring, Localization.subalgebra.ofField, ← SetLike.mem_coe,
    Subalgebra.coe_copy, Set.mem_ofPred_eq]
  simp only [exists_prop]

variable (L) in
/-- A place of `R` is determined by its localization, as a valuation subring of `L`. -/
theorem valuationSubringAtPrime_injective :
    Function.Injective (valuationSubringAtPrime (R := R) L) := fun v w h ↦ by
  rw [valuationSubringAtPrime_eq_valuationSubring,
    valuationSubringAtPrime_eq_valuationSubring] at h
  exact valuationSubring_valuation_injective L h

section Group

variable {G : Type*} [Group G] [MulSemiringAction G L] [MulSemiringAction G R]
  [SMulDistribClass G R L]

/-- The image under `σ` of the localization at `w` is contained in the localization at `σ • w`. -/
private theorem smul_valuationSubringAtPrime_le (σ : G) (w : HeightOneSpectrum R) :
    σ • valuationSubringAtPrime L w ≤ valuationSubringAtPrime L (σ • w) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (ValuationSubring.mem_smul_pointwise_iff_exists _ _ _).1 hx
  obtain ⟨a, s, hs, rfl⟩ := mem_valuationSubringAtPrime_iff.1 hy
  refine mem_valuationSubringAtPrime_iff.2 ⟨σ • a, σ • s, ?_, ?_⟩
  · simpa [Ideal.primeCompl, Ideal.smul_mem_pointwise_smul_iff] using hs
  · simp [algebraMap.smul']

/-- The localization of a Dedekind domain `R` at `σ • w`, as a valuation subring of its fraction
field `L`, is the image under `σ` of the localization at `w`, for a group acting compatibly on `R`
and `L` by ring automorphisms. -/
@[simp]
theorem smul_valuationSubringAtPrime (σ : G) (w : HeightOneSpectrum R) :
    σ • valuationSubringAtPrime L w = valuationSubringAtPrime L (σ • w) := by
  refine le_antisymm (smul_valuationSubringAtPrime_le σ w) ?_
  rw [ValuationSubring.subset_pointwise_smul_iff]
  simpa using smul_valuationSubringAtPrime_le σ⁻¹ (σ • w)

/-- The stabilizer of a place `w` is the stabilizer of its valuation subring
`valuationSubringAtPrime L w`. -/
theorem stabilizer_valuationSubringAtPrime (w : HeightOneSpectrum R) :
    MulAction.stabilizer G (valuationSubringAtPrime L w) = MulAction.stabilizer G w := by
  ext σ
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, smul_valuationSubringAtPrime,
    (valuationSubringAtPrime_injective L).eq_iff]

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
