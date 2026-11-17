/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import TauCeti.NumberTheory.NumberField.AutomorphismAction
public import TauCeti.RingTheory.DedekindDomain.HeightOneSpectrumAction

/-!
# The Galois action on the finite places of a number field

For an extension of number fields `L/K`, the automorphism group `Gal(L/K) = L ≃ₐ[K] L` acts on
the finite places `HeightOneSpectrum (𝓞 L)` through the pointwise action of
`IsDedekindDomain.HeightOneSpectrum.pointwiseMulAction`, so that
`(σ • w).asIdeal = σ • w.asIdeal`, the preimage of `w.asIdeal` under `σ⁻¹`. The contraction of
`σ • w` to `𝓞 K` is that of `w` (`IsDedekindDomain.HeightOneSpectrum.under_smul`). For `L/K`
finite Galois, Mathlib's `IsGaloisGroup Gal(L/K) (𝓞 K) (𝓞 L)` instance (in
`Mathlib.FieldTheory.Galois.IsGaloisGroup`) makes `𝓞 L` invariant over `𝓞 K`, so
`IsDedekindDomain.HeightOneSpectrum.mem_orbit_iff_under_eq` says that the places above a given
place of `K` form a single orbit.

This file compares the action with Mathlib's pointwise action on valuation subrings of `L`: the
localization of `𝓞 L` at `σ • w`, as a valuation subring of `L`, is the image under `σ` of the
localization at `w`. Since the localization is the valuation subring of the `w`-adic valuation,
which determines the place (Mathlib's `valuationSubringAtPrime_eq_valuationSubring` and
`valuationSubring_valuation_injective`), the stabilizer of `w` is
Mathlib's decomposition subgroup `ValuationSubring.decompositionSubgroup` of the valuation subring
`valuationSubringAtPrime L w`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.smul_valuationSubringAtPrime`:
  `σ • valuationSubringAtPrime L w = valuationSubringAtPrime L (σ • w)`.
* `IsDedekindDomain.HeightOneSpectrum.stabilizer_eq_decompositionSubgroup`: the stabilizer of a
  finite place is the decomposition subgroup of its valuation subring.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9 and Chapter II, §9.
-/

public section

open NumberField
open scoped Pointwise

namespace IsDedekindDomain.HeightOneSpectrum

variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]

/-- The image under `σ` of the localization at `w` is contained in the localization at `σ • w`. -/
private theorem smul_valuationSubringAtPrime_le (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    σ • valuationSubringAtPrime L w ≤ valuationSubringAtPrime L (σ • w) := by
  intro x hx
  obtain ⟨y, ⟨a, s, hs, rfl⟩, rfl⟩ := (ValuationSubring.mem_smul_pointwise_iff_exists _ _ _).1 hx
  refine ⟨σ • a, σ • s, ?_, ?_⟩
  · simpa [Ideal.primeCompl, Ideal.smul_mem_pointwise_smul_iff] using hs
  · simp [AlgEquiv.smul_def]

/-- The localization of `𝓞 L` at `σ • w` is the image under `σ` of the localization at `w`. -/
theorem smul_valuationSubringAtPrime (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    σ • valuationSubringAtPrime L w = valuationSubringAtPrime L (σ • w) := by
  refine le_antisymm (smul_valuationSubringAtPrime_le σ w) ?_
  rw [ValuationSubring.subset_pointwise_smul_iff]
  simpa using smul_valuationSubringAtPrime_le σ⁻¹ (σ • w)

/-- The stabilizer of a finite place `w` of `L` in `Gal(L/K)` is Mathlib's decomposition subgroup
of the valuation subring `valuationSubringAtPrime L w`. -/
theorem stabilizer_eq_decompositionSubgroup (w : HeightOneSpectrum (𝓞 L)) :
    MulAction.stabilizer (L ≃ₐ[K] L) w =
      (valuationSubringAtPrime L w).decompositionSubgroup K := by
  ext σ
  rw [MulAction.mem_stabilizer_iff, ValuationSubring.decompositionSubgroup,
    MulAction.mem_stabilizer_iff, smul_valuationSubringAtPrime,
    valuationSubringAtPrime_eq_valuationSubring, valuationSubringAtPrime_eq_valuationSubring,
    (valuationSubring_valuation_injective L).eq_iff]

end IsDedekindDomain.HeightOneSpectrum
