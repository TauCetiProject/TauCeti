/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
public import TauCeti.NumberTheory.LocalField.Topology
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Basic
public import TauCeti.RingTheory.DedekindDomain.Ideal.Basic
public import TauCeti.Topology.Algebra.RestrictedProduct.SecondCountable

/-!
# Local compactness and second countability of finite adele rings

The finite adele ring of a Dedekind domain with finite residue fields is locally compact.  Each
adic completion is a nonarchimedean local field, and its integer ring is compact and open.  The
result then follows from the local-compactness theorem for restricted products.  If the Dedekind
domain is moreover countable, the finite adele ring is σ-compact: every finite adele has a common
denominator `b`, so it lies in one of the countably many compact sets `b⁻¹ · ∏_v 𝒪_v`. It is also
second countable: it is the restricted product over the countably many height-one primes
(`IsDedekindDomain.HeightOneSpectrum.instCountable`) of the completions `K_v`, which are
nonarchimedean local fields and hence second countable, with respect to the open integer rings
`𝒪_v`.

The finite-residue-field hypothesis is stated directly, rather than specialized to rings of
integers, so this applies to every Dedekind domain for which the same local compactness argument is
valid.

## Main results

* `IsDedekindDomain.FiniteAdeleRing.instFactIsOpenAdicCompletionIntegers`: the local integer rings
  are open.
* `IsDedekindDomain.FiniteAdeleRing.instLocallyCompactSpace`: the finite adele ring is locally
  compact when all residue fields are finite.
* `IsDedekindDomain.FiniteAdeleRing.instSigmaCompactSpace`: the finite adele ring is σ-compact
  when moreover the Dedekind domain is countable.
* `IsDedekindDomain.FiniteAdeleRing.instSecondCountableTopology`: the finite adele ring is second
  countable when moreover the Dedekind domain is countable.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §14.
* V. Platonov, A. Rapinchuk and I. Rapinchuk, *Algebraic Groups and Number Theory*, Vol. I,
  2nd ed., Lemma 3.63, pp. 188–189 (the countable restricted-product topology).
-/

public section
noncomputable section

open IsDedekindDomain TopologicalSpace

namespace IsDedekindDomain.FiniteAdeleRing

variable (R : Type*) [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The local integer rings `𝒪_v` are open in the completions `K_v`. This is the openness
hypothesis of the restricted-product topology on `FiniteAdeleRing R K`. -/
instance instFactIsOpenAdicCompletionIntegers : Fact (∀ v : HeightOneSpectrum R,
    IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
  ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩

/-- The finite adele ring of a Dedekind domain with finite residue fields is locally compact. -/
instance instLocallyCompactSpace [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)] :
    LocallyCompactSpace (FiniteAdeleRing R K) := by
  let _ (v : HeightOneSpectrum R) : IsNonarchimedeanLocalField (v.adicCompletion K) :=
    inferInstance
  exact inferInstanceAs <| LocallyCompactSpace <|
    RestrictedProduct (fun v : HeightOneSpectrum R ↦ v.adicCompletion K)
      (fun v ↦ v.adicCompletionIntegers K) Filter.cofinite

/-- The finite adele ring of a countable Dedekind domain with finite residue fields is
σ-compact. -/
instance instSigmaCompactSpace [Countable R] [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)] :
    SigmaCompactSpace (FiniteAdeleRing R K) := by
  let s (b : R) : Set (FiniteAdeleRing R K) :=
    (· * algebraMap K (FiniteAdeleRing R K) (algebraMap R K b)⁻¹) ''
      (integralAdeles R K : Set (FiniteAdeleRing R K))
  -- Every finite adele has a common denominator `b`, so it lies in `s b`.
  have hs : ⋃ b, s b = Set.univ := by
    refine Set.eq_univ_of_forall fun a ↦ Set.mem_iUnion.mpr ?_
    obtain ⟨b, hb0, hb⟩ := mul_nonZeroDivisor_mem_integralAdeles a
    have hb' : algebraMap R K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb0
    rw [IsScalarTower.algebraMap_apply R K] at hb
    refine ⟨b, _, hb, ?_⟩
    dsimp only
    rw [mul_assoc, ← map_mul, mul_inv_cancel₀ hb', map_one, mul_one]
  rw [← isSigmaCompact_univ_iff, ← hs]
  exact isSigmaCompact_iUnion_of_isCompact _ fun b ↦
    isCompact_integralAdeles.image (continuous_id.mul continuous_const)

/-- The finite adele ring of a countable Dedekind domain with finite residue fields is second
countable. -/
instance instSecondCountableTopology [Countable R]
    [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)] :
    SecondCountableTopology (FiniteAdeleRing R K) :=
  RestrictedProduct.instSecondCountableTopology
    (R := fun v : HeightOneSpectrum R ↦ v.adicCompletion K)
    (A := fun v ↦ (v.adicCompletionIntegers K : Set (v.adicCompletion K)))

end IsDedekindDomain.FiniteAdeleRing
