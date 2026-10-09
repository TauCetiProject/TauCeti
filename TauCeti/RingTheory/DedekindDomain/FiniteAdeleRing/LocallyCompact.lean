/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Basic

/-!
# Local compactness of finite adele rings

The finite adele ring of a Dedekind domain with finite residue fields is locally compact.  Each
adic completion is a nonarchimedean local field, and its integer ring is compact and open.  The
result then follows from the local-compactness theorem for restricted products.  If the Dedekind
domain is moreover countable, the finite adele ring is σ-compact: every finite adele has a common
denominator `b`, so it lies in one of the countably many compact sets `b⁻¹ · ∏_v 𝒪_v`.

The finite-residue-field hypothesis is stated directly, rather than specialized to rings of
integers, so this applies to every Dedekind domain for which the same local compactness argument is
valid.

## Main results

* `IsDedekindDomain.FiniteAdeleRing.instLocallyCompactSpace`: the finite adele ring is locally
  compact when all residue fields are finite.
* `IsDedekindDomain.FiniteAdeleRing.instSigmaCompactSpace`: the finite adele ring is σ-compact
  when moreover the Dedekind domain is countable.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §14.
-/

public section
noncomputable section

open IsDedekindDomain

namespace IsDedekindDomain.FiniteAdeleRing

variable (R : Type*) [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The finite adele ring of a Dedekind domain with finite residue fields is locally compact. -/
instance instLocallyCompactSpace [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)] :
    LocallyCompactSpace (FiniteAdeleRing R K) := by
  let _ (v : HeightOneSpectrum R) : IsNonarchimedeanLocalField (v.adicCompletion K) :=
    inferInstance
  let _ : Fact (∀ v : HeightOneSpectrum R,
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  exact inferInstanceAs <| LocallyCompactSpace <|
    RestrictedProduct (fun v : HeightOneSpectrum R ↦ v.adicCompletion K)
      (fun v ↦ v.adicCompletionIntegers K) Filter.cofinite

/-- The finite adele ring of a countable Dedekind domain with finite residue fields is
σ-compact. -/
instance instSigmaCompactSpace [Countable R] [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)] :
    SigmaCompactSpace (FiniteAdeleRing R K) := by
  let s (b : R) : Set (FiniteAdeleRing R K) :=
    (· * algebraMap K (FiniteAdeleRing R K) (algebraMap R K b)⁻¹) ''
      {a | ∀ v, a v ∈ v.adicCompletionIntegers K}
  -- Every finite adele has a common denominator `b`, so it lies in `s b`.
  have hs : ⋃ b, s b = Set.univ := by
    refine Set.eq_univ_of_forall fun a ↦ Set.mem_iUnion.mpr ?_
    obtain ⟨b, hb0, hb⟩ := mul_nonZeroDivisor_mem_adicCompletionIntegers a
    have hb' : algebraMap R K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb0
    refine ⟨b, a * algebraMap K (FiniteAdeleRing R K) (algebraMap R K b), fun v ↦ ?_, ?_⟩
    · simpa [IsScalarTower.algebraMap_apply R K (v.adicCompletion K)] using hb v
    · dsimp only
      rw [mul_assoc, ← map_mul, mul_inv_cancel₀ hb', map_one, mul_one]
  rw [← isSigmaCompact_univ_iff, ← hs]
  exact isSigmaCompact_iUnion_of_isCompact _ fun b ↦
    isCompact_integralFiniteAdeles.image (continuous_id.mul continuous_const)

end IsDedekindDomain.FiniteAdeleRing
