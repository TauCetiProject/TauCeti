/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Basic

/-!
# The residue field of an adic valuation

For a height-one prime `v` of a Dedekind domain `R` with fraction field `K`, the residue field
of the valuation ring of `v.valuation K` is canonically `R ⧸ v.asIdeal`. This identifies reduction
in the fraction field with reduction in the original domain, without passing to a completion.

The construction parallels `residueFieldEquivAdicCompletionIntegers` in
`TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion`, using Mathlib's approximation
`exists_valuation_sub_lt_of_integer` in the uncompleted field.
-/

public section

open IsLocalRing

namespace IsDedekindDomain.HeightOneSpectrum

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)
  [Algebra R (v.valuation K).valuationSubring]
  [IsScalarTower R (v.valuation K).valuationSubring K]

/-- The residue field of the valuation ring at a height-one prime is the quotient by that prime.
-/
noncomputable def residueFieldEquivValuationSubring :
    (R ⧸ v.asIdeal) ≃+* ResidueField (v.valuation K).valuationSubring := by
  unfold ResidueField
  have hker : (maximalIdeal (v.valuation K).valuationSubring).comap
      (algebraMap R (v.valuation K).valuationSubring) = v.asIdeal := by
    ext r
    exact v.algebraMap_mem_maximalIdeal_valuationSubring_iff r
  refine RingEquiv.ofBijective (Ideal.quotientMap (maximalIdeal _)
    (algebraMap R (v.valuation K).valuationSubring) (le_of_eq hker.symm)) ⟨?_, ?_⟩
  · exact Ideal.quotientMap_injective' (le_of_eq hker)
  · intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer x.2 1
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [Ideal.quotientMap_mk]
    refine Ideal.Quotient.eq.mpr ((Valuation.mem_maximalIdeal_iff _ _).mpr ?_)
    rw [AddSubgroupClass.coe_sub, ← ValuationSubring.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply R (v.valuation K).valuationSubring K]
    exact ha

/-- On a representative, the residue-field comparison sends `a mod v` to the residue of `a`.
-/
@[simp]
theorem residueFieldEquivValuationSubring_apply_mk (a : R) :
    v.residueFieldEquivValuationSubring (K := K) (Ideal.Quotient.mk v.asIdeal a) =
      residue _ (algebraMap R (v.valuation K).valuationSubring a) := (rfl)

end IsDedekindDomain.HeightOneSpectrum
