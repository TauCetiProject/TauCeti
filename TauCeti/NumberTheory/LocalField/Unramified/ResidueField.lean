/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Unramified.DiscreteValuation
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.Finite.Extension

/-!
# Algebraic closure of the residue field of `Breve E`

Every monic polynomial over `𝓀[E^{ur}]` descends to the residue field of some finite unramified
subextension `E_N / E` and splits in a finite unramified extension `E_M / E` of degree a multiple
of `N`. Consequently `𝓀[E^{ur}]` is algebraically closed, and by the canonical residue-field
isomorphism `UniformSpace.Completion.residueFieldRingEquiv` so is `𝓀[Breve E]`.

## Main results

* `TauCeti.MaxUnramifiedCompletion.unramifiedResidueField_isAlgClosed`: `𝓀[E^{ur}]` is
  algebraically closed.
* `TauCeti.MaxUnramifiedCompletion.residueField_isAlgClosed`: `𝓀[Breve E]` is algebraically closed.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter III, §5.
* R. E. Kottwitz, *Isocrystals with additional structure. II*, Compositio Math. 109 (1997), §1.1.
-/

public section

open scoped Polynomial
open ValuativeRel UniformSpace IntermediateField

namespace TauCeti.MaxUnramifiedCompletion

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- **The residue field of `E^{ur}` is algebraically closed.** Every monic polynomial over
`𝓀[E^{ur}]` lifts to some finite unramified level `E_N` and splits in a finite unramified level
`E_M` above `E_N`. -/
instance unramifiedResidueField_isAlgClosed : IsAlgClosed 𝓀[Unramified E] := by
  refine IsAlgClosed.of_exists_root _ fun p hp_mon hp_irr ↦ ?_
  choose c hc using fun i : ℕ ↦ IsLocalRing.residue_surjective (p.coeff i)
  choose f hf0 hcf using fun i : ℕ ↦
    mem_maximalUnramifiedExtension_iff.1 (c i : Unramified E).2
  let N : ℕ := ∏ i ∈ Finset.range (p.natDegree + 1), f i
  have hN0 : N ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ ↦ hf0 i
  let L := unramifiedExtension E (AlgebraicClosure E) N
  let := finiteIntermediateFieldValuativeRel E (AlgebraicClosure E) L
  let := finiteIntermediateFieldTopology E (AlgebraicClosure E) L
  have := finiteIntermediateField_isNonarchimedeanLocalField E (AlgebraicClosure E) L
  have := finiteIntermediateField_valuativeExtension E (AlgebraicClosure E) L
  have : IsUnramified E L := isUnramified_unramifiedExtension
  let jL : L →ₐ[E] Unramified E :=
    inclusion (unramifiedExtension_le_maximalUnramifiedExtension E (AlgebraicClosure E) N)
  let := jL.toAlgebra
  have := jL.valuativeExtension
  have hlifts : p ∈ Polynomial.lifts (algebraMap 𝓀[L] 𝓀[Unramified E]) := by
    refine (Polynomial.lifts_iff_coeff_lifts _).2 fun i ↦ ?_
    by_cases hi : p.natDegree < i
    · exact ⟨0, by rw [map_zero, Polynomial.coeff_eq_zero_of_natDegree_lt hi]⟩
    · have hdvd : f i ∣ N := Finset.dvd_prod_of_mem f (Finset.mem_range_succ_iff.2 (not_lt.1 hi))
      let y : L := ⟨((c i : Unramified E) : AlgebraicClosure E),
        unramifiedExtension_le_of_dvd hN0 hdvd (hcf i)⟩
      have hy_eq : algebraMap L (Unramified E) y = (c i : Unramified E) :=
        Subtype.ext (IntermediateField.coe_inclusion _ _)
      have hy1 : valuation L y ≤ 1 :=
        (ValuativeExtension.valuation_algebraMap_le_one_iff y).1 (by rw [hy_eq]; exact (c i).2)
      have hy₀ : algebraMap 𝒪[L] 𝒪[Unramified E] ⟨y, hy1⟩ = c i := Subtype.ext hy_eq
      exact ⟨IsLocalRing.residue 𝒪[L] ⟨y, hy1⟩,
        by rw [ValuativeExtension.residueField_algebraMap_residue, hy₀, hc]⟩
  obtain ⟨q₀, hq₀_map, hq₀_deg, _⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hp_mon
  obtain ⟨r, hr_irr, hr_dvd⟩ :=
    Polynomial.exists_irreducible_of_natDegree_pos (hq₀_deg ▸ hp_irr.natDegree_pos)
  have hr_X : r ∣ Polynomial.X ^ Nat.card 𝓀[L] ^ r.natDegree - Polynomial.X :=
    hr_irr.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.mp dvd_rfl
  let M : ℕ := N * r.natDegree
  have hM0 : M ≠ 0 := mul_ne_zero hN0 hr_irr.natDegree_pos.ne'
  let LM := unramifiedExtension E (AlgebraicClosure E) M
  let := finiteIntermediateFieldValuativeRel E (AlgebraicClosure E) LM
  let := finiteIntermediateFieldTopology E (AlgebraicClosure E) LM
  have := finiteIntermediateField_isNonarchimedeanLocalField E (AlgebraicClosure E) LM
  have := finiteIntermediateField_valuativeExtension E (AlgebraicClosure E) LM
  have : IsUnramified E LM := isUnramified_unramifiedExtension
  have hcard : Nat.card 𝓀[LM] = Nat.card 𝓀[L] ^ r.natDegree := by
    rw [natCard_residueField E LM, IsUnramified.inertiaDegree_eq_finrank,
      finrank_unramifiedExtension hM0, natCard_residueField E L,
      IsUnramified.inertiaDegree_eq_finrank, finrank_unramifiedExtension hN0, pow_mul]
  let _ : Fintype 𝓀[LM] := Fintype.ofFinite 𝓀[LM]
  have hsplit_ur : (Polynomial.X ^ Nat.card 𝓀[L] ^ r.natDegree - Polynomial.X :
      𝓀[Unramified E][X]).Splits := by
    let jM : LM →ₐ[E] Unramified E :=
      inclusion (unramifiedExtension_le_maximalUnramifiedExtension E (AlgebraicClosure E) M)
    let := jM.toAlgebra
    have := jM.valuativeExtension
    have : Polynomial.IsSplittingField 𝓀[LM] 𝓀[LM]
        (Polynomial.X ^ Fintype.card 𝓀[LM] - Polynomial.X) :=
      FiniteField.isSplittingField_sub 𝓀[LM] 𝓀[LM]
    have hs := Polynomial.IsSplittingField.splits 𝓀[LM]
      (Polynomial.X ^ Fintype.card 𝓀[LM] - Polynomial.X : 𝓀[LM][X])
    rw [Algebra.algebraMap_self, Polynomial.map_id, Fintype.card_eq_nat_card] at hs
    rw [← hcard]
    simpa using hs.map (algebraMap 𝓀[LM] 𝓀[Unramified E])
  have hr_split : (r.map (algebraMap 𝓀[L] 𝓀[Unramified E])).Splits :=
    hsplit_ur.of_dvd
      (Polynomial.X_pow_sub_X_ne_zero (Nat.one_lt_pow hr_irr.natDegree_pos.ne' Finite.one_lt_card))
      (by simpa using Polynomial.map_dvd (algebraMap 𝓀[L] 𝓀[Unramified E]) hr_X)
  have hr_deg : (r.map (algebraMap 𝓀[L] 𝓀[Unramified E])).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective (algebraMap 𝓀[L] 𝓀[Unramified E]).injective]
    exact (Polynomial.degree_pos_of_irreducible hr_irr).ne'
  obtain ⟨z, hz⟩ := hr_split.exists_eval_eq_zero hr_deg
  exact ⟨z, Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero
    (hq₀_map ▸ Polynomial.map_dvd (algebraMap 𝓀[L] 𝓀[Unramified E]) hr_dvd) hz⟩

/-- **The residue field of `Breve E` is algebraically closed.** -/
instance residueField_isAlgClosed : IsAlgClosed 𝓀[Breve E] :=
  IsAlgClosed.of_ringEquiv 𝓀[Unramified E] 𝓀[Breve E]
    (Completion.residueFieldRingEquiv (Unramified E))

end TauCeti.MaxUnramifiedCompletion
