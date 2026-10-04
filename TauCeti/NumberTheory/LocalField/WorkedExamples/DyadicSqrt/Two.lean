/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Different.Hilbert
public import TauCeti.NumberTheory.LocalField.Discriminant.Basic
public import TauCeti.NumberTheory.LocalField.Eisenstein.TotallyRamified
public import TauCeti.NumberTheory.LocalField.Padic
public import TauCeti.RingTheory.AdjoinRoot
import TauCeti.FieldTheory.Kummer.Extension

/-!
# Ramification of `ℚ₂(√2)`

Adjoining a root of `X² - 2` gives a totally ramified quadratic extension of `ℚ₂`.
Its root is a uniformizer, its residue field has two elements, and its different and
discriminant exponents are both three. The nonidentity automorphism sends `√2` to `-√2`,
so its displacement at the integral generator has valuation three. Consequently the lower
ramification groups are the whole Galois group through index two and trivial from index three.

This explicit filtration is useful for comparing lower numbering in the dyadic cyclotomic
extension with its quadratic subextension: the third lower group of `ℚ₂(√2)/ℚ₂` is trivial.
The computations use the canonical local-field structures and the integral Eisenstein and
Hilbert different formulas.

## References

* J.-P. Serre, *Local Fields*, Chapter III, §6 and Chapter IV, §1.
* `TauCeti.NumberTheory.LocalField.WorkedExamples.DyadicSqrt.Five` and
  `TauCeti.NumberTheory.LocalField.WorkedExamples.NonGaloisCubic`: formal antecedents
  for the finite-extension construction and integral Eisenstein generator proofs.
-/

public section
noncomputable section

open Polynomial ValuativeRel IsLocalRing
open scoped IntermediateField

namespace TauCeti

/-- The local field `ℚ₂(√2)`, obtained by adjoining a root of `X² - 2` to `ℚ₂`. -/
def DyadicSqrtTwo : Type := AdjoinRoot (X ^ 2 - C 2 : ℚ_[2][X])

namespace DyadicSqrtTwo

local instance : Fact (Irreducible (X ^ 2 - C 2 : ℚ_[2][X])) :=
  ⟨by
    have h := X_pow_sub_C_irreducible_of_irreducible (R := ℤ_[2]) (K := ℚ_[2])
      PadicInt.irreducible_p two_ne_zero
    rw [map_natCast, Nat.cast_ofNat] at h
    exact h⟩

instance : Field DyadicSqrtTwo := inferInstanceAs (Field (AdjoinRoot (X ^ 2 - C 2 : ℚ_[2][X])))

instance : Algebra ℚ_[2] DyadicSqrtTwo :=
  inferInstanceAs (Algebra ℚ_[2] (AdjoinRoot (X ^ 2 - C 2 : ℚ_[2][X])))

private def powerBasis : PowerBasis ℚ_[2] DyadicSqrtTwo :=
  AdjoinRoot.powerBasis (Fact.out : Irreducible (X ^ 2 - C 2 : ℚ_[2][X])).ne_zero

instance : FiniteDimensional ℚ_[2] DyadicSqrtTwo := powerBasis.finite

instance : CharZero DyadicSqrtTwo :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[2] DyadicSqrtTwo).injective

instance : ValuativeRel DyadicSqrtTwo := finiteExtensionValuativeRel ℚ_[2] DyadicSqrtTwo

instance : TopologicalSpace DyadicSqrtTwo :=
  finiteExtensionNormedFieldTopology ℚ_[2] DyadicSqrtTwo

instance : ValuativeExtension ℚ_[2] DyadicSqrtTwo :=
  finiteExtension_valuativeExtension ℚ_[2] DyadicSqrtTwo

instance : IsNonarchimedeanLocalField DyadicSqrtTwo :=
  finiteExtension_isNonarchimedeanLocalField ℚ_[2] DyadicSqrtTwo

/-- The square root `√2` generating `ℚ₂(√2)`, the class of `X`. -/
def sqrtTwo : DyadicSqrtTwo := AdjoinRoot.root (X ^ 2 - C 2 : ℚ_[2][X])

/-- The defining equation of the generator `√2`. -/
@[simp]
theorem sqrtTwo_sq : sqrtTwo ^ 2 = 2 := by
  convert! TauCeti.AdjoinRoot.root_sq (2 : ℚ_[2]) using 1

/-- `√2` generates `ℚ₂(√2)` as a field extension of `ℚ₂`. -/
theorem adjoin_sqrtTwo_eq_top : ℚ_[2]⟮sqrtTwo⟯ = ⊤ :=
  IntermediateField.adjoin_root_eq_top _

/-- The degree of `ℚ₂(√2)/ℚ₂` is two. -/
@[simp]
theorem finrank_eq_two : Module.finrank ℚ_[2] DyadicSqrtTwo = 2 := by
  rw [powerBasis.finrank, powerBasis, AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C]

instance : Algebra.IsQuadraticExtension ℚ_[2] DyadicSqrtTwo := ⟨finrank_eq_two⟩

private theorem integral_sqrtTwo : IsIntegral 𝒪[ℚ_[2]] sqrtTwo :=
  ⟨X ^ 2 - C 2, by monicity!, by simp [map_ofNat]⟩

/-- `√2`, viewed as an element of the ring of integers. -/
def integerSqrtTwo : 𝒪[DyadicSqrtTwo] :=
  ⟨sqrtTwo, (Valuation.Integers.isIntegral_iff_valuation_le_one
    (Valuation.integer.integers (valuation ℚ_[2])) _).1 integral_sqrtTwo⟩

@[simp]
theorem coe_integerSqrtTwo : (integerSqrtTwo : DyadicSqrtTwo) = sqrtTwo := (rfl)

private theorem addVal_two : IsDiscreteValuationRing.addVal 𝒪[ℚ_[2]] 2 = 1 := by
  simpa using (TauCeti.IsDiscreteValuationRing.addVal_natCast ℚ_[2] 2 (by norm_num)).trans
    (congrArg (fun n : ℕ => (n : ℕ∞)) (Padic.natCastValuation_self (p := 2)))

private theorem isEisensteinAt : (X ^ 2 - C 2 : 𝒪[ℚ_[2]][X]).IsEisensteinAt 𝓂[ℚ_[2]] := by
  refine ⟨?_, ?_, ?_⟩
  · simp [leadingCoeff_X_pow_sub_C (by norm_num : 0 < (2 : ℕ))]
  · intro n hn
    rw [natDegree_X_pow_sub_C] at hn
    interval_cases n
    · simp only [coeff_sub, coeff_X_pow, show ¬(0 : ℕ) = 2 by omega, ↓reduceIte, coeff_C_zero,
        zero_sub]
      rw [Ideal.neg_mem_iff, ← pow_one 𝓂[ℚ_[2]],
        TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal, addVal_two]
      norm_num
    · simp
  · simp only [coeff_sub, coeff_X_pow, show ¬(0 : ℕ) = 2 by omega, ↓reduceIte, coeff_C_zero,
      zero_sub]
    rw [Ideal.neg_mem_iff, TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal,
      addVal_two]
    norm_num

private theorem isRoot :
    ((X ^ 2 - C 2 : 𝒪[ℚ_[2]][X]).map
      (algebraMap 𝒪[ℚ_[2]] 𝒪[DyadicSqrtTwo])).IsRoot integerSqrtTwo := by
  have htwoL : ((2 : 𝒪[DyadicSqrtTwo]) : DyadicSqrtTwo) = 2 :=
    map_ofNat (Subring.subtype 𝒪[DyadicSqrtTwo]) 2
  apply Subtype.ext
  simp [map_ofNat, htwoL]

/-- `√2` is a uniformizer of the integer ring of `ℚ₂(√2)`. -/
theorem irreducible_integerSqrtTwo : Irreducible integerSqrtTwo :=
  irreducible_of_eisenstein_adjoin_eq_top _ isEisensteinAt _ isRoot adjoin_sqrtTwo_eq_top

/-- The ramification index of `ℚ₂(√2)/ℚ₂` is two. -/
@[simp]
theorem ramificationIndex_eq_two : ramificationIndex ℚ_[2] DyadicSqrtTwo = 2 := by
  simpa using ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top
    _ isEisensteinAt _ isRoot adjoin_sqrtTwo_eq_top

/-- The residue degree of `ℚ₂(√2)/ℚ₂` is one. -/
@[simp]
theorem inertiaDegree_eq_one : inertiaDegree ℚ_[2] DyadicSqrtTwo = 1 :=
  inertiaDegree_eq_one_of_eisenstein_adjoin_eq_top _ isEisensteinAt _ isRoot adjoin_sqrtTwo_eq_top

/-- `ℚ₂(√2)/ℚ₂` is totally ramified. -/
theorem isTotallyRamified : IsTotallyRamified ℚ_[2] DyadicSqrtTwo :=
  (isTotallyRamified_iff_inertiaDegree_eq_one _ _).2 inertiaDegree_eq_one

/-- The residue field of `ℚ₂(√2)` has two elements. -/
@[simp high]
theorem natCard_residueField : Nat.card 𝓀[DyadicSqrtTwo] = 2 := by
  rw [TauCeti.natCard_residueField (K := ℚ_[2]), inertiaDegree_eq_one,
    Padic.natCard_residueField, pow_one]

/-- The extension `ℚ₂(√2)/ℚ₂` is ramified. -/
theorem not_isUnramified : ¬IsUnramified ℚ_[2] DyadicSqrtTwo := by
  rw [isUnramified_iff_ramificationIndex_eq_one, ramificationIndex_eq_two]
  norm_num

/-- The ring of integers is `𝒪[ℚ₂][√2]`. -/
theorem adjoin_integerSqrtTwo_eq_top : Algebra.adjoin 𝒪[ℚ_[2]] {integerSqrtTwo} = ⊤ :=
  algebra_adjoin_eq_top_of_eisenstein_adjoin_eq_top isEisensteinAt isRoot adjoin_sqrtTwo_eq_top

/-- Every nonidentity automorphism sends `√2` to `-√2`. -/
theorem apply_sqrtTwo_of_ne_one {σ : DyadicSqrtTwo ≃ₐ[ℚ_[2]] DyadicSqrtTwo} (hσ : σ ≠ 1) :
    σ sqrtTwo = -sqrtTwo := by
  have hsq : σ sqrtTwo ^ 2 = sqrtTwo ^ 2 := by rw [← map_pow, sqrtTwo_sq, map_ofNat]
  refine (sq_eq_sq_iff_eq_or_eq_neg.1 hsq).resolve_left fun h ↦ hσ ?_
  exact AlgEquiv.coe_toAlgHom_injective (AdjoinRoot.algHom_ext h)

/-- The displacement of any nonidentity automorphism at the integral generator has valuation
three: `v(-√2 - √2) = v(2) + v(√2) = 2 + 1`. -/
theorem addVal_smul_integerSqrtTwo_sub_of_ne_one
    {σ : DyadicSqrtTwo ≃ₐ[ℚ_[2]] DyadicSqrtTwo} (hσ : σ ≠ 1) :
    IsDiscreteValuationRing.addVal 𝒪[DyadicSqrtTwo]
      (σ • integerSqrtTwo - integerSqrtTwo) = 3 := by
  have h : σ • integerSqrtTwo - integerSqrtTwo = -(2 * integerSqrtTwo) := by
    have htwoL : ((2 : 𝒪[DyadicSqrtTwo]) : DyadicSqrtTwo) = 2 :=
      map_ofNat (Subring.subtype 𝒪[DyadicSqrtTwo]) 2
    apply Subtype.ext
    simp only [AddSubgroupClass.coe_sub, AlgEquiv.coe_smul_integerRing, coe_integerSqrtTwo,
      apply_sqrtTwo_of_ne_one hσ, Subring.coe_neg, Subring.coe_mul, htwoL]
    ring
  have htwo : (2 : 𝒪[DyadicSqrtTwo]) = algebraMap 𝒪[ℚ_[2]] 𝒪[DyadicSqrtTwo] 2 :=
    (map_ofNat _ 2).symm
  rw [h, AddValuation.map_neg, IsDiscreteValuationRing.addVal_mul, htwo,
    addVal_algebraMap, addVal_two, ramificationIndex_eq_two,
    IsDiscreteValuationRing.addVal_uniformizer irreducible_integerSqrtTwo]
  norm_num

/-- Every nonidentity automorphism has lower index three. -/
theorem lowerIndex_of_ne_one {σ : DyadicSqrtTwo ≃ₐ[ℚ_[2]] DyadicSqrtTwo} (hσ : σ ≠ 1) :
    TauCeti.IsLocalRing.lowerIndex 𝒪[DyadicSqrtTwo] σ = 3 := by
  rw [TauCeti.IsLocalRing.lowerIndex_eq_addVal_of_adjoin_singleton_eq_top
    adjoin_integerSqrtTwo_eq_top, addVal_smul_integerSqrtTwo_sub_of_ne_one hσ]

/-- The lower ramification groups are the whole Galois group through index two and trivial
from index three, including the negative-index convention. -/
@[simp]
theorem lowerRamificationGroup_eq (i : ℤ) :
    LocalFieldsRamification.lowerRamificationGroup ℚ_[2] DyadicSqrtTwo i =
      if i ≤ 2 then ⊤ else ⊥ := by
  classical
  ext σ
  rw [LocalFieldsRamification.mem_lowerRamificationGroup_iff_le_lowerIndex]
  by_cases hσ : σ = 1
  · subst σ
    simp
  · rw [lowerIndex_of_ne_one hσ]
    split_ifs with hi
    · simp only [Subgroup.mem_top, iff_true]
      norm_cast
      omega
    · simp only [Subgroup.mem_bot, hσ, iff_false, not_le]
      norm_cast
      omega

/-- The different exponent of `ℚ₂(√2)/ℚ₂` is three. -/
@[simp]
theorem differentExponent_eq_three : differentExponent ℚ_[2] DyadicSqrtTwo = 3 := by
  have h := differentExponent_eq_of_lowerRamificationGroup_eq_at_zero_eq_bot
    ℚ_[2] DyadicSqrtTwo (t := 2) (by simp) (by simp)
  rw [LocalFieldsRamification.natCard_lowerRamificationGroup_zero,
    ramificationIndex_eq_two] at h
  exact h

/-- The local discriminant exponent of `ℚ₂(√2)/ℚ₂` is three. -/
@[simp]
theorem discriminantExponent_eq_three : discriminantExponent ℚ_[2] DyadicSqrtTwo = 3 := by
  rw [discriminantExponent_eq_inertiaDegree_mul_differentExponent, inertiaDegree_eq_one,
    differentExponent_eq_three, one_mul]

end DyadicSqrtTwo

end TauCeti
