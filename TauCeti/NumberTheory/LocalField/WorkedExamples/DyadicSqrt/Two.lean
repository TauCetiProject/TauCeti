/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Different.Hilbert
public import TauCeti.NumberTheory.LocalField.Discriminant.Basic
public import TauCeti.NumberTheory.LocalField.Eisenstein.TotallyRamified
public import TauCeti.NumberTheory.LocalField.AbsoluteRamificationIndex
public import TauCeti.RingTheory.AdjoinRoot
import TauCeti.FieldTheory.Galois.SquareRoot
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

## Main definitions

* `TauCeti.DyadicSqrtTwo`: the local field `ℚ₂(√2)`.
* `TauCeti.DyadicSqrtTwo.sqrtTwo`: its distinguished square root of two.
* `TauCeti.DyadicSqrtTwo.integerSqrtTwo`: the same generator in its ring of integers.

## Main results

* `TauCeti.DyadicSqrtTwo.sqrtTwo_sq` and `TauCeti.DyadicSqrtTwo.minpoly_sqrtTwo`:
  the generator equation and minimal polynomial.
* `TauCeti.DyadicSqrtTwo.adjoin_sqrtTwo_eq_top` and
  `TauCeti.DyadicSqrtTwo.adjoin_integerSqrtTwo_eq_top`: field and integral generation.
* `TauCeti.DyadicSqrtTwo.irreducible_integerSqrtTwo`: the generator is a uniformizer.
* `TauCeti.DyadicSqrtTwo.isEisensteinAt_X_sq_sub_two` and
  `TauCeti.DyadicSqrtTwo.isRoot_integerSqrtTwo`:
  the Eisenstein polynomial and its integral root.
* `TauCeti.DyadicSqrtTwo.finrank_eq_two`, `TauCeti.DyadicSqrtTwo.ramificationIndex_eq_two`,
  `TauCeti.DyadicSqrtTwo.absoluteRamificationIndex_eq_two`,
  `TauCeti.DyadicSqrtTwo.inertiaDegree_eq_one`, and
  `TauCeti.DyadicSqrtTwo.natCard_residueField`: the degree, ramification, and residue invariants.
* `TauCeti.DyadicSqrtTwo.isTotallyRamified` and `TauCeti.DyadicSqrtTwo.not_isUnramified`:
  the ramification predicates.
* `TauCeti.DyadicSqrtTwo.apply_sqrtTwo_of_ne_one`,
  `TauCeti.DyadicSqrtTwo.addVal_smul_sub_integerSqrtTwo_of_ne_one`, and
  `TauCeti.DyadicSqrtTwo.lowerIndex_of_ne_one`: the nonidentity automorphism and its lower index.
* `TauCeti.DyadicSqrtTwo.lowerRamificationGroup_eq`: the complete lower filtration.
* `TauCeti.DyadicSqrtTwo.differentExponent_eq_three` and
  `TauCeti.DyadicSqrtTwo.discriminantExponent_eq_three`: both exponents are three.

## References

* J.-P. Serre, *Local Fields*, Chapter III, §6 and Chapter IV, §1.

## Formal sources

The construction is adapted from
`TauCeti.NumberTheory.LocalField.WorkedExamples.DyadicSqrt.Five` and
`TauCeti.NumberTheory.LocalField.WorkedExamples.NonGaloisCubic`.
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
theorem sqrtTwo_sq : sqrtTwo ^ 2 = 2 :=
  (TauCeti.AdjoinRoot.root_sq (2 : ℚ_[2])).trans (map_ofNat _ 2)

/-- The minimal polynomial of `√2` over `ℚ₂` is `X² - 2`. -/
@[simp]
theorem minpoly_sqrtTwo : minpoly ℚ_[2] sqrtTwo = X ^ 2 - C 2 := by
  exact (AdjoinRoot.minpoly_root
    (Fact.out : Irreducible (X ^ 2 - C 2 : ℚ_[2][X])).ne_zero).trans
    (by simp [leadingCoeff_X_pow_sub_C (by norm_num : 0 < (2 : ℕ))])

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

@[simp]
private theorem coe_ofNat_two : ((2 : 𝒪[DyadicSqrtTwo]) : DyadicSqrtTwo) = 2 :=
  map_ofNat (Subring.subtype 𝒪[DyadicSqrtTwo]) 2

/-- The integer generator `√2` is a root of `X² - 2` over `𝒪[ℚ₂]`. -/
theorem isRoot_integerSqrtTwo :
    ((X ^ 2 - C 2 : 𝒪[ℚ_[2]][X]).map
      (algebraMap 𝒪[ℚ_[2]] 𝒪[DyadicSqrtTwo])).IsRoot integerSqrtTwo := by
  apply Subtype.ext
  simp [map_ofNat]

/-- The polynomial `X² - 2` is Eisenstein over the integer ring of `ℚ₂`. -/
theorem isEisensteinAt_X_sq_sub_two :
    (X ^ 2 - C 2 : 𝒪[ℚ_[2]][X]).IsEisensteinAt 𝓂[ℚ_[2]] :=
  isEisensteinAt_X_pow_sub_C_of_irreducible (Padic.irreducible_natCast_self 2) (by decide)

/-- `√2` is a uniformizer of the integer ring of `ℚ₂(√2)`. -/
theorem irreducible_integerSqrtTwo : Irreducible integerSqrtTwo :=
  irreducible_of_eisenstein_adjoin_eq_top _ isEisensteinAt_X_sq_sub_two _ isRoot_integerSqrtTwo
    adjoin_sqrtTwo_eq_top

/-- The ramification index of `ℚ₂(√2)/ℚ₂` is two. -/
@[simp]
theorem ramificationIndex_eq_two : ramificationIndex ℚ_[2] DyadicSqrtTwo = 2 := by
  simpa using ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top
    _ isEisensteinAt_X_sq_sub_two _ isRoot_integerSqrtTwo adjoin_sqrtTwo_eq_top

/-- The absolute ramification index of `ℚ₂(√2)` is two. -/
@[simp high] -- Compute the index before the general valuation comparison changes its form.
theorem absoluteRamificationIndex_eq_two : absoluteRamificationIndex DyadicSqrtTwo 2 = 2 := by
  rw [absoluteRamificationIndex_tower ℚ_[2] 2 DyadicSqrtTwo, ramificationIndex_eq_two,
    absoluteRamificationIndex_padic, mul_one]

/-- The residue degree of `ℚ₂(√2)/ℚ₂` is one. -/
@[simp]
theorem inertiaDegree_eq_one : inertiaDegree ℚ_[2] DyadicSqrtTwo = 1 :=
  inertiaDegree_eq_one_of_eisenstein_adjoin_eq_top _ isEisensteinAt_X_sq_sub_two _
    isRoot_integerSqrtTwo
    adjoin_sqrtTwo_eq_top

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
  algebra_adjoin_eq_top_of_eisenstein_adjoin_eq_top
    isEisensteinAt_X_sq_sub_two isRoot_integerSqrtTwo adjoin_sqrtTwo_eq_top

/-- Every nonidentity automorphism sends `√2` to `-√2`. -/
@[simp]
theorem apply_sqrtTwo_of_ne_one {σ : DyadicSqrtTwo ≃ₐ[ℚ_[2]] DyadicSqrtTwo} (hσ : σ ≠ 1) :
    σ sqrtTwo = -sqrtTwo := by
  refine (AlgEquiv.apply_eq_or_eq_neg_of_sq_eq σ
    (c := (2 : ℚ_[2])) (by simpa only [map_ofNat] using sqrtTwo_sq)).resolve_left fun h ↦ hσ ?_
  exact AlgEquiv.coe_toAlgHom_injective (AdjoinRoot.algHom_ext h)

/-- The displacement of any nonidentity automorphism at the integral generator has valuation
three: `v(-√2 - √2) = v(2) + v(√2) = 2 + 1`. -/
@[simp]
theorem addVal_smul_sub_integerSqrtTwo_of_ne_one
    {σ : DyadicSqrtTwo ≃ₐ[ℚ_[2]] DyadicSqrtTwo} (hσ : σ ≠ 1) :
    IsDiscreteValuationRing.addVal 𝒪[DyadicSqrtTwo]
      (σ • integerSqrtTwo - integerSqrtTwo) = 3 := by
  have h : σ • integerSqrtTwo - integerSqrtTwo = -(2 * integerSqrtTwo) := by
    apply Subtype.ext
    simp only [AddSubgroupClass.coe_sub, AlgEquiv.coe_smul_integerRing, coe_integerSqrtTwo,
      apply_sqrtTwo_of_ne_one hσ, Subring.coe_neg, Subring.coe_mul, coe_ofNat_two]
    ring
  have htwo : (2 : 𝒪[DyadicSqrtTwo]) = algebraMap 𝒪[ℚ_[2]] 𝒪[DyadicSqrtTwo] 2 :=
    (map_ofNat _ 2).symm
  rw [h, AddValuation.map_neg, IsDiscreteValuationRing.addVal_mul, htwo,
    addVal_algebraMap, ← Nat.cast_ofNat (R := 𝒪[ℚ_[2]]),
    IsDiscreteValuationRing.addVal_uniformizer (Padic.irreducible_natCast_self 2),
    ramificationIndex_eq_two,
    IsDiscreteValuationRing.addVal_uniformizer irreducible_integerSqrtTwo]
  norm_num

/-- Every nonidentity automorphism has lower index three. -/
@[simp]
theorem lowerIndex_of_ne_one {σ : DyadicSqrtTwo ≃ₐ[ℚ_[2]] DyadicSqrtTwo} (hσ : σ ≠ 1) :
    TauCeti.IsLocalRing.lowerIndex 𝒪[DyadicSqrtTwo] σ = 3 := by
  rw [TauCeti.IsLocalRing.lowerIndex_eq_addVal_of_adjoin_singleton_eq_top
    adjoin_integerSqrtTwo_eq_top, addVal_smul_sub_integerSqrtTwo_of_ne_one hσ]

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
