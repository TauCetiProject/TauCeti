/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.WorkedExamples.CyclotomicEight.Basic
public import TauCeti.NumberTheory.LocalField.WorkedExamples.DyadicSqrt.Two
import TauCeti.FieldTheory.Galois.FixedField

/-!
# A quotient that does not preserve lower ramification groups

Embed `ℚ₂(√2)` in `ℚ₂(ζ₈)` by `√2 ↦ ζ₈ - ζ₈³ = ζ₈ + ζ₈⁻¹`.
The image is the fixed field of the involution `ζ₈ ↦ ζ₈⁻¹`.
Restriction maps the third lower ramification group of the cyclotomic extension onto the
whole quadratic Galois group, whereas the third lower group of the quadratic extension is
trivial. This gives a concrete failure of compatibility of lower numbering with quotients.

The restriction map is Mathlib's `AlgEquiv.restrictNormalHom` for this embedding. The lower
filtrations are the canonical ones computed in the two imported worked examples.

## References

* J.-P. Serre, *Local Fields*, Chapter IV, §§1 and 3.
-/

public section
noncomputable section

open Polynomial IntermediateField

namespace TauCeti.DyadicCyclotomicEight

private theorem zetaEight_sub_cube_sq : (zetaEight - zetaEight ^ 3) ^ 2 = 2 := by
  linear_combination (zetaEight ^ 2 - 2) * zetaEight_pow_four

private def sqrtTwoPowerBasis : PowerBasis ℚ_[2] DyadicSqrtTwo :=
  PowerBasis.ofAdjoinSimpleEqTop (Algebra.IsIntegral.isIntegral DyadicSqrtTwo.sqrtTwo)
    DyadicSqrtTwo.adjoin_sqrtTwo_eq_top

@[simp]
private theorem sqrtTwoPowerBasis_gen : sqrtTwoPowerBasis.gen = DyadicSqrtTwo.sqrtTwo := by
  simp [sqrtTwoPowerBasis]

/-- The embedding `ℚ₂(√2) → ℚ₂(ζ₈)` sending `√2` to `ζ₈ - ζ₈³`. -/
def sqrtTwoEmbedding : DyadicSqrtTwo →ₐ[ℚ_[2]] DyadicCyclotomicEight :=
  sqrtTwoPowerBasis.lift (zetaEight - zetaEight ^ 3) (by
    rw [sqrtTwoPowerBasis_gen, DyadicSqrtTwo.minpoly_sqrtTwo]
    simp [zetaEight_sub_cube_sq, map_ofNat])

/-- The image of the distinguished quadratic generator. -/
@[simp]
theorem sqrtTwoEmbedding_sqrtTwo :
    sqrtTwoEmbedding DyadicSqrtTwo.sqrtTwo = zetaEight - zetaEight ^ 3 := by
  rw [sqrtTwoEmbedding, ← sqrtTwoPowerBasis_gen, PowerBasis.lift_gen]

-- Use only this embedding to construct the restriction map; the exported map below
-- retains the original quadratic carrier and its existing local-field structure.
private local instance : Algebra DyadicSqrtTwo DyadicCyclotomicEight :=
  sqrtTwoEmbedding.toRingHom.toAlgebra

private local instance : IsScalarTower ℚ_[2] DyadicSqrtTwo DyadicCyclotomicEight :=
  IsScalarTower.of_algHom sqrtTwoEmbedding

/-- Restriction from the cyclotomic Galois group to its `√2` subextension. -/
def restrictSqrtTwo : (DyadicCyclotomicEight ≃ₐ[ℚ_[2]] DyadicCyclotomicEight) →*
    (DyadicSqrtTwo ≃ₐ[ℚ_[2]] DyadicSqrtTwo) :=
  AlgEquiv.restrictNormalHom DyadicSqrtTwo

/-- Restriction commutes with the chosen embedding. -/
@[simp]
theorem sqrtTwoEmbedding_restrictSqrtTwo
    (σ : DyadicCyclotomicEight ≃ₐ[ℚ_[2]] DyadicCyclotomicEight) (x : DyadicSqrtTwo) :
    sqrtTwoEmbedding (restrictSqrtTwo σ x) = σ (sqrtTwoEmbedding x) :=
  AlgEquiv.restrictNormal_commutes σ DyadicSqrtTwo x

/-- Every quadratic automorphism extends to the cyclotomic field. -/
theorem restrictSqrtTwo_surjective : Function.Surjective restrictSqrtTwo :=
  AlgEquiv.restrictNormalHom_surjective (F := ℚ_[2])
    (K₁ := DyadicSqrtTwo) DyadicCyclotomicEight

/-- The exponent-seven involution, sending `ζ₈` to `ζ₈⁻¹`. -/
def sigmaSeven : DyadicCyclotomicEight ≃ₐ[ℚ_[2]] DyadicCyclotomicEight :=
  IsCyclotomicExtension.fromZetaAut isPrimitiveRoot_zetaEight.inv
    (irreducible_cyclotomic_prime_pow_ratPadic 2 3)

/-- The exponent-seven automorphism inverts the distinguished root. -/
@[simp]
theorem sigmaSeven_zetaEight : sigmaSeven zetaEight = zetaEight⁻¹ := by
  have h := IsCyclotomicExtension.fromZetaAut_spec isPrimitiveRoot_zetaEight.inv
    (irreducible_cyclotomic_prime_pow_ratPadic 2 3)
  rw [← zetaEight_def] at h
  exact h

private theorem inv_zetaEight : zetaEight⁻¹ = -zetaEight ^ 3 := by
  apply inv_eq_of_mul_eq_one_right
  linear_combination -zetaEight_pow_four

private theorem sigmaSeven_ne_one : sigmaSeven ≠ 1 := by
  intro h
  have hz := congrArg (fun σ : DyadicCyclotomicEight ≃ₐ[ℚ_[2]] DyadicCyclotomicEight ↦
    σ zetaEight) h
  have hsq : zetaEight ^ 2 = 1 := by
    rw [sigmaSeven_zetaEight, AlgEquiv.one_apply] at hz
    rw [pow_two]
    calc
      zetaEight * zetaEight = zetaEight * zetaEight⁻¹ := congrArg (zetaEight * ·) hz.symm
      _ = 1 := mul_inv_cancel₀ (isPrimitiveRoot_zetaEight.ne_zero (by decide))
  have hdvd := (isPrimitiveRoot_zetaEight.pow_eq_one_iff_dvd 2).1 hsq
  norm_num at hdvd

/-- The exponent-seven automorphism has order two. -/
@[simp]
theorem orderOf_sigmaSeven : orderOf sigmaSeven = 2 := by
  apply orderOf_eq_prime
  · apply AlgEquiv.coe_toAlgHom_injective
    apply (isPrimitiveRoot_zetaEight.powerBasis ℚ_[2]).algHom_ext
    simp [pow_two, AlgEquiv.mul_apply]
  · exact sigmaSeven_ne_one

private theorem sigmaSeven_sub_cube :
    sigmaSeven (zetaEight - zetaEight ^ 3) = zetaEight - zetaEight ^ 3 := by
  rw [map_sub, map_pow, sigmaSeven_zetaEight, inv_zetaEight]
  linear_combination (zetaEight ^ 5 - zetaEight) * zetaEight_pow_four

/-- The embedded quadratic field is generated by `ζ₈ - ζ₈³`. -/
theorem fieldRange_sqrtTwoEmbedding :
    sqrtTwoEmbedding.fieldRange = adjoin ℚ_[2] {zetaEight - zetaEight ^ 3} := by
  rw [AlgHom.fieldRange_eq_map, ← DyadicSqrtTwo.adjoin_sqrtTwo_eq_top,
    adjoin_map, Set.image_singleton, sqrtTwoEmbedding_sqrtTwo]

/-- The fixed field of the exponent-seven involution is the embedded copy of `ℚ₂(√2)`. -/
theorem fixedField_zpowers_sigmaSeven :
    fixedField (Subgroup.zpowers sigmaSeven) = sqrtTwoEmbedding.fieldRange := by
  have hle : sqrtTwoEmbedding.fieldRange ≤ fixedField (Subgroup.zpowers sigmaSeven) := by
    rw [fieldRange_sqrtTwoEmbedding, adjoin_le_iff, Set.singleton_subset_iff]
    exact (mem_fixedField_zpowers_iff _ _).2 sigmaSeven_sub_cube
  have hdegree := finrank_fixedField_zpowers_mul_orderOf sigmaSeven
  rw [orderOf_sigmaSeven, finrank_eq_four] at hdegree
  have hrange : Module.finrank ℚ_[2] sqrtTwoEmbedding.fieldRange = 2 := by
    rw [← sqrtTwoEmbedding.equivFieldRange.toLinearEquiv.finrank_eq, DyadicSqrtTwo.finrank_eq_two]
  exact (eq_of_le_of_finrank_eq hle (by omega)).symm

/-- The kernel of quadratic restriction is generated by the exponent-seven involution. -/
@[simp]
theorem ker_restrictSqrtTwo : restrictSqrtTwo.ker = Subgroup.zpowers sigmaSeven := by
  have heq : IsScalarTower.toAlgHom ℚ_[2] DyadicSqrtTwo DyadicCyclotomicEight =
      sqrtTwoEmbedding := by ext x; rfl
  rw [restrictSqrtTwo, AlgEquiv.ker_restrictNormalHom, heq,
    ← fixedField_zpowers_sigmaSeven, fixingSubgroup_fixedField]

/-- The inversion subgroup is normal, as the kernel of quadratic restriction. -/
instance : (Subgroup.zpowers sigmaSeven).Normal :=
  ker_restrictSqrtTwo ▸ inferInstance

/-- Restriction identifies the quotient by inversion with the quadratic Galois group. -/
def quotientEquivSqrtTwo :
    (DyadicCyclotomicEight ≃ₐ[ℚ_[2]] DyadicCyclotomicEight) ⧸ Subgroup.zpowers sigmaSeven ≃*
      (DyadicSqrtTwo ≃ₐ[ℚ_[2]] DyadicSqrtTwo) :=
  QuotientGroup.liftEquiv _ restrictSqrtTwo_surjective ker_restrictSqrtTwo.symm

/-- On a cyclotomic automorphism's class, the quotient equivalence is restriction. -/
@[simp]
theorem quotientEquivSqrtTwo_mk
    (σ : DyadicCyclotomicEight ≃ₐ[ℚ_[2]] DyadicCyclotomicEight) :
    quotientEquivSqrtTwo (σ :
      (DyadicCyclotomicEight ≃ₐ[ℚ_[2]] DyadicCyclotomicEight) ⧸ Subgroup.zpowers sigmaSeven) =
        restrictSqrtTwo σ :=
  QuotientGroup.liftEquiv_mk _ restrictSqrtTwo_surjective ker_restrictSqrtTwo.symm σ

/-- The restriction of the exponent-five automorphism negates `√2`. -/
@[simp]
theorem restrictSqrtTwo_sigmaFive_sqrtTwo :
    restrictSqrtTwo sigmaFive DyadicSqrtTwo.sqrtTwo = -DyadicSqrtTwo.sqrtTwo := by
  have h : sqrtTwoEmbedding (restrictSqrtTwo sigmaFive DyadicSqrtTwo.sqrtTwo) =
      sqrtTwoEmbedding (-DyadicSqrtTwo.sqrtTwo) := by
    simp only [sqrtTwoEmbedding_restrictSqrtTwo, sqrtTwoEmbedding_sqrtTwo, map_sub, map_pow,
      sigmaFive_zetaEight, map_neg]
    ring
  exact sqrtTwoEmbedding.injective h

private theorem restrictSqrtTwo_sigmaFive_ne_one : restrictSqrtTwo sigmaFive ≠ 1 := by
  intro h
  have hz := congrArg (fun σ : DyadicSqrtTwo ≃ₐ[ℚ_[2]] DyadicSqrtTwo ↦
    σ DyadicSqrtTwo.sqrtTwo) h
  simp only [restrictSqrtTwo_sigmaFive_sqrtTwo, AlgEquiv.one_apply] at hz
  have hzero : DyadicSqrtTwo.sqrtTwo = 0 := by linear_combination -hz / 2
  have hsq := DyadicSqrtTwo.sqrtTwo_sq
  rw [hzero] at hsq
  norm_num at hsq

/-- The third cyclotomic lower ramification group restricts onto the whole quadratic group. -/
-- Use as a rewrite lemma: `simp` first computes the source lower group.
theorem map_restrictSqrtTwo_lowerRamificationGroup_three_eq_top :
    (LocalFieldsRamification.lowerRamificationGroup ℚ_[2] DyadicCyclotomicEight 3).map
      restrictSqrtTwo = ⊤ := by
  rw [lowerRamificationGroup_eq]
  norm_num only
  apply top_unique
  intro σ _
  by_cases hσ : σ = 1
  · subst σ
    exact Subgroup.one_mem _
  · have heq : σ = restrictSqrtTwo sigmaFive := by
      apply AlgEquiv.coe_toAlgHom_injective
      apply sqrtTwoPowerBasis.algHom_ext
      rw [sqrtTwoPowerBasis_gen]
      exact (DyadicSqrtTwo.apply_sqrtTwo_of_ne_one hσ).trans
        (restrictSqrtTwo_sigmaFive_sqrtTwo).symm
    exact heq ▸ Subgroup.mem_map.2 ⟨sigmaFive, Subgroup.mem_zpowers _, rfl⟩

/-- Lower numbering fails to commute with this restriction: the image at depth three is
the whole quadratic Galois group, but the quadratic lower group at depth three is trivial. -/
theorem map_restrictSqrtTwo_lowerRamificationGroup_three_ne :
    (LocalFieldsRamification.lowerRamificationGroup ℚ_[2] DyadicCyclotomicEight 3).map
      restrictSqrtTwo ≠
        LocalFieldsRamification.lowerRamificationGroup ℚ_[2] DyadicSqrtTwo 3 := by
  rw [map_restrictSqrtTwo_lowerRamificationGroup_three_eq_top,
    DyadicSqrtTwo.lowerRamificationGroup_eq]
  norm_num only [ite_false]
  intro h
  exact restrictSqrtTwo_sigmaFive_ne_one
    (Subgroup.mem_bot.1 (h ▸ Subgroup.mem_top (restrictSqrtTwo sigmaFive)))

/-- In quotient notation, `G₃H/H = G/H` for the inversion subgroup `H`. -/
-- Use as a rewrite lemma: `simp` first computes the source lower group.
theorem map_mk_lowerRamificationGroup_three_eq_top :
    (LocalFieldsRamification.lowerRamificationGroup ℚ_[2] DyadicCyclotomicEight 3).map
      (QuotientGroup.mk' (Subgroup.zpowers sigmaSeven)) = ⊤ := by
  have hcomp : quotientEquivSqrtTwo.toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.zpowers sigmaSeven)) = restrictSqrtTwo := by
    apply MonoidHom.ext
    intro σ
    exact quotientEquivSqrtTwo_mk σ
  apply Subgroup.map_injective (f := quotientEquivSqrtTwo.toMonoidHom)
    quotientEquivSqrtTwo.injective
  rw [Subgroup.map_map, hcomp, map_restrictSqrtTwo_lowerRamificationGroup_three_eq_top,
    Subgroup.map_top]
  exact (MonoidHom.range_eq_top (f := quotientEquivSqrtTwo.toMonoidHom)).2
    quotientEquivSqrtTwo.surjective |>.symm

end TauCeti.DyadicCyclotomicEight
