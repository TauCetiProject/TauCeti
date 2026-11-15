/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ThetaSeries.RealModel
public import TauCeti.Algebra.Module.ZLattice.RootLattice
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightOne.Normalized
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightOne.ConstantTerm
import TauCeti.NumberTheory.ModularForms.ThetaSeries.Cusp
import TauCeti.NumberTheory.ModularForms.ThetaSeries.GeneralLevel
import TauCeti.NumberTheory.ModularForms.SturmBound
import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# The theta series of A₂

The real model of the root lattice `typeARootLattice 2` has theta series equal to six times
the normalized weight-one Eisenstein series for the Kronecker character `χ₋₃ = (-3 / ·)`.
Thus its number of vectors of rational norm `2m` is `6 ∑_{d ∣ m} χ₋₃(d)` for every positive
`m`; in particular, its kissing number is six.
The norm-two count and kissing number for all ranks are provided by
`TauCeti.IntegralLattice.representationNumber_typeARootLattice_two` and
`TauCeti.IntegralLattice.kissingNumber_typeARootLattice` in the root-lattice API.

Both series are weight-one modular forms on `Γ₁(3)`. The index of this subgroup is eight,
so the Sturm bound identifies them from their common constant coefficient one.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 3.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 2, §2.3.
-/

public noncomputable section

open Complex ModularForm UpperHalfPlane
open scoped MatrixGroups

namespace TauCeti.IntegralLattice

local instance : NeZero (-3 : ℤ).natAbs := ⟨by decide⟩

local notation "χ₋₃" => kroneckerChar ℂ (-3) (by decide) (by decide)

private theorem a2_character_parity :
    (1 : DirichletCharacter ℂ 1) (-1) * χ₋₃ (-1) = -1 := by
  rw [DirichletCharacter.modOne_eq_one', one_mul, kroneckerChar_neg_one]
  norm_num

private theorem a2_character_primitive : χ₋₃.IsPrimitive :=
  conductor_kroneckerChar_eq_natAbs_of_prime _ _ (by decide)

private def a2ThetaForm :
    ModularForm ((CongruenceSubgroup.Gamma1 3).map (Matrix.SpecialLinearGroup.mapGL ℝ)) 1 :=
  (ZLattice.thetaFormOfLevel
    ((isEven_realModel_iff _ (isPosDef_typeARootLattice 2)).mpr (isEven_typeARootLattice 2))
    (k := 1) (by simp [RealModelSpace.finrank_eq, finrank_carrier])).mcast rfl
    (by rw [level_realModel_typeARootLattice_two])

private theorem coe_a2ThetaForm : ⇑a2ThetaForm = ZLattice.thetaSeries
    ((typeARootLattice 2).realModel (isPosDef_typeARootLattice 2)) := by
  dsimp only [a2ThetaForm, ModularForm.coe_mcast]
  exact ZLattice.coe_thetaFormOfLevel _ _

private theorem a2_eisenstein_constant :
    (qExpansion 1 (EisensteinSeries.normalizedCharE1MF
      (1 : DirichletCharacter ℂ 1) χ₋₃ (N := 3) (by decide))).coeff 0 = 1 / 6 := by
  rw [EisensteinSeries.qExpansion_normalizedCharE1MF_coeff_zero _ _ _
    a2_character_parity a2_character_primitive]
  rw [DirichletCharacter.generalizedBernoulli_one_kroneckerChar_neg_three]
  norm_num

private theorem a2_eisenstein_coeff {m : ℕ} (hm : m ≠ 0) :
    (qExpansion 1 (EisensteinSeries.normalizedCharE1MF
      (1 : DirichletCharacter ℂ 1) χ₋₃ (N := 3) (by decide))).coeff m =
      ∑ d ∈ m.divisors, (kroneckerSym (-3) d : ℂ) := by
  rw [EisensteinSeries.qExpansion_normalizedCharE1MF_coeff _ _ _
    a2_character_parity a2_character_primitive hm, DirichletCharacter.twistedDivisorSum_apply]
  simp only [DirichletCharacter.modOne_eq_one', one_mul, pow_zero, mul_one,
    kroneckerChar_natCast]

private theorem a2_six_eisenstein_coeff (m : ℕ) :
    (qExpansion 1 ⇑((6 : ℂ) • EisensteinSeries.normalizedCharE1MF
      (1 : DirichletCharacter ℂ 1) χ₋₃ (N := 3) (by decide))).coeff m =
      6 * (qExpansion 1 (EisensteinSeries.normalizedCharE1MF
        (1 : DirichletCharacter ℂ 1) χ₋₃ (N := 3) (by decide))).coeff m := by
  rw [FunLike.coe_smul, ModularForm.qExpansion_smul one_pos
    (TauCeti.one_mem_strictPeriods_Gamma1_map 3), PowerSeries.coeff_smul, smul_eq_mul]

/-- The theta series of the real model of `A₂` is six times the normalized weight-one
Eisenstein series of character `(-3 / ·)` with first coefficient one, giving constant
coefficient one. -/
theorem thetaSeries_realModel_typeARootLattice_two :
    ZLattice.thetaSeries ((typeARootLattice 2).realModel (isPosDef_typeARootLattice 2)) =
      ⇑((6 : ℂ) • EisensteinSeries.normalizedCharE1MF
        (1 : DirichletCharacter ℂ 1) χ₋₃ (N := 3) (by decide)) := by
  have hindex : (CongruenceSubgroup.Gamma1 3).index = 8 := by
    rw [CongruenceSubgroup.Gamma1_index,
      CongruenceSubgroup.Gamma0_prime_index 3 Nat.prime_three, Nat.card_eq_fintype_card]
    decide
  have hzero : a2ThetaForm - (6 : ℂ) • EisensteinSeries.normalizedCharE1MF
      (1 : DirichletCharacter ℂ 1) χ₋₃ (N := 3) (by decide) = 0 := by
    apply ModularForm.sturm_bound_finiteIndex_SL2Z
    rw [CongruenceSubgroup.strictWidthInfty_Gamma1, hindex]
    norm_num only [Int.cast_ofNat, one_mul, Int.toNat_natCast, Nat.reduceDiv]
    apply lt_of_lt_of_le (by norm_num : (0 : ℕ∞) < 1)
    apply PowerSeries.nat_le_order
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    rw [FunLike.coe_sub, ModularForm.qExpansion_sub one_pos
      (TauCeti.one_mem_strictPeriods_Gamma1_map 3), map_sub,
      a2_six_eisenstein_coeff, coe_a2ThetaForm,
      ZLattice.IsEven.qExpansion_thetaSeries_coeff_zero
        ((isEven_realModel_iff _ _).mpr (isEven_typeARootLattice 2)),
      a2_eisenstein_constant]
    norm_num
  rw [← coe_a2ThetaForm, sub_eq_zero.mp hzero]

/-- The classical expansion `Θ_{A₂}(τ) = 1 + 6 ∑_{m ≥ 1} (∑_{d ∣ m} (-3 / d)) q^m`,
where `q = exp (2 π i τ)`. -/
theorem thetaSeries_realModel_typeARootLattice_two_eq_tsum (τ : ℍ) :
    ZLattice.thetaSeries ((typeARootLattice 2).realModel (isPosDef_typeARootLattice 2)) τ =
      1 + 6 * ∑' m : ℕ, (∑ d ∈ (m + 1).divisors, (kroneckerSym (-3) d : ℂ)) *
        Function.Periodic.qParam 1 τ ^ (m + 1) := by
  let E := EisensteinSeries.normalizedCharE1MF
    (1 : DirichletCharacter ℂ 1) χ₋₃ (N := 3) (by decide)
  have hs := ModularForm.hasSum_qExpansion E one_pos
    (TauCeti.one_mem_strictPeriods_Gamma1_map 3) τ
  have ht := hs.summable.sum_add_tsum_nat_add 1
  rw [hs.tsum_eq] at ht
  simp only [Finset.sum_range_one, pow_zero, mul_one] at ht
  have hcoeff (m : ℕ) : (qExpansion 1 E).coeff (m + 1) =
      ∑ d ∈ (m + 1).divisors, (kroneckerSym (-3) d : ℂ) :=
    a2_eisenstein_coeff (by omega)
  simp_rw [hcoeff] at ht
  rw [a2_eisenstein_constant] at ht
  rw [thetaSeries_realModel_typeARootLattice_two]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  linear_combination -6 * ht

/-- The number of vectors of norm `2m` in `A₂` is six times the divisor sum of the Kronecker
character `(-3 / ·)`, for every positive `m`. -/
theorem representationNumber_typeARootLattice_two_mul {m : ℕ} (hm : m ≠ 0) :
    ((typeARootLattice 2).representationNumber (2 * m) : ℤ) =
      6 * ∑ d ∈ m.divisors, kroneckerSym (-3) d := by
  have hcoeff := (isEven_typeARootLattice 2).qExpansion_thetaSeries_realModel_coeff
    (isPosDef_typeARootLattice 2) m
  rw [thetaSeries_realModel_typeARootLattice_two, a2_six_eisenstein_coeff,
    a2_eisenstein_coeff hm] at hcoeff
  exact_mod_cast hcoeff.symm

end TauCeti.IntegralLattice
