/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ThetaSeries.RealModel
public import TauCeti.Algebra.Module.ZLattice.RootLattice
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightOne.Normalized
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.GeneralLevel
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightOne.ConstantTerm
import TauCeti.NumberTheory.ModularForms.ThetaSeries.Cusp
import TauCeti.NumberTheory.ModularForms.SturmBound
import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# The theta series of A₂

The real model of the root lattice `typeARootLattice 2` has level `3` and signed discriminant `-3`.
Its general-level theta form `thetaFormRealModelTypeARootLatticeTwo` is a weight-one modular form on
`Γ₁(3)` with quadratic nebentypus `χ₋₃ = (-3 / ·)`, equal to six times the normalized weight-one
Eisenstein series for `χ₋₃`. Thus its number of vectors of rational norm `2m` is
`6 ∑_{d ∣ m} χ₋₃(d)` for every positive `m`; in particular, its kissing number is six.
The norm-two count and kissing number for all ranks are provided by
`TauCeti.IntegralLattice.representationNumber_typeARootLattice_two` and
`TauCeti.IntegralLattice.kissingNumber_typeARootLattice` in the root-lattice API.

Both series lie in `M_1(Γ₁(3), χ₋₃)`. The index of `Γ₁(3)` in `SL(2, ℤ)` is eight, so the Sturm
bound identifies the two modular forms from their common constant coefficient one.

## Main definitions

* `TauCeti.IntegralLattice.thetaFormRealModelTypeARootLatticeTwo`: the theta series of `A₂` as a
  weight-one modular form on `Γ₁(3)`.

## Main statements

* `TauCeti.IntegralLattice.changeLevel_thetaCharacter_realModel_typeARootLattice_two`: the lattice's
  quadratic theta character at level `3` agrees with `χ₋₃`.
* `TauCeti.IntegralLattice.thetaSeries_realModel_typeARootLattice_two_slash_of_mem_Gamma0`: under
  `A ∈ Γ₀(3)`, `Θ_{A₂}` transforms by `(-3 / A 1 1)`.
* `TauCeti.IntegralLattice.thetaFormRealModelTypeARootLatticeTwo_mem_modFormCharSpace`,
  `TauCeti.IntegralLattice.diamondOpNat_thetaFormRealModelTypeARootLatticeTwo`: `Θ_{A₂}` belongs to
  `M_1(Γ₁(3), χ₋₃)`, with diamond eigenvalues `(-3 / n)`.
* `TauCeti.IntegralLattice.thetaFormRealModelTypeARootLatticeTwo_eq`,
  `TauCeti.IntegralLattice.thetaSeries_realModel_typeARootLattice_two`: `Θ_{A₂} = 6 E₁^{1, χ₋₃}`.
* `TauCeti.IntegralLattice.representationNumber_typeARootLattice_two_mul`: for `m ≠ 0`,
  `r_{A₂}(2m) = 6 ∑_{d ∣ m} (-3 / d)`.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 3.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 2, §2.3.
-/

public noncomputable section

open Complex ModularForm UpperHalfPlane Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

namespace TauCeti.IntegralLattice

local notation "χ₋₃" => kroneckerChar ℂ (-3) (by decide) (by decide)

private theorem a2_character_parity :
    (1 : DirichletCharacter ℂ 1) (-1) * χ₋₃ (-1) = -1 := by
  rw [DirichletCharacter.modOne_eq_one', one_mul, kroneckerChar_neg_one]
  norm_num

private theorem a2_character_primitive : χ₋₃.IsPrimitive := by
  have : NeZero (-3 : ℤ).natAbs := ⟨by decide⟩
  exact conductor_kroneckerChar_eq_natAbs_of_prime _ _ (by decide)

/-- The quadratic theta character of the real `A₂` lattice, cast along `level = 3`, equals the
Kronecker character `χ₋₃ = (-3 / ·)` at modulus `3`. -/
theorem changeLevel_thetaCharacter_realModel_typeARootLattice_two :
    DirichletCharacter.changeLevel (dvd_of_eq level_realModel_typeARootLattice_two)
      (((isEven_realModel_iff _ (isPosDef_typeARootLattice 2)).mpr
        (isEven_typeARootLattice 2)).thetaCharacter (by simp [finrank_carrier])) =
      DirichletCharacter.changeLevel (by decide : (-3 : ℤ).natAbs ∣ 3) χ₋₃ := by
  ext u
  obtain ⟨a, ha⟩ := ZMod.intCast_surjective (u : ZMod 3)
  have hcop : IsCoprime a 3 :=
    isCoprime_comm.mp ((ZMod.isUnit_intCast_iff_isCoprime a 3).mp (ha ▸ u.isUnit))
  have hcop' : IsCoprime a
      (ZLattice.level ((typeARootLattice 2).realModel (isPosDef_typeARootLattice 2))) := by
    rwa [level_realModel_typeARootLattice_two]
  rw [← ha, DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hcop,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hcop,
    ZLattice.IsEven.thetaCharacter_intCast _ _ hcop', signedDiscr_realModel_typeARootLattice_two,
    kroneckerChar_intCast]

/-- Under `A ∈ Γ₀(3)`, the theta series of the real `A₂` lattice transforms in weight `1` by the
Kronecker symbol `(-3 / A 1 1)`. -/
theorem thetaSeries_realModel_typeARootLattice_two_slash_of_mem_Gamma0 {A : SL(2, ℤ)}
    (hA : A ∈ CongruenceSubgroup.Gamma0 3) :
    ZLattice.thetaSeries ((typeARootLattice 2).realModel (isPosDef_typeARootLattice 2)) ∣[(1 : ℤ)]
      A = (kroneckerSym (-3) (A 1 1) : ℂ) •
        ZLattice.thetaSeries ((typeARootLattice 2).realModel (isPosDef_typeARootLattice 2)) := by
  have hL : ZLattice.IsEven ((typeARootLattice 2).realModel (isPosDef_typeARootLattice 2)) :=
    (isEven_realModel_iff _ (isPosDef_typeARootLattice 2)).mpr (isEven_typeARootLattice 2)
  have hA' : A ∈ CongruenceSubgroup.Gamma0
      (ZLattice.level ((typeARootLattice 2).realModel (isPosDef_typeARootLattice 2))) := by
    rwa [level_realModel_typeARootLattice_two]
  have hcop : IsCoprime (A 1 1)
      (ZLattice.level ((typeARootLattice 2).realModel (isPosDef_typeARootLattice 2))) := by
    have hu : IsUnit ((A 1 1 : ℤ) :
        ZMod (ZLattice.level ((typeARootLattice 2).realModel (isPosDef_typeARootLattice 2)))) := by
      simpa only [CongruenceSubgroup.Gamma0Map_apply, MonoidHom.coe_toHomUnits] using
        ((CongruenceSubgroup.Gamma0Map _).toHomUnits ⟨A, hA'⟩).isUnit
    exact isCoprime_comm.mp ((ZMod.isUnit_intCast_iff_isCoprime _ _).mp hu)
  have hslash := hL.thetaSeries_slash_of_mem_Gamma0 (k := 1) (by simp [finrank_carrier]) hA'
  rw [Nat.cast_one] at hslash
  rw [hslash, hL.thetaCharacter_intCast _ hcop, signedDiscr_realModel_typeARootLattice_two]

/-- The theta series of the real model of `A₂` as a weight-one modular form on `Γ₁(3)`. -/
def thetaFormRealModelTypeARootLatticeTwo :
    ModularForm ((CongruenceSubgroup.Gamma1 3).map (mapGL ℝ)) 1 :=
  (ZLattice.thetaFormOfLevel
    ((isEven_realModel_iff _ (isPosDef_typeARootLattice 2)).mpr (isEven_typeARootLattice 2))
    (k := 1) (by simp [finrank_carrier])).mcast rfl
    (by rw [level_realModel_typeARootLattice_two])

/-- The underlying function of `thetaFormRealModelTypeARootLatticeTwo` is `Θ_{A₂}`. -/
@[simp]
theorem coe_thetaFormRealModelTypeARootLatticeTwo :
    ⇑thetaFormRealModelTypeARootLatticeTwo =
      ZLattice.thetaSeries ((typeARootLattice 2).realModel (isPosDef_typeARootLattice 2)) := by
  dsimp only [thetaFormRealModelTypeARootLatticeTwo, ModularForm.coe_mcast]
  exact ZLattice.coe_thetaFormOfLevel _ _

/-- The `A₂` theta form is nonzero. -/
@[simp]
theorem thetaFormRealModelTypeARootLatticeTwo_ne_zero :
    thetaFormRealModelTypeARootLatticeTwo ≠ 0 := fun h ↦
  ZLattice.thetaSeries_ne_zero_of_re_eq_zero _ UpperHalfPlane.I_re (by
    rw [← coe_thetaFormRealModelTypeARootLatticeTwo, h, FunLike.coe_zero]
    rfl)

/-- The `A₂` theta form is not a cusp form. -/
@[simp]
theorem not_isCuspForm_thetaFormRealModelTypeARootLatticeTwo :
    ¬ ModularForm.IsCuspForm thetaFormRealModelTypeARootLatticeTwo :=
  ZLattice.not_isCuspForm_of_coe_eq_thetaSeries _ coe_thetaFormRealModelTypeARootLatticeTwo

/-- The `A₂` theta form lies in `M_1(Γ₁(3), χ₋₃)`, with nebentypus computed from the lattice's
signed discriminant `-3`. -/
theorem thetaFormRealModelTypeARootLatticeTwo_mem_modFormCharSpace :
    thetaFormRealModelTypeARootLatticeTwo ∈
      TauCeti.modFormCharSpace 1
        (MulChar.equivToUnitHom
          (DirichletCharacter.changeLevel (by decide : (-3 : ℤ).natAbs ∣ 3) χ₋₃)) := by
  rw [← changeLevel_thetaCharacter_realModel_typeARootLattice_two]
  exact ZLattice.mcast_thetaFormOfLevel_mem_modFormCharSpace _ _
    level_realModel_typeARootLattice_two

/-- Every natural-indexed diamond operator `⟨n⟩` acts on `thetaFormRealModelTypeARootLatticeTwo`
with eigenvalue `(-3 / n)`. -/
@[simp]
theorem diamondOpNat_thetaFormRealModelTypeARootLatticeTwo (n : ℕ) :
    TauCeti.diamondOpNat 1 n thetaFormRealModelTypeARootLatticeTwo =
      (kroneckerSym (-3) n : ℂ) • thetaFormRealModelTypeARootLatticeTwo := by
  by_cases hn : n.Coprime 3
  · have hcop : IsCoprime (n : ℤ) 3 := Nat.isCoprime_iff_coprime.mpr hn
    rw [TauCeti.diamondOpNat_of_coprime _ hn,
      TauCeti.diamondOp_apply_of_mem_modFormCharSpace _ _ _
        thetaFormRealModelTypeARootLatticeTwo_mem_modFormCharSpace,
      MulChar.coe_equivToUnitHom, ZMod.coe_unitOfCoprime, ← Int.cast_natCast n,
      DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hcop, kroneckerChar_intCast]
  · have hgcd : (-3 : ℤ).gcd n ≠ 1 := fun h ↦ hn <| by
      rw [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_natCast] at h
      exact Nat.coprime_comm.mp h
    rw [TauCeti.diamondOpNat_of_not_coprime _ hn, LinearMap.zero_apply,
      kroneckerSym_eq_zero_iff.mpr hgcd, Int.cast_zero, zero_smul]

private theorem a2_eisenstein_constant :
    (qExpansion 1 (EisensteinSeries.normalizedCharE1MF
      (1 : DirichletCharacter ℂ 1) χ₋₃ (N := 3) (by decide))).coeff 0 = 1 / 6 := by
  have : NeZero (-3 : ℤ).natAbs := ⟨by decide⟩
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

/-- As modular forms on `Γ₁(3)`, the theta form of `A₂` equals six times the normalized weight-one
Eisenstein series of character `χ₋₃`. -/
theorem thetaFormRealModelTypeARootLatticeTwo_eq :
    thetaFormRealModelTypeARootLatticeTwo =
      (6 : ℂ) • EisensteinSeries.normalizedCharE1MF
        (1 : DirichletCharacter ℂ 1) χ₋₃ (N := 3) (by decide) := by
  have hindex : (CongruenceSubgroup.Gamma1 3).index = 8 := by
    rw [CongruenceSubgroup.Gamma1_index,
      CongruenceSubgroup.Gamma0_prime_index 3 Nat.prime_three, Nat.card_eq_fintype_card]
    decide
  apply sub_eq_zero.mp
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
    a2_six_eisenstein_coeff, coe_thetaFormRealModelTypeARootLatticeTwo,
    ZLattice.IsEven.qExpansion_thetaSeries_coeff_zero
      ((isEven_realModel_iff _ _).mpr (isEven_typeARootLattice 2)),
    a2_eisenstein_constant]
  norm_num

/-- The theta series of the real model of `A₂` is six times the normalized weight-one
Eisenstein series of character `(-3 / ·)` with first coefficient one, giving constant
coefficient one. -/
theorem thetaSeries_realModel_typeARootLattice_two :
    ZLattice.thetaSeries ((typeARootLattice 2).realModel (isPosDef_typeARootLattice 2)) =
      ⇑((6 : ℂ) • EisensteinSeries.normalizedCharE1MF
        (1 : DirichletCharacter ℂ 1) χ₋₃ (N := 3) (by decide)) := by
  rw [← coe_thetaFormRealModelTypeARootLatticeTwo, thetaFormRealModelTypeARootLatticeTwo_eq]

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
