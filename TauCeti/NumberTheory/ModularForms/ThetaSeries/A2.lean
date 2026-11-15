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

The real model of the root lattice `typeARootLattice 2` is an even full lattice of rank `2`,
level `3` and signed discriminant `-3`. By the general-level Hecke–Schoeneberg theorem, its theta
series bundles as a weight-one modular form on `Γ₁(3)`
(`TauCeti.IntegralLattice.typeARootLatticeTwoThetaForm`) lying in the character
space `M_1(Γ₀(3), χ₋₃)` for the Kronecker character `χ₋₃ = (-3 / ·)`
(`TauCeti.IntegralLattice.typeARootLatticeTwoThetaForm_mem_modFormCharSpace`),
with both the level and the nebentypus computed from the lattice invariants rather than from an
Eisenstein series.

The subgroup `Γ₁(3)` has index `8` in `SL(2, ℤ)`, so the Sturm bound identifies this modular form
with six times the normalized weight-one Eisenstein series for `χ₋₃` from their common constant
coefficient `1` (`TauCeti.IntegralLattice.typeARootLatticeTwoThetaForm_eq`).
Thus its number of vectors of rational norm `2m` is `6 ∑_{d ∣ m} χ₋₃(d)` for every positive `m`;
in particular, its kissing number is six. The norm-two count and kissing number for all ranks are
provided by `TauCeti.IntegralLattice.representationNumber_typeARootLattice_two` and
`TauCeti.IntegralLattice.kissingNumber_typeARootLattice` in the root-lattice API.

## Main definitions

* `TauCeti.IntegralLattice.typeARootLatticeTwoThetaForm`: `Θ_{A₂}` as a bundled
  weight-one modular form on `Γ₁(3)`.

## Main statements

* `TauCeti.IntegralLattice.thetaSeries_realModel_typeARootLattice_two_slash_of_mem_Gamma0`:
  the `Γ₀(3)` transformation law `Θ_{A₂} ∣[1] A = (-3 / d) • Θ_{A₂}`.
* `TauCeti.IntegralLattice.typeARootLatticeTwoThetaForm_mem_modFormCharSpace`
  and its `iff` form: `Θ_{A₂} ∈ M_1(Γ₀(3), χ₋₃)`, and `χ₋₃` is its unique nebentypus.
* `TauCeti.IntegralLattice.typeARootLatticeTwoThetaForm_eq`,
  `TauCeti.IntegralLattice.thetaSeries_realModel_typeARootLattice_two`: bundled and function-level
  identification with `6 E₁^{1, χ₋₃}`.
* `TauCeti.IntegralLattice.thetaSeries_realModel_typeARootLattice_two_eq_tsum`,
  `TauCeti.IntegralLattice.representationNumber_typeARootLattice_two_mul`: the `q`-series and
  divisor-sum representation numbers of `A₂`.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 3.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 2, §2.3.
-/

public noncomputable section

open Complex ModularForm UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace TauCeti.IntegralLattice

local instance : NeZero (-3 : ℤ).natAbs := ⟨by decide⟩

local notation "χ₋₃" => kroneckerChar ℂ (-3) (by decide) (by decide)

private theorem a2_character_parity :
    (1 : DirichletCharacter ℂ 1) (-1) * χ₋₃ (-1) = -1 := by
  rw [DirichletCharacter.modOne_eq_one', one_mul, kroneckerChar_neg_one]
  norm_num

private theorem a2_character_primitive : χ₋₃.IsPrimitive :=
  conductor_kroneckerChar_eq_natAbs_of_prime _ _ (by decide)

/-- The theta series of the real model of `A₂`, bundled as a weight-one modular form on
`Γ₁(3)`. -/
def typeARootLatticeTwoThetaForm :
    ModularForm ((CongruenceSubgroup.Gamma1 3).map (Matrix.SpecialLinearGroup.mapGL ℝ)) 1 :=
  (ZLattice.thetaFormOfLevel
    ((isEven_realModel_iff _ (isPosDef_typeARootLattice 2)).mpr (isEven_typeARootLattice 2))
    (k := 1) (by simp [RealModelSpace.finrank_eq, finrank_carrier])).mcast rfl
    (by rw [level_realModel_typeARootLattice_two])

/-- The underlying function of `typeARootLatticeTwoThetaForm` is the theta
series of the real model of `A₂`. -/
@[simp]
theorem coe_typeARootLatticeTwoThetaForm :
    ⇑typeARootLatticeTwoThetaForm =
      ZLattice.thetaSeries ((typeARootLattice 2).realModel (isPosDef_typeARootLattice 2)) := by
  dsimp only [typeARootLatticeTwoThetaForm, ModularForm.coe_mcast]
  exact ZLattice.coe_thetaFormOfLevel _ _

/-- The `q`-expansion coefficients of `typeARootLatticeTwoThetaForm` are the
rational representation numbers of `A₂` at even norms. -/
theorem qExpansion_typeARootLatticeTwoThetaForm_coeff (m : ℕ) :
    (qExpansion 1 typeARootLatticeTwoThetaForm).coeff m =
      ((typeARootLattice 2).representationNumber (2 * m) : ℂ) := by
  rw [coe_typeARootLatticeTwoThetaForm,
    (isEven_typeARootLattice 2).qExpansion_thetaSeries_realModel_coeff
      (isPosDef_typeARootLattice 2)]

/-- The weight-one theta form of `A₂` is nonzero. -/
@[simp]
theorem typeARootLatticeTwoThetaForm_ne_zero :
    typeARootLatticeTwoThetaForm ≠ 0 := fun h ↦
  ZLattice.thetaSeries_ne_zero_of_re_eq_zero _ UpperHalfPlane.I_re (by
    rw [← coe_typeARootLatticeTwoThetaForm, h, FunLike.coe_zero]
    rfl)

/-- The weight-one theta form of `A₂` is not a cusp form: its constant term at `∞` is `1`. -/
@[simp]
theorem not_isCuspForm_typeARootLatticeTwoThetaForm :
    ¬ ModularForm.IsCuspForm typeARootLatticeTwoThetaForm :=
  ZLattice.not_isCuspForm_of_coe_eq_thetaSeries _
    coe_typeARootLatticeTwoThetaForm

/-- **Hecke–Schoeneberg transformation law for `A₂`.** Under every matrix `A ∈ Γ₀(3)`, the theta
series of the real model of `A₂` transforms in weight `1` by `(-3 / A 1 1)`. -/
theorem thetaSeries_realModel_typeARootLattice_two_slash_of_mem_Gamma0
    {A : SL(2, ℤ)} (hA : A ∈ CongruenceSubgroup.Gamma0 3) :
    ZLattice.thetaSeries
        ((typeARootLattice 2).realModel (isPosDef_typeARootLattice 2)) ∣[(1 : ℤ)] A =
      (kroneckerSym (-3) (A 1 1) : ℂ) •
        ZLattice.thetaSeries
          ((typeARootLattice 2).realModel (isPosDef_typeARootLattice 2)) := by
  have hL : ZLattice.IsEven ((typeARootLattice 2).realModel (isPosDef_typeARootLattice 2)) :=
    (isEven_realModel_iff _ (isPosDef_typeARootLattice 2)).mpr (isEven_typeARootLattice 2)
  have hA' : A ∈ CongruenceSubgroup.Gamma0
      (ZLattice.level ((typeARootLattice 2).realModel (isPosDef_typeARootLattice 2))) := by
    rwa [level_realModel_typeARootLattice_two]
  simpa only [Nat.cast_one, signedDiscr_realModel_typeARootLattice_two] using
    hL.thetaSeries_slash_of_mem_Gamma0_eq_kroneckerSym_smul
      (k := 1) (by simp [RealModelSpace.finrank_eq, finrank_carrier]) hA'

/-- **Modularity of `Θ_{A₂}` with character `χ₋₃`.** The theta form of the real model of `A₂` lies
in `M_1(Γ₀(3), χ₋₃)`, where `χ₋₃` is viewed at modulus `3`. -/
theorem typeARootLatticeTwoThetaForm_mem_modFormCharSpace :
    typeARootLatticeTwoThetaForm ∈
      TauCeti.modFormCharSpace 1
        (MulChar.equivToUnitHom (χ₋₃.changeLevel (by decide))) := by
  apply (TauCeti.mem_modFormCharSpace_iff_nebentypus _ _ _).mpr
  intro A
  have hunit : IsUnit (((A : SL(2, ℤ)) 1 1 : ℤ) : ZMod 3) := by
    simpa only [MonoidHom.coe_toHomUnits, CongruenceSubgroup.Gamma0Map_apply] using
      Units.isUnit ((CongruenceSubgroup.Gamma0Map 3).toHomUnits A)
  have hcop : IsCoprime ((A : SL(2, ℤ)) 1 1) (3 : ℕ) :=
    isCoprime_comm.mp ((ZMod.isUnit_intCast_iff_isCoprime _ _).mp hunit)
  have hchar : (χ₋₃.changeLevel (by decide : (-3 : ℤ).natAbs ∣ 3)) ((A : SL(2, ℤ)) 1 1 : ℤ) =
      (kroneckerSym (-3) ((A : SL(2, ℤ)) 1 1) : ℂ) := by
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hcop, kroneckerChar_intCast]
  simpa only [coe_typeARootLatticeTwoThetaForm, MulChar.coe_equivToUnitHom,
    MonoidHom.coe_toHomUnits, CongruenceSubgroup.Gamma0Map_apply, ModularForm.SL_slash,
    TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, hchar] using
    thetaSeries_realModel_typeARootLattice_two_slash_of_mem_Gamma0 A.property

/-- `χ₋₃` (at modulus `3`) is the unique character in `TauCeti.modFormCharSpace` for the theta
form of `A₂`. -/
theorem typeARootLatticeTwoThetaForm_mem_modFormCharSpace_iff
    (χ : (ZMod 3)ˣ →* ℂˣ) :
    typeARootLatticeTwoThetaForm ∈ TauCeti.modFormCharSpace 1 χ ↔
      χ = MulChar.equivToUnitHom (χ₋₃.changeLevel (by decide)) :=
  ⟨fun h ↦ TauCeti.eq_of_mem_modFormCharSpace_of_ne_zero h
    typeARootLatticeTwoThetaForm_mem_modFormCharSpace
    typeARootLatticeTwoThetaForm_ne_zero,
    fun h ↦ h ▸ typeARootLatticeTwoThetaForm_mem_modFormCharSpace⟩

/-- Every diamond operator `⟨d⟩` on `Γ₁(3)` acts on the theta form of `A₂` by `χ₋₃(d)`. -/
@[simp]
theorem diamondOp_typeARootLatticeTwoThetaForm (d : (ZMod 3)ˣ) :
    TauCeti.diamondOp 1 d typeARootLatticeTwoThetaForm =
      (χ₋₃.changeLevel (by decide) (d : ZMod 3) : ℂ) •
        typeARootLatticeTwoThetaForm := by
  simpa only [MulChar.coe_equivToUnitHom] using
    TauCeti.diamondOp_apply_of_mem_modFormCharSpace 1
      (MulChar.equivToUnitHom (χ₋₃.changeLevel (by decide))) d
      typeARootLatticeTwoThetaForm_mem_modFormCharSpace

/-- Every natural-number diamond operator `⟨n⟩` on `Γ₁(3)` acts on the theta form of `A₂` by
`χ₋₃(n)` (which vanishes when `3 ∣ n`). -/
@[simp]
theorem diamondOpNat_typeARootLatticeTwoThetaForm (n : ℕ) :
    TauCeti.diamondOpNat (N := 3) 1 n typeARootLatticeTwoThetaForm =
      (χ₋₃.changeLevel (by decide) (n : ZMod 3) : ℂ) •
        typeARootLatticeTwoThetaForm := by
  by_cases hn : Nat.Coprime n 3
  · rw [TauCeti.diamondOpNat_of_coprime _ hn,
      diamondOp_typeARootLatticeTwoThetaForm, ZMod.coe_unitOfCoprime]
  · have hnu : ¬ IsUnit (n : ZMod 3) := by rwa [ZMod.isUnit_iff_coprime]
    rw [TauCeti.diamondOpNat_of_not_coprime _ hn, MulChar.map_nonunit _ hnu, zero_smul,
      LinearMap.zero_apply]

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

/-- As weight-one modular forms on `Γ₁(3)` (lying in `M_1(Γ₀(3), χ₋₃)`), the theta form of the
real model of `A₂` equals six times the normalized weight-one Eisenstein series of character
`(-3 / ·)`. -/
theorem typeARootLatticeTwoThetaForm_eq :
    typeARootLatticeTwoThetaForm =
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
    a2_six_eisenstein_coeff, coe_typeARootLatticeTwoThetaForm,
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
  rw [← coe_typeARootLatticeTwoThetaForm,
    typeARootLatticeTwoThetaForm_eq]

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
