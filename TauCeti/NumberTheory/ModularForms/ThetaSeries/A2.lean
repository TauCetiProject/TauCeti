/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ThetaSeries.RealModel
public import TauCeti.Algebra.Module.ZLattice.RootLattice
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightOne.Normalized
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Character
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightOne.ConstantTerm
import TauCeti.NumberTheory.ModularForms.ThetaSeries.Cusp
import TauCeti.NumberTheory.ModularForms.ThetaSeries.GeneralLevel
import TauCeti.NumberTheory.ModularForms.SturmBound
import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# The theta series of A₂

The root lattice `A₂ = typeARootLattice 2` has rank `2`, level `3`, and signed discriminant `-3`.
Through the general-level Hecke–Schoeneberg theorem, the theta series of its real model bundles as
a weight-one modular form `thetaFormRealModelTypeARootLatticeTwo` on `Γ₁(3)` lying in the
character space `M₁(Γ₀(3), χ₋₃)` for the primitive Kronecker character `χ₋₃ = (-3 / ·)`, with
level, signed discriminant, nebentypus, and diamond eigenvalues computed directly from the lattice.

Both this theta form and six times the normalized weight-one Eisenstein series for `χ₋₃` are
weight-one modular forms on `Γ₁(3)`. The index of `Γ₁(3)` in `SL(2, ℤ)` is eight, so the Sturm
bound (`⌊8 / 12⌋ = 0`) identifies them in `M₁(Γ₁(3))` — and hence in `M₁(Γ₀(3), χ₋₃)` — from
their common constant coefficient one. Thus the number of vectors of rational norm `2m` in `A₂` is
`6 ∑_{d ∣ m} χ₋₃(d)` for every positive `m`; in particular, its kissing number is six.
The norm-two count and kissing number for all ranks are provided by
`TauCeti.IntegralLattice.representationNumber_typeARootLattice_two` and
`TauCeti.IntegralLattice.kissingNumber_typeARootLattice` in the root-lattice API.

## Main definitions

* `TauCeti.IntegralLattice.thetaFormRealModelTypeARootLatticeTwo`: the theta series of the real
  model of `A₂`, bundled as a weight-one modular form on `Γ₁(3)`.

## Main statements

* `TauCeti.IntegralLattice.changeLevel_thetaCharacter_realModel_typeARootLattice_two`: the
  lattice's quadratic theta character at level `3` agrees with `χ₋₃`.
* `TauCeti.IntegralLattice.thetaFormRealModelTypeARootLatticeTwo_mem_modFormCharSpace`,
  `TauCeti.IntegralLattice.diamondOpNat_thetaFormRealModelTypeARootLatticeTwo`:
  `Θ_{A₂}` lies in `M₁(Γ₀(3), χ₋₃)` (`TauCeti.modFormCharSpace` for `χ₋₃` at modulus `3`), with
  diamond eigenvalues `(-3 / n)`.
* `TauCeti.IntegralLattice.thetaSeries_realModel_typeARootLattice_two_slash_of_mem_Gamma0`:
  `Θ_{A₂} ∣[1] A = (-3 / A 1 1) • Θ_{A₂}` for every `A ∈ Γ₀(3)`.
* `TauCeti.IntegralLattice.thetaFormRealModelTypeARootLatticeTwo_eq_smul_normalizedCharE1MF`,
  `TauCeti.IntegralLattice.thetaSeries_realModel_typeARootLattice_two`: equality of `Θ_{A₂}` with
  six times the normalized weight-one Eisenstein series of character `χ₋₃`, as modular forms and
  as functions on `ℍ`.
* `TauCeti.IntegralLattice.thetaSeries_realModel_typeARootLattice_two_eq_tsum`: the convergent
  expansion `Θ_{A₂}(τ) = 1 + 6 ∑_{m ≥ 1} (∑_{d ∣ m} (-3 / d)) q^m`.
* `TauCeti.IntegralLattice.representationNumber_typeARootLattice_two_mul`:
  `r_{A₂}(2m) = 6 ∑_{d ∣ m} (-3 / d)` for `m ≠ 0`.

## References

* W. Ebeling, *Lattices and Codes*, third edition, Chapter 3.
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
      χ₋₃.changeLevel (by decide) := by
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

/-- The theta series of the real model of the root lattice `A₂`, bundled as a weight-one modular
form on `Γ₁(3)` via `ZLattice.thetaFormOfLevel` and `level_realModel_typeARootLattice_two`. -/
def thetaFormRealModelTypeARootLatticeTwo :
    ModularForm ((CongruenceSubgroup.Gamma1 3).map (Matrix.SpecialLinearGroup.mapGL ℝ)) 1 :=
  (ZLattice.thetaFormOfLevel
    ((isEven_realModel_iff _ (isPosDef_typeARootLattice 2)).mpr (isEven_typeARootLattice 2))
    (k := 1) (by simp [finrank_carrier])).mcast rfl
    (by rw [level_realModel_typeARootLattice_two])

/-- The underlying function of the bundled `A₂` theta form is the lattice theta series. -/
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

/-- **Modularity of `Θ_{A₂}` with character `χ₋₃`**: the bundled `A₂` theta form lies in
`M₁(Γ₀(3), χ₋₃)`, proved directly from the lattice invariants `level A₂ = 3` and
`signedDiscr A₂ = -3`. -/
theorem thetaFormRealModelTypeARootLatticeTwo_mem_modFormCharSpace :
    thetaFormRealModelTypeARootLatticeTwo ∈
      TauCeti.modFormCharSpace 1
        (MulChar.equivToUnitHom (χ₋₃.changeLevel (by decide))) :=
  ZLattice.mcast_thetaFormOfLevel_mem_modFormCharSpace _ _
    level_realModel_typeARootLattice_two fun _ ha ↦ by
      rw [DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ ha, kroneckerChar_intCast,
        signedDiscr_realModel_typeARootLattice_two]

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

/-- Under every matrix `A ∈ Γ₀(3)`, the theta series of the real model of `A₂` transforms in
weight one by the Kronecker symbol `(-3 / d)` of its lower-right entry `d = A 1 1`. -/
theorem thetaSeries_realModel_typeARootLattice_two_slash_of_mem_Gamma0 {A : SL(2, ℤ)}
    (hA : A ∈ CongruenceSubgroup.Gamma0 3) :
    ZLattice.thetaSeries ((typeARootLattice 2).realModel (isPosDef_typeARootLattice 2))
        ∣[(1 : ℤ)] A =
      (kroneckerSym (-3) (A 1 1) : ℂ) •
        ZLattice.thetaSeries ((typeARootLattice 2).realModel (isPosDef_typeARootLattice 2)) := by
  have hmem := (TauCeti.mem_modFormCharSpace_iff_nebentypus _ _ _).mp
    thetaFormRealModelTypeARootLatticeTwo_mem_modFormCharSpace ⟨A, hA⟩
  have hunit : IsUnit ((A 1 1 : ℤ) : ZMod 3) := by
    simpa [CongruenceSubgroup.Gamma0Map_apply] using
      ((CongruenceSubgroup.Gamma0Map 3).toHomUnits ⟨A, hA⟩).isUnit
  have ha : IsCoprime (A 1 1) 3 :=
    isCoprime_comm.mp ((ZMod.isUnit_intCast_iff_isCoprime _ _).mp hunit)
  simpa only [coe_thetaFormRealModelTypeARootLatticeTwo, ModularForm.SL_slash,
    TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, MulChar.coe_equivToUnitHom,
    MonoidHom.coe_toHomUnits, CongruenceSubgroup.Gamma0Map_apply,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ ha, kroneckerChar_intCast] using hmem

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

/-- As weight-one modular forms on `Γ₁(3)` (and hence in `M₁(Γ₀(3), χ₋₃)`), the theta form of
the real model of `A₂` equals six times the normalized weight-one Eisenstein series of character
`(-3 / ·)` with first coefficient one. -/
theorem thetaFormRealModelTypeARootLatticeTwo_eq_smul_normalizedCharE1MF :
    thetaFormRealModelTypeARootLatticeTwo =
      (6 : ℂ) • EisensteinSeries.normalizedCharE1MF
        (1 : DirichletCharacter ℂ 1) χ₋₃ (N := 3) (by decide) := by
  have hindex : (CongruenceSubgroup.Gamma1 3).index = 8 := by
    rw [CongruenceSubgroup.Gamma1_index,
      CongruenceSubgroup.Gamma0_prime_index 3 Nat.prime_three, Nat.card_eq_fintype_card]
    decide
  rw [← sub_eq_zero]
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
  rw [← coe_thetaFormRealModelTypeARootLatticeTwo,
    thetaFormRealModelTypeARootLatticeTwo_eq_smul_normalizedCharE1MF]

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
