/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import TauCeti.NumberTheory.NumberField.Cyclotomic.MaximalRealSubfield
public import TauCeti.NumberTheory.NumberField.Cyclotomic.SeventhCyclotomic.Basic
public import TauCeti.NumberTheory.NumberField.Index.Discriminant
public import TauCeti.NumberTheory.NumberField.IntrinsicLabel
public import TauCeti.NumberTheory.NumberField.Monogenic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import TauCeti.NumberTheory.NumberField.ClassNumber.SmallDiscriminant

/-!
# The maximal real subfield of a seventh cyclotomic field

Let `L` be a seventh cyclotomic field over `ℚ` and `ζ` a primitive seventh root of unity in `L`.
The maximal real subfield `L⁺ = maximalRealSubfield L` has degree `φ(7) / 2 = 3` over `ℚ` and is
fixed by the cube of the cyclotomic Frobenius `frobeniusThreeSeven` at `3` (which acts as `-1` in
`(ℤ/7ℤ)ˣ`).

For any primitive seventh root of unity `ζ`, the real integer `θ = ζ + ζ⁻¹` generates `L⁺` over `ℚ`
and satisfies `θ³ + θ² - 2 θ - 1 = 0`, obtained by dividing `1 + ζ + ζ² + ζ³ + ζ⁴ + ζ⁵ + ζ⁶ = 0` by
`ζ³`. Since `[L⁺ : ℚ] = 3`, this monic cubic is `minpoly ℤ θ`, of discriminant `49 = 7²`. In the
index formula `49 = [𝓞 L⁺ : ℤ[θ]]² · discr L⁺`, index `7` would force `|discr L⁺| = 1`,
contradicting Minkowski's lower bound `|discr L⁺| > 2` in degree `3`; hence `[𝓞 L⁺ : ℤ[θ]] = 1`,
`𝓞 L⁺ = ℤ[ζ + ζ⁻¹]`, and `discr L⁺ = 49`.

As `L⁺` is totally real of degree `3` and discriminant `49`, its intrinsic label prefix is `3.3.49`,
and Minkowski's cubic bound (`49` threshold in
`TauCeti.NumberTheory.NumberField.ClassNumber.SmallDiscriminant`) makes `𝓞 L⁺` a principal ideal
domain of class number `1`.

## Main results

* `IsPrimitiveRoot.add_inv_pow_three_add_sq_sub_two_mul_sub_one`:
  `(ζ + ζ⁻¹)³ + (ζ + ζ⁻¹)² - 2 (ζ + ζ⁻¹) - 1 = 0`.
* `IsPrimitiveRoot.minpoly_addInvMaximalRealInteger_seven` and
  `IsPrimitiveRoot.discr_minpoly_addInvMaximalRealInteger_seven`:
  `minpoly ℤ (ζ + ζ⁻¹) = X³ + X² - 2 X - 1`, of discriminant `49`.
* `IsPrimitiveRoot.index_addInvMaximalRealInteger_seven` and
  `IsPrimitiveRoot.adjoin_addInvMaximalRealInteger_seven`: `[𝓞 L⁺ : ℤ[ζ + ζ⁻¹]] = 1` and
  `𝓞 L⁺ = ℤ[ζ + ζ⁻¹]`.
* `TauCeti.NumberField.frobeniusThreeSeven_pow_three` and
  `TauCeti.NumberField.toSubfield_fixedField_zpowers_frobeniusThreeSeven_pow_three`: the cube of
  `frobeniusThreeSeven` is complex conjugation, with fixed field `L⁺`.
* `TauCeti.NumberField.finrank_maximalRealSubfield_seven`,
  `TauCeti.NumberField.isMonogenic_maximalRealSubfield_seven`,
  `TauCeti.NumberField.discr_maximalRealSubfield_seven`,
  `TauCeti.NumberField.nrRealPlaces_maximalRealSubfield_seven`,
  `TauCeti.NumberField.hasLMFDBIntrinsicLabel_maximalRealSubfield_seven`: `[L⁺ : ℚ] = 3`, `L⁺` is
  monogenic, `discr L⁺ = 49`, `r₁ = 3`, and `HasLMFDBIntrinsicLabel L⁺ 3 3 49`.
* `TauCeti.NumberField.isPrincipalIdealRing_maximalRealSubfield_seven` and
  `TauCeti.NumberField.classNumber_maximalRealSubfield_seven`: `𝓞 L⁺` is a principal ideal domain
  and `classNumber L⁺ = 1`.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 2 (Proposition 2.16) and
  Chapter 11 §1.
-/

public section
noncomputable section

open NumberField NumberField.InfinitePlace Polynomial IntermediateField IsCyclotomicExtension
open scoped NumberField

/-- For a primitive seventh root of unity `ζ` in a field, `ζ + ζ⁻¹` satisfies
`(ζ + ζ⁻¹)³ + (ζ + ζ⁻¹)² - 2 (ζ + ζ⁻¹) - 1 = 0`. -/
theorem IsPrimitiveRoot.add_inv_pow_three_add_sq_sub_two_mul_sub_one {F : Type*} [Field F] {ζ : F}
    (hζ : IsPrimitiveRoot ζ 7) :
    (ζ + ζ⁻¹) ^ 3 + (ζ + ζ⁻¹) ^ 2 - 2 * (ζ + ζ⁻¹) - 1 = 0 := by
  have h0 : ζ ≠ 0 := hζ.ne_zero (by decide)
  have h1 : (ζ + ζ⁻¹) * ζ = ζ ^ 2 + 1 := by linear_combination inv_mul_cancel₀ h0
  have hsum : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 + ζ ^ 5 + ζ ^ 6 = 0 := by
    simpa [Finset.sum_range_succ] using hζ.geom_sum_eq_zero (by decide)
  apply mul_right_cancel₀ (pow_ne_zero 3 h0)
  calc ((ζ + ζ⁻¹) ^ 3 + (ζ + ζ⁻¹) ^ 2 - 2 * (ζ + ζ⁻¹) - 1) * ζ ^ 3
    _ = ((ζ + ζ⁻¹) * ζ) ^ 3 + ((ζ + ζ⁻¹) * ζ) ^ 2 * ζ - 2 * ((ζ + ζ⁻¹) * ζ) * ζ ^ 2 -
          ζ ^ 3 := by ring
    _ = 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 + ζ ^ 5 + ζ ^ 6 := by rw [h1]; ring
    _ = 0 * ζ ^ 3 := by rw [hsum, zero_mul]

namespace TauCeti.NumberField

section CyclotomicSeven

variable {L : Type*} [Field L] [NumberField L] [IsCyclotomicExtension {7} ℚ L]

private instance : IsGalois ℚ L := IsCyclotomicExtension.isGalois {7} ℚ L

/-- **The cube of the Frobenius at `3` in `ℚ(ζ₇)` is complex conjugation** (`-1 ∈ (ℤ/7ℤ)ˣ`). -/
theorem frobeniusThreeSeven_pow_three :
    frobeniusThreeSeven (L := L) ^ 3 = (Rat.galEquivZMod 7 L).symm (-1) := by
  apply (Rat.galEquivZMod 7 L).injective
  ext
  have hexp :
      ((zeta_spec 7 ℚ L).autToPow ℚ (frobeniusThreeSeven (L := L) ^ 3) : ZMod 7) = -1 := by
    rw [map_pow, Units.val_pow_eq_pow_val, autToPow_frobeniusThreeSeven]
    decide
  rw [(zeta_spec 7 ℚ L).autToPow_eq_unitsMap_galEquivZMod dvd_rfl, ZMod.unitsMap_self,
    MonoidHom.id_apply] at hexp
  simp only [MulEquiv.apply_symm_apply, Units.val_neg, Units.val_one]
  exact hexp

/-- **The fixed field of `frobeniusThreeSeven ^ 3` is the maximal real subfield of `ℚ(ζ₇)`.** -/
theorem toSubfield_fixedField_zpowers_frobeniusThreeSeven_pow_three :
    (fixedField (Subgroup.zpowers (frobeniusThreeSeven (L := L) ^ 3))).toSubfield =
      maximalRealSubfield L := by
  rw [frobeniusThreeSeven_pow_three,
    TauCeti.IsCyclotomicExtension.Rat.toSubfield_fixedField_zpowers_galEquivZMod_symm_neg_one 7 L]

end CyclotomicSeven

/-- **The maximal real subfield of `ℚ(ζ₇)` has degree `3` over `ℚ`.** -/
@[simp]
theorem finrank_maximalRealSubfield_seven {L : Type*} [Field L] [CharZero L]
    [IsCyclotomicExtension {7} ℚ L] :
    Module.finrank ℚ (maximalRealSubfield L) = 3 := by
  rw [TauCeti.IsCyclotomicExtension.Rat.finrank_rat_maximalRealSubfield_of_two_lt 7 L (by decide)]
  decide

end TauCeti.NumberField

namespace IsPrimitiveRoot

open TauCeti.NumberField

/-- **The minimal polynomial over `ℤ` of `ζ₇ + ζ₇⁻¹` in `𝓞 (ℚ(ζ₇)⁺)` is `X³ + X² - 2 X - 1`.** -/
theorem minpoly_addInvMaximalRealInteger_seven {L : Type*} [Field L] [CharZero L]
    [IsCyclotomicExtension {7} ℚ L] {ζ : L} (hζ : IsPrimitiveRoot ζ 7) :
    minpoly ℤ hζ.addInvMaximalRealInteger = X ^ 3 + X ^ 2 - 2 * X - 1 := by
  have : NumberField L := IsCyclotomicExtension.numberField {7} ℚ L
  let p : ℤ[X] := X ^ 3 + X ^ 2 - 2 * X - 1
  have hp_le : p.natDegree ≤ 3 := by dsimp [p]; compute_degree!
  have hp_coeff : p.coeff 3 = 1 := by simp [p, coeff_X, coeff_one]
  have hp_monicℤ : p.Monic := monic_of_natDegree_le_of_coeff_eq_one 3 hp_le hp_coeff
  have hp_degℤ : p.natDegree = 3 :=
    le_antisymm hp_le (Polynomial.le_natDegree_of_ne_zero (by rw [hp_coeff]; decide))
  have hp_monic : (p.map (algebraMap ℤ ℚ)).Monic := hp_monicℤ.map _
  have hp_deg : (p.map (algebraMap ℤ ℚ)).natDegree = 3 :=
    (hp_monicℤ.natDegree_map _).trans hp_degℤ
  have hp_aeval : aeval (hζ.addInvMaximalRealInteger : maximalRealSubfield L)
      (p.map (algebraMap ℤ ℚ)) = 0 := by
    apply (maximalRealSubfield L).subtype.injective
    rw [map_zero]
    simpa [p, aeval_map_algebraMap, map_sub, map_add, map_mul, map_pow, map_ofNat, map_one,
      coe_coe_addInvMaximalRealInteger] using hζ.add_inv_pow_three_add_sq_sub_two_mul_sub_one
  -- Over `ℚ`, `θ` generates the cubic field `L⁺`, so `minpoly ℚ θ` has degree `3` and equals `p`.
  have : Algebra.IsAlgebraic ℚ (maximalRealSubfield L) := NumberField.isAlgebraic _
  have htop :
      IntermediateField.adjoin ℚ {(hζ.addInvMaximalRealInteger : maximalRealSubfield L)} = ⊤ := by
    apply IntermediateField.toSubalgebra_injective
    rw [IntermediateField.top_toSubalgebra, IntermediateField.adjoin_toSubalgebra]
    exact hζ.adjoin_rat_addInvMaximalRealInteger_eq_top
  have hmin_deg :
      (minpoly ℚ (hζ.addInvMaximalRealInteger : maximalRealSubfield L)).natDegree = 3 := by
    rw [← IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral _), htop,
      IntermediateField.finrank_top', finrank_maximalRealSubfield_seven]
  have hminℚ : (minpoly ℤ hζ.addInvMaximalRealInteger).map (algebraMap ℤ ℚ) =
      p.map (algebraMap ℤ ℚ) := by
    rw [← RingOfIntegers.minpoly_coe hζ.addInvMaximalRealInteger,
      ← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hζ.addInvMaximalRealInteger.isIntegral_coe]
    exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic (Algebra.IsIntegral.isIntegral _)) hp_monic
      (minpoly.dvd ℚ _ hp_aeval) (hp_deg.trans_le hmin_deg.ge)).symm
  exact Polynomial.map_injective (algebraMap ℤ ℚ) (RingHom.injective_int (algebraMap ℤ ℚ)) hminℚ

/-- **The minimal polynomial over `ℤ` of `ζ₇ + ζ₇⁻¹` in `𝓞 (ℚ(ζ₇)⁺)` has discriminant `49`.** -/
@[simp]
theorem discr_minpoly_addInvMaximalRealInteger_seven {L : Type*} [Field L] [CharZero L]
    [IsCyclotomicExtension {7} ℚ L] {ζ : L} (hζ : IsPrimitiveRoot ζ 7) :
    (minpoly ℤ hζ.addInvMaximalRealInteger).discr = 49 := by
  rw [hζ.minpoly_addInvMaximalRealInteger_seven,
    Polynomial.discr_of_degree_eq_three (by compute_degree <;> norm_num)]
  norm_num [coeff_add, coeff_sub, coeff_X_pow, coeff_one, coeff_X, coeff_C_mul]

/-- **`ζ₇ + ζ₇⁻¹` has index `1` in `𝓞 (ℚ(ζ₇)⁺)`.** -/
@[simp]
theorem index_addInvMaximalRealInteger_seven {L : Type*} [Field L] [NumberField L]
    [IsCyclotomicExtension {7} ℚ L] {ζ : L} (hζ : IsPrimitiveRoot ζ 7) :
    IntegralPrimitiveElement.index
      (⟨hζ.addInvMaximalRealInteger, hζ.adjoin_rat_addInvMaximalRealInteger_eq_top⟩ :
        IntegralPrimitiveElement (maximalRealSubfield L)) = 1 := by
  let t : IntegralPrimitiveElement (maximalRealSubfield L) :=
    ⟨hζ.addInvMaximalRealInteger, hζ.adjoin_rat_addInvMaximalRealInteger_eq_top⟩
  have hd := t.discr_minpoly_eq_index_sq_mul_discr
  rw [hζ.discr_minpoly_addInvMaximalRealInteger_seven] at hd
  -- In `49 = t.index ^ 2 * |discr L⁺|`, `|discr L⁺| > 2` forces `t.index = 1`.
  have hgt : 2 < |NumberField.discr (maximalRealSubfield L)| :=
    NumberField.abs_discr_gt_two (by rw [finrank_maximalRealSubfield_seven]; decide)
  have : 2 < (NumberField.discr (maximalRealSubfield L)).natAbs := by
    rw [Int.abs_eq_natAbs] at hgt
    exact_mod_cast hgt
  have : 49 = t.index ^ 2 * (NumberField.discr (maximalRealSubfield L)).natAbs := by
    have := congrArg Int.natAbs hd
    simpa [Int.natAbs_mul, Int.natAbs_pow] using this
  have : t.index ^ 2 < 25 := by nlinarith
  have : 0 < t.index := t.index_pos
  have : t.index < 5 := by nlinarith
  interval_cases t.index <;> omega

/-- **The ring of integers of `ℚ(ζ₇)⁺` is `ℤ[ζ₇ + ζ₇⁻¹]`.** -/
@[simp]
theorem adjoin_addInvMaximalRealInteger_seven {L : Type*} [Field L] [CharZero L]
    [IsCyclotomicExtension {7} ℚ L] {ζ : L} (hζ : IsPrimitiveRoot ζ 7) :
    Algebra.adjoin ℤ {hζ.addInvMaximalRealInteger} = ⊤ := by
  have : NumberField L := IsCyclotomicExtension.numberField {7} ℚ L
  let t : IntegralPrimitiveElement (maximalRealSubfield L) :=
    ⟨hζ.addInvMaximalRealInteger, hζ.adjoin_rat_addInvMaximalRealInteger_eq_top⟩
  rw [← IntegralPrimitiveElement.adjoin_def t]
  exact (IntegralPrimitiveElement.index_eq_one_iff t).mp hζ.index_addInvMaximalRealInteger_seven

end IsPrimitiveRoot

namespace TauCeti.NumberField

/-- **`ℚ(ζ₇)⁺` is monogenic.** -/
theorem isMonogenic_maximalRealSubfield_seven (L : Type*) [Field L] [CharZero L]
    [IsCyclotomicExtension {7} ℚ L] :
    IsMonogenic (maximalRealSubfield L) :=
  let hζ := IsCyclotomicExtension.zeta_spec 7 ℚ L
  isMonogenic_def.mpr ⟨hζ.addInvMaximalRealInteger, hζ.adjoin_addInvMaximalRealInteger_seven⟩

section NumberField

variable (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {7} ℚ L]

/-- **The discriminant of `ℚ(ζ₇)⁺` is `49`.** -/
@[simp]
theorem discr_maximalRealSubfield_seven :
    NumberField.discr (maximalRealSubfield L) = 49 := by
  have hζ := IsCyclotomicExtension.zeta_spec 7 ℚ L
  let t : IntegralPrimitiveElement (maximalRealSubfield L) :=
    ⟨hζ.addInvMaximalRealInteger, hζ.adjoin_rat_addInvMaximalRealInteger_eq_top⟩
  have hd := t.discr_minpoly_eq_index_sq_mul_discr
  rw [hζ.discr_minpoly_addInvMaximalRealInteger_seven,
    hζ.index_addInvMaximalRealInteger_seven] at hd
  simpa using hd.symm

/-- **`ℚ(ζ₇)⁺` has three real places.** -/
@[simp]
theorem nrRealPlaces_maximalRealSubfield_seven :
    nrRealPlaces (maximalRealSubfield L) = 3 := by
  rw [← IsTotallyReal.finrank, finrank_maximalRealSubfield_seven]

/-- **The intrinsic label prefix of `ℚ(ζ₇)⁺` is `3.3.49`.** -/
theorem hasLMFDBIntrinsicLabel_maximalRealSubfield_seven :
    HasLMFDBIntrinsicLabel (maximalRealSubfield L) 3 3 49 := by
  rw [hasLMFDBIntrinsicLabel_iff]
  refine ⟨finrank_maximalRealSubfield_seven (L := L),
    nrRealPlaces_maximalRealSubfield_seven L, ?_⟩
  rw [discr_maximalRealSubfield_seven L]
  norm_num

end NumberField

/-- **The ring of integers of `ℚ(ζ₇)⁺` is a principal ideal domain.** -/
theorem isPrincipalIdealRing_maximalRealSubfield_seven (L : Type*) [Field L] [CharZero L]
    [IsCyclotomicExtension {7} ℚ L] :
    IsPrincipalIdealRing (𝓞 (maximalRealSubfield L)) := by
  have : NumberField L := IsCyclotomicExtension.numberField {7} ℚ L
  exact isPrincipalIdealRing_of_finrank_eq_three_of_natAbs_discr_le_forty_nine
    (finrank_maximalRealSubfield_seven (L := L))
    (by rw [discr_maximalRealSubfield_seven L]; norm_num)

/-- **The class number of `ℚ(ζ₇)⁺` is `1`.** -/
@[simp]
theorem classNumber_maximalRealSubfield_seven (L : Type*) [Field L] [NumberField L]
    [IsCyclotomicExtension {7} ℚ L] :
    NumberField.classNumber (maximalRealSubfield L) = 1 :=
  NumberField.classNumber_eq_one_iff.mpr (isPrincipalIdealRing_maximalRealSubfield_seven L)

end TauCeti.NumberField

end
