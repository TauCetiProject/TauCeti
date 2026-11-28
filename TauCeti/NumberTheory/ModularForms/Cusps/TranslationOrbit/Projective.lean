/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Cusps.Regularity
public import TauCeti.NumberTheory.ModularForms.Cusps.TranslationOrbit.Basic
import TauCeti.GroupTheory.GroupAction.ConjAct
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ModularGroup
import TauCeti.NumberTheory.Modular.ConjugateTranslation
import TauCeti.NumberTheory.ModularForms.ArithmeticSubgroups

/-!
# Projection from cusp translation orbits to projective cusp orbits

For finite-index `Γ ≤ SL(2, ℤ)`, this file defines `Γ.cuspOrbitOfTranslationOrbit` sending the
translation orbit of `γ` in `CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))` to
`Γ.cuspOrbitOfSL2Z γ⁻¹`, proves the bijection
`Γ.cuspTranslationOrbitAdjoinNegOneEquivCuspOrbit` between the geometric cusp translation orbits
`CuspTranslationOrbit (Γ.adjoinNegOne : Subgroup (GL (Fin 2) ℝ))` and
`(Γ.map sl2zToPSL2R).CuspOrbit`, and characterizes the fibre `{c₀, c₁}` of
`Γ.cuspOrbitOfTranslationOrbit` and its coincidence criterion
`c₀ = c₁ ↔ (-1 : SL(2, ℤ)) ∈ Γ ∨ ¬Γ.IsRegularCusp (Γ.cuspOrbitOfSL2Z γ)`.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005],
  §§2.4, 3.2, 3.6.
-/

public section

open Function Matrix Matrix.SpecialLinearGroup MulAction UpperHalfPlane
open scoped MatrixGroups ModularForm Pointwise

namespace TauCeti.ModularForm

/-- Integral matrices whose cosets lie in the same cusp translation orbit have inverses
representing the same cusp. -/
theorem cuspOrbitOfSL2Z_inv_eq_of_cuspTranslationOrbit_mk_eq {H : Subgroup SL(2, ℤ)}
    [H.FiniteIndex] {γ γ' : SL(2, ℤ)}
    (h : (⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ)⟧ : CuspTranslationOrbit (H.map (mapGL ℝ))) =
      ⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ')⟧) :
    H.cuspOrbitOfSL2Z γ⁻¹ = H.cuspOrbitOfSL2Z γ'⁻¹ := by
  obtain ⟨j, h₀, hh₀, hγ⟩ := cuspTranslationOrbit_mk_rangeRestrict_eq_iff.mp h
  refine (H.cuspOrbitOfSL2Z_eq_iff _ _).mpr ⟨h₀⁻¹, inv_mem hh₀, ?_⟩
  have hconj : γ⁻¹⁻¹ * h₀⁻¹ * γ'⁻¹ = ModularGroup.T ^ j := by rw [inv_inv, hγ]; group
  rw [hconj]; simp [ModularGroup.coe_T_zpow]

end TauCeti.ModularForm

namespace Subgroup

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

/-- **Projection from matrix cusp translation orbits to projective cusp orbits**, sending the
translation orbit of `γ ∈ SL(2, ℤ)` in `𝒮ℒ ⧸ Γ` to `Γ.cuspOrbitOfSL2Z γ⁻¹`. -/
noncomputable def cuspOrbitOfTranslationOrbit :
    TauCeti.ModularForm.CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ)) →
      (Γ.map sl2zToPSL2R).CuspOrbit :=
  let e := MonoidHom.ofInjective (mapGL_injective (S := ℝ))
  have hlift {x y : 𝒮ℒ}
      (h : (⟦QuotientGroup.mk x⟧ : TauCeti.ModularForm.CuspTranslationOrbit
        (Γ : Subgroup (GL (Fin 2) ℝ))) = ⟦QuotientGroup.mk y⟧) :
      Γ.cuspOrbitOfSL2Z (e.symm x)⁻¹ = Γ.cuspOrbitOfSL2Z (e.symm y)⁻¹ := by
    rw [← e.apply_symm_apply x, ← e.apply_symm_apply y] at h
    exact TauCeti.ModularForm.cuspOrbitOfSL2Z_inv_eq_of_cuspTranslationOrbit_mk_eq h
  Quotient.lift (Quotient.lift (fun x : 𝒮ℒ ↦ Γ.cuspOrbitOfSL2Z (e.symm x)⁻¹)
      fun _ _ h ↦ hlift (congrArg Quotient.mk'' (Quotient.sound h)))
    fun q₁ q₂ h ↦ Quotient.inductionOn₂ q₁ q₂ (fun _ _ h ↦ hlift (Quotient.sound h)) h

/-- `cuspOrbitOfTranslationOrbit` sends the translation orbit of `γ` to `Γ.cuspOrbitOfSL2Z γ⁻¹`. -/
@[simp] theorem cuspOrbitOfTranslationOrbit_mk (γ : SL(2, ℤ)) :
    Γ.cuspOrbitOfTranslationOrbit
        (⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ)⟧ :
          TauCeti.ModularForm.CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) =
      Γ.cuspOrbitOfSL2Z γ⁻¹ :=
  congrArg (Γ.cuspOrbitOfSL2Z ·⁻¹)
    ((MonoidHom.ofInjective (mapGL_injective (S := ℝ))).symm_apply_apply γ)

/-- Every projective cusp orbit is the image of a cusp translation orbit. -/
theorem cuspOrbitOfTranslationOrbit_surjective :
    Function.Surjective Γ.cuspOrbitOfTranslationOrbit := fun C ↦ by
  obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
  exact ⟨⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹)⟧, by
    rw [cuspOrbitOfTranslationOrbit_mk, inv_inv]⟩

private theorem cuspOrbitOfTranslationOrbit_adjoinNegOne_eq_iff (γ γ' : SL(2, ℤ)) :
    (⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ)⟧ :
        TauCeti.ModularForm.CuspTranslationOrbit (Γ.adjoinNegOne : Subgroup (GL (Fin 2) ℝ))) =
      ⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ')⟧ ↔
        Γ.cuspOrbitOfSL2Z γ⁻¹ = Γ.cuspOrbitOfSL2Z γ'⁻¹ := by
  rw [TauCeti.ModularForm.cuspTranslationOrbit_mk_rangeRestrict_eq_iff,
    Γ.cuspOrbitOfSL2Z_eq_iff, inv_inv]
  constructor
  · rintro ⟨j, h₀, hh₀, hγ⟩
    rcases Subgroup.mem_adjoinNegOne_iff.mp hh₀ with hh₀ | hh₀
    · refine ⟨h₀⁻¹, inv_mem hh₀, ?_⟩
      have hconj : γ * h₀⁻¹ * γ'⁻¹ = ModularGroup.T ^ j := by rw [hγ]; group
      rw [hconj]; simp [ModularGroup.coe_T_zpow]
    · refine ⟨-h₀⁻¹, by simpa using inv_mem hh₀, ?_⟩
      have hconj : γ * (-h₀⁻¹) * γ'⁻¹ = -(ModularGroup.T ^ j) := by
        rw [hγ]; simp only [mul_neg, neg_mul]; group
      rw [hconj]; simp [ModularGroup.coe_T_zpow]
  · rintro ⟨h₀, hh₀, hc⟩
    set m : SL(2, ℤ) := γ * h₀ * γ'⁻¹ with hm_def
    rcases TauCeti.ModularGroup.eq_T_zpow_or_eq_neg_T_zpow_of_c_eq_zero hc with hm | hm
    · exact ⟨m 0 1, h₀⁻¹, Subgroup.mem_adjoinNegOne_iff.mpr (.inl (inv_mem hh₀)),
        by rw [← hm, hm_def]; group⟩
    · refine ⟨-m 0 1, -h₀⁻¹,
        Subgroup.mem_adjoinNegOne_iff.mpr (.inr (by simpa using inv_mem hh₀)), ?_⟩
      have hm' : ModularGroup.T ^ (-m 0 1) = -m := by conv_rhs => rw [hm, neg_neg]
      rw [mul_neg, hm', hm_def]
      simp only [neg_mul, neg_neg]
      group

/-- **Equivalence between geometric cusp translation orbits (`CuspTranslationOrbit ±Γ`) and
projective cusp orbits (`(Γ.map sl2zToPSL2R).CuspOrbit`)**, sending `⟦mk γ⟧` to
`Γ.cuspOrbitOfSL2Z γ⁻¹`. -/
noncomputable def cuspTranslationOrbitAdjoinNegOneEquivCuspOrbit :
    TauCeti.ModularForm.CuspTranslationOrbit (Γ.adjoinNegOne : Subgroup (GL (Fin 2) ℝ)) ≃
      (Γ.map sl2zToPSL2R).CuspOrbit :=
  let e := MonoidHom.ofInjective (mapGL_injective (S := ℝ))
  let toFun : TauCeti.ModularForm.CuspTranslationOrbit
      (Γ.adjoinNegOne : Subgroup (GL (Fin 2) ℝ)) → (Γ.map sl2zToPSL2R).CuspOrbit :=
    have hlift {x y : 𝒮ℒ}
        (h : (⟦QuotientGroup.mk x⟧ : TauCeti.ModularForm.CuspTranslationOrbit
          (Γ.adjoinNegOne : Subgroup (GL (Fin 2) ℝ))) = ⟦QuotientGroup.mk y⟧) :
        Γ.cuspOrbitOfSL2Z (e.symm x)⁻¹ = Γ.cuspOrbitOfSL2Z (e.symm y)⁻¹ := by
      rw [← e.apply_symm_apply x, ← e.apply_symm_apply y] at h
      exact (Γ.cuspOrbitOfTranslationOrbit_adjoinNegOne_eq_iff (e.symm x) (e.symm y)).mp h
    Quotient.lift (Quotient.lift (fun x : 𝒮ℒ ↦ Γ.cuspOrbitOfSL2Z (e.symm x)⁻¹)
        fun _ _ h ↦ hlift (congrArg Quotient.mk'' (Quotient.sound h)))
      fun q₁ q₂ h ↦ Quotient.inductionOn₂ q₁ q₂ (fun _ _ h ↦ hlift (Quotient.sound h)) h
  have he (γ : SL(2, ℤ)) : e.symm ((mapGL ℝ).rangeRestrict γ) = γ := e.symm_apply_apply γ
  Equiv.ofBijective toFun
    ⟨fun c₁ c₂ hc ↦ by
      induction c₁ using TauCeti.ModularForm.CuspTranslationOrbit.induction_on with | h γ₁ =>
      induction c₂ using TauCeti.ModularForm.CuspTranslationOrbit.induction_on with | h γ₂ =>
      have h' : Γ.cuspOrbitOfSL2Z γ₁⁻¹ = Γ.cuspOrbitOfSL2Z γ₂⁻¹ := by
        simpa only [toFun, Quotient.lift_mk, he] using hc
      exact (Γ.cuspOrbitOfTranslationOrbit_adjoinNegOne_eq_iff γ₁ γ₂).mpr h',
    fun C ↦ by
      obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
      refine ⟨⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹)⟧, ?_⟩
      change Γ.cuspOrbitOfSL2Z (e.symm ((mapGL ℝ).rangeRestrict γ⁻¹))⁻¹ = Γ.cuspOrbitOfSL2Z γ
      rw [he, inv_inv]⟩

/-- `cuspTranslationOrbitAdjoinNegOneEquivCuspOrbit` sends `⟦mk γ⟧` to `Γ.cuspOrbitOfSL2Z γ⁻¹`. -/
@[simp] theorem cuspTranslationOrbitAdjoinNegOneEquivCuspOrbit_mk (γ : SL(2, ℤ)) :
    Γ.cuspTranslationOrbitAdjoinNegOneEquivCuspOrbit
        (⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ)⟧ :
          TauCeti.ModularForm.CuspTranslationOrbit (Γ.adjoinNegOne : Subgroup (GL (Fin 2) ℝ))) =
      Γ.cuspOrbitOfSL2Z γ⁻¹ :=
  congrArg (Γ.cuspOrbitOfSL2Z ·⁻¹)
    ((MonoidHom.ofInjective (mapGL_injective (S := ℝ))).symm_apply_apply γ)

/-- The inverse of `cuspTranslationOrbitAdjoinNegOneEquivCuspOrbit` sends `Γ.cuspOrbitOfSL2Z γ`
to `⟦mk γ⁻¹⟧`. -/
@[simp] theorem cuspTranslationOrbitAdjoinNegOneEquivCuspOrbit_symm_cuspOrbitOfSL2Z (γ : SL(2, ℤ)) :
    Γ.cuspTranslationOrbitAdjoinNegOneEquivCuspOrbit.symm (Γ.cuspOrbitOfSL2Z γ) =
      ⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹)⟧ :=
  Γ.cuspTranslationOrbitAdjoinNegOneEquivCuspOrbit.symm_apply_eq.mpr
    (by rw [cuspTranslationOrbitAdjoinNegOneEquivCuspOrbit_mk, inv_inv])

end Subgroup

namespace TauCeti.ModularForm

variable {Γ : Subgroup SL(2, ℤ)}

/-- **Fibre of `Subgroup.cuspOrbitOfTranslationOrbit` over `Γ.cuspOrbitOfSL2Z γ`**: every
translation orbit mapping to `Γ.cuspOrbitOfSL2Z γ` is the orbit of `γ⁻¹` or `-γ⁻¹`. -/
theorem cuspOrbitOfTranslationOrbit_eq_cuspOrbitOfSL2Z_iff [Γ.FiniteIndex] (γ : SL(2, ℤ))
    (c : CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) :
    Γ.cuspOrbitOfTranslationOrbit c = Γ.cuspOrbitOfSL2Z γ ↔
      c = ⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹)⟧ ∨
        c = ⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict (-γ⁻¹))⟧ := by
  refine ⟨fun hc ↦ ?_, ?_⟩
  · induction c using CuspTranslationOrbit.induction_on with | h δ => ?_
    rw [Subgroup.cuspOrbitOfTranslationOrbit_mk] at hc
    obtain ⟨h₀, hh₀, hm_10⟩ := (Γ.cuspOrbitOfSL2Z_eq_iff δ⁻¹ γ).mp hc
    rw [inv_inv] at hm_10
    set m : SL(2, ℤ) := δ * h₀ * γ with hm_def
    rcases TauCeti.ModularGroup.eq_T_zpow_or_eq_neg_T_zpow_of_c_eq_zero hm_10 with hm | hm
    · exact Or.inl <| cuspTranslationOrbit_mk_rangeRestrict_eq_iff.mpr
        ⟨m 0 1, h₀⁻¹, inv_mem hh₀, by rw [← hm, hm_def]; group⟩
    · refine Or.inr <| cuspTranslationOrbit_mk_rangeRestrict_eq_iff.mpr
        ⟨-m 0 1, h₀⁻¹, inv_mem hh₀, ?_⟩
      rw [mul_neg, ← neg_mul, ← hm, hm_def]; group
  · rintro (rfl | rfl)
    · rw [Subgroup.cuspOrbitOfTranslationOrbit_mk, inv_inv]
    · rw [Subgroup.cuspOrbitOfTranslationOrbit_mk, inv_neg, inv_inv, Γ.cuspOrbitOfSL2Z_neg]

/-- **Coincidence criterion for the fibre `{c₀, c₁}` over `Γ.cuspOrbitOfSL2Z γ`**: the translation
orbits of `γ⁻¹` and `-γ⁻¹` coincide iff `-I ∈ Γ` or the cusp is irregular. -/
theorem cuspTranslationOrbit_mk_inv_eq_mk_neg_inv_iff [Γ.FiniteIndex] (γ : SL(2, ℤ)) :
    (⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹)⟧ :
        CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) =
      ⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict (-γ⁻¹))⟧ ↔
        (-1 : SL(2, ℤ)) ∈ Γ ∨ ¬Γ.IsRegularCusp (Γ.cuspOrbitOfSL2Z γ) := by
  set Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))
  have hex : (⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹)⟧ :
        CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) =
      ⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict (-γ⁻¹))⟧ ↔
        ∃ j : ℤ, -Matrix.GeneralLinearGroup.upperRightHom (j : ℝ) ∈ Γγ := by
    simp_rw [Γγ, ← neg_conj_T_zpow_mem_iff_neg_upperRightHom_mem_conj]
    rw [eq_comm, cuspTranslationOrbit_mk_rangeRestrict_eq_iff]
    refine ⟨fun ⟨j, h₀, hh₀, hneg⟩ ↦ ⟨-j, ?_⟩,
      fun ⟨j, hj⟩ ↦ ⟨-j, -(γ * ModularGroup.T ^ j * γ⁻¹), hj, ?_⟩⟩
    · have hh₀_eq : -(γ * ModularGroup.T ^ (-j) * γ⁻¹) = h₀ := by
        rw [_root_.zpow_neg]
        have hneg' : h₀ = (ModularGroup.T ^ j * γ⁻¹)⁻¹ * (-γ⁻¹) :=
          eq_inv_mul_of_mul_eq (by simpa [mul_assoc] using hneg.symm)
        rw [hneg']
        simp only [mul_neg]
        group
      exact hh₀_eq ▸ hh₀
    · rw [_root_.zpow_neg]
      simp only [mul_neg]
      group
  rw [hex, Subgroup.isRegularCusp_cuspOrbitOfSL2Z]
  refine ⟨fun ⟨j, hj⟩ ↦ or_iff_not_imp_right.mpr fun hreg ↦ ?_, ?_⟩
  · have hsp : Matrix.GeneralLinearGroup.upperRightHom (j : ℝ) ∈ Γγ := by
      rw [← Subgroup.mem_strictPeriods_iff, not_not.mp hreg, Subgroup.periods,
        Subgroup.mem_strictPeriods_iff, Subgroup.mem_adjoinNegOne_iff]; exact Or.inr hj
    have hneg' := Subgroup.mem_conjAct_smul_of_mem_center
      (Subgroup.mem_center_iff.mpr fun _ ↦ by simp) (mapGL ℝ γ)
      (by simpa only [neg_mul, mul_inv_cancel] using mul_mem hj (inv_mem hsp) :
        (-1 : GL (Fin 2) ℝ) ∈ Γγ)
    rwa [smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul,
      ← Matrix.SpecialLinearGroup.mapGL_neg_one (R := ℤ),
      Subgroup.mem_map_iff_mem (mapGL_injective (S := ℝ))] at hneg'
  · rintro (hneg | hirr)
    · exact ⟨0, (neg_conj_T_zpow_mem_iff_neg_upperRightHom_mem_conj γ 0).mp (by simpa using hneg)⟩
    · obtain ⟨j, hj, -⟩ := exists_int_eq_and_neg_conj_T_zpow_mem_of_neg_upperRightHom_mem_conj γ
        (Subgroup.neg_upperRightHom_widthInfty_mem_of_not_isRegularAtInfty Γγ hirr)
      exact ⟨j, hj ▸ Subgroup.neg_upperRightHom_widthInfty_mem_of_not_isRegularAtInfty Γγ hirr⟩

end TauCeti.ModularForm

end
