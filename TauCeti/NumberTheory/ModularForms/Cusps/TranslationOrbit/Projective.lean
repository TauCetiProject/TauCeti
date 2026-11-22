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

/-!
# Projection from cusp translation orbits to projective cusp orbits

For finite-index `Γ ≤ SL(2, ℤ)`, this file defines `Γ.cuspOrbitOfTranslationOrbit` sending the
translation orbit of `γ` in `CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))` to
`Γ.cuspOrbitOfSL2Z γ⁻¹`, characterizes its fibre `{c₀, c₁}` and coincidence criterion
`c₀ = c₁ ↔ (-1 : SL(2, ℤ)) ∈ Γ ∨ ¬Γ.IsRegularCusp (Γ.cuspOrbitOfSL2Z γ)`, and identifies
`cuspTranslationOrbitWidth` at `γ⁻¹` with `strictWidthInfty` of `γ⁻¹ Γ γ`.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005],
  §§2.4, 3.2, 3.6.
-/

public section

open Function Matrix Matrix.SpecialLinearGroup MulAction UpperHalfPlane
open scoped MatrixGroups ModularForm Pointwise

namespace TauCeti.ModularForm

private lemma coe_inv_TSL_zpow_mul (j : ℤ) (α δ : SL(2, ℤ)) :
    (((TSL ^ j * (mapGL ℝ).rangeRestrict α)⁻¹ * (mapGL ℝ).rangeRestrict δ : 𝒮ℒ) : GL (Fin 2) ℝ) =
      mapGL ℝ ((ModularGroup.T ^ j * α)⁻¹ * δ) := by
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv, coe_TSL_zpow,
    Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, MonoidHom.coe_rangeRestrict, map_mul, map_inv]

/-- Integral matrices whose cosets lie in the same cusp translation orbit have inverses
representing the same cusp. -/
theorem cuspOrbitOfSL2Z_inv_eq_of_cuspTranslationOrbit_mk_eq {H : Subgroup SL(2, ℤ)}
    [H.FiniteIndex] {γ γ' : SL(2, ℤ)}
    (h : (⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ)⟧ : CuspTranslationOrbit (H.map (mapGL ℝ))) =
      ⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ')⟧) :
    H.cuspOrbitOfSL2Z γ⁻¹ = H.cuspOrbitOfSL2Z γ'⁻¹ := by
  obtain ⟨⟨_, hg⟩, hgq⟩ := MulAction.orbitRel_apply.mp (Quotient.exact h)
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  simp only [Subgroup.mk_smul, MulAction.Quotient.smul_mk, smul_eq_mul] at hgq
  obtain ⟨h₀, hh₀, he⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hgq))
  have hγ : γ = ModularGroup.T ^ j * γ' * h₀ := by
    rw [mapGL_injective (he.trans (coe_inv_TSL_zpow_mul j γ' γ))]; group
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

end Subgroup

namespace TauCeti.ModularForm

variable {Γ : Subgroup SL(2, ℤ)}

private lemma mk_rangeRestrict_eq_of_mul_T_zpow {δ α h₀ : SL(2, ℤ)} (hh₀ : h₀ ∈ Γ) (j : ℤ)
    (hδ : δ = ModularGroup.T ^ j * α * h₀) :
    (⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict δ)⟧ :
        CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) =
      ⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict α)⟧ := by
  refine Quotient.sound ⟨⟨TSL ^ j, Subgroup.mem_zpowers_iff.mpr ⟨j, rfl⟩⟩, ?_⟩
  dsimp only; rw [Subgroup.mk_smul, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq,
    Subgroup.mem_subgroupOf, coe_inv_TSL_zpow_mul, hδ, inv_mul_cancel_left]
  exact Subgroup.mem_map_of_mem _ hh₀

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
    · exact Or.inl <| mk_rangeRestrict_eq_of_mul_T_zpow (inv_mem hh₀) (m 0 1)
        (by rw [← hm, hm_def]; group)
    · refine Or.inr <| mk_rangeRestrict_eq_of_mul_T_zpow (inv_mem hh₀) (-m 0 1) ?_
      rw [mul_neg, ← neg_mul, ← hm, hm_def]; group
  · rintro (rfl | rfl)
    · rw [Subgroup.cuspOrbitOfTranslationOrbit_mk, inv_inv]
    · rw [Subgroup.cuspOrbitOfTranslationOrbit_mk, inv_neg, inv_inv, Γ.cuspOrbitOfSL2Z_neg]

private lemma neg_conj_T_zpow_mem_iff_neg_upperRightHom_mem (γ : SL(2, ℤ)) (j : ℤ) :
    -(γ * ModularGroup.T ^ j * γ⁻¹) ∈ Γ ↔
      -Matrix.GeneralLinearGroup.upperRightHom (j : ℝ) ∈
        ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ)) := by
  rw [Subgroup.mem_conjAct_inv_smul_iff, ← ModularGroup.mapGL_T_zpow_eq_upperRightHom, mul_neg,
    neg_mul, ← map_inv, ← map_mul, ← map_mul, ← mapGL_neg,
    Subgroup.mem_map_iff_mem (mapGL_injective (S := ℝ))]

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
    simp_rw [Γγ, ← neg_conj_T_zpow_mem_iff_neg_upperRightHom_mem]
    refine ⟨fun h ↦ ?_, fun ⟨j, hj⟩ ↦ mk_rangeRestrict_eq_of_mul_T_zpow hj (-j) <| by
      symm; simp only [mul_neg, neg_mul, neg_neg]; group⟩
    obtain ⟨⟨_, hg⟩, hgq⟩ := MulAction.orbitRel_apply.mp (Quotient.exact h.symm)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    dsimp only at hgq; rw [Subgroup.mk_smul, MulAction.Quotient.smul_mk, smul_eq_mul,
      QuotientGroup.eq, Subgroup.mem_subgroupOf, coe_inv_TSL_zpow_mul, _root_.mul_inv_rev, inv_inv,
      mul_neg, ← _root_.zpow_neg, Subgroup.mem_map_iff_mem (mapGL_injective (S := ℝ))] at hgq
    exact ⟨-j, hgq⟩
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
    · exact ⟨0, (neg_conj_T_zpow_mem_iff_neg_upperRightHom_mem γ 0).mp (by simpa using hneg)⟩
    · obtain ⟨j, hj, -⟩ := exists_int_eq_and_neg_conj_T_zpow_mem_of_neg_upperRightHom_mem_conj γ
        (Subgroup.neg_upperRightHom_widthInfty_mem_of_not_isRegularAtInfty Γγ hirr)
      exact ⟨j, hj ▸ Subgroup.neg_upperRightHom_widthInfty_mem_of_not_isRegularAtInfty Γγ hirr⟩

/-- **Strict cusp width equals integer cusp-translation-orbit width**: `strictWidthInfty` of
`γ⁻¹ Γ γ` equals the width of the cusp translation orbit of `γ⁻¹`. -/
theorem natCast_cuspTranslationOrbitWidth_mk_inv_eq_strictWidthInfty (γ : SL(2, ℤ)) :
    (cuspTranslationOrbitWidth
      (⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹)⟧ :
        CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) : ℝ) =
      (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).strictWidthInfty := by
  set w₀ := cuspTranslationOrbitWidth (⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹)⟧ :
    CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ)))
  refine (Subgroup.strictWidthInfty_eq_of_strictPeriods_eq_zmultiples ?_ (Nat.cast_nonneg _)).symm
  ext x
  rw [Subgroup.mem_strictPeriods_iff, AddSubgroup.mem_zmultiples_iff]
  refine ⟨fun hx ↦ ?_, fun ⟨m, hm⟩ ↦ ?_⟩
  · obtain ⟨j, rfl, hj_mem⟩ := exists_int_eq_and_conj_T_zpow_mem_of_upperRightHom_mem_conj γ hx
    obtain ⟨m, hm⟩ := Int.natCast_dvd.mpr <|
      (cuspTranslationOrbitWidth_mk_dvd_iff γ⁻¹ j.natAbs).mpr <| by
        rw [inv_inv]
        rcases Int.natAbs_eq j with h | h
        · rwa [← zpow_natCast, ← h]
        · have hinv : (γ * ModularGroup.T ^ j * γ⁻¹)⁻¹ = γ * ModularGroup.T ^ (-j) * γ⁻¹ := by
            group
          rw [← zpow_natCast, ← neg_eq_iff_eq_neg.mpr h, ← hinv]; exact inv_mem hj_mem
    exact ⟨m, by rw [zsmul_eq_mul, mul_comm, ← Int.cast_natCast, ← Int.cast_mul, ← hm]⟩
  · have hm_mem : γ * ModularGroup.T ^ ((w₀ : ℤ) * m) * γ⁻¹ ∈ Γ := by
      rw [_root_.zpow_mul, zpow_natCast, ← conj_zpow]
      exact zpow_mem
        (by simpa only [inv_inv] using (cuspTranslationOrbitWidth_mk_dvd_iff γ⁻¹ w₀).mp dvd_rfl) m
    rw [← hm, zsmul_eq_mul, mul_comm, ← Int.cast_natCast, ← Int.cast_mul,
      ← ModularGroup.mapGL_T_zpow_eq_upperRightHom, Subgroup.mem_conjAct_inv_smul_iff]
    simpa [map_mul, map_inv, mul_assoc] using Subgroup.mem_map_of_mem (mapGL ℝ) hm_mem

end TauCeti.ModularForm

end
