/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Cusps.Regularity
public import TauCeti.NumberTheory.ModularForms.Norm.Cusps
import TauCeti.NumberTheory.Modular.ConjugateTranslation

/-!
# Projection from cusp translation orbits to projective cusp orbits

For a finite-index subgroup `Γ ≤ SL(2, ℤ)`, the matrix valence formula indexes cusp terms by the
translation orbits `CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))` of `⟨T⟩` on `𝒮ℒ ⧸ Γ`,
whereas the compactified modular curve `(Γ.map sl2zToPSL2R).CompactifiedQuotient` indexes cusps by
projective cusp orbits `(Γ.map sl2zToPSL2R).CuspOrbit`.

This file constructs the canonical surjection `Γ.cuspOrbitOfTranslationOrbit` sending the
translation orbit of `γ ∈ SL(2, ℤ)` to `Γ.cuspOrbitOfSL2Z γ⁻¹`, proves that its fibre over
`Γ.cuspOrbitOfSL2Z γ` consists of the orbits `c₀` and `c₁` of `γ⁻¹` and `-γ⁻¹` with
`c₀ = c₁ ↔ (-1 : SL(2, ℤ)) ∈ Γ ∨ ¬Γ.IsRegularCusp (Γ.cuspOrbitOfSL2Z γ)`, and identifies the
translation-orbit width `cuspTranslationOrbitWidth` at `γ⁻¹` with the strict cusp width
`strictWidthInfty` of `γ⁻¹ Γ γ`.

## Main definitions

* `Subgroup.cuspOrbitOfTranslationOrbit`: canonical projection from
  `CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))` to `(Γ.map sl2zToPSL2R).CuspOrbit`.

## Main results

* `TauCeti.ModularForm.cuspOrbitOfSL2Z_inv_eq_of_cuspTranslationOrbit_mk_eq`: integral matrices in
  the same cusp translation orbit have inverses representing the same cusp orbit.
* `Subgroup.cuspOrbitOfTranslationOrbit_surjective`: surjectivity of the projection.
* `TauCeti.ModularForm.cuspOrbitOfTranslationOrbit_eq_cuspOrbitOfSL2Z_iff` and
  `TauCeti.ModularForm.cuspTranslationOrbit_mk_inv_eq_mk_neg_inv_iff`: description of the fibre
  `{c₀, c₁}` over `Γ.cuspOrbitOfSL2Z γ` and the coincidence criterion
  `c₀ = c₁ ↔ -1 ∈ Γ ∨ ¬Γ.IsRegularCusp (Γ.cuspOrbitOfSL2Z γ)`.
* `TauCeti.ModularForm.natCast_cuspTranslationOrbitWidth_mk_inv_eq_strictWidthInfty`: the integer
  width of the translation orbit of `γ⁻¹` equals `strictWidthInfty` of `γ⁻¹ Γ γ`.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], §§2.4, 3.2,
  3.6.
-/

public section

open Function Matrix Matrix.SpecialLinearGroup MulAction UpperHalfPlane
open scoped MatrixGroups ModularForm Pointwise

namespace TauCeti.ModularForm

/-- Integral matrices whose cosets lie in the same cusp translation orbit have inverses
representing the same cusp. -/
theorem cuspOrbitOfSL2Z_inv_eq_of_cuspTranslationOrbit_mk_eq {H : Subgroup SL(2, ℤ)}
    [H.FiniteIndex] {γ γ' : SL(2, ℤ)}
    (h : (⟦(QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ) :
        𝒮ℒ ⧸ (H.map (mapGL ℝ)).subgroupOf 𝒮ℒ)⟧ : CuspTranslationOrbit (H.map (mapGL ℝ))) =
      ⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ')⟧) :
    H.cuspOrbitOfSL2Z γ⁻¹ = H.cuspOrbitOfSL2Z γ'⁻¹ := by
  obtain ⟨⟨_, hg⟩, hgq⟩ := MulAction.orbitRel_apply.mp (Quotient.exact h)
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  -- The orbit relation says `γ = Tʲ γ' h₀` for some `h₀ ∈ H`.
  have hmk : (QuotientGroup.mk (TSL ^ j * (mapGL ℝ).rangeRestrict γ') :
      𝒮ℒ ⧸ (H.map (mapGL ℝ)).subgroupOf 𝒮ℒ) = QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ) := by
    simpa only [Subgroup.mk_smul, MulAction.Quotient.smul_mk, smul_eq_mul] using hgq
  obtain ⟨h₀, hh₀, he⟩ :=
    Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hmk))
  have hcoe : (((TSL ^ j * (mapGL ℝ).rangeRestrict γ')⁻¹ * (mapGL ℝ).rangeRestrict γ : 𝒮ℒ) :
      GL (Fin 2) ℝ) = mapGL ℝ ((ModularGroup.T ^ j * γ')⁻¹ * γ) := by
    simp only [coe_TSL_zpow, TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, map_mul, map_inv,
      Subgroup.coe_mul, InvMemClass.coe_inv, MonoidHom.coe_rangeRestrict]
  have hγ : γ = ModularGroup.T ^ j * γ' * h₀ := by
    rw [mapGL_injective (he.trans hcoe)]
    group
  refine (H.cuspOrbitOfSL2Z_eq_iff _ _).mpr ⟨h₀⁻¹, inv_mem hh₀, ?_⟩
  have hT : γ⁻¹⁻¹ * h₀⁻¹ * γ'⁻¹ = ModularGroup.T ^ j := by
    rw [inv_inv, hγ]
    group
  rw [hT]
  simp [ModularGroup.coe_T_zpow]

end TauCeti.ModularForm

namespace Subgroup

private noncomputable def sl2zOfSL (x : 𝒮ℒ) : SL(2, ℤ) :=
  Function.surjInv (mapGL ℝ).rangeRestrict_surjective x

private lemma rangeRestrict_sl2zOfSL (x : 𝒮ℒ) : (mapGL ℝ).rangeRestrict (sl2zOfSL x) = x :=
  Function.surjInv_eq (mapGL ℝ).rangeRestrict_surjective x

private lemma sl2zOfSL_rangeRestrict (γ : SL(2, ℤ)) :
    sl2zOfSL ((mapGL ℝ).rangeRestrict γ) = γ :=
  mapGL_injective (S := ℝ) (congrArg Subtype.val (rangeRestrict_sl2zOfSL _))

/-- **Projection from matrix cusp translation orbits to projective cusp orbits.**
The translation orbit of the coset of `γ ∈ SL(2, ℤ)` in `𝒮ℒ ⧸ Γ`, whose coset factor in the norm is
`f ∣[k] γ⁻¹`, maps to `Γ.cuspOrbitOfSL2Z γ⁻¹` (the `Γ`-orbit of `γ⁻¹ • ∞`). -/
noncomputable def cuspOrbitOfTranslationOrbit (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    TauCeti.ModularForm.CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ)) →
      (Γ.map sl2zToPSL2R).CuspOrbit :=
  Quotient.lift
    (Quotient.lift (fun x : 𝒮ℒ ↦ Γ.cuspOrbitOfSL2Z (sl2zOfSL x)⁻¹) fun x y hxy ↦ by
      apply TauCeti.ModularForm.cuspOrbitOfSL2Z_inv_eq_of_cuspTranslationOrbit_mk_eq
      rw [rangeRestrict_sl2zOfSL, rangeRestrict_sl2zOfSL]
      exact congrArg Quotient.mk'' (Quotient.sound hxy))
    fun q₁ q₂ hq ↦ by
      induction q₁ using Quotient.inductionOn with | h x => ?_
      induction q₂ using Quotient.inductionOn with | h y => ?_
      apply TauCeti.ModularForm.cuspOrbitOfSL2Z_inv_eq_of_cuspTranslationOrbit_mk_eq
      rw [rangeRestrict_sl2zOfSL, rangeRestrict_sl2zOfSL]
      exact Quotient.sound hq

/-- `cuspOrbitOfTranslationOrbit` sends the translation orbit of `γ` to `Γ.cuspOrbitOfSL2Z γ⁻¹`. -/
@[simp]
theorem cuspOrbitOfTranslationOrbit_mk (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (γ : SL(2, ℤ)) :
    Γ.cuspOrbitOfTranslationOrbit
        (⟦(QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ) :
          𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)⟧ :
            TauCeti.ModularForm.CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) =
      Γ.cuspOrbitOfSL2Z γ⁻¹ :=
  congrArg (fun g ↦ Γ.cuspOrbitOfSL2Z g⁻¹) (sl2zOfSL_rangeRestrict γ)

/-- Every projective cusp orbit is the image of a cusp translation orbit. -/
theorem cuspOrbitOfTranslationOrbit_surjective (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    Function.Surjective Γ.cuspOrbitOfTranslationOrbit := fun C ↦ by
  obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
  exact ⟨⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹)⟧,
    by rw [cuspOrbitOfTranslationOrbit_mk, inv_inv]⟩

end Subgroup

namespace TauCeti.ModularForm

variable {Γ : Subgroup SL(2, ℤ)}

private lemma mk_rangeRestrict_eq_of_mul_T_zpow {δ α h₀ : SL(2, ℤ)} (hh₀ : h₀ ∈ Γ) (j : ℤ)
    (hδ : δ = ModularGroup.T ^ j * α * h₀) :
    (⟦(QuotientGroup.mk ((mapGL ℝ).rangeRestrict δ) :
      𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)⟧ :
        CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) =
      ⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict α)⟧ := by
  refine Quotient.sound ⟨⟨TSL ^ j, Subgroup.mem_zpowers_iff.mpr ⟨j, rfl⟩⟩, ?_⟩
  dsimp only
  rw [Subgroup.mk_smul, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  have hcoe : (((TSL ^ j * (mapGL ℝ).rangeRestrict α)⁻¹ * (mapGL ℝ).rangeRestrict δ : 𝒮ℒ) :
      GL (Fin 2) ℝ) = mapGL ℝ h₀ := by
    rw [hδ]
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, coe_TSL_zpow,
      TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, MonoidHom.coe_rangeRestrict, map_mul,
      _root_.mul_inv_rev]
    group
  rw [hcoe]
  exact Subgroup.mem_map_of_mem _ hh₀

/-- **Fibre of `Subgroup.cuspOrbitOfTranslationOrbit` over `Γ.cuspOrbitOfSL2Z γ`.** Every
translation orbit mapping to `Γ.cuspOrbitOfSL2Z γ` is either the orbit of `γ⁻¹` or that of
`-γ⁻¹`. -/
theorem cuspOrbitOfTranslationOrbit_eq_cuspOrbitOfSL2Z_iff [Γ.FiniteIndex] (γ : SL(2, ℤ))
    (c : CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) :
    Γ.cuspOrbitOfTranslationOrbit c = Γ.cuspOrbitOfSL2Z γ ↔
      c = ⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹)⟧ ∨
        c = ⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict (-γ⁻¹))⟧ := by
  refine ⟨fun hc ↦ ?_, fun hc ↦ ?_⟩
  · induction c using CuspTranslationOrbit.induction_on with | h δ => ?_
    rw [Subgroup.cuspOrbitOfTranslationOrbit_mk] at hc
    obtain ⟨h₀, hh₀, hm_10⟩ := (Γ.cuspOrbitOfSL2Z_eq_iff δ⁻¹ γ).mp hc
    rw [inv_inv] at hm_10
    set m : SL(2, ℤ) := δ * h₀ * γ
    rcases TauCeti.ModularGroup.eq_T_zpow_or_eq_neg_T_zpow_of_c_eq_zero hm_10 with hm | hm
    · left
      refine mk_rangeRestrict_eq_of_mul_T_zpow (inv_mem hh₀) (m 0 1) ?_
      have h1 : δ * h₀ * γ = ModularGroup.T ^ (m 0 1) := hm
      rw [← h1]
      group
    · right
      refine mk_rangeRestrict_eq_of_mul_T_zpow (inv_mem hh₀) (-m 0 1) ?_
      have h1 : δ * h₀ * γ = ModularGroup.T ^ (-m 0 1) * (-1) := by
        simpa [mul_neg, mul_one] using hm
      have h2 : (-γ⁻¹ : SL(2, ℤ)) = (-1) * γ⁻¹ := by simp
      rw [h2, ← mul_assoc, ← h1]
      group
  · rcases hc with rfl | rfl
    · rw [Subgroup.cuspOrbitOfTranslationOrbit_mk, inv_inv]
    · have hinv : (-γ⁻¹ : SL(2, ℤ))⁻¹ = -γ := by simp
      rw [Subgroup.cuspOrbitOfTranslationOrbit_mk, hinv, Γ.cuspOrbitOfSL2Z_neg]

private lemma cuspTranslationOrbit_mk_inv_eq_mk_neg_inv_iff_exists (γ : SL(2, ℤ)) :
    (⟦(QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹) :
      𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)⟧ :
        CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) =
      ⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict (-γ⁻¹))⟧ ↔
        ∃ j : ℤ, -(γ * ModularGroup.T ^ j * γ⁻¹) ∈ Γ := by
  refine ⟨fun h ↦ ?_, fun ⟨j, hj⟩ ↦ ?_⟩
  · obtain ⟨⟨_, hg⟩, hgq⟩ := MulAction.orbitRel_apply.mp (Quotient.exact h.symm)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    dsimp only at hgq
    rw [Subgroup.mk_smul, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at hgq
    have hcoe : (((TSL ^ j * (mapGL ℝ).rangeRestrict γ⁻¹)⁻¹ *
        (mapGL ℝ).rangeRestrict (-γ⁻¹) : 𝒮ℒ) : GL (Fin 2) ℝ) =
          mapGL ℝ (-(γ * ModularGroup.T ^ (-j) * γ⁻¹)) := by
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv, coe_TSL_zpow,
        TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, MonoidHom.coe_rangeRestrict, mapGL_neg,
        map_mul, map_inv, map_zpow, _root_.zpow_neg, _root_.mul_inv_rev, inv_inv, mul_neg]
    rw [hcoe, Subgroup.mem_map_iff_mem (mapGL_injective (S := ℝ))] at hgq
    exact ⟨-j, hgq⟩
  · refine mk_rangeRestrict_eq_of_mul_T_zpow hj (-j) ?_
    symm
    calc ModularGroup.T ^ (-j) * (-γ⁻¹) * -(γ * ModularGroup.T ^ j * γ⁻¹)
        = ModularGroup.T ^ (-j) * (γ⁻¹ * (γ * ModularGroup.T ^ j * γ⁻¹)) := by
            simp [mul_assoc]
      _ = γ⁻¹ := by group

private lemma neg_conj_T_zpow_mem_iff_neg_upperRightHom_mem (γ : SL(2, ℤ)) (j : ℤ) :
    -(γ * ModularGroup.T ^ j * γ⁻¹) ∈ Γ ↔
      -Matrix.GeneralLinearGroup.upperRightHom (j : ℝ) ∈
        ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ)) := by
  rw [Subgroup.mem_conj_mapGL_inv_iff, ← ModularGroup.mapGL_T_zpow_eq_upperRightHom, mul_neg,
    neg_mul, ← map_inv, ← map_mul, ← map_mul, ← mapGL_neg,
    Subgroup.mem_map_iff_mem (mapGL_injective (S := ℝ))]

/-- **Coincidence criterion for the fibre `{c₀, c₁}` over `Γ.cuspOrbitOfSL2Z γ`.**
The cusp translation orbits of `γ⁻¹` and `-γ⁻¹` coincide if and only if `-I ∈ Γ` or the cusp orbit
`Γ.cuspOrbitOfSL2Z γ` is irregular. -/
theorem cuspTranslationOrbit_mk_inv_eq_mk_neg_inv_iff [Γ.FiniteIndex] (γ : SL(2, ℤ)) :
    (⟦(QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹) :
      𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)⟧ :
        CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) =
      ⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict (-γ⁻¹))⟧ ↔
        (-1 : SL(2, ℤ)) ∈ Γ ∨ ¬Γ.IsRegularCusp (Γ.cuspOrbitOfSL2Z γ) := by
  rw [cuspTranslationOrbit_mk_inv_eq_mk_neg_inv_iff_exists, Subgroup.isRegularCusp_cuspOrbitOfSL2Z]
  set Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))
  simp_rw [neg_conj_T_zpow_mem_iff_neg_upperRightHom_mem]
  refine ⟨fun ⟨j, hj⟩ ↦ or_iff_not_imp_right.mpr fun hreg ↦ ?_, ?_⟩
  · rw [not_not] at hreg
    have hper : (j : ℝ) ∈ Γγ.periods := by
      rw [Subgroup.periods, Subgroup.mem_strictPeriods_iff, Subgroup.mem_adjoinNegOne_iff]
      exact Or.inr hj
    have hsp : Matrix.GeneralLinearGroup.upperRightHom (j : ℝ) ∈ Γγ := by
      rwa [← Subgroup.mem_strictPeriods_iff, hreg]
    have hneg_mem : (-1 : GL (Fin 2) ℝ) ∈ Γγ := by
      have hmul : (-Matrix.GeneralLinearGroup.upperRightHom (j : ℝ)) *
          (Matrix.GeneralLinearGroup.upperRightHom (j : ℝ))⁻¹ = -1 := by
        rw [neg_mul, mul_inv_cancel]
      exact hmul ▸ mul_mem hj (inv_mem hsp)
    have hneg' := Subgroup.mem_conjAct_smul_of_mem_center
      (Subgroup.mem_center_iff.mpr fun _ ↦ by simp) (mapGL ℝ γ) hneg_mem
    rw [smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul,
      ← Matrix.SpecialLinearGroup.mapGL_neg_one (R := ℤ),
      Subgroup.mem_map_iff_mem (mapGL_injective (S := ℝ))] at hneg'
    exact hneg'
  · rintro (hneg | hirr)
    · refine ⟨0, ?_⟩
      rw [← neg_conj_T_zpow_mem_iff_neg_upperRightHom_mem]
      simpa using hneg
    · have hmem := Subgroup.neg_upperRightHom_widthInfty_mem_of_not_isRegularAtInfty Γγ hirr
      obtain ⟨j, hj, -⟩ :=
        exists_int_eq_and_neg_conj_T_zpow_mem_of_neg_upperRightHom_mem_conj γ hmem
      exact ⟨j, hj ▸ hmem⟩

private lemma strictPeriods_conj_eq_zmultiples_cuspTranslationOrbitWidth (γ : SL(2, ℤ)) :
    (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).strictPeriods =
      AddSubgroup.zmultiples
        (cuspTranslationOrbitWidth
          (⟦(QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹) :
            𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)⟧ :
              CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) : ℝ) := by
  set w₀ := cuspTranslationOrbitWidth
    (⟦(QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹) :
      𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)⟧ :
        CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ)))
  ext x
  rw [Subgroup.mem_strictPeriods_iff, AddSubgroup.mem_zmultiples_iff]
  refine ⟨fun hx ↦ ?_, fun ⟨m, hm⟩ ↦ ?_⟩
  · obtain ⟨j, rfl, hj_mem⟩ := exists_int_eq_and_conj_T_zpow_mem_of_upperRightHom_mem_conj γ hx
    have hnat_mem : (γ⁻¹)⁻¹ * ModularGroup.T ^ j.natAbs * γ⁻¹ ∈ Γ := by
      rw [inv_inv]
      rcases Int.natAbs_eq j with hj_abs | hj_abs
      · rwa [← zpow_natCast, ← hj_abs]
      · have hinv : (γ * ModularGroup.T ^ j * γ⁻¹)⁻¹ =
            γ * ModularGroup.T ^ (-j) * γ⁻¹ := by group
        rw [← zpow_natCast, ← neg_eq_iff_eq_neg.mpr hj_abs, ← hinv]
        exact inv_mem hj_mem
    obtain ⟨m, hm⟩ := Int.natCast_dvd.mpr
      ((cuspTranslationOrbitWidth_mk_dvd_iff γ⁻¹ j.natAbs).mpr hnat_mem)
    exact ⟨m, by rw [zsmul_eq_mul, mul_comm, ← Int.cast_natCast, ← Int.cast_mul, ← hm]⟩
  · have hw₀_mem : (γ⁻¹)⁻¹ * ModularGroup.T ^ w₀ * γ⁻¹ ∈ Γ :=
      (cuspTranslationOrbitWidth_mk_dvd_iff γ⁻¹ w₀).mp dvd_rfl
    rw [inv_inv] at hw₀_mem
    have hm_mem : γ * ModularGroup.T ^ ((w₀ : ℤ) * m) * γ⁻¹ ∈ Γ := by
      simpa only [conj_zpow, ← zpow_natCast, ← _root_.zpow_mul] using zpow_mem hw₀_mem m
    rw [← hm, zsmul_eq_mul, mul_comm, ← Int.cast_natCast, ← Int.cast_mul,
      ← ModularGroup.mapGL_T_zpow_eq_upperRightHom, Subgroup.mem_conj_mapGL_inv_iff]
    simpa [map_mul, map_inv, mul_assoc] using Subgroup.mem_map_of_mem (mapGL ℝ) hm_mem

/-- **Strict cusp width equals integer cusp-translation-orbit width.** For any subgroup
`Γ ≤ SL(2, ℤ)` and `γ ∈ SL(2, ℤ)`, the strict width `strictWidthInfty` of `γ⁻¹ Γ γ` equals the
width of the cusp translation orbit of `γ⁻¹`. -/
theorem natCast_cuspTranslationOrbitWidth_mk_inv_eq_strictWidthInfty (γ : SL(2, ℤ)) :
    (cuspTranslationOrbitWidth
      (⟦(QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹) :
        𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)⟧ :
          CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) : ℝ) =
      (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).strictWidthInfty :=
  (Subgroup.strictWidthInfty_eq_of_strictPeriods_eq_zmultiples
    (strictPeriods_conj_eq_zmultiples_cuspTranslationOrbitWidth γ) (Nat.cast_nonneg _)).symm

end TauCeti.ModularForm

end
