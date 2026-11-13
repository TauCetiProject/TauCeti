/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Basic
public import TauCeti.NumberTheory.ModularForms.Norm.Cusps
public import TauCeti.NumberTheory.ModularForms.Order.CuspOrbits
public import TauCeti.NumberTheory.ModularForms.Order.EffectiveOrbits
import TauCeti.NumberTheory.Modular.ConjugateTranslation
import TauCeti.NumberTheory.ModularForms.Cusps.Codimension

/-!
# The projective valence formula on the compactified quotient

For a finite-index subgroup `Γ ≤ SL(2, ℤ)`, `TauCeti.ModularForm.valence_formula_finiteIndex`
expresses the total vanishing mass of a nonzero weight-`k` modular form `f` in the matrix-coset
convention:
`∑_{o ∈ Γ \ ℍ} (2 / |Stab_Γ o|) · ord_o f + ∑_{c ∈ T \ (𝒮ℒ / Γ)} ord_c f = k · [SL(2, ℤ) : Γ] / 12`.

Geometrically, the modular curve attached to `Γ` is the compactified quotient
`(Γ.map sl2zToPSL2R).CompactifiedQuotient` of `ℍ` by the effective image `Γ.map sl2zToPSL2R` in
`PSL(2, ℝ)`, whose projective index is `[PSL(2, ℤ) : Γ.map sl2zToPSL2R] = [SL(2, ℤ) : ±Γ]`
(`Γ.withCenter.index`). The passage from the matrix identity to the projective identity divides
every local term and the right-hand side by the central index `δ = [±Γ : Γ]`
(`Γ.relIndex Γ.withCenter`, equal to `1` if `-I ∈ Γ` and `2` if `-I ∉ Γ`), rather than by an
unconditional factor `2`:

* **Interior orbits** (`Order/EffectiveOrbits.lean`): each matrix orbit `o` corresponds bijectively
  to an effective orbit `P` with `2 / |Stab_Γ o| = δ / e_P`, where `e_P` is the effective
  stabiliser order in `Γ.map sl2zToPSL2R`.
* **Cusps** (this file): the projection `cuspOrbitOfTranslationOrbit` sends the `T`-orbit of the
  coset of `γ⁻¹ ∈ SL(2, ℤ)` to the cusp orbit `Γ.cuspOrbitOfSL2Z γ` of `γ • ∞`. Its fibre over
  `Γ.cuspOrbitOfSL2Z γ` consists of the translation orbits `c₀` and `c₁` of `γ⁻¹` and `-γ⁻¹`, which
  carry equal `q`-expansion orders at the strict width `strictWidthInfty` of `γ⁻¹ Γ γ` and coincide
  if and only if `-I ∈ Γ` or the cusp is irregular:
  - When `-I ∈ Γ` (`δ = 1`), every cusp is regular, `c₀ = c₁`, `strictWidthInfty = widthInfty`, and
    the singleton fibre contributes `1 · orderAtCuspOrbit f C`.
  - When `-I ∉ Γ` (`δ = 2`) and `C` is regular, `c₀ ≠ c₁`, `strictWidthInfty = widthInfty`, and the
    two-element fibre `{c₀, c₁}` contributes `2 · orderAtCuspOrbit f C`.
  - When `-I ∉ Γ` (`δ = 2`) and `C` is irregular, `c₀ = c₁`, `strictWidthInfty = 2 · widthInfty`,
    and the single width-`2h` translation orbit already has order `2 · orderAtCuspOrbit f C`.
* **Right-hand side**: `[SL(2, ℤ) : Γ] = [±Γ : Γ] · [SL(2, ℤ) : ±Γ] = δ · Γ.withCenter.index`.

Cancelling `δ ≠ 0` yields `valence_formula_projective` and its unified form
`valence_formula_compactifiedQuotient` over `(Γ.map sl2zToPSL2R).CompactifiedQuotient`, with
effective stabiliser order `1` at cusps.

## Main definitions and results

* `TauCeti.ModularForm.cuspOrbitOfTranslationOrbit`: canonical projection from
  `CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))` to `(Γ.map sl2zToPSL2R).CuspOrbit`.
* `TauCeti.ModularForm.cuspOrbitOfTranslationOrbit_eq_cuspOrbitOfSL2Z_iff` and
  `TauCeti.ModularForm.cuspTranslationOrbit_mk_inv_eq_mk_neg_inv_iff`: description of the fibre
  `{c₀, c₁}` over `Γ.cuspOrbitOfSL2Z γ` and the criterion `c₀ = c₁ ↔ -1 ∈ Γ ∨ ¬IsRegularCusp Γ C`.
* `TauCeti.ModularForm.coe_cuspTranslationOrbitWidth_mk_inv`: the integer width of the translation
  orbit of `γ⁻¹` equals the strict width `strictWidthInfty` of `γ⁻¹ Γ γ`.
* `TauCeti.ModularForm.sum_orderAtCuspTranslationOrbit_eq_relIndex_withCenter_mul`: the sum of
  cusp translation-orbit orders is `[±Γ : Γ]` times the sum of projective cusp orders.
* `TauCeti.ModularForm.valence_formula_projective`: the projective valence formula
  `∑ᶠ P, ord_P f / e_P + ∑ᶠ C, ord_C f = k · [SL(2, ℤ) : ±Γ] / 12`.
* `TauCeti.ModularForm.orderOnCompactifiedQuotient`,
  `TauCeti.ModularForm.effectiveStabilizerOrderOnCompactifiedQuotient`,
  `TauCeti.ModularForm.weightedOrderOnCompactifiedQuotient`, and
  `TauCeti.ModularForm.valence_formula_compactifiedQuotient`: unified geometric order and valence
  formula on `(Γ.map sl2zToPSL2R).CompactifiedQuotient`.
* `twelve_mul_orderOfVanishingOnEffectiveOrbit_le_weight_mul_index_withCenter_mul_cardStabilizer`,
  `orderOfVanishingOnEffectiveOrbit_eq_zero_of_mul_lt_twelve`, and
  `twelve_mul_orderAtCuspOrbit_le_weight_mul_index_withCenter`: single-orbit and single-cusp
  vanishing bounds in projective index.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], §§3.2–3.3
  (with the authors' errata to pp. 74–75 on irregular cusps in odd weight).
-/

public section

open Filter Function Matrix Matrix.SpecialLinearGroup MulAction UpperHalfPlane
open scoped MatrixGroups ModularForm Pointwise

namespace TauCeti.ModularForm

private local instance isArithmeticConjMapGL {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    (γ : SL(2, ℤ)) :
    (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).IsArithmetic := by
  simpa [← (Rat.castHom ℝ).algebraMap_toAlgebra, map_inv, map_mapGL]
    using Subgroup.IsArithmetic.conj (Γ : Subgroup (GL (Fin 2) ℝ)) (mapGL ℚ γ)⁻¹

section CuspProjection

private noncomputable def sl2zOfSL (x : 𝒮ℒ) : SL(2, ℤ) :=
  Function.surjInv (mapGL ℝ).rangeRestrict_surjective x

private lemma rangeRestrict_sl2zOfSL (x : 𝒮ℒ) : (mapGL ℝ).rangeRestrict (sl2zOfSL x) = x :=
  Function.surjInv_eq (mapGL ℝ).rangeRestrict_surjective x

private lemma sl2zOfSL_rangeRestrict (γ : SL(2, ℤ)) :
    sl2zOfSL ((mapGL ℝ).rangeRestrict γ) = γ :=
  mapGL_injective (S := ℝ) (congrArg Subtype.val (rangeRestrict_sl2zOfSL _))

private lemma mapGL_T_zpow_eq_upperRightHom (j : ℤ) :
    mapGL ℝ (ModularGroup.T ^ j) = Matrix.GeneralLinearGroup.upperRightHom (j : ℝ) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.GeneralLinearGroup.upperRightHom]

private lemma cuspOrbitOfSL2Z_neg {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (γ : SL(2, ℤ)) :
    Γ.cuspOrbitOfSL2Z (-γ) = Γ.cuspOrbitOfSL2Z γ := by
  apply Subtype.ext
  rw [Γ.cuspOrbitOfSL2Z_val, Γ.cuspOrbitOfSL2Z_val, sl2zToPSL2R_neg]

private lemma conj_mapGL_neg (𝒢 : Subgroup (GL (Fin 2) ℝ)) (γ : SL(2, ℤ)) :
    ConjAct.toConjAct (mapGL ℝ (-γ))⁻¹ • 𝒢 = ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • 𝒢 := by
  have hneg : mapGL ℝ (-γ) = mapGL ℝ γ * (-1) := by
    have hneg' : (-γ : SL(2, ℤ)) = γ * (-1) := by simp
    rw [hneg', map_mul, Matrix.SpecialLinearGroup.mapGL_neg_one]
  ext x
  simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul, hneg, _root_.mul_inv_rev]
  have hcomm : (mapGL ℝ γ * (-1)) * x * ((-1)⁻¹ * (mapGL ℝ γ)⁻¹) =
      mapGL ℝ γ * x * (mapGL ℝ γ)⁻¹ := by
    apply Units.ext
    simp [mul_assoc]
  rw [hcomm]

/-- **Projection from matrix cusp translation orbits to projective cusp orbits.**
The translation orbit of the coset of `γ ∈ SL(2, ℤ)` in `𝒮ℒ ⧸ Γ`, whose coset factor in the norm is
`f ∣[k] γ⁻¹`, maps to `Γ.cuspOrbitOfSL2Z γ⁻¹` (the `Γ`-orbit of `γ⁻¹ • ∞`). -/
noncomputable def cuspOrbitOfTranslationOrbit (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ)) → (Γ.map sl2zToPSL2R).CuspOrbit :=
  Quotient.lift
    (Quotient.lift (fun x : 𝒮ℒ ↦ Γ.cuspOrbitOfSL2Z (sl2zOfSL x)⁻¹) fun x y hxy ↦ by
      apply cuspOrbitOfSL2Z_inv_eq_of_cuspTranslationOrbit_mk_eq
      rw [rangeRestrict_sl2zOfSL, rangeRestrict_sl2zOfSL]
      exact congrArg Quotient.mk'' (Quotient.sound hxy))
    fun q₁ q₂ hq ↦ by
      induction q₁ using Quotient.inductionOn with | h x => ?_
      induction q₂ using Quotient.inductionOn with | h y => ?_
      apply cuspOrbitOfSL2Z_inv_eq_of_cuspTranslationOrbit_mk_eq
      rw [rangeRestrict_sl2zOfSL, rangeRestrict_sl2zOfSL]
      exact Quotient.sound hq

@[simp]
theorem cuspOrbitOfTranslationOrbit_mk {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (γ : SL(2, ℤ)) :
    cuspOrbitOfTranslationOrbit Γ
        (⟦(QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ) :
          𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)⟧ :
            CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) =
      Γ.cuspOrbitOfSL2Z γ⁻¹ :=
  congrArg (fun g ↦ Γ.cuspOrbitOfSL2Z g⁻¹) (sl2zOfSL_rangeRestrict γ)

/-- Every projective cusp orbit is the image of a cusp translation orbit. -/
theorem cuspOrbitOfTranslationOrbit_surjective (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    Function.Surjective (cuspOrbitOfTranslationOrbit Γ) := fun C ↦ by
  obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
  exact ⟨⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹)⟧,
    by rw [cuspOrbitOfTranslationOrbit_mk, inv_inv]⟩

end CuspProjection

section CuspFiber

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

/-- **Fibre of `cuspOrbitOfTranslationOrbit` over `Γ.cuspOrbitOfSL2Z γ`.** Every translation orbit
mapping to `Γ.cuspOrbitOfSL2Z γ` is either the orbit of `γ⁻¹` or that of `-γ⁻¹`. -/
theorem cuspOrbitOfTranslationOrbit_eq_cuspOrbitOfSL2Z_iff [Γ.FiniteIndex] (γ : SL(2, ℤ))
    (c : CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) :
    cuspOrbitOfTranslationOrbit Γ c = Γ.cuspOrbitOfSL2Z γ ↔
      c = ⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹)⟧ ∨
        c = ⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict (-γ⁻¹))⟧ := by
  refine ⟨fun hc ↦ ?_, fun hc ↦ ?_⟩
  · induction c using CuspTranslationOrbit.induction_on with | h δ => ?_
    rw [cuspOrbitOfTranslationOrbit_mk] at hc
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
    · rw [cuspOrbitOfTranslationOrbit_mk, inv_inv]
    · have hinv : (-γ⁻¹ : SL(2, ℤ))⁻¹ = -γ := by simp
      rw [cuspOrbitOfTranslationOrbit_mk, hinv, cuspOrbitOfSL2Z_neg]

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
      have hneg : (-γ⁻¹ : SL(2, ℤ)) = γ⁻¹ * (-1) := by simp
      have hneg' : -(γ * ModularGroup.T ^ (-j) * γ⁻¹) =
          γ * ModularGroup.T ^ (-j) * γ⁻¹ * (-1) := by simp
      rw [hneg, hneg']
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv, coe_TSL_zpow,
        TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, MonoidHom.coe_rangeRestrict, map_mul,
        map_inv, map_zpow, _root_.zpow_neg, _root_.mul_inv_rev, inv_inv]
      group
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
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul, ← mapGL_T_zpow_eq_upperRightHom]
  have hmat : mapGL ℝ γ * -mapGL ℝ (ModularGroup.T ^ j) * (mapGL ℝ γ)⁻¹ =
      mapGL ℝ (-(γ * ModularGroup.T ^ j * γ⁻¹)) := by
    have h1 : -(γ * ModularGroup.T ^ j * γ⁻¹) = γ * ((-1) * ModularGroup.T ^ j) * γ⁻¹ := by simp
    have h2 : -mapGL ℝ (ModularGroup.T ^ j) = (-1) * mapGL ℝ (ModularGroup.T ^ j) := by
      apply Units.ext
      simp
    rw [h1, h2, map_mul, map_mul, map_mul, map_inv, Matrix.SpecialLinearGroup.mapGL_neg_one]
  rw [hmat, Subgroup.mem_map_iff_mem (mapGL_injective (S := ℝ))]

private lemma exists_int_eq_of_neg_upperRightHom_mem_conj (γ : SL(2, ℤ)) {w : ℝ}
    (hmem : -Matrix.GeneralLinearGroup.upperRightHom w ∈
      ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))) :
    ∃ j : ℤ, w = j := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul] at hmem
  obtain ⟨g, -, hg_eq⟩ := Subgroup.mem_map.mp hmem
  set u : SL(2, ℤ) := γ⁻¹ * g * γ with hu_def
  have hconj : mapGL ℝ u = -Matrix.GeneralLinearGroup.upperRightHom w := by
    rw [hu_def, map_mul, map_mul, map_inv, hg_eq]
    group
  have h01 : (u 0 1 : ℝ) = -w := by
    simpa [mapGL_coe_matrix, Matrix.GeneralLinearGroup.upperRightHom] using
      congr_arg (fun M : GL (Fin 2) ℝ ↦ (M : Matrix (Fin 2) (Fin 2) ℝ) 0 1) hconj
  exact ⟨-u 0 1, by push_cast; linarith⟩

private lemma exists_int_eq_and_conj_T_zpow_mem_of_upperRightHom_mem_conj (γ : SL(2, ℤ)) {x : ℝ}
    (hx : Matrix.GeneralLinearGroup.upperRightHom x ∈
      ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))) :
    ∃ j : ℤ, x = j ∧ γ * ModularGroup.T ^ j * γ⁻¹ ∈ Γ := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul] at hx
  obtain ⟨h, hh, hh_eq⟩ := Subgroup.mem_map.mp hx
  set u : SL(2, ℤ) := γ⁻¹ * h * γ with hu_def
  have hconj : mapGL ℝ u = Matrix.GeneralLinearGroup.upperRightHom x := by
    rw [hu_def, map_mul, map_mul, map_inv, hh_eq]
    group
  have hx_eq : x = (u 0 1 : ℝ) := by
    have h01 := congr_arg (fun M : GL (Fin 2) ℝ ↦ (M : Matrix (Fin 2) (Fin 2) ℝ) 0 1) hconj
    simpa [mapGL_coe_matrix, Matrix.GeneralLinearGroup.upperRightHom] using h01.symm
  have hT : u = ModularGroup.T ^ (u 0 1) :=
    mapGL_injective (S := ℝ) (by rw [hconj, hx_eq, mapGL_T_zpow_eq_upperRightHom])
  have hj_mem : γ * ModularGroup.T ^ (u 0 1) * γ⁻¹ ∈ Γ := by
    have : γ * u * γ⁻¹ = h := by rw [hu_def]; group
    rwa [← hT, this]
  exact ⟨u 0 1, hx_eq, hj_mem⟩

/-- **Coincidence criterion for the fibre `{c₀, c₁}` over `Γ.cuspOrbitOfSL2Z γ`.**
The cusp translation orbits of `γ⁻¹` and `-γ⁻¹` coincide if and only if `-I ∈ Γ` or the cusp orbit
`Γ.cuspOrbitOfSL2Z γ` is irregular. -/
theorem cuspTranslationOrbit_mk_inv_eq_mk_neg_inv_iff [Γ.FiniteIndex] (γ : SL(2, ℤ)) :
    (⟦(QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹) :
      𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)⟧ :
        CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) =
      ⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict (-γ⁻¹))⟧ ↔
        (-1 : SL(2, ℤ)) ∈ Γ ∨ ¬IsRegularCusp Γ (Γ.cuspOrbitOfSL2Z γ) := by
  rw [cuspTranslationOrbit_mk_inv_eq_mk_neg_inv_iff_exists, isRegularCusp_cuspOrbitOfSL2Z]
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
        apply Units.ext
        ext a b
        fin_cases a <;> fin_cases b <;> simp [Matrix.GeneralLinearGroup.upperRightHom]
      exact hmul ▸ mul_mem hj (inv_mem hsp)
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
      ConjAct.toConjAct_smul] at hneg_mem
    have hcenter : mapGL ℝ γ * (-1) * (mapGL ℝ γ)⁻¹ = (-1 : GL (Fin 2) ℝ) := by
      apply Units.ext
      simp
    rw [hcenter, ← Matrix.SpecialLinearGroup.mapGL_neg_one (R := ℤ),
      Subgroup.mem_map_iff_mem (mapGL_injective (S := ℝ))] at hneg_mem
    exact hneg_mem
  · rintro (hneg | hirr)
    · refine ⟨0, ?_⟩
      rw [← neg_conj_T_zpow_mem_iff_neg_upperRightHom_mem]
      simpa using hneg
    · have hmem := Subgroup.neg_upperRightHom_widthInfty_mem_of_not_isRegularAtInfty Γγ hirr
      obtain ⟨j, hj⟩ := exists_int_eq_of_neg_upperRightHom_mem_conj γ hmem
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
      have hpow : (γ * ModularGroup.T ^ w₀ * γ⁻¹) ^ m =
          γ * ModularGroup.T ^ ((w₀ : ℤ) * m) * γ⁻¹ := by
        calc (γ * ModularGroup.T ^ w₀ * γ⁻¹) ^ m
            = (MulAut.conj γ (ModularGroup.T ^ (w₀ : ℤ))) ^ m := by rw [zpow_natCast]; rfl
          _ = MulAut.conj γ ((ModularGroup.T ^ (w₀ : ℤ)) ^ m) := (map_zpow _ _ _).symm
          _ = γ * ModularGroup.T ^ ((w₀ : ℤ) * m) * γ⁻¹ := by rw [← _root_.zpow_mul]; rfl
      exact hpow ▸ zpow_mem hw₀_mem m
    rw [← hm, zsmul_eq_mul, mul_comm, ← Int.cast_natCast, ← Int.cast_mul,
      ← mapGL_T_zpow_eq_upperRightHom, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ← ConjAct.toConjAct_inv, inv_inv, ConjAct.toConjAct_smul]
    simpa [map_mul, map_inv, mul_assoc] using Subgroup.mem_map_of_mem (mapGL ℝ) hm_mem

/-- **Strict cusp width equals integer cusp-translation-orbit width.** For any subgroup
`Γ ≤ SL(2, ℤ)` and `γ ∈ SL(2, ℤ)`, the strict width `strictWidthInfty` of `γ⁻¹ Γ γ` equals the
width of the cusp translation orbit of `γ⁻¹`. -/
theorem coe_cuspTranslationOrbitWidth_mk_inv (γ : SL(2, ℤ)) :
    (cuspTranslationOrbitWidth
      (⟦(QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹) :
        𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)⟧ :
          CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) : ℝ) =
      (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).strictWidthInfty :=
  (Subgroup.strictWidthInfty_eq_of_strictPeriods_eq_zmultiples
    (strictPeriods_conj_eq_zmultiples_cuspTranslationOrbitWidth γ) (Nat.cast_nonneg _)).symm

end CuspFiber

section CuspOrderComparison

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ}
variable {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]

/-- The vanishing order at the cusp translation orbit of `γ⁻¹` is the `q`-expansion order of
`f ∣[k] γ` at the strict width `strictWidthInfty` of `γ⁻¹ Γ γ`. -/
theorem orderAtCuspTranslationOrbit_mk_inv_eq_qExpansionOrderAtCusp (f : F) (γ : SL(2, ℤ)) :
    orderAtCuspTranslationOrbit f
        (⟦(QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹) :
          𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)⟧ :
            CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) =
      qExpansionOrderAtCusp
        (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).strictWidthInfty
        (⇑f ∣[k] mapGL ℝ γ) := by
  have hqf : SlashInvariantForm.quotientFunc f
      (QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹) :
        𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) = ⇑f ∣[k] mapGL ℝ γ := by
    rw [_root_.SlashInvariantForm.quotientFunc_mk, MonoidHom.coe_rangeRestrict, map_inv, inv_inv]
  rw [orderAtCuspTranslationOrbit_mk, ← cuspTranslationOrbitWidth_mk,
    coe_cuspTranslationOrbitWidth_mk_inv, hqf]

/-- Negating the representative `γ⁻¹` preserves `orderAtCuspTranslationOrbit`: `f ∣[k] (-γ)` and
`f ∣[k] γ` differ by the nonzero scalar `(-1) ^ k`. -/
theorem orderAtCuspTranslationOrbit_mk_neg_inv (f : F) (γ : SL(2, ℤ)) :
    orderAtCuspTranslationOrbit f
        (⟦(QuotientGroup.mk ((mapGL ℝ).rangeRestrict (-γ⁻¹)) :
          𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)⟧ :
            CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) =
      orderAtCuspTranslationOrbit f ⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹)⟧ := by
  have hinv : (-γ⁻¹ : SL(2, ℤ)) = (-γ)⁻¹ := by simp
  rw [hinv, orderAtCuspTranslationOrbit_mk_inv_eq_qExpansionOrderAtCusp,
    orderAtCuspTranslationOrbit_mk_inv_eq_qExpansionOrderAtCusp, conj_mapGL_neg]
  set Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))
  let fγ : ModularForm Γγ k := _root_.ModularForm.translate f (mapGL ℝ γ)
  have hfγ_coe : ⇑fγ = ⇑f ∣[k] mapGL ℝ γ := rfl
  have hslash : ⇑f ∣[k] mapGL ℝ (-γ) = ⇑fγ ∣[k] mapGL ℝ (-1 : SL(2, ℝ))⁻¹ := by
    have hneg : (-γ : SL(2, ℤ)) = γ * (-1) := by simp
    have hneg_sl : (-1 : SL(2, ℝ))⁻¹ = -1 := by ext a b; simp
    rw [hfγ_coe, hneg, hneg_sl, map_mul, Matrix.SpecialLinearGroup.mapGL_neg_one,
      Matrix.SpecialLinearGroup.mapGL_neg_one, SlashAction.slash_mul]
  have hw_eq : ((-1 : SL(2, ℝ)) 0 0) ^ 2 * Γγ.strictWidthInfty = Γγ.strictWidthInfty := by simp
  conv_lhs => rw [hslash, ← hw_eq]
  rw [← hfγ_coe]
  exact qExpansionOrderAtCusp_slash_mapGL_inv (t := -1) Γγ.strictWidthInfty_pos (by simp)
    (SlashInvariantFormClass.periodic_comp_ofComplex fγ Γγ.strictWidthInfty_mem_strictPeriods)
    (ModularFormClass.analyticAt_cuspFunction_zero fγ Γγ.strictWidthInfty_pos
      Γγ.strictWidthInfty_mem_strictPeriods)

/-- At a regular cusp `Γ.cuspOrbitOfSL2Z γ`, the translation orbit of `γ⁻¹` has the same order as
the projective cusp orbit. -/
theorem coe_orderAtCuspTranslationOrbit_mk_inv_of_isRegularCusp (f : F) {γ : SL(2, ℤ)}
    (hreg : IsRegularCusp Γ (Γ.cuspOrbitOfSL2Z γ)) :
    (orderAtCuspTranslationOrbit f
      (⟦(QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹) :
        𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)⟧ :
          CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) : ℚ) =
      orderAtCuspOrbit f (Γ.cuspOrbitOfSL2Z γ) := by
  have hreg' := (isRegularCusp_cuspOrbitOfSL2Z γ).mp hreg
  rw [orderAtCuspTranslationOrbit_mk_inv_eq_qExpansionOrderAtCusp,
    Subgroup.strictWidthInfty_of_isRegularAtInfty _ hreg',
    orderAtCuspOrbit_cuspOrbitOfSL2Z_eq_qExpansionOrderAtCusp_of_isRegularCusp f hreg]

/-- At an irregular cusp `Γ.cuspOrbitOfSL2Z γ`, the translation orbit of `γ⁻¹` has strict width
`2 · widthInfty` and therefore twice the projective cusp order. -/
theorem coe_orderAtCuspTranslationOrbit_mk_inv_of_not_isRegularCusp (f : F) {γ : SL(2, ℤ)}
    (hirr : ¬IsRegularCusp Γ (Γ.cuspOrbitOfSL2Z γ)) :
    (orderAtCuspTranslationOrbit f
      (⟦(QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹) :
        𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)⟧ :
          CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) : ℚ) =
      2 * orderAtCuspOrbit f (Γ.cuspOrbitOfSL2Z γ) := by
  have hirr' : ¬(ConjAct.toConjAct (mapGL ℝ γ)⁻¹ •
      (Γ : Subgroup (GL (Fin 2) ℝ))).IsRegularAtInfty :=
    mt (isRegularCusp_cuspOrbitOfSL2Z γ).mpr hirr
  rw [orderAtCuspTranslationOrbit_mk_inv_eq_qExpansionOrderAtCusp,
    Subgroup.strictWidthInfty_of_not_isRegularAtInfty _ hirr',
    orderAtCuspOrbit_cuspOrbitOfSL2Z, TauCeti.orderAtCusp_def]
  ring

/-- **Local cusp-fibre comparison**: the orders on the cusp translation orbits over a single
projective cusp orbit `C` sum to `[±Γ : Γ] · orderAtCuspOrbit f C` across all cases of `-I ∈ Γ`
and cusp regularity. -/
theorem sum_filter_cuspOrbitOfTranslationOrbit_eq [DecidableEq (Γ.map sl2zToPSL2R).CuspOrbit]
    (f : F) (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    (∑ c ∈ Finset.univ.filter (fun c ↦ cuspOrbitOfTranslationOrbit Γ c = C),
        (orderAtCuspTranslationOrbit f c : ℚ)) =
      (Γ.relIndex Γ.withCenter : ℚ) * orderAtCuspOrbit f C := by
  classical
  obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
  set c₀ : CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ)) :=
    ⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹)⟧
  set c₁ : CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ)) :=
    ⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict (-γ⁻¹))⟧
  have hfib : Finset.univ.filter
      (fun c ↦ cuspOrbitOfTranslationOrbit Γ c = Γ.cuspOrbitOfSL2Z γ) = {c₀, c₁} := by
    ext c
    simp [c₀, c₁, cuspOrbitOfTranslationOrbit_eq_cuspOrbitOfSL2Z_iff]
  rw [hfib]
  by_cases hneg : (-1 : SL(2, ℤ)) ∈ Γ
  · have hc : c₀ = c₁ := (cuspTranslationOrbit_mk_inv_eq_mk_neg_inv_iff γ).mpr (Or.inl hneg)
    have hreg : IsRegularCusp Γ (Γ.cuspOrbitOfSL2Z γ) := isRegularCusp_of_neg_one_mem hneg _
    rw [hc, Finset.pair_eq_singleton, Finset.sum_singleton, ← hc,
      coe_orderAtCuspTranslationOrbit_mk_inv_of_isRegularCusp f hreg,
      relIndex_withCenter_eq_one_of_neg_one_mem hneg, Nat.cast_one, one_mul]
  · rw [relIndex_withCenter_eq_two_of_neg_one_notMem hneg, Nat.cast_ofNat]
    by_cases hreg : IsRegularCusp Γ (Γ.cuspOrbitOfSL2Z γ)
    · have hcne : c₀ ≠ c₁ := fun hc ↦
        ((cuspTranslationOrbit_mk_inv_eq_mk_neg_inv_iff γ).mp hc).elim hneg fun hirr ↦ hirr hreg
      rw [Finset.sum_pair hcne, orderAtCuspTranslationOrbit_mk_neg_inv f γ,
        coe_orderAtCuspTranslationOrbit_mk_inv_of_isRegularCusp f hreg]
      ring
    · have hc : c₀ = c₁ := (cuspTranslationOrbit_mk_inv_eq_mk_neg_inv_iff γ).mpr (Or.inr hreg)
      rw [hc, Finset.pair_eq_singleton, Finset.sum_singleton, ← hc,
        coe_orderAtCuspTranslationOrbit_mk_inv_of_not_isRegularCusp f hreg]

/-- **Global cusp-sum comparison**: summing `orderAtCuspTranslationOrbit` over all cusp translation
orbits multiplies the projective cusp-order sum over `(Γ.map sl2zToPSL2R).CuspOrbit` by
`[±Γ : Γ]`. -/
theorem sum_orderAtCuspTranslationOrbit_eq_relIndex_withCenter_mul (f : F) :
    (∑ c : CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ)),
        (orderAtCuspTranslationOrbit f c : ℚ)) =
      (Γ.relIndex Γ.withCenter : ℚ) *
        ∑ᶠ C : (Γ.map sl2zToPSL2R).CuspOrbit, orderAtCuspOrbit f C := by
  classical
  let _ : Fintype (Γ.map sl2zToPSL2R).CuspOrbit := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, Finset.mul_sum,
    ← Finset.sum_fiberwise_of_maps_to (g := cuspOrbitOfTranslationOrbit Γ)
      (fun _ _ ↦ Finset.mem_univ _)]
  exact Finset.sum_congr rfl fun C _ ↦ sum_filter_cuspOrbitOfTranslationOrbit_eq f C

end CuspOrderComparison

section ProjectiveValenceFormula

variable {Γ : Subgroup SL(2, ℤ)}

/-- **Effective stabiliser order `e_x` on the compactified quotient**: `cardStabilizerOnOrbit P` at
an interior orbit `P` of `Γ.map sl2zToPSL2R`, and `1` at every cusp. -/
noncomputable def effectiveStabilizerOrderOnCompactifiedQuotient :
    (Γ.map sl2zToPSL2R).CompactifiedQuotient → ℕ
  | .ofQuotient P => cardStabilizerOnOrbit P
  | .ofCusp _ => 1

@[simp]
theorem effectiveStabilizerOrderOnCompactifiedQuotient_ofQuotient
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    effectiveStabilizerOrderOnCompactifiedQuotient (.ofQuotient P) = cardStabilizerOnOrbit P :=
  (rfl)

@[simp]
theorem effectiveStabilizerOrderOnCompactifiedQuotient_ofCusp
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    effectiveStabilizerOrderOnCompactifiedQuotient (.ofCusp C) = 1 :=
  (rfl)

/-- The effective stabiliser order `e_x` is nonzero at every point of the compactified quotient. -/
theorem effectiveStabilizerOrderOnCompactifiedQuotient_ne_zero
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    effectiveStabilizerOrderOnCompactifiedQuotient x ≠ 0 := by
  cases x with
  | ofQuotient P => exact cardStabilizerOnOrbit_effective_ne_zero P
  | ofCusp _ => exact one_ne_zero

variable [Γ.FiniteIndex] {k k₁ k₂ : ℤ}
variable {F : Type*} [FunLike F ℍ ℂ]

/-- **The projective valence formula.** For a nonzero modular form `f` of weight `k` on a
finite-index subgroup `Γ ≤ SL(2, ℤ)`, the effective-stabiliser-weighted interior vanishing orders
over `(Γ.map sl2zToPSL2R) \ ℍ` plus the geometric cusp orders over `(Γ.map sl2zToPSL2R).CuspOrbit`
equal `k · [SL(2, ℤ) : ±Γ] / 12`. -/
theorem valence_formula_projective [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]
    (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    (∑ᶠ P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ,
          weightedOrderOfVanishingOnEffectiveOrbit f P) +
        (∑ᶠ C : (Γ.map sl2zToPSL2R).CuspOrbit, orderAtCuspOrbit f C) =
      (k : ℚ) * Γ.withCenter.index / 12 := by
  have hval := valence_formula_finiteIndex f hf
  rw [finsum_weightedOrderOfVanishingOnSubgroupOrbit_eq_relIndex_withCenter_mul f,
    sum_orderAtCuspTranslationOrbit_eq_relIndex_withCenter_mul f,
    _root_.Subgroup.card_quotient_mapGL_eq_index Γ,
    ← Subgroup.relIndex_mul_index Γ.le_withCenter, Nat.cast_mul, ← mul_add] at hval
  have hδ : (Γ.relIndex Γ.withCenter : ℚ) ≠ 0 := by
    exact_mod_cast relIndex_withCenter_ne_zero Γ
  exact mul_left_cancel₀ hδ (hval.trans (by ring))

/-! ### Unified geometric order on `(Γ.map sl2zToPSL2R).CompactifiedQuotient` -/

/-- **Geometric vanishing order on `(Γ.map sl2zToPSL2R).CompactifiedQuotient`**: the integer
analytic order on interior points and the rational (`ℕ`- or `(1/2)ℕ`-valued) cusp order at
cusps. -/
noncomputable def orderOnCompactifiedQuotient
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]
    (f : F) : (Γ.map sl2zToPSL2R).CompactifiedQuotient → ℚ
  | .ofQuotient P => orderOfVanishingOnEffectiveOrbit f P
  | .ofCusp C => orderAtCuspOrbit f C

@[simp]
theorem orderOnCompactifiedQuotient_ofQuotient
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    orderOnCompactifiedQuotient f (.ofQuotient P) = orderOfVanishingOnEffectiveOrbit f P :=
  (rfl)

@[simp]
theorem orderOnCompactifiedQuotient_ofCusp
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    orderOnCompactifiedQuotient f (.ofCusp C) = orderAtCuspOrbit f C :=
  (rfl)

@[simp]
theorem orderOnCompactifiedQuotient_zero (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    orderOnCompactifiedQuotient (0 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) x = 0 := by
  cases x <;> simp

/-- **Weighted geometric order `ord_x f / e_x` on the compactified quotient.** -/
noncomputable def weightedOrderOnCompactifiedQuotient
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) : ℚ :=
  orderOnCompactifiedQuotient f x / effectiveStabilizerOrderOnCompactifiedQuotient x

@[simp]
theorem weightedOrderOnCompactifiedQuotient_ofQuotient
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    weightedOrderOnCompactifiedQuotient f (.ofQuotient P) =
      weightedOrderOfVanishingOnEffectiveOrbit f P := by
  rw [weightedOrderOnCompactifiedQuotient, orderOnCompactifiedQuotient_ofQuotient,
    effectiveStabilizerOrderOnCompactifiedQuotient_ofQuotient,
    weightedOrderOfVanishingOnEffectiveOrbit_def]

@[simp]
theorem weightedOrderOnCompactifiedQuotient_ofCusp
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    weightedOrderOnCompactifiedQuotient f (.ofCusp C) = orderAtCuspOrbit f C := by
  simp [weightedOrderOnCompactifiedQuotient]

@[simp]
theorem weightedOrderOnCompactifiedQuotient_zero (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    weightedOrderOnCompactifiedQuotient
      (0 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) x = 0 := by
  simp [weightedOrderOnCompactifiedQuotient]

/-- The geometric vanishing order of a modular form is nonnegative at every point of the
compactified quotient. -/
theorem orderOnCompactifiedQuotient_nonneg [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]
    (f : F) (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    0 ≤ orderOnCompactifiedQuotient f x := by
  cases x with
  | ofQuotient P =>
    rw [orderOnCompactifiedQuotient_ofQuotient]
    exact_mod_cast orderOfVanishingOnEffectiveOrbit_nonneg f P
  | ofCusp C => exact orderAtCuspOrbit_nonneg f C

/-- The weighted geometric vanishing order of a modular form is nonnegative at every point of the
compactified quotient. -/
theorem weightedOrderOnCompactifiedQuotient_nonneg
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    0 ≤ weightedOrderOnCompactifiedQuotient f x :=
  div_nonneg (orderOnCompactifiedQuotient_nonneg f x) (by positivity)

/-- **Additivity on products**: for nonzero modular forms `f` and `g` on `Γ`, the geometric order of
`f.mul g` on `(Γ.map sl2zToPSL2R).CompactifiedQuotient` is the sum of their geometric orders. -/
theorem _root_.ModularForm.orderOnCompactifiedQuotient_mul
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₁)
    (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₂)
    (hf : f ≠ 0) (hg : g ≠ 0) (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    orderOnCompactifiedQuotient (f.mul g) x =
      orderOnCompactifiedQuotient f x + orderOnCompactifiedQuotient g x := by
  cases x with
  | ofQuotient P =>
    simp [f.orderOfVanishingOnEffectiveOrbit_mul g hf hg P]
  | ofCusp C =>
    exact f.orderAtCuspOrbit_mul g hf hg C

/-- Additivity of the weighted geometric order on products of nonzero modular forms. -/
theorem _root_.ModularForm.weightedOrderOnCompactifiedQuotient_mul
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₁)
    (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₂)
    (hf : f ≠ 0) (hg : g ≠ 0) (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    weightedOrderOnCompactifiedQuotient (f.mul g) x =
      weightedOrderOnCompactifiedQuotient f x + weightedOrderOnCompactifiedQuotient g x := by
  rw [weightedOrderOnCompactifiedQuotient, weightedOrderOnCompactifiedQuotient,
    weightedOrderOnCompactifiedQuotient, f.orderOnCompactifiedQuotient_mul g hf hg x, add_div]

/-- A modular form on finite-index `Γ` has nonzero geometric order at only finitely many points of
`(Γ.map sl2zToPSL2R).CompactifiedQuotient`. -/
theorem hasFiniteSupport_orderOnCompactifiedQuotient
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) :
    Function.HasFiniteSupport (orderOnCompactifiedQuotient (Γ := Γ) (k := k) f) := by
  refine (((hasFiniteSupport_orderOfVanishingOnEffectiveOrbit f).image
      Subgroup.CompactifiedQuotient.ofQuotient).union
    ((hasFiniteSupport_orderAtCuspOrbit f).image Subgroup.CompactifiedQuotient.ofCusp)).subset ?_
  rintro (P | C) hx
  · exact Or.inl ⟨P, by simpa using hx, rfl⟩
  · exact Or.inr ⟨C, by simpa using hx, rfl⟩

/-- Only finitely many points of `(Γ.map sl2zToPSL2R).CompactifiedQuotient` carry nonzero weighted
geometric order. -/
theorem hasFiniteSupport_weightedOrderOnCompactifiedQuotient
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) :
    Function.HasFiniteSupport (weightedOrderOnCompactifiedQuotient (Γ := Γ) (k := k) f) := by
  refine (hasFiniteSupport_orderOnCompactifiedQuotient f).subset fun x hx ↦ ?_
  simp only [Function.mem_support, ne_eq] at hx ⊢
  exact fun h0 ↦ hx (by rw [weightedOrderOnCompactifiedQuotient, h0, zero_div])

/-- Splitting the divisor sum over `(Γ.map sl2zToPSL2R).CompactifiedQuotient` into its interior and
cusp parts. -/
theorem finsum_weightedOrderOnCompactifiedQuotient_eq_add
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) :
    (∑ᶠ x : (Γ.map sl2zToPSL2R).CompactifiedQuotient, weightedOrderOnCompactifiedQuotient f x) =
      (∑ᶠ P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ,
          weightedOrderOfVanishingOnEffectiveOrbit f P) +
        (∑ᶠ C : (Γ.map sl2zToPSL2R).CuspOrbit, orderAtCuspOrbit f C) := by
  have hfin := hasFiniteSupport_weightedOrderOnCompactifiedQuotient f
  have huniv : (Set.univ : Set (Γ.map sl2zToPSL2R).CompactifiedQuotient) =
      Set.range Subgroup.CompactifiedQuotient.ofQuotient ∪
        Set.range Subgroup.CompactifiedQuotient.ofCusp := by
    rw [← Subgroup.CompactifiedQuotient.compl_range_ofQuotient, Set.union_compl_self]
  have hdisj : Disjoint
      (Set.range (Subgroup.CompactifiedQuotient.ofQuotient (Γ := Γ.map sl2zToPSL2R)))
      (Set.range Subgroup.CompactifiedQuotient.ofCusp) := by
    rw [← Subgroup.CompactifiedQuotient.compl_range_ofQuotient]
    exact disjoint_compl_right
  rw [← finsum_mem_univ, huniv,
    finsum_mem_union' hdisj (hfin.subset Set.inter_subset_right)
      (hfin.subset Set.inter_subset_right),
    finsum_mem_range Subgroup.CompactifiedQuotient.ofQuotient_injective,
    finsum_mem_range (fun _ _ h ↦ Subgroup.CompactifiedQuotient.ofCusp.inj h)]
  simp only [weightedOrderOnCompactifiedQuotient_ofQuotient,
    weightedOrderOnCompactifiedQuotient_ofCusp]

/-- **Unified projective valence formula on the compactified quotient**:
`∑_{x ∈ X(Γ)} ord_x(f) / e_x = k · [SL(2, ℤ) : ±Γ] / 12`, with `e_x = 1` at cusps. -/
theorem valence_formula_compactifiedQuotient
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    (∑ᶠ x : (Γ.map sl2zToPSL2R).CompactifiedQuotient, weightedOrderOnCompactifiedQuotient f x) =
      (k : ℚ) * Γ.withCenter.index / 12 := by
  rw [finsum_weightedOrderOnCompactifiedQuotient_eq_add, valence_formula_projective f hf]

/-! ### Single-point and single-cusp vanishing bounds -/

/-- **Projective interior vanishing bound**: for a nonzero modular form `f` of weight `k` on `Γ`,
`12 · ord_P f ≤ k · [SL(2, ℤ) : ±Γ] · e_P` at every effective orbit `P`. -/
theorem
    twelve_mul_orderOfVanishingOnEffectiveOrbit_le_weight_mul_index_withCenter_mul_cardStabilizer
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    12 * orderOfVanishingOnEffectiveOrbit f P ≤
      k * Γ.withCenter.index * cardStabilizerOnOrbit P := by
  have he : (0 : ℚ) < (cardStabilizerOnOrbit P : ℚ) := by
    exact_mod_cast Nat.pos_of_ne_zero (cardStabilizerOnOrbit_effective_ne_zero P)
  have hsingle := single_le_finsum P
    (hasFiniteSupport_weightedOrderOfVanishingOnEffectiveOrbit f)
    (weightedOrderOfVanishingOnEffectiveOrbit_nonneg f)
  have hcusp : (0 : ℚ) ≤ ∑ᶠ C : (Γ.map sl2zToPSL2R).CuspOrbit, orderAtCuspOrbit f C :=
    finsum_nonneg (orderAtCuspOrbit_nonneg f)
  have htotal := valence_formula_projective f hf
  have hle : weightedOrderOfVanishingOnEffectiveOrbit f P ≤
      (k : ℚ) * Γ.withCenter.index / 12 := by linarith
  rw [weightedOrderOfVanishingOnEffectiveOrbit_def, div_le_iff₀ he] at hle
  have hq : (12 : ℚ) * (orderOfVanishingOnEffectiveOrbit f P : ℚ) ≤
      (k : ℚ) * Γ.withCenter.index * (cardStabilizerOnOrbit P : ℚ) := by linarith
  exact_mod_cast hq

/-- A small enough projective degree `k · [SL(2, ℤ) : ±Γ] · e_P < 12` forces vanishing order zero
at `P`. -/
theorem orderOfVanishingOnEffectiveOrbit_eq_zero_of_mul_lt_twelve
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    {P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ}
    (hk : k * Γ.withCenter.index * cardStabilizerOnOrbit P < 12) :
    orderOfVanishingOnEffectiveOrbit f P = 0 := by
  rcases eq_or_ne (⇑f : ℍ → ℂ) 0 with hf | hf
  · induction P using Quotient.inductionOn' with
    | _ z => simp [hf]
  · have hbound :=
      twelve_mul_orderOfVanishingOnEffectiveOrbit_le_weight_mul_index_withCenter_mul_cardStabilizer
        f hf P
    have := orderOfVanishingOnEffectiveOrbit_nonneg f P
    omega

/-- **Projective cusp vanishing bound**: for a nonzero modular form `f` of weight `k` on `Γ`,
`12 · ord_C f ≤ k · [SL(2, ℤ) : ±Γ]` at every cusp orbit `C`. -/
theorem twelve_mul_orderAtCuspOrbit_le_weight_mul_index_withCenter
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    12 * orderAtCuspOrbit f C ≤ (k : ℚ) * Γ.withCenter.index := by
  have hinterior : (0 : ℚ) ≤ ∑ᶠ P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ,
      weightedOrderOfVanishingOnEffectiveOrbit f P :=
    finsum_nonneg (weightedOrderOfVanishingOnEffectiveOrbit_nonneg f)
  have hsingle := single_le_finsum C (hasFiniteSupport_orderAtCuspOrbit f)
    (orderAtCuspOrbit_nonneg f)
  have htotal := valence_formula_projective f hf
  linarith

end ProjectiveValenceFormula

end TauCeti.ModularForm

end
