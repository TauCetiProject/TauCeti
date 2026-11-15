/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Cusps.TranslationOrbit
public import TauCeti.NumberTheory.ModularForms.Order.CuspOrbits
public import TauCeti.NumberTheory.ModularForms.Order.EffectiveOrbits
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.Analysis.Complex.Fuchsian.ProperAction

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
* **Cusps** (`Cusps/TranslationOrbit.lean` and this file): the projection
  `Γ.cuspOrbitOfTranslationOrbit` sends the `T`-orbit of the coset of `γ⁻¹ ∈ SL(2, ℤ)` to the cusp
  orbit `Γ.cuspOrbitOfSL2Z γ` of `γ • ∞`. Its fibre over `Γ.cuspOrbitOfSL2Z γ` consists of the
  translation orbits `c₀` and `c₁` of `γ⁻¹` and `-γ⁻¹`, which carry equal `q`-expansion orders at
  the strict width `strictWidthInfty` of `γ⁻¹ Γ γ` and coincide if and only if `-I ∈ Γ` or the cusp
  is irregular:
  - When `-I ∈ Γ` (`δ = 1`), every cusp is regular, `c₀ = c₁`, `strictWidthInfty = widthInfty`, and
    the singleton fibre contributes `1 · orderAtCuspOrbit f C`.
  - When `-I ∉ Γ` (`δ = 2`) and `C` is regular, `c₀ ≠ c₁`, `strictWidthInfty = widthInfty`, and the
    two-element fibre `{c₀, c₁}` contributes `2 · orderAtCuspOrbit f C`.
  - When `-I ∉ Γ` (`δ = 2`) and `C` is irregular, `c₀ = c₁`, `strictWidthInfty = 2 · widthInfty`,
    and the single width-`2h` translation orbit already has order `2 · orderAtCuspOrbit f C`.
* **Right-hand side**: `[SL(2, ℤ) : Γ] = [±Γ : Γ] · [SL(2, ℤ) : ±Γ] = δ · Γ.withCenter.index`.

Cancelling `δ ≠ 0` yields `valence_formula_projective` and its unified form
`valence_formula_compactifiedQuotient` over `(Γ.map sl2zToPSL2R).CompactifiedQuotient`, weighted by
`Subgroup.CompactifiedQuotient.effectiveStabilizerOrder` (`e_x = 1` at cusps).

## Main definitions and results

* `intCast_orderAtCuspTranslationOrbit_mk_inv_eq_orderAtCuspOrbit_of_isRegularCusp` and
  `intCast_orderAtCuspTranslationOrbit_mk_inv_eq_two_mul_orderAtCuspOrbit_of_not_isRegularCusp`:
  translation-orbit order at `γ⁻¹` equals `orderAtCuspOrbit` at regular cusps and twice
  `orderAtCuspOrbit` at irregular cusps.
* `TauCeti.ModularForm.sum_orderAtCuspTranslationOrbit_filter_eq_relIndex_withCenter_mul` and
  `TauCeti.ModularForm.sum_orderAtCuspTranslationOrbit_eq_relIndex_withCenter_mul`: fibrewise and
  global comparison between cusp translation-orbit orders and `[±Γ : Γ] · orderAtCuspOrbit`.
* `TauCeti.ModularForm.valence_formula_projective`: the projective valence formula
  `∑ᶠ P, ord_P f / e_P + ∑ᶠ C, ord_C f = k · [SL(2, ℤ) : ±Γ] / 12`.
* `TauCeti.ModularForm.orderOnCompactifiedQuotient`,
  `TauCeti.ModularForm.weightedOrderOnCompactifiedQuotient`, and
  `TauCeti.ModularForm.valence_formula_compactifiedQuotient`: unified geometric order and valence
  formula on `(Γ.map sl2zToPSL2R).CompactifiedQuotient`.
* `weightedOrderOnCompactifiedQuotient_le_weight_mul_index_withCenter_div_twelve`,
  `twelve_mul_orderOfVanishingOnEffectiveOrbit_le_weight_mul_index_withCenter_mul_cardStabilizer`,
  and `twelve_mul_orderAtCuspOrbit_le_weight_mul_index_withCenter`: unified, single-orbit, and
  single-cusp vanishing bounds in projective index, with zero-vanishing corollaries.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], §§3.2–3.3
  (with the authors' errata to pp. 74–75 on irregular cusps in odd weight).
-/

public noncomputable section

open Filter Function Matrix Matrix.SpecialLinearGroup MulAction UpperHalfPlane
open scoped MatrixGroups ModularForm Pointwise

namespace TauCeti.ModularForm

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
    natCast_cuspTranslationOrbitWidth_mk_inv_eq_strictWidthInfty, hqf]

/-- Negating the representative `γ⁻¹` preserves `orderAtCuspTranslationOrbit`: `f ∣[k] (-γ)` and
`f ∣[k] γ` differ by the nonzero scalar `(-1) ^ k`. -/
theorem orderAtCuspTranslationOrbit_mk_neg_inv (f : F) (γ : SL(2, ℤ)) :
    orderAtCuspTranslationOrbit f
        (⟦(QuotientGroup.mk ((mapGL ℝ).rangeRestrict (-γ⁻¹)) :
          𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)⟧ :
            CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) =
      orderAtCuspTranslationOrbit f ⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹)⟧ := by
  have hinv : (-γ⁻¹ : SL(2, ℤ)) = (-γ)⁻¹ := by simp
  set Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))
  let fγ : ModularForm Γγ k := _root_.ModularForm.translate f (mapGL ℝ γ)
  rw [hinv, orderAtCuspTranslationOrbit_mk_inv_eq_qExpansionOrderAtCusp,
    orderAtCuspTranslationOrbit_mk_inv_eq_qExpansionOrderAtCusp, Subgroup.conj_mapGL_neg,
    ← TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL (-γ), ← _root_.ModularForm.SL_slash,
    SL_slash_neg, _root_.ModularForm.SL_slash,
    TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL γ,
    ← _root_.ModularForm.coe_translate f (mapGL ℝ γ)]
  exact TauCeti.qExpansionOrderAtCusp_smul
    (ModularFormClass.analyticAt_cuspFunction_zero fγ Γγ.strictWidthInfty_pos
      Γγ.strictWidthInfty_mem_strictPeriods)
    (zpow_ne_zero k (neg_ne_zero.mpr one_ne_zero))

/-- At a regular cusp `Γ.cuspOrbitOfSL2Z γ`, the translation orbit of `γ⁻¹` has the same order as
the projective cusp orbit. -/
theorem intCast_orderAtCuspTranslationOrbit_mk_inv_eq_orderAtCuspOrbit_of_isRegularCusp
    (f : F) {γ : SL(2, ℤ)} (hreg : Γ.IsRegularCusp (Γ.cuspOrbitOfSL2Z γ)) :
    (orderAtCuspTranslationOrbit f
      (⟦(QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹) :
        𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)⟧ :
          CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) : ℚ) =
      orderAtCuspOrbit f (Γ.cuspOrbitOfSL2Z γ) := by
  have hreg' := (Γ.isRegularCusp_cuspOrbitOfSL2Z γ).mp hreg
  rw [orderAtCuspTranslationOrbit_mk_inv_eq_qExpansionOrderAtCusp,
    Subgroup.strictWidthInfty_of_isRegularAtInfty _ hreg',
    orderAtCuspOrbit_cuspOrbitOfSL2Z_eq_qExpansionOrderAtCusp_of_isRegularCusp f hreg]

/-- At an irregular cusp `Γ.cuspOrbitOfSL2Z γ`, the translation orbit of `γ⁻¹` has strict width
`2 · widthInfty` and therefore twice the projective cusp order. -/
theorem intCast_orderAtCuspTranslationOrbit_mk_inv_eq_two_mul_orderAtCuspOrbit_of_not_isRegularCusp
    (f : F) {γ : SL(2, ℤ)} (hirr : ¬Γ.IsRegularCusp (Γ.cuspOrbitOfSL2Z γ)) :
    (orderAtCuspTranslationOrbit f
      (⟦(QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹) :
        𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)⟧ :
          CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) : ℚ) =
      2 * orderAtCuspOrbit f (Γ.cuspOrbitOfSL2Z γ) := by
  have hirr' : ¬(ConjAct.toConjAct (mapGL ℝ γ)⁻¹ •
      (Γ : Subgroup (GL (Fin 2) ℝ))).IsRegularAtInfty :=
    mt (Γ.isRegularCusp_cuspOrbitOfSL2Z γ).mpr hirr
  rw [orderAtCuspTranslationOrbit_mk_inv_eq_qExpansionOrderAtCusp,
    Subgroup.strictWidthInfty_of_not_isRegularAtInfty _ hirr',
    orderAtCuspOrbit_cuspOrbitOfSL2Z, TauCeti.orderAtCusp_def]
  ring

/-- **Local cusp-fibre comparison**: the orders on the cusp translation orbits over a single
projective cusp orbit `C` sum to `[±Γ : Γ] · orderAtCuspOrbit f C` across all cases of `-I ∈ Γ`
and cusp regularity. -/
theorem sum_orderAtCuspTranslationOrbit_filter_eq_relIndex_withCenter_mul
    [DecidableEq (Γ.map sl2zToPSL2R).CuspOrbit] (f : F) (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    (∑ c ∈ Finset.univ.filter (fun c ↦ Γ.cuspOrbitOfTranslationOrbit c = C),
        (orderAtCuspTranslationOrbit f c : ℚ)) =
      (Γ.relIndex Γ.withCenter : ℚ) * orderAtCuspOrbit f C := by
  classical
  obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
  set c₀ : CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ)) :=
    ⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹)⟧
  set c₁ : CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ)) :=
    ⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict (-γ⁻¹))⟧
  have hfib : Finset.univ.filter
      (fun c ↦ Γ.cuspOrbitOfTranslationOrbit c = Γ.cuspOrbitOfSL2Z γ) = {c₀, c₁} := by
    ext c
    simp [c₀, c₁, cuspOrbitOfTranslationOrbit_eq_cuspOrbitOfSL2Z_iff]
  rw [hfib]
  by_cases hneg : (-1 : SL(2, ℤ)) ∈ Γ
  · have hc : c₀ = c₁ := (cuspTranslationOrbit_mk_inv_eq_mk_neg_inv_iff γ).mpr (Or.inl hneg)
    have hreg : Γ.IsRegularCusp (Γ.cuspOrbitOfSL2Z γ) := Γ.isRegularCusp_of_neg_one_mem hneg _
    rw [hc, Finset.pair_eq_singleton, Finset.sum_singleton, ← hc,
      intCast_orderAtCuspTranslationOrbit_mk_inv_eq_orderAtCuspOrbit_of_isRegularCusp f hreg,
      Γ.relIndex_withCenter_eq_one_of_neg_one_mem hneg, Nat.cast_one, one_mul]
  · rw [Matrix.SpecialLinearGroup.relIndex_withCenter_eq_two_of_neg_one_notMem hneg,
      Nat.cast_ofNat]
    by_cases hreg : Γ.IsRegularCusp (Γ.cuspOrbitOfSL2Z γ)
    · have hcne : c₀ ≠ c₁ := fun hc ↦
        ((cuspTranslationOrbit_mk_inv_eq_mk_neg_inv_iff γ).mp hc).elim hneg fun hirr ↦ hirr hreg
      rw [Finset.sum_pair hcne, orderAtCuspTranslationOrbit_mk_neg_inv f γ,
        intCast_orderAtCuspTranslationOrbit_mk_inv_eq_orderAtCuspOrbit_of_isRegularCusp f hreg]
      ring
    · have hc : c₀ = c₁ := (cuspTranslationOrbit_mk_inv_eq_mk_neg_inv_iff γ).mpr (Or.inr hreg)
      rw [hc, Finset.pair_eq_singleton, Finset.sum_singleton, ← hc,
        intCast_orderAtCuspTranslationOrbit_mk_inv_eq_two_mul_orderAtCuspOrbit_of_not_isRegularCusp
          f hreg]

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
    ← Finset.sum_fiberwise_of_maps_to (g := Γ.cuspOrbitOfTranslationOrbit)
      (fun _ _ ↦ Finset.mem_univ _)]
  exact Finset.sum_congr rfl fun C _ ↦
    sum_orderAtCuspTranslationOrbit_filter_eq_relIndex_withCenter_mul f C

end CuspOrderComparison

section ProjectiveValenceFormula

variable {Γ : Subgroup SL(2, ℤ)} {k k₁ k₂ : ℤ}
variable {F F₁ F₂ F₃ : Type*} [FunLike F ℍ ℂ] [FunLike F₁ ℍ ℂ] [FunLike F₂ ℍ ℂ] [FunLike F₃ ℍ ℂ]

/-- **The projective valence formula.** For a nonzero modular form `f` of weight `k` on a
finite-index subgroup `Γ ≤ SL(2, ℤ)`, the effective-stabiliser-weighted interior vanishing orders
over `(Γ.map sl2zToPSL2R) \ ℍ` plus the geometric cusp orders over `(Γ.map sl2zToPSL2R).CuspOrbit`
equal `k · [SL(2, ℤ) : ±Γ] / 12`. -/
theorem valence_formula_projective [Γ.FiniteIndex]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    (∑ᶠ P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ,
          weightedOrderOfVanishingOnEffectiveOrbit f P) +
        (∑ᶠ C : (Γ.map sl2zToPSL2R).CuspOrbit, orderAtCuspOrbit f C) =
      (k : ℚ) * Γ.withCenter.index / 12 := by
  have hcard : Nat.card (𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) = Γ.index := by
    rw [← Subgroup.index_eq_card, ← Subgroup.relIndex,
      MonoidHom.range_eq_map (mapGL ℝ), ← Subgroup.relIndex_comap,
      Subgroup.comap_map_eq_self_of_injective mapGL_injective, Subgroup.relIndex_top_right]
  have hval := valence_formula_finiteIndex f hf
  rw [finsum_weightedOrderOfVanishingOnSubgroupOrbit_eq_relIndex_withCenter_mul f,
    sum_orderAtCuspTranslationOrbit_eq_relIndex_withCenter_mul f, hcard,
    ← Subgroup.relIndex_mul_index Γ.le_withCenter, Nat.cast_mul, ← mul_add] at hval
  have hδ : (Γ.relIndex Γ.withCenter : ℚ) ≠ 0 := by
    exact_mod_cast Γ.relIndex_withCenter_ne_zero
  exact mul_left_cancel₀ hδ (hval.trans (by ring))

/-! ### Unified geometric order on `(Γ.map sl2zToPSL2R).CompactifiedQuotient` -/

/-- **Geometric vanishing order on `(Γ.map sl2zToPSL2R).CompactifiedQuotient`**: the integer
analytic order on interior points and the rational (`ℕ`- or `(1/2)ℕ`-valued) cusp order at
cusps. -/
def orderOnCompactifiedQuotient
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]
    (f : F) : (Γ.map sl2zToPSL2R).CompactifiedQuotient → ℚ
  | .ofQuotient P => orderOfVanishingOnEffectiveOrbit f P
  | .ofCusp C => orderAtCuspOrbit f C

/-- On an interior orbit `P`, `orderOnCompactifiedQuotient` agrees with
`orderOfVanishingOnEffectiveOrbit`. -/
@[simp]
theorem orderOnCompactifiedQuotient_ofQuotient
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    orderOnCompactifiedQuotient f (.ofQuotient P) = orderOfVanishingOnEffectiveOrbit f P :=
  (rfl)

/-- At a cusp `C`, `orderOnCompactifiedQuotient` is `orderAtCuspOrbit`. -/
@[simp]
theorem orderOnCompactifiedQuotient_ofCusp
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    orderOnCompactifiedQuotient f (.ofCusp C) = orderAtCuspOrbit f C :=
  (rfl)

/-- The zero form has geometric vanishing order `0` everywhere on the compactified quotient. -/
@[simp]
theorem orderOnCompactifiedQuotient_zero
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] [Zero F] [IsZeroApply F]
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    orderOnCompactifiedQuotient (0 : F) x = 0 := by
  cases x <;> simp

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

/-- **Weighted geometric order `ord_x f / e_x` on the compactified quotient**, where
`e_x = x.effectiveStabilizerOrder` is the effective stabiliser order (`1` at cusps). -/
def weightedOrderOnCompactifiedQuotient
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) : ℚ :=
  orderOnCompactifiedQuotient f x / x.effectiveStabilizerOrder

/-- Unfolding `weightedOrderOnCompactifiedQuotient` across module boundaries. -/
theorem weightedOrderOnCompactifiedQuotient_def
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    weightedOrderOnCompactifiedQuotient f x =
      orderOnCompactifiedQuotient f x / x.effectiveStabilizerOrder :=
  (rfl)

/-- On an interior orbit `P`, `weightedOrderOnCompactifiedQuotient` agrees with
`weightedOrderOfVanishingOnEffectiveOrbit`. -/
@[simp]
theorem weightedOrderOnCompactifiedQuotient_ofQuotient
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    weightedOrderOnCompactifiedQuotient f (.ofQuotient P) =
      weightedOrderOfVanishingOnEffectiveOrbit f P := by
  rw [weightedOrderOnCompactifiedQuotient_def, orderOnCompactifiedQuotient_ofQuotient,
    Subgroup.CompactifiedQuotient.effectiveStabilizerOrder_ofQuotient,
    weightedOrderOfVanishingOnEffectiveOrbit_def]

/-- At a cusp `C`, `weightedOrderOnCompactifiedQuotient` is `orderAtCuspOrbit` since `e_C = 1`. -/
@[simp]
theorem weightedOrderOnCompactifiedQuotient_ofCusp
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    weightedOrderOnCompactifiedQuotient f (.ofCusp C) = orderAtCuspOrbit f C := by
  simp [weightedOrderOnCompactifiedQuotient_def]

/-- Multiplying `weightedOrderOnCompactifiedQuotient f x` by `x.effectiveStabilizerOrder` recovers
`orderOnCompactifiedQuotient f x`. -/
theorem effectiveStabilizerOrder_mul_weightedOrderOnCompactifiedQuotient
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    (x.effectiveStabilizerOrder : ℚ) * weightedOrderOnCompactifiedQuotient f x =
      orderOnCompactifiedQuotient f x := by
  rw [weightedOrderOnCompactifiedQuotient_def]
  exact mul_div_cancel₀ _ (by exact_mod_cast x.effectiveStabilizerOrder_ne_zero)

/-- The zero form has weighted geometric order `0` everywhere on the compactified quotient. -/
@[simp]
theorem weightedOrderOnCompactifiedQuotient_zero
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] [Zero F] [IsZeroApply F]
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    weightedOrderOnCompactifiedQuotient (0 : F) x = 0 := by
  simp [weightedOrderOnCompactifiedQuotient_def]

/-- The weighted geometric vanishing order of a modular form is nonnegative at every point of the
compactified quotient. -/
theorem weightedOrderOnCompactifiedQuotient_nonneg
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    0 ≤ weightedOrderOnCompactifiedQuotient f x :=
  div_nonneg (orderOnCompactifiedQuotient_nonneg f x) (by positivity)

/-- The weighted geometric order vanishes at `x` if and only if the plain geometric order vanishes
at `x`. -/
theorem weightedOrderOnCompactifiedQuotient_eq_zero_iff
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    weightedOrderOnCompactifiedQuotient f x = 0 ↔ orderOnCompactifiedQuotient f x = 0 := by
  have he : (x.effectiveStabilizerOrder : ℚ) ≠ 0 := by
    exact_mod_cast x.effectiveStabilizerOrder_ne_zero
  rw [weightedOrderOnCompactifiedQuotient_def, div_eq_zero_iff, or_iff_left he]

/-- The weighted geometric order is positive at `x` if and only if the plain geometric order is
positive at `x`. -/
theorem weightedOrderOnCompactifiedQuotient_pos_iff
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    0 < weightedOrderOnCompactifiedQuotient f x ↔ 0 < orderOnCompactifiedQuotient f x := by
  have he : (0 : ℚ) < (x.effectiveStabilizerOrder : ℚ) := by
    exact_mod_cast x.effectiveStabilizerOrder_pos
  rw [weightedOrderOnCompactifiedQuotient_def, div_pos_iff_of_pos_right he]

/-- Scaling a modular form by a nonzero complex constant leaves its geometric order on the
compactified quotient unchanged. -/
@[simp]
theorem orderOnCompactifiedQuotient_smul [Γ.FiniteIndex]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] [SMul ℂ F] [IsSMulApply ℂ F]
    {c : ℂ} (hc : c ≠ 0) (f : F) (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    orderOnCompactifiedQuotient (c • f) x = orderOnCompactifiedQuotient f x := by
  cases x <;> simp [hc]

/-- Scaling a modular form by a nonzero complex constant leaves its weighted geometric order on the
compactified quotient unchanged. -/
@[simp]
theorem weightedOrderOnCompactifiedQuotient_smul [Γ.FiniteIndex]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] [SMul ℂ F] [IsSMulApply ℂ F]
    {c : ℂ} (hc : c ≠ 0) (f : F) (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    weightedOrderOnCompactifiedQuotient (c • f) x = weightedOrderOnCompactifiedQuotient f x := by
  simp [weightedOrderOnCompactifiedQuotient_def, hc]

/-- Zero-detection for `orderOnCompactifiedQuotient` of a nonzero modular form across interior
points and cusps. -/
theorem orderOnCompactifiedQuotient_eq_zero_iff [Γ.FiniteIndex]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    orderOnCompactifiedQuotient f x = 0 ↔
      match x with
      | .ofQuotient P =>
        ∀ z : ℍ, (Quotient.mk'' z : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) = P → f z ≠ 0
      | .ofCusp C =>
        ∀ γ : SL(2, ℤ), Γ.cuspOrbitOfSL2Z γ = C → ¬IsZeroAtImInfty (⇑f ∣[k] mapGL ℝ γ) := by
  cases x with
  | ofQuotient P =>
    rw [orderOnCompactifiedQuotient_ofQuotient, Int.cast_eq_zero]
    exact orderOfVanishingOnEffectiveOrbit_eq_zero_iff hf P
  | ofCusp C =>
    exact orderAtCuspOrbit_eq_zero_iff hf C

/-- Positivity characterization for `orderOnCompactifiedQuotient` of a nonzero modular form across
interior points and cusps. -/
theorem orderOnCompactifiedQuotient_pos_iff [Γ.FiniteIndex]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    0 < orderOnCompactifiedQuotient f x ↔
      match x with
      | .ofQuotient P =>
        ∃ z : ℍ, (Quotient.mk'' z : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) = P ∧ f z = 0
      | .ofCusp C =>
        ∃ γ : SL(2, ℤ), Γ.cuspOrbitOfSL2Z γ = C ∧ IsZeroAtImInfty (⇑f ∣[k] mapGL ℝ γ) := by
  cases x with
  | ofQuotient P =>
    rw [orderOnCompactifiedQuotient_ofQuotient, Int.cast_pos]
    exact orderOfVanishingOnEffectiveOrbit_pos_iff hf P
  | ofCusp C =>
    exact orderAtCuspOrbit_pos_iff hf C

/-- **Additivity on products (`ModularFormClass` form)** on the compactified quotient. -/
theorem orderOnCompactifiedQuotient_eq_add_of_coe_eq_mul [Γ.FiniteIndex]
    [ModularFormClass F₁ (Γ : Subgroup (GL (Fin 2) ℝ)) k₁]
    [ModularFormClass F₂ (Γ : Subgroup (GL (Fin 2) ℝ)) k₂]
    [ModularFormClass F₃ (Γ : Subgroup (GL (Fin 2) ℝ)) (k₁ + k₂)]
    (f : F₁) (g : F₂) (fg : F₃) (hfg : ⇑fg = ⇑f * ⇑g)
    (hf : (⇑f : ℍ → ℂ) ≠ 0) (hg : (⇑g : ℍ → ℂ) ≠ 0)
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    orderOnCompactifiedQuotient fg x =
      orderOnCompactifiedQuotient f x + orderOnCompactifiedQuotient g x := by
  cases x with
  | ofQuotient P =>
    simp [orderOfVanishingOnEffectiveOrbit_eq_add_of_coe_eq_mul f g fg hfg hf hg P]
  | ofCusp C =>
    exact orderAtCuspOrbit_eq_add_of_coe_eq_mul f g fg hfg hf hg C

/-- **Power scaling (`ModularFormClass` form)** on the compactified quotient. -/
theorem orderOnCompactifiedQuotient_eq_mul_of_coe_eq_pow [Γ.FiniteIndex] {n : ℕ}
    [ModularFormClass F₁ (Γ : Subgroup (GL (Fin 2) ℝ)) k]
    [ModularFormClass F₂ (Γ : Subgroup (GL (Fin 2) ℝ)) (n * k)]
    (f : F₁) (fn : F₂) (hfn : ⇑fn = ⇑f ^ n)
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    orderOnCompactifiedQuotient fn x = n * orderOnCompactifiedQuotient f x := by
  cases x with
  | ofQuotient P =>
    simp [orderOfVanishingOnEffectiveOrbit_eq_mul_of_coe_eq_pow f n fn hfn P]
  | ofCusp C =>
    exact orderAtCuspOrbit_eq_mul_of_coe_eq_pow f fn hfn C

/-- **Finite-product additivity (`ModularFormClass` form)** on the compactified quotient. -/
theorem orderOnCompactifiedQuotient_eq_sum_of_coe_eq_prod [Γ.FiniteIndex] {ι : Type*}
    {s : Finset ι} {kᵢ : ι → ℤ} {G : ι → Type*} [∀ i, FunLike (G i) ℍ ℂ]
    [∀ i, ModularFormClass (G i) (Γ : Subgroup (GL (Fin 2) ℝ)) (kᵢ i)]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (hk : k = ∑ i ∈ s, kᵢ i)
    (g : (i : ι) → G i) (fp : F) (hfp : ⇑fp = ∏ i ∈ s, ⇑(g i))
    (hg : ∀ i ∈ s, (⇑(g i) : ℍ → ℂ) ≠ 0)
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    orderOnCompactifiedQuotient fp x = ∑ i ∈ s, orderOnCompactifiedQuotient (g i) x := by
  cases x with
  | ofQuotient P =>
    simp [orderOfVanishingOnEffectiveOrbit_eq_sum_of_coe_eq_prod g fp hfp hg P]
  | ofCusp C =>
    exact orderAtCuspOrbit_eq_sum_of_coe_eq_prod hk g fp hfp hg C

/-- **Additivity on products**: for nonzero modular forms `f` and `g` on `Γ`, the geometric order of
`f.mul g` on `(Γ.map sl2zToPSL2R).CompactifiedQuotient` is the sum of their geometric orders. -/
theorem _root_.ModularForm.orderOnCompactifiedQuotient_mul [Γ.FiniteIndex]
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₁)
    (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₂)
    (hf : f ≠ 0) (hg : g ≠ 0) (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    orderOnCompactifiedQuotient (f.mul g) x =
      orderOnCompactifiedQuotient f x + orderOnCompactifiedQuotient g x :=
  orderOnCompactifiedQuotient_eq_add_of_coe_eq_mul f g (f.mul g) (_root_.ModularForm.coe_mul f g)
    (fun h ↦ hf (DFunLike.ext' h)) (fun h ↦ hg (DFunLike.ext' h)) x

/-- Geometric orders on the compactified quotient scale under `ModularForm.pow`. -/
theorem _root_.ModularForm.orderOnCompactifiedQuotient_pow [Γ.FiniteIndex]
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (n : ℕ)
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    orderOnCompactifiedQuotient (f.pow n) x = n * orderOnCompactifiedQuotient f x :=
  orderOnCompactifiedQuotient_eq_mul_of_coe_eq_pow f (f.pow n) (_root_.ModularForm.coe_pow f n) x

/-- Geometric orders on the compactified quotient sum over `ModularForm.prod` of nonzero forms. -/
theorem _root_.ModularForm.orderOnCompactifiedQuotient_prod [Γ.FiniteIndex] {ι : Type*}
    {s : Finset ι} {kᵢ : ι → ℤ} (m : ℤ) (hm : m = ∑ i ∈ s, kᵢ i)
    (g : (i : ι) → ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (kᵢ i))
    (hg : ∀ i ∈ s, g i ≠ 0) (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    orderOnCompactifiedQuotient (_root_.ModularForm.prod m hm g) x =
      ∑ i ∈ s, orderOnCompactifiedQuotient (g i) x :=
  orderOnCompactifiedQuotient_eq_sum_of_coe_eq_prod hm g (_root_.ModularForm.prod m hm g) (by simp)
    (fun i hi h ↦ hg i hi (DFunLike.ext' h)) x

/-- Additivity of `orderOnCompactifiedQuotient` on `CuspForm.mulModularForm` for nonzero forms. -/
theorem _root_.CuspForm.orderOnCompactifiedQuotient_mulModularForm [Γ.FiniteIndex]
    (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₁)
    (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₂)
    (hf : f ≠ 0) (hg : g ≠ 0) (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    orderOnCompactifiedQuotient (f.mulModularForm g) x =
      orderOnCompactifiedQuotient f x + orderOnCompactifiedQuotient g x :=
  orderOnCompactifiedQuotient_eq_add_of_coe_eq_mul f g (f.mulModularForm g)
    (_root_.CuspForm.coe_mulModularForm f g)
    (fun h ↦ hf (DFunLike.ext' h)) (fun h ↦ hg (DFunLike.ext' h)) x

/-- Additivity of the weighted geometric order on products (`ModularFormClass` form). -/
theorem weightedOrderOnCompactifiedQuotient_eq_add_of_coe_eq_mul [Γ.FiniteIndex]
    [ModularFormClass F₁ (Γ : Subgroup (GL (Fin 2) ℝ)) k₁]
    [ModularFormClass F₂ (Γ : Subgroup (GL (Fin 2) ℝ)) k₂]
    [ModularFormClass F₃ (Γ : Subgroup (GL (Fin 2) ℝ)) (k₁ + k₂)]
    (f : F₁) (g : F₂) (fg : F₃) (hfg : ⇑fg = ⇑f * ⇑g)
    (hf : (⇑f : ℍ → ℂ) ≠ 0) (hg : (⇑g : ℍ → ℂ) ≠ 0)
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    weightedOrderOnCompactifiedQuotient fg x =
      weightedOrderOnCompactifiedQuotient f x + weightedOrderOnCompactifiedQuotient g x := by
  rw [weightedOrderOnCompactifiedQuotient_def, weightedOrderOnCompactifiedQuotient_def,
    weightedOrderOnCompactifiedQuotient_def,
    orderOnCompactifiedQuotient_eq_add_of_coe_eq_mul f g fg hfg hf hg x, add_div]

/-- Power scaling of the weighted geometric order (`ModularFormClass` form). -/
theorem weightedOrderOnCompactifiedQuotient_eq_mul_of_coe_eq_pow [Γ.FiniteIndex] {n : ℕ}
    [ModularFormClass F₁ (Γ : Subgroup (GL (Fin 2) ℝ)) k]
    [ModularFormClass F₂ (Γ : Subgroup (GL (Fin 2) ℝ)) (n * k)]
    (f : F₁) (fn : F₂) (hfn : ⇑fn = ⇑f ^ n)
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    weightedOrderOnCompactifiedQuotient fn x = n * weightedOrderOnCompactifiedQuotient f x := by
  rw [weightedOrderOnCompactifiedQuotient_def, weightedOrderOnCompactifiedQuotient_def,
    orderOnCompactifiedQuotient_eq_mul_of_coe_eq_pow f fn hfn x, mul_div_assoc]

/-- Finite-product additivity of the weighted geometric order (`ModularFormClass` form). -/
theorem weightedOrderOnCompactifiedQuotient_eq_sum_of_coe_eq_prod [Γ.FiniteIndex] {ι : Type*}
    {s : Finset ι} {kᵢ : ι → ℤ} {G : ι → Type*} [∀ i, FunLike (G i) ℍ ℂ]
    [∀ i, ModularFormClass (G i) (Γ : Subgroup (GL (Fin 2) ℝ)) (kᵢ i)]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (hk : k = ∑ i ∈ s, kᵢ i)
    (g : (i : ι) → G i) (fp : F) (hfp : ⇑fp = ∏ i ∈ s, ⇑(g i))
    (hg : ∀ i ∈ s, (⇑(g i) : ℍ → ℂ) ≠ 0)
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    weightedOrderOnCompactifiedQuotient fp x =
      ∑ i ∈ s, weightedOrderOnCompactifiedQuotient (g i) x := by
  simp only [weightedOrderOnCompactifiedQuotient_def,
    orderOnCompactifiedQuotient_eq_sum_of_coe_eq_prod hk g fp hfp hg x, Finset.sum_div]

/-- Additivity of the weighted geometric order on products of nonzero modular forms. -/
theorem _root_.ModularForm.weightedOrderOnCompactifiedQuotient_mul [Γ.FiniteIndex]
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₁)
    (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₂)
    (hf : f ≠ 0) (hg : g ≠ 0) (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    weightedOrderOnCompactifiedQuotient (f.mul g) x =
      weightedOrderOnCompactifiedQuotient f x + weightedOrderOnCompactifiedQuotient g x :=
  weightedOrderOnCompactifiedQuotient_eq_add_of_coe_eq_mul f g (f.mul g)
    (_root_.ModularForm.coe_mul f g)
    (fun h ↦ hf (DFunLike.ext' h)) (fun h ↦ hg (DFunLike.ext' h)) x

/-- Weighted geometric orders on the compactified quotient scale under `ModularForm.pow`. -/
theorem _root_.ModularForm.weightedOrderOnCompactifiedQuotient_pow [Γ.FiniteIndex]
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (n : ℕ)
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    weightedOrderOnCompactifiedQuotient (f.pow n) x =
      n * weightedOrderOnCompactifiedQuotient f x :=
  weightedOrderOnCompactifiedQuotient_eq_mul_of_coe_eq_pow f (f.pow n)
    (_root_.ModularForm.coe_pow f n) x

/-- Weighted geometric orders sum over `ModularForm.prod` of nonzero forms. -/
theorem _root_.ModularForm.weightedOrderOnCompactifiedQuotient_prod [Γ.FiniteIndex] {ι : Type*}
    {s : Finset ι} {kᵢ : ι → ℤ} (m : ℤ) (hm : m = ∑ i ∈ s, kᵢ i)
    (g : (i : ι) → ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (kᵢ i))
    (hg : ∀ i ∈ s, g i ≠ 0) (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    weightedOrderOnCompactifiedQuotient (_root_.ModularForm.prod m hm g) x =
      ∑ i ∈ s, weightedOrderOnCompactifiedQuotient (g i) x :=
  weightedOrderOnCompactifiedQuotient_eq_sum_of_coe_eq_prod hm g
    (_root_.ModularForm.prod m hm g) (by simp) (fun i hi h ↦ hg i hi (DFunLike.ext' h)) x

/-- Additivity of `weightedOrderOnCompactifiedQuotient` on `CuspForm.mulModularForm`. -/
theorem _root_.CuspForm.weightedOrderOnCompactifiedQuotient_mulModularForm [Γ.FiniteIndex]
    (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₁)
    (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₂)
    (hf : f ≠ 0) (hg : g ≠ 0) (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    weightedOrderOnCompactifiedQuotient (f.mulModularForm g) x =
      weightedOrderOnCompactifiedQuotient f x + weightedOrderOnCompactifiedQuotient g x :=
  weightedOrderOnCompactifiedQuotient_eq_add_of_coe_eq_mul f g (f.mulModularForm g)
    (_root_.CuspForm.coe_mulModularForm f g)
    (fun h ↦ hf (DFunLike.ext' h)) (fun h ↦ hg (DFunLike.ext' h)) x

/-- A modular form on finite-index `Γ` has nonzero geometric order at only finitely many points of
`(Γ.map sl2zToPSL2R).CompactifiedQuotient`. -/
theorem hasFiniteSupport_orderOnCompactifiedQuotient [Γ.FiniteIndex]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) :
    Function.HasFiniteSupport (orderOnCompactifiedQuotient (Γ := Γ) (k := k) f) := by
  let e := Subgroup.CompactifiedQuotient.equivSum (Γ.map sl2zToPSL2R)
  have hg : Function.HasFiniteSupport
      (orderOnCompactifiedQuotient (Γ := Γ) (k := k) f ∘ e.symm) := by
    refine TauCeti.hasFiniteSupport_sum_type ?_ ?_
    · refine (hasFiniteSupport_orderOfVanishingOnEffectiveOrbit f).subset fun P hP ↦ ?_
      simpa [e, Function.comp_def] using hP
    · simpa [e, Function.comp_def] using hasFiniteSupport_orderAtCuspOrbit f
  simpa [e, Function.HasFiniteSupport, Function.support_comp_eq_preimage] using
    hg.preimage e.injective.injOn

/-- Only finitely many points of `(Γ.map sl2zToPSL2R).CompactifiedQuotient` carry nonzero weighted
geometric order. -/
theorem hasFiniteSupport_weightedOrderOnCompactifiedQuotient [Γ.FiniteIndex]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) :
    Function.HasFiniteSupport (weightedOrderOnCompactifiedQuotient (Γ := Γ) (k := k) f) := by
  refine (hasFiniteSupport_orderOnCompactifiedQuotient f).subset fun x hx ↦ ?_
  rwa [Function.mem_support, ne_eq, weightedOrderOnCompactifiedQuotient_eq_zero_iff] at hx

/-- Splitting the divisor sum over `(Γ.map sl2zToPSL2R).CompactifiedQuotient` into its interior and
cusp parts. -/
theorem finsum_weightedOrderOnCompactifiedQuotient_eq_add [Γ.FiniteIndex]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) :
    (∑ᶠ x : (Γ.map sl2zToPSL2R).CompactifiedQuotient, weightedOrderOnCompactifiedQuotient f x) =
      (∑ᶠ P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ,
          weightedOrderOfVanishingOnEffectiveOrbit f P) +
        (∑ᶠ C : (Γ.map sl2zToPSL2R).CuspOrbit, orderAtCuspOrbit f C) := by
  let e := Subgroup.CompactifiedQuotient.equivSum (Γ.map sl2zToPSL2R)
  rw [← finsum_comp_equiv e.symm,
    TauCeti.finsum_sum_type (fun s ↦ weightedOrderOnCompactifiedQuotient f (e.symm s))
      (by simpa [e, Function.HasFiniteSupport, Function.comp_def] using
        hasFiniteSupport_weightedOrderOfVanishingOnEffectiveOrbit f)
      (by simpa [e, Function.HasFiniteSupport, Function.comp_def] using
        hasFiniteSupport_orderAtCuspOrbit f)]
  simp [e]

/-- **Unified projective valence formula on the compactified quotient**:
`∑_{x ∈ X(Γ)} ord_x(f) / e_x = k · [SL(2, ℤ) : ±Γ] / 12`, with `e_x = 1` at cusps. -/
theorem valence_formula_compactifiedQuotient [Γ.FiniteIndex]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    (∑ᶠ x : (Γ.map sl2zToPSL2R).CompactifiedQuotient, weightedOrderOnCompactifiedQuotient f x) =
      (k : ℚ) * Γ.withCenter.index / 12 := by
  rw [finsum_weightedOrderOnCompactifiedQuotient_eq_add, valence_formula_projective f hf]

/-! ### Unified, single-orbit, and single-cusp vanishing bounds -/

/-- At every point `x` of the compactified quotient, the weighted geometric order of a nonzero
modular form is bounded by the total projective degree `k · [SL(2, ℤ) : ±Γ] / 12`. -/
theorem weightedOrderOnCompactifiedQuotient_le_weight_mul_index_withCenter_div_twelve
    [Γ.FiniteIndex] [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]
    (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0) (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    weightedOrderOnCompactifiedQuotient f x ≤ (k : ℚ) * Γ.withCenter.index / 12 :=
  (single_le_finsum x (hasFiniteSupport_weightedOrderOnCompactifiedQuotient f)
    (weightedOrderOnCompactifiedQuotient_nonneg f)).trans_eq
    (valence_formula_compactifiedQuotient f hf)

/-- **Unified projective vanishing bound on `(Γ.map sl2zToPSL2R).CompactifiedQuotient`**: for a
nonzero modular form `f` of weight `k` on `Γ`, `12 · ord_x f ≤ k · [SL(2, ℤ) : ±Γ] · e_x` at every
point `x` (interior or cusp). -/
theorem
  twelve_mul_orderOnCompactifiedQuotient_le_weight_mul_index_withCenter_mul_effectiveStabilizerOrder
    [Γ.FiniteIndex] [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]
    (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0) (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    12 * orderOnCompactifiedQuotient f x ≤
      (k : ℚ) * Γ.withCenter.index * x.effectiveStabilizerOrder := by
  have he : (0 : ℚ) < (x.effectiveStabilizerOrder : ℚ) := by
    exact_mod_cast x.effectiveStabilizerOrder_pos
  have hle := weightedOrderOnCompactifiedQuotient_le_weight_mul_index_withCenter_div_twelve f hf x
  rw [weightedOrderOnCompactifiedQuotient_def, div_le_iff₀ he] at hle
  linarith

/-- **Projective interior vanishing bound**: for a nonzero modular form `f` of weight `k` on `Γ`,
`12 · ord_P f ≤ k · [SL(2, ℤ) : ±Γ] · e_P` at every effective orbit `P`. -/
theorem
    twelve_mul_orderOfVanishingOnEffectiveOrbit_le_weight_mul_index_withCenter_mul_cardStabilizer
    [Γ.FiniteIndex] [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]
    (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0) (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    12 * orderOfVanishingOnEffectiveOrbit f P ≤
      k * Γ.withCenter.index * cardStabilizerOnOrbit P := by
  have hle :=
    weightedOrderOnCompactifiedQuotient_le_weight_mul_index_withCenter_div_twelve f hf
      (.ofQuotient P)
  rw [weightedOrderOnCompactifiedQuotient_ofQuotient] at hle
  have hmul := mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg (α := ℚ) (cardStabilizerOnOrbit P))
  rw [cardStabilizerOnOrbit_mul_weightedOrderOfVanishingOnEffectiveOrbit] at hmul
  have hq : (12 : ℚ) * orderOfVanishingOnEffectiveOrbit f P ≤
      (k : ℚ) * Γ.withCenter.index * cardStabilizerOnOrbit P := by linarith
  exact_mod_cast hq

/-- A projective degree `k · [SL(2, ℤ) : ±Γ] · e_P < 12` forces vanishing order zero at the
effective orbit `P`. -/
theorem
orderOfVanishingOnEffectiveOrbit_eq_zero_of_weight_mul_index_withCenter_mul_cardStabilizer_lt_twelve
    [Γ.FiniteIndex] [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    {P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ}
    (hk : k * Γ.withCenter.index * cardStabilizerOnOrbit P < 12) :
    orderOfVanishingOnEffectiveOrbit f P = 0 := by
  rcases eq_or_ne (⇑f : ℍ → ℂ) 0 with hf | hf
  · induction P using Quotient.inductionOn' with
    | h z => simp [hf]
  · have hbound :=
      twelve_mul_orderOfVanishingOnEffectiveOrbit_le_weight_mul_index_withCenter_mul_cardStabilizer
        f hf P
    have := orderOfVanishingOnEffectiveOrbit_nonneg f P
    omega

/-- **Projective cusp vanishing bound**: for a nonzero modular form `f` of weight `k` on `Γ`,
`12 · ord_C f ≤ k · [SL(2, ℤ) : ±Γ]` at every cusp orbit `C`. -/
theorem twelve_mul_orderAtCuspOrbit_le_weight_mul_index_withCenter
    [Γ.FiniteIndex] [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]
    (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0) (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    12 * orderAtCuspOrbit f C ≤ (k : ℚ) * Γ.withCenter.index := by
  have hle :=
    weightedOrderOnCompactifiedQuotient_le_weight_mul_index_withCenter_div_twelve f hf (.ofCusp C)
  rw [weightedOrderOnCompactifiedQuotient_ofCusp] at hle
  linarith

/-- Since `orderAtCuspOrbit` lies in `(1/2)ℕ`, `k · [SL(2, ℤ) : ±Γ] < 6` forces vanishing order zero
at every cusp orbit `C` (regular or irregular). -/
theorem orderAtCuspOrbit_eq_zero_of_weight_mul_index_withCenter_lt_six
    [Γ.FiniteIndex] [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    {C : (Γ.map sl2zToPSL2R).CuspOrbit} (hk : k * Γ.withCenter.index < 6) :
    orderAtCuspOrbit f C = 0 := by
  rcases eq_or_ne (⇑f : ℍ → ℂ) 0 with hf | hf
  · obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
    simp [hf, SlashAction.zero_slash, TauCeti.orderAtCusp_def]
  · have hbound := twelve_mul_orderAtCuspOrbit_le_weight_mul_index_withCenter f hf C
    obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
    rw [orderAtCuspOrbit_cuspOrbitOfSL2Z, TauCeti.orderAtCusp_def] at hbound ⊢
    set n : ℤ := qExpansionOrderAtCusp
      (2 * (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).widthInfty)
      (⇑f ∣[k] mapGL ℝ γ)
    have hn0 : 0 ≤ n := qExpansionOrderAtCusp_nonneg _ _
    have h6 : 6 * n ≤ k * Γ.withCenter.index := by
      have h6q : (6 : ℚ) * n ≤ (k : ℚ) * Γ.withCenter.index := by linarith
      exact_mod_cast h6q
    have hn_eq : n = 0 := by omega
    simp [hn_eq]

/-- At a regular cusp orbit `C`, `orderAtCuspOrbit f C` is an integer, so `k · [SL(2, ℤ) : ±Γ] < 12`
already forces `orderAtCuspOrbit f C = 0`. -/
theorem orderAtCuspOrbit_eq_zero_of_isRegularCusp_of_weight_mul_index_withCenter_lt_twelve
    [Γ.FiniteIndex] [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    {C : (Γ.map sl2zToPSL2R).CuspOrbit} (hreg : Γ.IsRegularCusp C)
    (hk : k * Γ.withCenter.index < 12) :
    orderAtCuspOrbit f C = 0 := by
  rcases eq_or_ne (⇑f : ℍ → ℂ) 0 with hf | hf
  · obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
    simp [hf, SlashAction.zero_slash, TauCeti.orderAtCusp_def]
  · obtain ⟨m, hm⟩ := exists_orderAtCuspOrbit_eq_natCast_of_isRegularCusp f hreg
    have hbound := twelve_mul_orderAtCuspOrbit_le_weight_mul_index_withCenter f hf C
    rw [hm] at hbound ⊢
    have h12 : (12 : ℤ) * m ≤ k * Γ.withCenter.index := by exact_mod_cast hbound
    have hm0 : m = 0 := by omega
    simp [hm0]

/-- In even weight, `orderAtCuspOrbit f C` is an integer at every cusp, so
`k · [SL(2, ℤ) : ±Γ] < 12` forces `orderAtCuspOrbit f C = 0`. -/
theorem orderAtCuspOrbit_eq_zero_of_even_of_weight_mul_index_withCenter_lt_twelve
    [Γ.FiniteIndex] [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (heven : Even k)
    {C : (Γ.map sl2zToPSL2R).CuspOrbit} (hk : k * Γ.withCenter.index < 12) :
    orderAtCuspOrbit f C = 0 := by
  rcases eq_or_ne (⇑f : ℍ → ℂ) 0 with hf | hf
  · obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
    simp [hf, SlashAction.zero_slash, TauCeti.orderAtCusp_def]
  · obtain ⟨m, hm⟩ := exists_orderAtCuspOrbit_eq_natCast_of_even f heven C
    have hbound := twelve_mul_orderAtCuspOrbit_le_weight_mul_index_withCenter f hf C
    rw [hm] at hbound ⊢
    have h12 : (12 : ℤ) * m ≤ k * Γ.withCenter.index := by exact_mod_cast hbound
    have hm0 : m = 0 := by omega
    simp [hm0]

end ProjectiveValenceFormula

end TauCeti.ModularForm

end
