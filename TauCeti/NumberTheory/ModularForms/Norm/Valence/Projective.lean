/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Cusps.TranslationOrbit.Projective
public import TauCeti.NumberTheory.ModularForms.Norm.Valence.Full
public import TauCeti.NumberTheory.ModularForms.Order.CompactifiedQuotient
import TauCeti.NumberTheory.ModularForms.ArithmeticSubgroups

/-!
# The projective valence formula on the compactified quotient

For finite-index `Γ ≤ SL(2, ℤ)`, dividing every interior term (`Order/EffectiveOrbits.lean`), every
cusp fibre over `Γ.cuspOrbitOfTranslationOrbit` (`Cusps/TranslationOrbit/Projective.lean`), and the
index `[SL(2, ℤ) : Γ] = [±Γ : Γ] · [SL(2, ℤ) : ±Γ]` in `valence_formula_finiteIndex` by `[±Γ : Γ]`
yields `valence_formula_projective`, its unified form `valence_formula_compactifiedQuotient` over
`Order/CompactifiedQuotient.lean`'s `weightedOrderOnCompactifiedQuotient`, and projective vanishing
bounds.

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

/-- At a regular cusp, the translation orbit of `γ⁻¹` has the same order as the cusp orbit. -/
theorem intCast_orderAtCuspTranslationOrbit_mk_inv_eq_orderAtCuspOrbit_of_isRegularCusp
    (f : F) {γ : SL(2, ℤ)} (hreg : Γ.IsRegularCusp (Γ.cuspOrbitOfSL2Z γ)) :
    (orderAtCuspTranslationOrbit f
      (⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹)⟧ :
        CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) : ℚ) =
      orderAtCuspOrbit f (Γ.cuspOrbitOfSL2Z γ) := by
  rw [orderAtCuspTranslationOrbit_mk_inv_eq_qExpansionOrderAtCusp,
    Subgroup.strictWidthInfty_of_isRegularAtInfty _ ((Γ.isRegularCusp_cuspOrbitOfSL2Z γ).mp hreg),
    orderAtCuspOrbit_cuspOrbitOfSL2Z_eq_qExpansionOrderAtCusp_of_isRegularCusp f hreg]

/-- At an irregular cusp, the translation orbit of `γ⁻¹` has twice the projective cusp order. -/
theorem intCast_orderAtCuspTranslationOrbit_mk_inv_eq_two_mul_orderAtCuspOrbit_of_not_isRegularCusp
    (f : F) {γ : SL(2, ℤ)} (hirr : ¬Γ.IsRegularCusp (Γ.cuspOrbitOfSL2Z γ)) :
    (orderAtCuspTranslationOrbit f
      (⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹)⟧ :
        CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) : ℚ) =
      2 * orderAtCuspOrbit f (Γ.cuspOrbitOfSL2Z γ) := by
  rw [orderAtCuspTranslationOrbit_mk_inv_eq_qExpansionOrderAtCusp,
    Subgroup.strictWidthInfty_of_not_isRegularAtInfty _
      (mt (Γ.isRegularCusp_cuspOrbitOfSL2Z γ).mpr hirr),
    orderAtCuspOrbit_cuspOrbitOfSL2Z, TauCeti.orderAtCusp_def]
  ring

/-- **Local cusp-fibre comparison**: orders on the fibre over `C` sum to `[±Γ : Γ] · ord_C f`. -/
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
  have hfilter : Finset.univ.filter
      (fun c ↦ Γ.cuspOrbitOfTranslationOrbit c = Γ.cuspOrbitOfSL2Z γ) = {c₀, c₁} := by
    ext c; simp [c₀, c₁, cuspOrbitOfTranslationOrbit_eq_cuspOrbitOfSL2Z_iff]
  rw [hfilter]
  by_cases hneg : (-1 : SL(2, ℤ)) ∈ Γ
  · have hc : c₀ = c₁ := (cuspTranslationOrbit_mk_inv_eq_mk_neg_inv_iff γ).mpr (Or.inl hneg)
    rw [hc, Finset.pair_eq_singleton, Finset.sum_singleton, ← hc,
      intCast_orderAtCuspTranslationOrbit_mk_inv_eq_orderAtCuspOrbit_of_isRegularCusp f
        (Γ.isRegularCusp_of_neg_one_mem hneg _),
      Subgroup.withCenter_eq_self_iff.mpr (Matrix.SpecialLinearGroup.center_le_iff_neg_one_mem.mpr
        hneg), Subgroup.relIndex_self, Nat.cast_one, one_mul]
  · rw [Matrix.SpecialLinearGroup.relIndex_withCenter_eq_two_of_neg_one_notMem hneg, Nat.cast_ofNat]
    by_cases hreg : Γ.IsRegularCusp (Γ.cuspOrbitOfSL2Z γ)
    · rw [Finset.sum_pair fun hc ↦ ((cuspTranslationOrbit_mk_inv_eq_mk_neg_inv_iff γ).mp hc).elim
        hneg (· hreg), orderAtCuspTranslationOrbit_mk_neg_inv f γ,
        intCast_orderAtCuspTranslationOrbit_mk_inv_eq_orderAtCuspOrbit_of_isRegularCusp f hreg]
      ring
    · have hc : c₀ = c₁ := (cuspTranslationOrbit_mk_inv_eq_mk_neg_inv_iff γ).mpr (Or.inr hreg)
      rw [hc, Finset.pair_eq_singleton, Finset.sum_singleton, ← hc,
        intCast_orderAtCuspTranslationOrbit_mk_inv_eq_two_mul_orderAtCuspOrbit_of_not_isRegularCusp
          f hreg]

/-- **Global cusp-sum comparison**: translation-orbit sum is `[±Γ : Γ]` times cusp-orbit sum. -/
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

/-- **The projective valence formula**: for nonzero modular `f` of weight `k` on finite-index `Γ`,
`∑ᶠ P, ord_P f / e_P + ∑ᶠ C, ord_C f = k · [SL(2, ℤ) : ±Γ] / 12`. -/
theorem valence_formula_projective (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    (∑ᶠ P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ,
          weightedOrderOfVanishingOnEffectiveOrbit f P) +
        (∑ᶠ C : (Γ.map sl2zToPSL2R).CuspOrbit, orderAtCuspOrbit f C) =
      (k : ℚ) * Γ.withCenter.index / 12 := by
  have hval := valence_formula_finiteIndex f hf
  rw [finsum_weightedOrderOfVanishingOnSubgroupOrbit_eq_relIndex_withCenter_mul f,
    sum_orderAtCuspTranslationOrbit_eq_relIndex_withCenter_mul f, Γ.card_quotient_mapGL_eq_index,
    ← Subgroup.relIndex_mul_index Γ.le_withCenter, Nat.cast_mul, ← mul_add] at hval
  have := Subgroup.isFiniteRelIndex_of_finiteIndex (H := Γ) (K := Γ.withCenter)
  exact mul_left_cancel₀ (by exact_mod_cast Subgroup.relIndex_ne_zero (H := Γ) (K := Γ.withCenter))
    (hval.trans (by ring))

end CuspOrderComparison

section Modular

variable {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]
  [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]

section FiniteIndex

variable [Γ.FiniteIndex]

/-- **Unified projective valence formula on the compactified quotient**:
`∑_{x ∈ X(Γ)} ord_x(f) / e_x = k · [SL(2, ℤ) : ±Γ] / 12`, with `e_x = 1` at cusps. -/
theorem valence_formula_compactifiedQuotient (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    (∑ᶠ x : (Γ.map sl2zToPSL2R).CompactifiedQuotient, weightedOrderOnCompactifiedQuotient f x) =
      (k : ℚ) * Γ.withCenter.index / 12 := by
  rw [finsum_weightedOrderOnCompactifiedQuotient_eq_add, valence_formula_projective f hf]

/-! ### Unified, single-orbit, and single-cusp vanishing bounds -/

/-- At every point `x` of the compactified quotient, `ord_x f / e_x ≤ k · [SL(2, ℤ) : ±Γ] / 12`. -/
theorem weightedOrderOnCompactifiedQuotient_le_weight_mul_index_withCenter_div_twelve
    (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0) (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    weightedOrderOnCompactifiedQuotient f x ≤ (k : ℚ) * Γ.withCenter.index / 12 :=
  (single_le_finsum x (hasFiniteSupport_weightedOrderOnCompactifiedQuotient f)
    (weightedOrderOnCompactifiedQuotient_nonneg f)).trans_eq
    (valence_formula_compactifiedQuotient f hf)

/-- **Unified projective vanishing bound**: `12 · ord_x f ≤ k · [SL(2, ℤ) : ±Γ] · e_x`. -/
theorem
  twelve_mul_orderOnCompactifiedQuotient_le_weight_mul_index_withCenter_mul_effectiveStabilizerOrder
    (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0) (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    12 * orderOnCompactifiedQuotient f x ≤
      (k : ℚ) * Γ.withCenter.index * x.effectiveStabilizerOrder := by
  have h := weightedOrderOnCompactifiedQuotient_le_weight_mul_index_withCenter_div_twelve f hf x
  rw [weightedOrderOnCompactifiedQuotient_def] at h
  linarith [(div_le_iff₀ (by exact_mod_cast x.effectiveStabilizerOrder_pos)).mp h]

/-- **Projective interior vanishing bound**: `12 · ord_P f ≤ k · [SL(2, ℤ) : ±Γ] · e_P`. -/
theorem
    twelve_mul_orderOfVanishingOnEffectiveOrbit_le_weight_mul_index_withCenter_mul_cardStabilizer
    (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0) (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    12 * orderOfVanishingOnEffectiveOrbit f P ≤
      k * Γ.withCenter.index * cardStabilizerOnOrbit P :=
  (fun h ↦ by exact_mod_cast (by simpa using h :
    ((12 * orderOfVanishingOnEffectiveOrbit f P : ℤ) : ℚ) ≤
      ((k * Γ.withCenter.index * cardStabilizerOnOrbit P : ℤ) : ℚ))) <|
  twelve_mul_orderOnCompactifiedQuotient_le_weight_mul_index_withCenter_mul_effectiveStabilizerOrder
    f hf (.ofQuotient P)

/-- `k · [SL(2, ℤ) : ±Γ] · e_P < 12` forces vanishing order zero at the effective orbit `P`. -/
theorem
orderOfVanishingOnEffectiveOrbit_eq_zero_of_weight_mul_index_withCenter_mul_cardStabilizer_lt_twelve
    (f : F) {P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ}
    (hk : k * Γ.withCenter.index * cardStabilizerOnOrbit P < 12) :
    orderOfVanishingOnEffectiveOrbit f P = 0 := by
  rcases eq_or_ne (⇑f : ℍ → ℂ) 0 with hf | hf
  · induction P using Quotient.inductionOn' with | h z => simp [hf]
  · have :=
      twelve_mul_orderOfVanishingOnEffectiveOrbit_le_weight_mul_index_withCenter_mul_cardStabilizer
        f hf P
    have := orderOfVanishingOnEffectiveOrbit_nonneg f P; omega

/-- **Projective cusp vanishing bound**: `12 · ord_C f ≤ k · [SL(2, ℤ) : ±Γ]`. -/
theorem twelve_mul_orderAtCuspOrbit_le_weight_mul_index_withCenter
    (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0) (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    12 * orderAtCuspOrbit f C ≤ (k : ℚ) * Γ.withCenter.index := by
  simpa using (
  twelve_mul_orderOnCompactifiedQuotient_le_weight_mul_index_withCenter_mul_effectiveStabilizerOrder
    f hf (.ofCusp C))

/-- Since `orderAtCuspOrbit` lies in `(1/2)ℕ`, `k · [SL(2, ℤ) : ±Γ] < 6` forces cusp order `0`. -/
theorem orderAtCuspOrbit_eq_zero_of_weight_mul_index_withCenter_lt_six (f : F)
    {C : (Γ.map sl2zToPSL2R).CuspOrbit} (hk : k * Γ.withCenter.index < 6) :
    orderAtCuspOrbit f C = 0 := by
  rcases eq_or_ne (⇑f : ℍ → ℂ) 0 with hf | hf
  · obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
    simp [hf, SlashAction.zero_slash, TauCeti.orderAtCusp_def]
  · obtain ⟨m, hm⟩ := exists_orderAtCuspOrbit_eq_natCast_div_two f C
    have hbound := hm ▸ twelve_mul_orderAtCuspOrbit_le_weight_mul_index_withCenter f hf C
    have : (6 : ℤ) * m ≤ k * Γ.withCenter.index := by
      exact_mod_cast (by linarith : (6 : ℚ) * m ≤ (k : ℚ) * Γ.withCenter.index)
    have hm0 : m = 0 := by omega
    simp [hm, hm0]

private lemma orderAtCuspOrbit_eq_zero_of_exists_natCast (f : F)
    {C : (Γ.map sl2zToPSL2R).CuspOrbit} (hm : ∃ m : ℕ, orderAtCuspOrbit f C = m)
    (hk : k * Γ.withCenter.index < 12) : orderAtCuspOrbit f C = 0 := by
  rcases eq_or_ne (⇑f : ℍ → ℂ) 0 with hf | hf
  · obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
    simp [hf, SlashAction.zero_slash, TauCeti.orderAtCusp_def]
  · obtain ⟨m, hm⟩ := hm
    have : (12 : ℤ) * m ≤ k * Γ.withCenter.index := by
      exact_mod_cast hm ▸ twelve_mul_orderAtCuspOrbit_le_weight_mul_index_withCenter f hf C
    have hm0 : m = 0 := by omega
    simp [hm, hm0]

/-- At a regular cusp orbit `C`, `k · [SL(2, ℤ) : ±Γ] < 12` forces `orderAtCuspOrbit f C = 0`. -/
theorem orderAtCuspOrbit_eq_zero_of_isRegularCusp_of_weight_mul_index_withCenter_lt_twelve (f : F)
    {C : (Γ.map sl2zToPSL2R).CuspOrbit} (hreg : Γ.IsRegularCusp C)
    (hk : k * Γ.withCenter.index < 12) : orderAtCuspOrbit f C = 0 :=
  orderAtCuspOrbit_eq_zero_of_exists_natCast f
    (exists_orderAtCuspOrbit_eq_natCast_of_isRegularCusp f hreg) hk

/-- In even weight, `k · [SL(2, ℤ) : ±Γ] < 12` forces `orderAtCuspOrbit f C = 0` at every cusp. -/
theorem orderAtCuspOrbit_eq_zero_of_even_of_weight_mul_index_withCenter_lt_twelve (f : F)
    (heven : Even k) {C : (Γ.map sl2zToPSL2R).CuspOrbit} (hk : k * Γ.withCenter.index < 12) :
    orderAtCuspOrbit f C = 0 :=
  orderAtCuspOrbit_eq_zero_of_exists_natCast f
    (exists_orderAtCuspOrbit_eq_natCast_of_even f heven C) hk

end FiniteIndex

end Modular

end TauCeti.ModularForm

end
