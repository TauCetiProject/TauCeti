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
import TauCeti.GroupTheory.GroupAction.ConjAct

/-!
# The projective valence formula on the compactified quotient

For finite-index `Γ ≤ SL(2, ℤ)`, dividing every interior term (`Order/EffectiveOrbits.lean`), every
cusp fibre over `Γ.cuspOrbitOfTranslationOrbit` (`Cusps/TranslationOrbit.lean`), and the index
`[SL(2, ℤ) : Γ] = [±Γ : Γ] · [SL(2, ℤ) : ±Γ]` in `valence_formula_finiteIndex` by `[±Γ : Γ]` yields
`valence_formula_projective`, its unified form `valence_formula_compactifiedQuotient` over
`(Γ.map sl2zToPSL2R).CompactifiedQuotient`, and projective vanishing bounds.

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
`f ∣[k] γ` at `strictWidthInfty` of `γ⁻¹ Γ γ`. -/
theorem orderAtCuspTranslationOrbit_mk_inv_eq_qExpansionOrderAtCusp (f : F) (γ : SL(2, ℤ)) :
    orderAtCuspTranslationOrbit f
        (⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹)⟧ :
          CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) =
      qExpansionOrderAtCusp
        (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).strictWidthInfty
        (⇑f ∣[k] mapGL ℝ γ) := by
  rw [orderAtCuspTranslationOrbit_mk, ← cuspTranslationOrbitWidth_mk,
    natCast_cuspTranslationOrbitWidth_mk_inv_eq_strictWidthInfty,
    _root_.SlashInvariantForm.quotientFunc_mk, MonoidHom.coe_rangeRestrict,
    map_inv (mapGL ℝ) γ, inv_inv]

/-- Negating `γ⁻¹` preserves `orderAtCuspTranslationOrbit` (up to `(-1) ^ k`). -/
theorem orderAtCuspTranslationOrbit_mk_neg_inv (f : F) (γ : SL(2, ℤ)) :
    orderAtCuspTranslationOrbit f
        (⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict (-γ⁻¹))⟧ :
          CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) =
      orderAtCuspTranslationOrbit f ⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹)⟧ := by
  set Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))
  let fγ : ModularForm Γγ k := _root_.ModularForm.translate f (mapGL ℝ γ)
  have hΓ : ConjAct.toConjAct (mapGL ℝ (-γ))⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ)) = Γγ := by
    rw [mapGL_neg, inv_neg, Subgroup.toConjAct_neg_smul]
  rw [← inv_neg, orderAtCuspTranslationOrbit_mk_inv_eq_qExpansionOrderAtCusp,
    orderAtCuspTranslationOrbit_mk_inv_eq_qExpansionOrderAtCusp, hΓ,
    ← Matrix.SpecialLinearGroup.coe_GL_eq_mapGL (-γ), ← _root_.ModularForm.SL_slash, SL_slash_neg,
    _root_.ModularForm.SL_slash, Matrix.SpecialLinearGroup.coe_GL_eq_mapGL γ,
    ← _root_.ModularForm.coe_translate f (mapGL ℝ γ)]
  exact TauCeti.qExpansionOrderAtCusp_smul (ModularFormClass.analyticAt_cuspFunction_zero fγ
    Γγ.strictWidthInfty_pos Γγ.strictWidthInfty_mem_strictPeriods) (zpow_ne_zero k (by norm_num))

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
      Γ.relIndex_withCenter_eq_one_of_neg_one_mem hneg, Nat.cast_one, one_mul]
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
  have hcard : Nat.card (𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) = Γ.index := by
    rw [← Subgroup.index_eq_card, ← Subgroup.relIndex, MonoidHom.range_eq_map (mapGL ℝ),
      ← Subgroup.relIndex_comap, Subgroup.comap_map_eq_self_of_injective mapGL_injective,
      Subgroup.relIndex_top_right]
  have hval := valence_formula_finiteIndex f hf
  rw [finsum_weightedOrderOfVanishingOnSubgroupOrbit_eq_relIndex_withCenter_mul f,
    sum_orderAtCuspTranslationOrbit_eq_relIndex_withCenter_mul f, hcard,
    ← Subgroup.relIndex_mul_index Γ.le_withCenter, Nat.cast_mul, ← mul_add] at hval
  exact mul_left_cancel₀ (by exact_mod_cast Γ.relIndex_withCenter_ne_zero) (hval.trans (by ring))

end CuspOrderComparison

variable {Γ : Subgroup SL(2, ℤ)} {k k₁ k₂ : ℤ}
variable {F F₁ F₂ F₃ : Type*} [FunLike F ℍ ℂ] [FunLike F₁ ℍ ℂ] [FunLike F₂ ℍ ℂ] [FunLike F₃ ℍ ℂ]

/-! ### Unified geometric order on `(Γ.map sl2zToPSL2R).CompactifiedQuotient` -/

section Slash

variable [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]

/-- **Geometric vanishing order on `(Γ.map sl2zToPSL2R).CompactifiedQuotient`**: the integer
analytic order on interior points and the rational cusp order at cusps. -/
def orderOnCompactifiedQuotient (f : F) : (Γ.map sl2zToPSL2R).CompactifiedQuotient → ℚ
  | .ofQuotient P => orderOfVanishingOnEffectiveOrbit f P
  | .ofCusp C => orderAtCuspOrbit f C

/-- On an interior orbit, `orderOnCompactifiedQuotient` is `orderOfVanishingOnEffectiveOrbit`. -/
@[simp] theorem orderOnCompactifiedQuotient_ofQuotient (f : F)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    orderOnCompactifiedQuotient f (.ofQuotient P) = orderOfVanishingOnEffectiveOrbit f P := (rfl)

/-- At a cusp `C`, `orderOnCompactifiedQuotient` is `orderAtCuspOrbit`. -/
@[simp] theorem orderOnCompactifiedQuotient_ofCusp (f : F) (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    orderOnCompactifiedQuotient f (.ofCusp C) = orderAtCuspOrbit f C := (rfl)

/-- The zero form has geometric vanishing order `0` everywhere on the compactified quotient. -/
@[simp] theorem orderOnCompactifiedQuotient_zero [Zero F] [IsZeroApply F]
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) : orderOnCompactifiedQuotient (0 : F) x = 0 := by
  cases x <;> simp

/-- **Weighted geometric order `ord_x f / e_x`** on `(Γ.map sl2zToPSL2R).CompactifiedQuotient`. -/
def weightedOrderOnCompactifiedQuotient (f : F) (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    ℚ := orderOnCompactifiedQuotient f x / x.effectiveStabilizerOrder

/-- Unfolding `weightedOrderOnCompactifiedQuotient` across module boundaries. -/
theorem weightedOrderOnCompactifiedQuotient_def (f : F)
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    weightedOrderOnCompactifiedQuotient f x =
      orderOnCompactifiedQuotient f x / x.effectiveStabilizerOrder := (rfl)

/-- On an interior orbit `P`, `weightedOrderOnCompactifiedQuotient` is the effective order. -/
@[simp] theorem weightedOrderOnCompactifiedQuotient_ofQuotient (f : F)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    weightedOrderOnCompactifiedQuotient f (.ofQuotient P) =
      weightedOrderOfVanishingOnEffectiveOrbit f P := by
  simp [weightedOrderOnCompactifiedQuotient_def, weightedOrderOfVanishingOnEffectiveOrbit_def]

/-- At a cusp `C`, `weightedOrderOnCompactifiedQuotient` is `orderAtCuspOrbit` since `e_C = 1`. -/
@[simp] theorem weightedOrderOnCompactifiedQuotient_ofCusp (f : F)
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    weightedOrderOnCompactifiedQuotient f (.ofCusp C) = orderAtCuspOrbit f C := by
  simp [weightedOrderOnCompactifiedQuotient_def]

/-- Multiplying `weightedOrderOnCompactifiedQuotient f x` by `e_x` recovers `ord_x f`. -/
theorem effectiveStabilizerOrder_mul_weightedOrderOnCompactifiedQuotient (f : F)
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    (x.effectiveStabilizerOrder : ℚ) * weightedOrderOnCompactifiedQuotient f x =
      orderOnCompactifiedQuotient f x :=
  mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr x.effectiveStabilizerOrder_ne_zero)

/-- The zero form has weighted geometric order `0` everywhere on the compactified quotient. -/
@[simp] theorem weightedOrderOnCompactifiedQuotient_zero [Zero F] [IsZeroApply F]
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    weightedOrderOnCompactifiedQuotient (0 : F) x = 0 := by
  simp [weightedOrderOnCompactifiedQuotient_def]

end Slash

section Modular

variable [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]

/-- The geometric vanishing order of a modular form is nonnegative on the compactified quotient. -/
theorem orderOnCompactifiedQuotient_nonneg (f : F)
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) : 0 ≤ orderOnCompactifiedQuotient f x := by
  cases x <;> simp [orderOfVanishingOnEffectiveOrbit_nonneg, orderAtCuspOrbit_nonneg]

/-- The weighted geometric vanishing order of a modular form is nonnegative everywhere. -/
theorem weightedOrderOnCompactifiedQuotient_nonneg (f : F)
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) : 0 ≤ weightedOrderOnCompactifiedQuotient f x :=
  div_nonneg (orderOnCompactifiedQuotient_nonneg f x) (by positivity)

section FiniteIndex

variable [Γ.FiniteIndex]

/-- Nonzero complex scalar multiples have the same geometric order on the compactified quotient. -/
@[simp] theorem orderOnCompactifiedQuotient_smul [SMul ℂ F] [IsSMulApply ℂ F] {c : ℂ} (hc : c ≠ 0)
    (f : F) (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    orderOnCompactifiedQuotient (c • f) x = orderOnCompactifiedQuotient f x := by
  cases x <;> simp [hc]

/-- Nonzero complex scalar multiples have the same weighted geometric order. -/
@[simp] theorem weightedOrderOnCompactifiedQuotient_smul [SMul ℂ F] [IsSMulApply ℂ F] {c : ℂ}
    (hc : c ≠ 0) (f : F) (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    weightedOrderOnCompactifiedQuotient (c • f) x = weightedOrderOnCompactifiedQuotient f x := by
  simp [weightedOrderOnCompactifiedQuotient_def, hc]

/-- Zero-detection for `orderOnCompactifiedQuotient` of a nonzero modular form. -/
theorem orderOnCompactifiedQuotient_eq_zero_iff {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    orderOnCompactifiedQuotient f x = 0 ↔
      match x with
      | .ofQuotient P =>
        ∀ z : ℍ, (Quotient.mk'' z : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) = P → f z ≠ 0
      | .ofCusp C =>
        ∀ γ : SL(2, ℤ), Γ.cuspOrbitOfSL2Z γ = C → ¬IsZeroAtImInfty (⇑f ∣[k] mapGL ℝ γ) := by
  cases x with
  | ofQuotient P => simpa using orderOfVanishingOnEffectiveOrbit_eq_zero_iff hf P
  | ofCusp C => exact orderAtCuspOrbit_eq_zero_iff hf C

/-- Positivity characterization for `orderOnCompactifiedQuotient` of a nonzero modular form. -/
theorem orderOnCompactifiedQuotient_pos_iff {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    0 < orderOnCompactifiedQuotient f x ↔
      match x with
      | .ofQuotient P =>
        ∃ z : ℍ, (Quotient.mk'' z : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) = P ∧ f z = 0
      | .ofCusp C =>
        ∃ γ : SL(2, ℤ), Γ.cuspOrbitOfSL2Z γ = C ∧ IsZeroAtImInfty (⇑f ∣[k] mapGL ℝ γ) := by
  cases x with
  | ofQuotient P => simpa using orderOfVanishingOnEffectiveOrbit_pos_iff hf P
  | ofCusp C => exact orderAtCuspOrbit_pos_iff hf C

/-- A modular form on finite-index `Γ` has nonzero geometric order at finitely many points. -/
theorem hasFiniteSupport_orderOnCompactifiedQuotient (f : F) :
    Function.HasFiniteSupport (orderOnCompactifiedQuotient (Γ := Γ) (k := k) f) := by
  let e := Subgroup.CompactifiedQuotient.equivSum (Γ.map sl2zToPSL2R)
  have hg : Function.HasFiniteSupport (orderOnCompactifiedQuotient (Γ := Γ) (k := k) f ∘ e.symm) :=
    TauCeti.hasFiniteSupport_sum_type
      ((hasFiniteSupport_orderOfVanishingOnEffectiveOrbit f).subset fun _ h ↦ by simpa [e] using h)
      (by simpa [e, Function.comp_def] using hasFiniteSupport_orderAtCuspOrbit f)
  simpa [e, Function.HasFiniteSupport, Function.support_comp_eq_preimage] using
    hg.preimage e.injective.injOn

/-- Only finitely many points of the compactified quotient carry nonzero weighted order. -/
theorem hasFiniteSupport_weightedOrderOnCompactifiedQuotient (f : F) :
    Function.HasFiniteSupport (weightedOrderOnCompactifiedQuotient (Γ := Γ) (k := k) f) :=
  (hasFiniteSupport_orderOnCompactifiedQuotient f).subset fun _ hx h0 ↦
    hx (by rw [weightedOrderOnCompactifiedQuotient_def, h0, zero_div])

/-- Splitting the divisor sum over `(Γ.map sl2zToPSL2R).CompactifiedQuotient`. -/
theorem finsum_weightedOrderOnCompactifiedQuotient_eq_add (f : F) :
    (∑ᶠ x : (Γ.map sl2zToPSL2R).CompactifiedQuotient, weightedOrderOnCompactifiedQuotient f x) =
      (∑ᶠ P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ,
          weightedOrderOfVanishingOnEffectiveOrbit f P) +
        (∑ᶠ C : (Γ.map sl2zToPSL2R).CuspOrbit, orderAtCuspOrbit f C) := by
  let e := Subgroup.CompactifiedQuotient.equivSum (Γ.map sl2zToPSL2R)
  rw [← finsum_comp_equiv e.symm,
    TauCeti.finsum_sum_type (fun s ↦ weightedOrderOnCompactifiedQuotient f (e.symm s))
      (by simpa [e, Function.comp_def] using
        hasFiniteSupport_weightedOrderOfVanishingOnEffectiveOrbit f)
      (by simpa [e, Function.comp_def] using hasFiniteSupport_orderAtCuspOrbit f)]
  simp [e]

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
  linarith [(div_le_iff₀ (by exact_mod_cast x.effectiveStabilizerOrder_pos)).mp
    (weightedOrderOnCompactifiedQuotient_le_weight_mul_index_withCenter_div_twelve f hf x)]

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
  linarith [weightedOrderOnCompactifiedQuotient_ofCusp f C ▸
    weightedOrderOnCompactifiedQuotient_le_weight_mul_index_withCenter_div_twelve f hf (.ofCusp C)]

/-- Since `orderAtCuspOrbit` lies in `(1/2)ℕ`, `k · [SL(2, ℤ) : ±Γ] < 6` forces cusp order `0`. -/
theorem orderAtCuspOrbit_eq_zero_of_weight_mul_index_withCenter_lt_six (f : F)
    {C : (Γ.map sl2zToPSL2R).CuspOrbit} (hk : k * Γ.withCenter.index < 6) :
    orderAtCuspOrbit f C = 0 := by
  obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
  rcases eq_or_ne (⇑f : ℍ → ℂ) 0 with hf | hf
  · simp [hf, SlashAction.zero_slash, TauCeti.orderAtCusp_def]
  · have hbound :=
      twelve_mul_orderAtCuspOrbit_le_weight_mul_index_withCenter f hf (Γ.cuspOrbitOfSL2Z γ)
    rw [orderAtCuspOrbit_cuspOrbitOfSL2Z, TauCeti.orderAtCusp_def, qExpansionOrderAtCusp_def,
      Int.cast_natCast] at hbound ⊢
    generalize (qExpansion _ _).order.toNat = m at hbound ⊢
    have : (6 : ℤ) * m ≤ k * Γ.withCenter.index := by
      exact_mod_cast (by linarith : (6 : ℚ) * m ≤ (k : ℚ) * Γ.withCenter.index)
    have hm0 : m = 0 := by omega
    simp [hm0]

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

section Mul

variable [Γ.FiniteIndex] [ModularFormClass F₁ (Γ : Subgroup (GL (Fin 2) ℝ)) k₁]
  [ModularFormClass F₂ (Γ : Subgroup (GL (Fin 2) ℝ)) k₂]
  [ModularFormClass F₃ (Γ : Subgroup (GL (Fin 2) ℝ)) (k₁ + k₂)]

/-- **Additivity on products (`ModularFormClass` form)** on the compactified quotient. -/
theorem orderOnCompactifiedQuotient_eq_add_of_coe_eq_mul (f : F₁) (g : F₂) (fg : F₃)
    (hfg : ⇑fg = ⇑f * ⇑g) (hf : (⇑f : ℍ → ℂ) ≠ 0) (hg : (⇑g : ℍ → ℂ) ≠ 0)
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    orderOnCompactifiedQuotient fg x =
      orderOnCompactifiedQuotient f x + orderOnCompactifiedQuotient g x := by
  cases x with
  | ofQuotient P => simp [orderOfVanishingOnEffectiveOrbit_eq_add_of_coe_eq_mul f g fg hfg hf hg P]
  | ofCusp C => exact orderAtCuspOrbit_eq_add_of_coe_eq_mul f g fg hfg hf hg C

/-- Additivity of the weighted geometric order on products (`ModularFormClass` form). -/
theorem weightedOrderOnCompactifiedQuotient_eq_add_of_coe_eq_mul (f : F₁) (g : F₂) (fg : F₃)
    (hfg : ⇑fg = ⇑f * ⇑g) (hf : (⇑f : ℍ → ℂ) ≠ 0) (hg : (⇑g : ℍ → ℂ) ≠ 0)
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    weightedOrderOnCompactifiedQuotient fg x =
      weightedOrderOnCompactifiedQuotient f x + weightedOrderOnCompactifiedQuotient g x := by
  simp only [weightedOrderOnCompactifiedQuotient_def,
    orderOnCompactifiedQuotient_eq_add_of_coe_eq_mul f g fg hfg hf hg x, add_div]

end Mul

/-- Additivity of `orderOnCompactifiedQuotient` on products of nonzero modular forms. -/
theorem _root_.ModularForm.orderOnCompactifiedQuotient_mul [Γ.FiniteIndex]
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₁)
    (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₂) (hf : f ≠ 0) (hg : g ≠ 0)
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    orderOnCompactifiedQuotient (f.mul g) x =
      orderOnCompactifiedQuotient f x + orderOnCompactifiedQuotient g x :=
  orderOnCompactifiedQuotient_eq_add_of_coe_eq_mul f g (f.mul g) (_root_.ModularForm.coe_mul f g)
    (FunLike.coe_zero_iff.not.mpr hf) (FunLike.coe_zero_iff.not.mpr hg) x

/-- Additivity of the weighted geometric order on products of nonzero modular forms. -/
theorem _root_.ModularForm.weightedOrderOnCompactifiedQuotient_mul [Γ.FiniteIndex]
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₁)
    (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₂) (hf : f ≠ 0) (hg : g ≠ 0)
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    weightedOrderOnCompactifiedQuotient (f.mul g) x =
      weightedOrderOnCompactifiedQuotient f x + weightedOrderOnCompactifiedQuotient g x := by
  simp only [weightedOrderOnCompactifiedQuotient_def,
    _root_.ModularForm.orderOnCompactifiedQuotient_mul f g hf hg x, add_div]

end TauCeti.ModularForm

end
