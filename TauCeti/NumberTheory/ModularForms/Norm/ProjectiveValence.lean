/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Basic
public import TauCeti.NumberTheory.ModularForms.Norm.Cusps
public import TauCeti.NumberTheory.ModularForms.Order.CuspOrbit
public import TauCeti.NumberTheory.ModularForms.Order.EffectiveQuotient
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.NumberTheory.Modular.ConjugateTranslation
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
import TauCeti.NumberTheory.ModularForms.Cusps.Codimension

/-!
# The projective valence formula for modular forms

For a finite-index subgroup `Γ ≤ SL(2, ℤ)` and its effective image `G = Γ.map sl2zToPSL2R ≤
PSL(2, ℝ)`, `TauCeti/NumberTheory/ModularForms/Norm/Cusps.lean` establishes the full-coset valence
formula (`valence_formula_finiteIndex`), whose interior weights use the matrix stabiliser
`2 / |Stab_Γ P|`, whose cusp sum runs over the `T`-orbits on `SL(2, ℤ) ⧸ Γ`
(`CuspTranslationOrbit`), and whose total mass is `k · [SL(2, ℤ) : Γ] / 12`.

This file divides out the centre factor `[±Γ : Γ]` uniformly across the interior, the cusps, and
the subgroup index — without a top-level case split on whether `-I ∈ Γ` — to obtain the classical
projective valence formula (`valence_formula_projective`, Diamond–Shurman Theorem 3.6.1):

`∑_{P ∈ G \ ℍ} ord_P(f) / e_P + ∑_{C ∈ Cusps(Γ)} ord_C(f) = k · [SL(2, ℤ) : ±Γ] / 12`,

where `e_P = |Stab_G P|` is the projective stabiliser order, `ord_C(f)` is the width-normalized
geometric cusp order `orderAtCuspOrbit f C`, and `[SL(2, ℤ) : ±Γ] = Γ.withCenter.index` equals
the projective subgroup index `[PSL(2, ℤ) : G]` (`Subgroup.relIndex_map_sl2zToPSL2R`). Packaging
both halves on `G.CompactifiedQuotient` gives the single-sum compactified-quotient valence formula
(`valence_formula_compactifiedQuotient`).

## The cusp fiber mechanism

Let `cuspOrbitOfTranslationOrbit Γ : CuspTranslationOrbit Γ → G.CuspOrbit` send the translation
orbit of the coset `γ⁻¹ Γ` to the geometric cusp orbit `Γ.cuspOrbitOfSL2Z γ` of `γ • ∞`. Over
a geometric cusp orbit represented by `γ ∈ SL(2, ℤ)`:

1. The fiber consists strictly of the translation orbits of `γ⁻¹ Γ` and `(-γ)⁻¹ Γ`
   (`cuspOrbitOfTranslationOrbit_eq_cuspOrbitOfSL2Z_iff`).
2. Those two translation orbits coalesce if and only if `-I ∈ Γ` or the cusp orbit is irregular
   (`cuspTranslationOrbitOfSL2Z_eq_neg_iff`).
3. The translation-orbit width at `γ⁻¹ Γ` equals the strict width `Γγ.strictWidthInfty` of
   `Γγ = γ⁻¹ Γ γ` (`cuspTranslationOrbitWidth_cuspTranslationOrbitOfSL2Z`), so the
   translation-orbit order equals `ord_C(f)` when `C` is regular and `2 · ord_C(f)` when `C` is
   irregular.

In all three geometric regimes (`-I ∈ Γ`; `-I ∉ Γ` at a regular cusp where the fiber has two
distinct orbits of order `ord_C(f)`; `-I ∉ Γ` at an irregular cusp where the fiber coalesces to
one orbit of order `2 · ord_C(f)`), the fiber sum equals `[±Γ : Γ] · ord_C(f)`
(`sum_fiber_orderAtCuspTranslationOrbit_eq`).

## Main declarations

* `TauCeti.ModularForm.finsum_weightedOrderOfVanishingOnSubgroupOrbit_eq_relIndex_withCenter_mul`:
  the full-coset interior weighted sum is `[±Γ : Γ]` times the projective interior weighted sum.
* `TauCeti.ModularForm.cuspTranslationOrbitOfSL2Z` and
  `TauCeti.ModularForm.cuspOrbitOfTranslationOrbit`: the projection from cusp translation orbits
  to geometric cusp orbits `G.CuspOrbit`, with
  `cuspTranslationOrbitWidth_cuspTranslationOrbitOfSL2Z`,
  `cuspOrbitOfTranslationOrbit_eq_cuspOrbitOfSL2Z_iff`, and
  `cuspTranslationOrbitOfSL2Z_eq_neg_iff`.
* `TauCeti.ModularForm.sum_orderAtCuspTranslationOrbit_eq_relIndex_withCenter_mul`: the
  translation-orbit cusp sum is `[±Γ : Γ]` times the geometric cusp-orbit sum.
* `TauCeti.ModularForm.valence_formula_projective`: **the projective valence formula** over
  `G \ ℍ` and `G.CuspOrbit`.
* `TauCeti.ModularForm.weightedOrderOnCompactifiedQuotient` and
  `TauCeti.ModularForm.valence_formula_compactifiedQuotient`: the unified weighted order divisor on
  `G.CompactifiedQuotient` and its single-sum valence formula.
* `twelve_mul_orderOfVanishingOnEffectiveOrbit_le_weight_mul_index_withCenter_mul_cardStabilizer`
  and `twelve_mul_orderAtCuspOrbit_le_weight_mul_index_withCenter`: single-point mass bounds on
  interior orbits and cusp orbits.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], Theorem 3.6.1.
* [G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*][shimura1971],
  Proposition 2.16.
-/

public noncomputable section

open Function Matrix Matrix.SpecialLinearGroup Matrix.ProjectiveSpecialLinearGroup MulAction
  OnePoint SlashInvariantForm Subgroup UpperHalfPlane
open scoped MatrixGroups Modular ModularForm Pointwise

namespace TauCeti.ModularForm

/-! ### Interior weighted sum: full-coset vs projective -/

section Interior

variable {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]

/-- **The full-coset interior weighted sum is `[±Γ : Γ]` times the projective interior weighted
sum.** Reindexing along `effectiveOrbitEquiv` converts each matrix-stabiliser weight into
`[±Γ : Γ]` times the projective weight `1 / e_P`, without assuming finite index or
holomorphicity: if the support is infinite, both `finsum`s vanish in `ℚ` since `[±Γ : Γ] ≠ 0`. -/
theorem finsum_weightedOrderOfVanishingOnSubgroupOrbit_eq_relIndex_withCenter_mul
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) :
    (∑ᶠ o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ,
        weightedOrderOfVanishingOnSubgroupOrbit f o) =
      (Γ.relIndex Γ.withCenter : ℚ) *
        ∑ᶠ P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ,
          weightedOrderOfVanishingOnEffectiveOrbit f P := by
  rw [mul_finsum, ← finsum_comp_equiv (effectiveOrbitEquiv Γ)]
  exact finsum_congr (weightedOrderOfVanishingOnSubgroupOrbit_eq_relIndex_withCenter_mul f)

end Interior

/-! ### Cusp translation orbits over geometric cusp orbits -/

section Cusps

/-- The cusp translation orbit of the coset `γ⁻¹ Γ`, representing the cusp `γ • ∞` in step
with `Subgroup.cuspOrbitOfSL2Z Γ γ`. -/
def cuspTranslationOrbitOfSL2Z (Γ : Subgroup SL(2, ℤ)) (γ : SL(2, ℤ)) :
    CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ)) :=
  ⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹)⟧

lemma cuspTranslationOrbitOfSL2Z_def (Γ : Subgroup SL(2, ℤ)) (γ : SL(2, ℤ)) :
    cuspTranslationOrbitOfSL2Z Γ γ = ⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹)⟧ :=
  (rfl)

section FiniteIndex

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]

private local instance isArithmeticConjInv (γ : SL(2, ℤ)) :
    (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).IsArithmetic :=
  Subgroup.isArithmetic_conj_of_mem (H := 𝒮ℒ) ⟨γ⁻¹, map_inv (mapGL ℝ) γ⟩

private lemma rangeRestrict_choose_eq (x : 𝒮ℒ) :
    x = (mapGL ℝ).rangeRestrict (Classical.choose x.2) :=
  Subtype.ext (Classical.choose_spec x.2).symm

/-- **Projection from cusp translation orbits to geometric cusp orbits.** The coset of `γ`
represents the cusp `γ⁻¹ • ∞`, so `cuspOrbitOfTranslationOrbit` maps its `T`-orbit to
`Γ.cuspOrbitOfSL2Z γ⁻¹`. -/
def cuspOrbitOfTranslationOrbit (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ)) → (Γ.map sl2zToPSL2R).CuspOrbit :=
  Quotient.lift
    (Quotient.lift (fun x : 𝒮ℒ ↦ Γ.cuspOrbitOfSL2Z (Classical.choose x.2)⁻¹)
      fun x y hxy ↦ by
        have hmk :
            (QuotientGroup.mk x : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) =
              QuotientGroup.mk y := Quotient.sound hxy
        rw [rangeRestrict_choose_eq x, rangeRestrict_choose_eq y] at hmk
        exact cuspOrbitOfSL2Z_inv_eq_of_cuspTranslationOrbit_mk_eq
          (Quotient.sound ⟨1, by simpa using hmk.symm⟩))
    fun q₁ q₂ hq ↦ by
      induction q₁ using Quotient.inductionOn with
      | h x =>
        induction q₂ using Quotient.inductionOn with
        | h y =>
          have heq :
              (⟦(QuotientGroup.mk x : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)⟧ :
                CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) =
                ⟦QuotientGroup.mk y⟧ :=
            Quotient.sound hq
          rw [rangeRestrict_choose_eq x, rangeRestrict_choose_eq y] at heq
          exact cuspOrbitOfSL2Z_inv_eq_of_cuspTranslationOrbit_mk_eq heq

@[simp]
theorem cuspOrbitOfTranslationOrbit_mk (γ : SL(2, ℤ)) :
    cuspOrbitOfTranslationOrbit Γ
        (⟦(QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ) :
          𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)⟧ :
            CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) =
      Γ.cuspOrbitOfSL2Z γ⁻¹ := by
  change Γ.cuspOrbitOfSL2Z (Classical.choose ((mapGL ℝ).rangeRestrict γ).2)⁻¹ =
    Γ.cuspOrbitOfSL2Z γ⁻¹
  rw [mapGL_injective (Classical.choose_spec ((mapGL ℝ).rangeRestrict γ).2)]

@[simp]
theorem cuspOrbitOfTranslationOrbit_cuspTranslationOrbitOfSL2Z (γ : SL(2, ℤ)) :
    cuspOrbitOfTranslationOrbit Γ (cuspTranslationOrbitOfSL2Z Γ γ) = Γ.cuspOrbitOfSL2Z γ := by
  rw [cuspTranslationOrbitOfSL2Z_def, cuspOrbitOfTranslationOrbit_mk, inv_inv]

theorem cuspOrbitOfTranslationOrbit_surjective :
    Function.Surjective (cuspOrbitOfTranslationOrbit Γ) := by
  intro C
  obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
  exact ⟨cuspTranslationOrbitOfSL2Z Γ γ,
    cuspOrbitOfTranslationOrbit_cuspTranslationOrbitOfSL2Z γ⟩

private lemma eq_intCast_and_eq_T_zpow_of_mapGL_eq_upperRightHom {b : SL(2, ℤ)} {x : ℝ}
    (hb : mapGL ℝ b = GeneralLinearGroup.upperRightHom x) :
    x = (b 0 1 : ℝ) ∧ b = ModularGroup.T ^ b 0 1 := by
  have hx : x = (b 0 1 : ℝ) := by
    have h01 := congrArg (fun M : GL (Fin 2) ℝ ↦ (M : Matrix (Fin 2) (Fin 2) ℝ) 0 1) hb
    simpa [mapGL_coe_matrix, GeneralLinearGroup.upperRightHom_apply, algebraMap_int_eq] using
      h01.symm
  have hbT : b = ModularGroup.T ^ b 0 1 := mapGL_injective <| by
    rw [hb, hx, TauCeti.ModularGroup.mapGL_T_zpow_eq_upperRightHom]
  exact ⟨hx, hbT⟩

omit [Γ.FiniteIndex] in
/-- Strict periods of `γ⁻¹ Γ γ` at an integer shift correspond to `γ T^m γ⁻¹ ∈ Γ`. -/
private lemma intCast_mem_strictPeriods_conj_inv_iff (γ : SL(2, ℤ)) (m : ℤ) :
    (m : ℝ) ∈
        (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).strictPeriods ↔
      γ * ModularGroup.T ^ m * γ⁻¹ ∈ Γ := by
  rw [Subgroup.mem_strictPeriods_iff, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.toConjAct_inv, inv_inv, ConjAct.toConjAct_smul,
    ← TauCeti.ModularGroup.mapGL_T_zpow_eq_upperRightHom, ← map_inv, ← map_mul, ← map_mul,
    Subgroup.mem_map_iff_mem mapGL_injective]

omit [Γ.FiniteIndex] in
/-- Every strict period of `γ⁻¹ Γ γ` is an integer multiple of the cusp translation orbit width
at `γ⁻¹ Γ`. -/
private lemma strictPeriods_conj_inv_eq_zmultiples_cuspTranslationOrbitWidth (γ : SL(2, ℤ)) :
    (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).strictPeriods =
      AddSubgroup.zmultiples
        (cuspTranslationOrbitWidth (cuspTranslationOrbitOfSL2Z Γ γ) : ℝ) := by
  set w := cuspTranslationOrbitWidth (cuspTranslationOrbitOfSL2Z Γ γ) with hw_def
  refine le_antisymm (fun x hx ↦ ?_) (AddSubgroup.zmultiples_le.mpr ?_)
  · rw [Subgroup.mem_strictPeriods_iff, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.toConjAct_inv, inv_inv, ConjAct.toConjAct_smul] at hx
    obtain ⟨a, ha, ha_eq⟩ := Subgroup.mem_map.mp hx
    set b : SL(2, ℤ) := γ⁻¹ * a * γ with hb_def
    set m : ℤ := b 0 1
    obtain ⟨hx_eq, hbT⟩ := eq_intCast_and_eq_T_zpow_of_mapGL_eq_upperRightHom (b := b) (x := x)
      (by rw [hb_def, map_mul, map_mul, map_inv, ha_eq]; group)
    have haT : γ * ModularGroup.T ^ m * γ⁻¹ = a := by rw [← hbT, hb_def]; group
    have hwn : w ∣ m.natAbs := by
      rw [hw_def, cuspTranslationOrbitOfSL2Z_def, cuspTranslationOrbitWidth_mk_dvd_iff, inv_inv]
      rcases Int.natAbs_eq m with hm | hm
      · have hpow : ModularGroup.T ^ m.natAbs = ModularGroup.T ^ m := by
          rw [← zpow_natCast, ← hm]
        rwa [hpow, haT]
      · have hm' : (m.natAbs : ℤ) = -m := by omega
        have hpow : γ * ModularGroup.T ^ m.natAbs * γ⁻¹ = a⁻¹ := by
          rw [← zpow_natCast, hm', _root_.zpow_neg, ← haT]; group
        rw [hpow]
        exact inv_mem ha
    obtain ⟨d, hd⟩ := Int.ofNat_dvd_left.mpr hwn
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨d, ?_⟩
    have hxm : x = (m : ℝ) := hx_eq
    rw [zsmul_eq_mul, hxm, hd]
    push_cast
    ring
  · have hw : γ * ModularGroup.T ^ (w : ℤ) * γ⁻¹ ∈ Γ := by
      have hdvd : w ∣ w := dvd_rfl
      rwa [hw_def, cuspTranslationOrbitOfSL2Z_def, cuspTranslationOrbitWidth_mk_dvd_iff, inv_inv,
        ← zpow_natCast] at hdvd
    exact_mod_cast (intCast_mem_strictPeriods_conj_inv_iff γ w).mpr hw

omit [Γ.FiniteIndex] in
/-- **The translation-orbit width at `γ⁻¹ Γ` equals the strict cusp width `strictWidthInfty` of
`γ⁻¹ Γ γ`.** -/
theorem cuspTranslationOrbitWidth_cuspTranslationOrbitOfSL2Z (γ : SL(2, ℤ)) :
    (cuspTranslationOrbitWidth (cuspTranslationOrbitOfSL2Z Γ γ) : ℝ) =
      (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ •
        (Γ : Subgroup (GL (Fin 2) ℝ))).strictWidthInfty :=
  (Subgroup.strictWidthInfty_eq_of_strictPeriods_eq_zmultiples
    (strictPeriods_conj_inv_eq_zmultiples_cuspTranslationOrbitWidth γ) (Nat.cast_nonneg _)).symm

/-- Evaluating `orderAtCuspTranslationOrbit` at `cuspTranslationOrbitOfSL2Z Γ γ` reads the
`q`-expansion order of `f ∣[k] γ` in the strict width `Γγ.strictWidthInfty`. -/
theorem orderAtCuspTranslationOrbit_cuspTranslationOrbitOfSL2Z
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (γ : SL(2, ℤ)) :
    orderAtCuspTranslationOrbit f (cuspTranslationOrbitOfSL2Z Γ γ) =
      qExpansionOrderAtCusp
        (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ •
          (Γ : Subgroup (GL (Fin 2) ℝ))).strictWidthInfty
        (⇑f ∣[k] mapGL ℝ γ) := by
  have hslash : quotientFunc f
      (QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹) :
        𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) =
      ⇑f ∣[k] mapGL ℝ γ := by
    rw [_root_.SlashInvariantForm.quotientFunc_mk, MonoidHom.coe_rangeRestrict, ← map_inv,
      inv_inv]
  rw [← cuspTranslationOrbitWidth_cuspTranslationOrbitOfSL2Z, cuspTranslationOrbitOfSL2Z_def,
    orderAtCuspTranslationOrbit_mk, ← cuspTranslationOrbitWidth_mk, hslash]

/-- At a **regular** cusp orbit, the translation-orbit order equals `orderAtCuspOrbit`. -/
theorem orderAtCuspTranslationOrbit_cuspTranslationOrbitOfSL2Z_of_isRegular
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) {γ : SL(2, ℤ)}
    (hreg : IsRegularCuspOrbit Γ (Γ.cuspOrbitOfSL2Z γ)) :
    (orderAtCuspTranslationOrbit f (cuspTranslationOrbitOfSL2Z Γ γ) : ℚ) =
      orderAtCuspOrbit f (Γ.cuspOrbitOfSL2Z γ) := by
  rw [orderAtCuspTranslationOrbit_cuspTranslationOrbitOfSL2Z,
    Subgroup.strictWidthInfty_of_isRegularAtInfty _
      ((isRegularCuspOrbit_cuspOrbitOfSL2Z γ).mp hreg),
    orderAtCuspOrbit_cuspOrbitOfSL2Z_of_isRegular f hreg]

/-- At an **irregular** cusp orbit, the translation-orbit order is twice `orderAtCuspOrbit`, since
the strict width is twice the projective cusp width. -/
theorem orderAtCuspTranslationOrbit_cuspTranslationOrbitOfSL2Z_of_not_isRegular
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) {γ : SL(2, ℤ)}
    (hirr : ¬IsRegularCuspOrbit Γ (Γ.cuspOrbitOfSL2Z γ)) :
    (orderAtCuspTranslationOrbit f (cuspTranslationOrbitOfSL2Z Γ γ) : ℚ) =
      2 * orderAtCuspOrbit f (Γ.cuspOrbitOfSL2Z γ) := by
  rw [orderAtCuspTranslationOrbit_cuspTranslationOrbitOfSL2Z,
    Subgroup.strictWidthInfty_of_not_isRegularAtInfty _
      (mt (isRegularCuspOrbit_cuspOrbitOfSL2Z γ).mpr hirr),
    orderAtCuspOrbit_cuspOrbitOfSL2Z, orderAtCusp_def]
  ring

omit [Γ.FiniteIndex] in
private lemma mk_eq_cuspTranslationOrbitOfSL2Z_of_eq_mul {δ γ g : SL(2, ℤ)}
    (hg : g ∈ Γ) (j : ℤ) (hδ : δ = ModularGroup.T ^ j * γ⁻¹ * g) :
    (⟦(QuotientGroup.mk ((mapGL ℝ).rangeRestrict δ) :
        𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)⟧ :
          CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) =
      cuspTranslationOrbitOfSL2Z Γ γ := by
  refine Quotient.sound ⟨⟨TSL ^ j, Subgroup.zpow_mem_zpowers TSL j⟩, ?_⟩
  simp only [Subgroup.mk_smul, MulAction.Quotient.smul_mk, smul_eq_mul]
  refine QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr ?_)
  have hcoe : (((TSL ^ j * (mapGL ℝ).rangeRestrict γ⁻¹)⁻¹ *
      (mapGL ℝ).rangeRestrict δ : 𝒮ℒ) : GL (Fin 2) ℝ) = mapGL ℝ g := by
    simp only [coe_TSL_zpow, TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, map_inv,
      Subgroup.coe_mul, InvMemClass.coe_inv, MonoidHom.coe_rangeRestrict]
    rw [hδ, map_mul, map_mul, map_inv]
    group
  rw [hcoe]
  exact Subgroup.mem_map_of_mem _ hg

/-- **Fiber description of `cuspOrbitOfTranslationOrbit`.** The translation orbits lying above the
geometric cusp orbit `Γ.cuspOrbitOfSL2Z γ` are precisely those of `γ⁻¹ Γ` and `(-γ)⁻¹ Γ`. -/
theorem cuspOrbitOfTranslationOrbit_eq_cuspOrbitOfSL2Z_iff
    (c : CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) (γ : SL(2, ℤ)) :
    cuspOrbitOfTranslationOrbit Γ c = Γ.cuspOrbitOfSL2Z γ ↔
      c = cuspTranslationOrbitOfSL2Z Γ γ ∨ c = cuspTranslationOrbitOfSL2Z Γ (-γ) := by
  refine ⟨fun h ↦ ?_, fun h ↦ by
    rcases h with rfl | rfl <;> simp⟩
  induction c using CuspTranslationOrbit.induction_on with
  | h δ =>
    rw [cuspOrbitOfTranslationOrbit_mk] at h
    obtain ⟨g, hg, hc⟩ := (Γ.cuspOrbitOfSL2Z_eq_iff δ⁻¹ γ).mp h
    rw [inv_inv] at hc
    set b : SL(2, ℤ) := δ * g * γ with hb_def
    rcases TauCeti.ModularGroup.eq_T_zpow_or_eq_neg_T_zpow_of_c_eq_zero hc with hT | hT
    · left
      set j : ℤ := b 0 1
      have hTm : b = ModularGroup.T ^ j := hT
      have hδ : δ = ModularGroup.T ^ j * γ⁻¹ * g⁻¹ := by
        calc δ = b * γ⁻¹ * g⁻¹ := by rw [hb_def]; group
          _ = ModularGroup.T ^ j * γ⁻¹ * g⁻¹ := by rw [hTm]
      exact mk_eq_cuspTranslationOrbitOfSL2Z_of_eq_mul (inv_mem hg) j hδ
    · right
      set j : ℤ := -b 0 1
      have hTm : b = -ModularGroup.T ^ j := hT
      have hδ : δ = ModularGroup.T ^ j * (-γ)⁻¹ * g⁻¹ := by
        calc δ = b * γ⁻¹ * g⁻¹ := by rw [hb_def]; group
          _ = ModularGroup.T ^ j * (-γ)⁻¹ * g⁻¹ := by
            rw [hTm, neg_mul, ← mul_neg (ModularGroup.T ^ j), neg_inv]
      exact mk_eq_cuspTranslationOrbitOfSL2Z_of_eq_mul (inv_mem hg) j hδ

omit [Γ.FiniteIndex] in
private lemma cuspTranslationOrbitOfSL2Z_eq_neg_iff_exists_neg_conj_T_zpow_mem (γ : SL(2, ℤ)) :
    cuspTranslationOrbitOfSL2Z Γ γ = cuspTranslationOrbitOfSL2Z Γ (-γ) ↔
      ∃ k : ℤ, -(γ * ModularGroup.T ^ k * γ⁻¹) ∈ Γ := by
  constructor
  · intro h
    obtain ⟨⟨_, hg⟩, hgq⟩ := MulAction.orbitRel_apply.mp (Quotient.exact h)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hmk : (QuotientGroup.mk (TSL ^ j * (mapGL ℝ).rangeRestrict (-γ)⁻¹) :
        𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) =
          QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹) := by
      simpa only [Subgroup.mk_smul, MulAction.Quotient.smul_mk, smul_eq_mul] using hgq
    obtain ⟨h₀, hh₀, he⟩ :=
      Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hmk))
    have hcoe : (((TSL ^ j * (mapGL ℝ).rangeRestrict (-γ)⁻¹)⁻¹ *
        (mapGL ℝ).rangeRestrict γ⁻¹ : 𝒮ℒ) : GL (Fin 2) ℝ) =
          mapGL ℝ ((ModularGroup.T ^ j * (-γ)⁻¹)⁻¹ * γ⁻¹) := by
      simp only [coe_TSL_zpow, TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, map_mul, map_inv,
        Subgroup.coe_mul, InvMemClass.coe_inv, MonoidHom.coe_rangeRestrict]
    have hh₀_eq : -(γ * ModularGroup.T ^ (-j) * γ⁻¹) = h₀ := by
      have hni : (-(ModularGroup.T ^ j * γ⁻¹))⁻¹ = -(ModularGroup.T ^ j * γ⁻¹)⁻¹ :=
        neg_inv.symm
      rw [mapGL_injective (he.trans hcoe), ← neg_inv, mul_neg, hni, neg_mul, _root_.mul_inv_rev,
        inv_inv, _root_.zpow_neg, mul_assoc]
    exact ⟨-j, hh₀_eq ▸ hh₀⟩
  · rintro ⟨k, hk⟩
    have hγ : γ⁻¹ =
        ModularGroup.T ^ (-k) * (-γ)⁻¹ * -(γ * ModularGroup.T ^ k * γ⁻¹) := by
      rw [← neg_inv, mul_neg, mul_neg, neg_mul, neg_neg, _root_.zpow_neg]
      group
    exact mk_eq_cuspTranslationOrbitOfSL2Z_of_eq_mul hk (-k) hγ

private lemma exists_neg_conj_T_zpow_mem_of_not_isRegular {γ : SL(2, ℤ)}
    (hirr : ¬IsRegularCuspOrbit Γ (Γ.cuspOrbitOfSL2Z γ)) :
    ∃ k : ℤ, -(γ * ModularGroup.T ^ k * γ⁻¹) ∈ Γ := by
  set Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))
  have hmem := Γγ.neg_upperRightHom_widthInfty_mem_of_not_isRegularAtInfty
    (mt (isRegularCuspOrbit_cuspOrbitOfSL2Z γ).mpr hirr)
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul] at hmem
  obtain ⟨a, ha, ha_eq⟩ := Subgroup.mem_map.mp hmem
  set b : SL(2, ℤ) := -(γ⁻¹ * a * γ) with hb_def
  obtain ⟨-, hbT⟩ := eq_intCast_and_eq_T_zpow_of_mapGL_eq_upperRightHom (b := b)
    (x := Γγ.widthInfty) (by
      have hneg1 : mapGL ℝ (-1 : SL(2, ℤ)) = -1 := mapGL_neg_one
      rw [hb_def, ← neg_one_mul (γ⁻¹ * a * γ), map_mul, hneg1, map_mul, map_mul, map_inv, ha_eq]
      simp [mul_assoc])
  have haT : -(γ * ModularGroup.T ^ b 0 1 * γ⁻¹) = a := by
    rw [← hbT, hb_def, mul_neg, neg_mul, neg_neg]; group
  exact ⟨b 0 1, haT ▸ ha⟩

/-- **Exact coalescing criterion for the two translation orbits over a cusp.** The translation
orbits of `γ⁻¹ Γ` and `(-γ)⁻¹ Γ` coincide iff `-I ∈ Γ` or the cusp orbit of `γ • ∞` is
irregular. -/
theorem cuspTranslationOrbitOfSL2Z_eq_neg_iff (γ : SL(2, ℤ)) :
    cuspTranslationOrbitOfSL2Z Γ γ = cuspTranslationOrbitOfSL2Z Γ (-γ) ↔
      (-1 : SL(2, ℤ)) ∈ Γ ∨ ¬IsRegularCuspOrbit Γ (Γ.cuspOrbitOfSL2Z γ) := by
  rw [cuspTranslationOrbitOfSL2Z_eq_neg_iff_exists_neg_conj_T_zpow_mem]
  set Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))
  constructor
  · rintro ⟨k, hk⟩
    by_cases hneg : (-1 : SL(2, ℤ)) ∈ Γ
    · exact Or.inl hneg
    · refine Or.inr fun hreg ↦ hneg ?_
      have hk_per : (k : ℝ) ∈ Γγ.periods := by
        simp only [Subgroup.periods, Subgroup.mem_strictPeriods_iff, Subgroup.mem_adjoinNegOne_iff,
          Γγ, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.toConjAct_inv, inv_inv,
          ConjAct.toConjAct_smul, ← TauCeti.ModularGroup.mapGL_T_zpow_eq_upperRightHom]
        right
        have hneg1 : mapGL ℝ (-1 : SL(2, ℤ)) = -1 := mapGL_neg_one
        have hmat : mapGL ℝ γ * -mapGL ℝ (ModularGroup.T ^ k) * (mapGL ℝ γ)⁻¹ =
            mapGL ℝ (-(γ * ModularGroup.T ^ k * γ⁻¹)) := by
          rw [← neg_one_mul (γ * ModularGroup.T ^ k * γ⁻¹), map_mul, hneg1, map_mul, map_mul,
            map_inv, mul_neg, neg_mul, neg_one_mul]
        rw [hmat]
        exact Subgroup.mem_map_of_mem _ hk
      have hk_sper : (k : ℝ) ∈ Γγ.strictPeriods :=
        ((isRegularCuspOrbit_cuspOrbitOfSL2Z γ).mp hreg).symm ▸ hk_per
      have hu : γ * ModularGroup.T ^ k * γ⁻¹ ∈ Γ :=
        (intCast_mem_strictPeriods_conj_inv_iff γ k).mp hk_sper
      have hprod : -(γ * ModularGroup.T ^ k * γ⁻¹) *
          (γ * ModularGroup.T ^ k * γ⁻¹)⁻¹ = -1 := by
        rw [neg_mul, mul_inv_cancel]
      exact hprod ▸ mul_mem hk (inv_mem hu)
  · rintro (hneg | hirr)
    · exact ⟨0, by simpa using hneg⟩
    · exact exists_neg_conj_T_zpow_mem_of_not_isRegular hirr

/-- **Fiber sum over a single geometric cusp orbit.** Whether `-I ∈ Γ`, `-I ∉ Γ` at a regular
cusp, or `-I ∉ Γ` at an irregular cusp, the sum of `orderAtCuspTranslationOrbit` over the
translation orbits above `C` equals `[±Γ : Γ] · orderAtCuspOrbit f C`. -/
theorem sum_fiber_orderAtCuspTranslationOrbit_eq
    [DecidableEq ((Γ.map sl2zToPSL2R).CuspOrbit)]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    (∑ c ∈ Finset.univ with cuspOrbitOfTranslationOrbit Γ c = C,
        (orderAtCuspTranslationOrbit f c : ℚ)) =
      (Γ.relIndex Γ.withCenter : ℚ) * orderAtCuspOrbit f C := by
  classical
  obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
  set c₁ := cuspTranslationOrbitOfSL2Z Γ γ
  set c₂ := cuspTranslationOrbitOfSL2Z Γ (-γ)
  have hfilter : ({c ∈ Finset.univ | cuspOrbitOfTranslationOrbit Γ c = Γ.cuspOrbitOfSL2Z γ} :
      Finset (CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ)))) = {c₁, c₂} := by
    ext c
    simp [c₁, c₂, cuspOrbitOfTranslationOrbit_eq_cuspOrbitOfSL2Z_iff]
  rw [hfilter]
  by_cases heq : c₁ = c₂
  · rw [heq, Finset.pair_eq_singleton, Finset.sum_singleton, ← heq]
    by_cases hneg : (-1 : SL(2, ℤ)) ∈ Γ
    · rw [relIndex_withCenter_eq_one_of_neg_one_mem hneg, Nat.cast_one, one_mul,
        orderAtCuspTranslationOrbit_cuspTranslationOrbitOfSL2Z_of_isRegular f
          (isRegularCuspOrbit_of_neg_one_mem hneg _)]
    · have hirr : ¬IsRegularCuspOrbit Γ (Γ.cuspOrbitOfSL2Z γ) :=
        ((cuspTranslationOrbitOfSL2Z_eq_neg_iff γ).mp heq).resolve_left hneg
      rw [relIndex_withCenter_eq_two_of_neg_one_notMem hneg, Nat.cast_ofNat,
        orderAtCuspTranslationOrbit_cuspTranslationOrbitOfSL2Z_of_not_isRegular f hirr]
  · obtain ⟨hneg, hreg⟩ :
        (-1 : SL(2, ℤ)) ∉ Γ ∧ IsRegularCuspOrbit Γ (Γ.cuspOrbitOfSL2Z γ) := by
      have hnot := mt (cuspTranslationOrbitOfSL2Z_eq_neg_iff γ).mpr heq
      exact ⟨fun h ↦ hnot (Or.inl h), Classical.not_not.mp fun h ↦ hnot (Or.inr h)⟩
    have hreg_neg : IsRegularCuspOrbit Γ (Γ.cuspOrbitOfSL2Z (-γ)) := by
      rwa [Γ.cuspOrbitOfSL2Z_neg]
    rw [Finset.sum_pair heq, relIndex_withCenter_eq_two_of_neg_one_notMem hneg, Nat.cast_ofNat,
      orderAtCuspTranslationOrbit_cuspTranslationOrbitOfSL2Z_of_isRegular f hreg,
      orderAtCuspTranslationOrbit_cuspTranslationOrbitOfSL2Z_of_isRegular f hreg_neg,
      Γ.cuspOrbitOfSL2Z_neg, two_mul]

/-- **The full-coset cusp sum is `[±Γ : Γ]` times the geometric cusp-orbit sum.** -/
theorem sum_orderAtCuspTranslationOrbit_eq_relIndex_withCenter_mul
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) :
    (∑ c : CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ)),
        (orderAtCuspTranslationOrbit f c : ℚ)) =
      (Γ.relIndex Γ.withCenter : ℚ) *
        ∑ᶠ C : (Γ.map sl2zToPSL2R).CuspOrbit, orderAtCuspOrbit f C := by
  classical
  rw [← finsum_sum_filter (cuspOrbitOfTranslationOrbit Γ) Finset.univ
    (fun c ↦ (orderAtCuspTranslationOrbit f c : ℚ)), mul_finsum]
  exact finsum_congr (sum_fiber_orderAtCuspTranslationOrbit_eq f)

end FiniteIndex

end Cusps

/-! ### The projective valence formula and compactified quotient form -/

section ValenceFormula

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]

/-- **The projective valence formula (Diamond–Shurman, Theorem 3.6.1).**

For any nonzero weight-`k` modular form `f` on a finite-index subgroup `Γ ≤ SL(2, ℤ)`, the sum
of the projective weighted interior vanishing orders `ord_P(f) / e_P` over
`(Γ.map sl2zToPSL2R) \ ℍ` plus the sum of the width-normalized cusp orders `ord_C(f)` over the
geometric cusp orbits `(Γ.map sl2zToPSL2R).CuspOrbit` equals `k · [SL(2, ℤ) : ±Γ] / 12`,
uniformly in the parity of `k` and in whether `-I ∈ Γ`. -/
theorem valence_formula_projective
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    (∑ᶠ P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ,
          weightedOrderOfVanishingOnEffectiveOrbit f P) +
        (∑ᶠ C : (Γ.map sl2zToPSL2R).CuspOrbit, orderAtCuspOrbit f C) =
      (k : ℚ) * Γ.withCenter.index / 12 := by
  have htotal := valence_formula_finiteIndex f hf
  rw [finsum_weightedOrderOfVanishingOnSubgroupOrbit_eq_relIndex_withCenter_mul,
    sum_orderAtCuspTranslationOrbit_eq_relIndex_withCenter_mul,
    Subgroup.card_quotient_mapGL_eq_index,
    ← Subgroup.relIndex_mul_index Γ.le_withCenter] at htotal
  have hr : (Γ.relIndex Γ.withCenter : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (relIndex_withCenter_pos Γ).ne'
  push_cast at htotal
  exact mul_left_cancel₀ hr (by linear_combination htotal)

/-- **Unified weighted vanishing order on the compactified modular quotient
`(Γ.map sl2zToPSL2R).CompactifiedQuotient`.**

Assigns `weightedOrderOfVanishingOnEffectiveOrbit f P = ord_P(f) / e_P` to an interior point
`ofQuotient P` and `orderAtCuspOrbit f C = ord_C(f)` to a cusp point `ofCusp C`. -/
def weightedOrderOnCompactifiedQuotient
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) :
    (Γ.map sl2zToPSL2R).CompactifiedQuotient → ℚ
  | .ofQuotient P => weightedOrderOfVanishingOnEffectiveOrbit f P
  | .ofCusp C => orderAtCuspOrbit f C

@[simp]
lemma weightedOrderOnCompactifiedQuotient_ofQuotient
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    weightedOrderOnCompactifiedQuotient f (.ofQuotient P) =
      weightedOrderOfVanishingOnEffectiveOrbit f P :=
  (rfl)

@[simp]
lemma weightedOrderOnCompactifiedQuotient_ofCusp
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    weightedOrderOnCompactifiedQuotient f (.ofCusp C) = orderAtCuspOrbit f C :=
  (rfl)

lemma weightedOrderOnCompactifiedQuotient_nonneg
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    0 ≤ weightedOrderOnCompactifiedQuotient f x := by
  cases x with
  | ofQuotient P => exact weightedOrderOfVanishingOnEffectiveOrbit_nonneg f P
  | ofCusp C => exact orderAtCuspOrbit_nonneg f C

theorem weightedOrderOnCompactifiedQuotient_eq_add_of_coe_eq_mul {k₁ k₂ : ℤ}
    {F₁ F₂ F₃ : Type*} [FunLike F₁ ℍ ℂ] [FunLike F₂ ℍ ℂ] [FunLike F₃ ℍ ℂ]
    [ModularFormClass F₁ (Γ : Subgroup (GL (Fin 2) ℝ)) k₁]
    [ModularFormClass F₂ (Γ : Subgroup (GL (Fin 2) ℝ)) k₂]
    [SlashInvariantFormClass F₃ (Γ : Subgroup (GL (Fin 2) ℝ)) (k₁ + k₂)]
    {f : F₁} {g : F₂} {fg : F₃} (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (hg : (⇑g : ℍ → ℂ) ≠ 0) (hfg : (⇑fg : ℍ → ℂ) = ⇑f * ⇑g)
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    weightedOrderOnCompactifiedQuotient fg x =
      weightedOrderOnCompactifiedQuotient f x + weightedOrderOnCompactifiedQuotient g x := by
  cases x with
  | ofQuotient P => exact weightedOrderOfVanishingOnEffectiveOrbit_eq_add_of_coe_eq_mul hf hg hfg P
  | ofCusp C => exact orderAtCuspOrbit_eq_add_of_coe_eq_mul hf hg hfg C

theorem weightedOrderOnCompactifiedQuotient_mul {k₁ k₂ : ℤ}
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₁)
    (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₂)
    (hf : (⇑f : ℍ → ℂ) ≠ 0) (hg : (⇑g : ℍ → ℂ) ≠ 0)
    (x : (Γ.map sl2zToPSL2R).CompactifiedQuotient) :
    weightedOrderOnCompactifiedQuotient (f.mul g) x =
      weightedOrderOnCompactifiedQuotient f x + weightedOrderOnCompactifiedQuotient g x :=
  weightedOrderOnCompactifiedQuotient_eq_add_of_coe_eq_mul hf hg (_root_.ModularForm.coe_mul f g) x

/-- Finite support of `weightedOrderOnCompactifiedQuotient` on the compactified modular curve. -/
theorem hasFiniteSupport_weightedOrderOnCompactifiedQuotient
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) :
    (weightedOrderOnCompactifiedQuotient (Γ := Γ) f).HasFiniteSupport := by
  have hsum : HasFiniteSupport
      (weightedOrderOnCompactifiedQuotient (Γ := Γ) f ∘
        (CompactifiedQuotient.equivSum (Γ.map sl2zToPSL2R)).symm) :=
    TauCeti.hasFiniteSupport_sum_type
      (by simpa [Function.comp_def] using
        hasFiniteSupport_weightedOrderOfVanishingOnEffectiveOrbit (Γ := Γ) f)
      (Set.toFinite _)
  refine (hsum.image (CompactifiedQuotient.equivSum (Γ.map sl2zToPSL2R)).symm).subset
    fun x hx ↦ ?_
  exact ⟨CompactifiedQuotient.equivSum _ x,
    by simpa [Function.mem_support] using hx, Equiv.symm_apply_apply _ x⟩

/-- **Single-sum projective valence formula on `(Γ.map sl2zToPSL2R).CompactifiedQuotient`.** -/
theorem valence_formula_compactifiedQuotient
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    (∑ᶠ x : (Γ.map sl2zToPSL2R).CompactifiedQuotient,
        weightedOrderOnCompactifiedQuotient f x) =
      (k : ℚ) * Γ.withCenter.index / 12 := by
  rw [← finsum_comp_equiv (CompactifiedQuotient.equivSum (Γ.map sl2zToPSL2R)).symm,
    TauCeti.finsum_sum_type
      (fun s ↦ weightedOrderOnCompactifiedQuotient f
        ((CompactifiedQuotient.equivSum (Γ.map sl2zToPSL2R)).symm s))
      (by simpa [Function.comp_def] using
        hasFiniteSupport_weightedOrderOfVanishingOnEffectiveOrbit (Γ := Γ) f)
      (Set.toFinite _)]
  simpa using valence_formula_projective f hf

/-- **Single-orbit interior mass bound**: `12 · ord_P(f) ≤ k · [SL(2, ℤ) : ±Γ] · e_P` for any
nonzero modular form `f`. -/
theorem
    twelve_mul_orderOfVanishingOnEffectiveOrbit_le_weight_mul_index_withCenter_mul_cardStabilizer
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (hf : (⇑f : ℍ → ℂ) ≠ 0) (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    12 * orderOfVanishingOnEffectiveOrbit f P ≤
      k * Γ.withCenter.index * cardStabilizerOnOrbit P := by
  have he : (0 : ℚ) < (cardStabilizerOnOrbit P : ℚ) := by
    exact_mod_cast cardStabilizerOnOrbit_effective_pos P
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

/-- **Single-cusp mass bound**: `12 · ord_C(f) ≤ k · [SL(2, ℤ) : ±Γ]` for any nonzero modular
form `f` and geometric cusp orbit `C`. -/
theorem twelve_mul_orderAtCuspOrbit_le_weight_mul_index_withCenter
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (hf : (⇑f : ℍ → ℂ) ≠ 0) (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    12 * orderAtCuspOrbit f C ≤ (k : ℚ) * Γ.withCenter.index := by
  have hinterior : (0 : ℚ) ≤ ∑ᶠ P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ,
      weightedOrderOfVanishingOnEffectiveOrbit f P :=
    finsum_nonneg (weightedOrderOfVanishingOnEffectiveOrbit_nonneg f)
  have hsingle := single_le_finsum C (hasFiniteSupport_orderAtCuspOrbit f)
    (orderAtCuspOrbit_nonneg f)
  have htotal := valence_formula_projective f hf
  linarith

end ValenceFormula

end TauCeti.ModularForm

end
