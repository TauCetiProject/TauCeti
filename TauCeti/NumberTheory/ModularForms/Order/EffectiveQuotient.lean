/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Arithmetic
public import TauCeti.NumberTheory.ModularForms.Norm.Valence
public import TauCeti.NumberTheory.ModularForms.WithCenter

/-!
# Vanishing orders on the interior effective modular quotient

For a subgroup `Γ ≤ SL(2, ℤ)` and its effective image `G = Γ.map sl2zToPSL2R ≤ PSL(2, ℝ)`, the
centre `{±I}` acts trivially on `ℍ`. This file builds the interior geometric order dictionary on
`G \ ℍ` and bridges it to the matrix-group orbit orders of
`TauCeti/NumberTheory/ModularForms/Norm/Valence.lean` without a case split on whether `-I ∈ Γ`:

* `effectiveOrbitEquiv`: the canonical equivalence `(Γ : Subgroup (GL (Fin 2) ℝ)) \ ℍ ≃ G \ ℍ`
  acting as the identity on representatives.
* `card_stabilizer_mapGL_eq_card_center_mul_card_stabilizer_map_sl2zToPSL2R` and
  `relIndex_withCenter_mul_cardStabilizerOnOrbit_eq_two_mul`: pointwise and orbitwise stabiliser
  splitting into `{±I} ∩ Γ` and the projective stabiliser `Stab_G P`, giving
  `[±Γ : Γ] · |Stab_Γ P| = 2 · e_P` (`e_P = |Stab_G P| > 0`) unconditionally.
* `orderOfVanishingOnEffectiveOrbit` and `weightedOrderOfVanishingOnEffectiveOrbit`: the plain
  (`ℤ`-valued) and `1 / e_P`-weighted (`ℚ`-valued) vanishing orders on `G \ ℍ`, together with
  `weightedOrderOfVanishingOnSubgroupOrbit_eq_relIndex_withCenter_mul`, nonnegativity, product
  additivity, and finite support for finite-index `Γ`.

Geometric cusp orders on `G.CuspOrbit` are developed in the companion file
`TauCeti/NumberTheory/ModularForms/Order/CuspOrbit.lean`.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], §§2.3, 3.6.
* [G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*][shimura1971], §2.1.
-/

public noncomputable section

open Matrix.SpecialLinearGroup MulAction Subgroup UpperHalfPlane
open scoped MatrixGroups Modular ModularForm

namespace TauCeti.ModularForm

variable {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]

/-- **The effective-quotient orbit equivalence**: `(Γ : Subgroup (GL (Fin 2) ℝ)) \ ℍ` and
`(Γ.map sl2zToPSL2R) \ ℍ` are canonically in bijection via the identity on representatives, since
`{±I}` acts trivially on `ℍ`. -/
def effectiveOrbitEquiv (Γ : Subgroup SL(2, ℤ)) :
    orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ ≃
      orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ :=
  Quotient.congrRight fun z w ↦ by
    rw [Subgroup.orbitRel_map_sl2zToPSL2R_iff, orbitRel_apply, mem_orbit_iff]
    simp only [Subtype.exists, Subgroup.mem_map]
    constructor
    · rintro ⟨_, ⟨g, hg, rfl⟩, hgw⟩
      exact ⟨g, hg, by simpa [Subgroup.smul_def, MulAction.compHom_smul_def] using hgw⟩
    · rintro ⟨g, hg, hgw⟩
      exact ⟨mapGL ℝ g, ⟨g, hg, rfl⟩,
        by simpa [Subgroup.smul_def, MulAction.compHom_smul_def] using hgw⟩

@[simp]
lemma effectiveOrbitEquiv_mk (p : ℍ) :
    effectiveOrbitEquiv Γ
        (Quotient.mk'' p : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ) =
      Quotient.mk'' p :=
  (rfl)

@[simp]
lemma effectiveOrbitEquiv_symm_mk (p : ℍ) :
    (effectiveOrbitEquiv Γ).symm
        (Quotient.mk'' p : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) =
      Quotient.mk'' p :=
  (rfl)

/-- **Pointwise stabiliser splitting into `{±I} ∩ Γ` and the effective `PSL(2, ℝ)`-stabiliser.** -/
theorem card_stabilizer_mapGL_eq_card_center_mul_card_stabilizer_map_sl2zToPSL2R (z : ℍ) :
    Nat.card (stabilizer (Γ : Subgroup (GL (Fin 2) ℝ)) z) =
      Nat.card ((Subgroup.center SL(2, ℤ)).subgroupOf Γ) *
        Nat.card (stabilizer (Γ.map sl2zToPSL2R) z) := by
  have h1 := TauCeti.card_stabilizer_eq_card_ker_mul_card_stabilizer ((mapGL ℝ).subgroupMap Γ)
    (MonoidHom.subgroupMap_surjective (mapGL ℝ) Γ) z fun g ↦ by
      change mapGL ℝ (g : SL(2, ℤ)) • z = (g : SL(2, ℤ)) • z
      exact (MulAction.compHom_smul_def _ _ _).symm
  have hbot : Nat.card (⊥ : Subgroup Γ) = 1 := Nat.card_unique
  rw [Subgroup.ker_subgroupMap, (mapGL ℝ).ker_eq_bot_iff.mpr mapGL_injective,
    Subgroup.bot_subgroupOf, hbot, one_mul] at h1
  have h2 := TauCeti.card_stabilizer_eq_card_ker_mul_card_stabilizer (sl2zToPSL2R.subgroupMap Γ)
    (MonoidHom.subgroupMap_surjective sl2zToPSL2R Γ) z fun g ↦ by
      change sl2zToPSL2R (g : SL(2, ℤ)) • z = (g : SL(2, ℤ)) • z
      exact sl2zToPSL2R_smul g z
  rw [Subgroup.ker_subgroupMap, sl2zToPSL2R_ker] at h2
  exact h1.symm.trans h2

/-- **Orbitwise stabiliser splitting** between the matrix-group orbit space and the effective
`PSL(2, ℝ)` orbit space. -/
theorem cardStabilizerOnOrbit_eq_card_center_mul_effectiveOrbitEquiv
    (o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    cardStabilizerOnOrbit o =
      Nat.card ((Subgroup.center SL(2, ℤ)).subgroupOf Γ) *
        cardStabilizerOnOrbit (effectiveOrbitEquiv Γ o) := by
  induction o using Quotient.inductionOn' with
  | h z =>
    simpa only [effectiveOrbitEquiv_mk, cardStabilizerOnOrbit_mk] using
      card_stabilizer_mapGL_eq_card_center_mul_card_stabilizer_map_sl2zToPSL2R (Γ := Γ) z

/-- **Unconditional stabiliser / relative-index identity**: `[±Γ : Γ] · |Stab_Γ P| = 2 · e_P` on
every orbit, with no case split on `-I ∈ Γ`. -/
theorem relIndex_withCenter_mul_cardStabilizerOnOrbit_eq_two_mul
    (o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    Γ.relIndex Γ.withCenter * cardStabilizerOnOrbit o =
      2 * cardStabilizerOnOrbit (effectiveOrbitEquiv Γ o) := by
  rw [cardStabilizerOnOrbit_eq_card_center_mul_effectiveOrbitEquiv, ← mul_assoc,
    mul_comm (Γ.relIndex Γ.withCenter), card_center_subgroupOf_mul_relIndex_withCenter]

/-- **Every effective interior orbit has positive stabiliser order `e_P > 0`.** -/
theorem cardStabilizerOnOrbit_effective_pos (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    0 < cardStabilizerOnOrbit P := by
  have h := relIndex_withCenter_mul_cardStabilizerOnOrbit_eq_two_mul
    ((effectiveOrbitEquiv Γ).symm P)
  rw [Equiv.apply_symm_apply] at h
  have hne := cardStabilizerOnOrbit_ne_zero ((effectiveOrbitEquiv Γ).symm P)
  have hr := (relIndex_withCenter_pos Γ).ne'
  exact Nat.pos_of_ne_zero fun h0 ↦ mul_ne_zero hr hne (by rw [h, h0, mul_zero])

theorem cardStabilizerOnOrbit_effective_ne_zero (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    cardStabilizerOnOrbit P ≠ 0 :=
  (cardStabilizerOnOrbit_effective_pos P).ne'

/-- **The plain vanishing order on the effective quotient `(Γ.map sl2zToPSL2R) \ ℍ`.** -/
def orderOfVanishingOnEffectiveOrbit
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) : ℤ :=
  orderOfVanishingOnSubgroupOrbit f ((effectiveOrbitEquiv Γ).symm P)

lemma orderOfVanishingOnEffectiveOrbit_def
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    orderOfVanishingOnEffectiveOrbit f P =
      orderOfVanishingOnSubgroupOrbit f ((effectiveOrbitEquiv Γ).symm P) :=
  (rfl)

@[simp]
lemma orderOfVanishingOnEffectiveOrbit_mk
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (p : ℍ) :
    orderOfVanishingOnEffectiveOrbit f
        (Quotient.mk'' p : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) =
      orderOfVanishingAt f p := by
  rw [orderOfVanishingOnEffectiveOrbit_def, effectiveOrbitEquiv_symm_mk,
    orderOfVanishingOnSubgroupOrbit_mk]

@[simp]
lemma orderOfVanishingOnEffectiveOrbit_effectiveOrbitEquiv
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    orderOfVanishingOnEffectiveOrbit f (effectiveOrbitEquiv Γ o) =
      orderOfVanishingOnSubgroupOrbit f o := by
  rw [orderOfVanishingOnEffectiveOrbit_def, Equiv.symm_apply_apply]

lemma orderOfVanishingOnEffectiveOrbit_nonneg
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    0 ≤ orderOfVanishingOnEffectiveOrbit f P :=
  orderOfVanishingOnSubgroupOrbit_nonneg f _

lemma orderOfVanishingOnEffectiveOrbit_mk_eq_zero_iff
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (p : ℍ) :
    orderOfVanishingOnEffectiveOrbit f
        (Quotient.mk'' p : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) = 0 ↔
      f p ≠ 0 := by
  rw [orderOfVanishingOnEffectiveOrbit_mk]
  exact orderOfVanishingAt_eq_zero_iff (ModularFormClass.holo f) hf

lemma orderOfVanishingOnEffectiveOrbit_mk_pos_iff
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (p : ℍ) :
    0 < orderOfVanishingOnEffectiveOrbit f
        (Quotient.mk'' p : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) ↔
      f p = 0 := by
  rw [orderOfVanishingOnEffectiveOrbit_mk]
  exact orderOfVanishingAt_pos_iff (ModularFormClass.holo f) hf

/-- Additivity of `orderOfVanishingOnEffectiveOrbit` on any form whose underlying function is the
pointwise product of two nonzero modular forms. -/
theorem orderOfVanishingOnEffectiveOrbit_eq_add_of_coe_eq_mul {k₁ k₂ k₃ : ℤ}
    {F₁ F₂ F₃ : Type*} [FunLike F₁ ℍ ℂ] [FunLike F₂ ℍ ℂ] [FunLike F₃ ℍ ℂ]
    [ModularFormClass F₁ (Γ : Subgroup (GL (Fin 2) ℝ)) k₁]
    [ModularFormClass F₂ (Γ : Subgroup (GL (Fin 2) ℝ)) k₂]
    [SlashInvariantFormClass F₃ (Γ : Subgroup (GL (Fin 2) ℝ)) k₃]
    {f : F₁} {g : F₂} {fg : F₃} (hf : (⇑f : ℍ → ℂ) ≠ 0) (hg : (⇑g : ℍ → ℂ) ≠ 0)
    (hfg : (⇑fg : ℍ → ℂ) = ⇑f * ⇑g) (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    orderOfVanishingOnEffectiveOrbit fg P =
      orderOfVanishingOnEffectiveOrbit f P + orderOfVanishingOnEffectiveOrbit g P := by
  induction P using Quotient.inductionOn' with
  | h p =>
    rw [orderOfVanishingOnEffectiveOrbit_mk, orderOfVanishingOnEffectiveOrbit_mk,
      orderOfVanishingOnEffectiveOrbit_mk, hfg]
    exact orderOfVanishingAt_mul (ModularFormClass.holo f) (ModularFormClass.holo g) hf hg p

/-- Additivity of `orderOfVanishingOnEffectiveOrbit` on `ModularForm.mul`. -/
theorem orderOfVanishingOnEffectiveOrbit_mul {k₁ k₂ : ℤ}
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₁)
    (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₂)
    (hf : (⇑f : ℍ → ℂ) ≠ 0) (hg : (⇑g : ℍ → ℂ) ≠ 0)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    orderOfVanishingOnEffectiveOrbit (f.mul g) P =
      orderOfVanishingOnEffectiveOrbit f P + orderOfVanishingOnEffectiveOrbit g P :=
  orderOfVanishingOnEffectiveOrbit_eq_add_of_coe_eq_mul hf hg (_root_.ModularForm.coe_mul f g) P

/-- Finite support of the interior order divisor on the effective quotient. -/
theorem hasFiniteSupport_orderOfVanishingOnEffectiveOrbit [Γ.FiniteIndex]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) :
    (orderOfVanishingOnEffectiveOrbit (Γ := Γ) f).HasFiniteSupport := by
  refine ((hasFiniteSupport_orderOfVanishingOnSubgroupOrbit f).image (effectiveOrbitEquiv Γ)).subset
    fun P hP ↦ ⟨(effectiveOrbitEquiv Γ).symm P, ?_, (effectiveOrbitEquiv Γ).apply_symm_apply P⟩
  simpa [Function.mem_support, orderOfVanishingOnEffectiveOrbit_def] using hP

/-- **The projective weighted vanishing order on `(Γ.map sl2zToPSL2R) \ ℍ`**:
`ord_P(f) / e_P`, where `e_P` is the stabiliser order in `Γ.map sl2zToPSL2R`. -/
def weightedOrderOfVanishingOnEffectiveOrbit
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) : ℚ :=
  (orderOfVanishingOnEffectiveOrbit f P : ℚ) / (cardStabilizerOnOrbit P : ℚ)

lemma weightedOrderOfVanishingOnEffectiveOrbit_def
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    weightedOrderOfVanishingOnEffectiveOrbit f P =
      (orderOfVanishingOnEffectiveOrbit f P : ℚ) / (cardStabilizerOnOrbit P : ℚ) :=
  (rfl)

@[simp]
lemma weightedOrderOfVanishingOnEffectiveOrbit_mk
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (p : ℍ) :
    weightedOrderOfVanishingOnEffectiveOrbit f
        (Quotient.mk'' p : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) =
      (orderOfVanishingAt ⇑f p : ℚ) / (Nat.card (stabilizer (Γ.map sl2zToPSL2R) p) : ℚ) := by
  rw [weightedOrderOfVanishingOnEffectiveOrbit_def, orderOfVanishingOnEffectiveOrbit_mk,
    cardStabilizerOnOrbit_mk]

lemma cardStabilizerOnOrbit_mul_weightedOrderOfVanishingOnEffectiveOrbit
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    (cardStabilizerOnOrbit P : ℚ) * weightedOrderOfVanishingOnEffectiveOrbit f P =
      (orderOfVanishingOnEffectiveOrbit f P : ℚ) := by
  rw [weightedOrderOfVanishingOnEffectiveOrbit_def]
  exact mul_div_cancel₀ _ (by exact_mod_cast cardStabilizerOnOrbit_effective_ne_zero P)

/-- **Full-coset vs projective interior weight**: the matrix-stabiliser weight
`2 · ord_P(f) / |Stab_Γ P|` equals `[±Γ : Γ] · (ord_P(f) / e_P)` on every orbit. -/
theorem weightedOrderOfVanishingOnSubgroupOrbit_eq_relIndex_withCenter_mul
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    weightedOrderOfVanishingOnSubgroupOrbit f o =
      (Γ.relIndex Γ.withCenter : ℚ) *
        weightedOrderOfVanishingOnEffectiveOrbit f (effectiveOrbitEquiv Γ o) := by
  have hstab : (Γ.relIndex Γ.withCenter : ℚ) * (cardStabilizerOnOrbit o : ℚ) =
      2 * (cardStabilizerOnOrbit (effectiveOrbitEquiv Γ o) : ℚ) := by
    exact_mod_cast relIndex_withCenter_mul_cardStabilizerOnOrbit_eq_two_mul o
  have hc₁ : (cardStabilizerOnOrbit o : ℚ) ≠ 0 := by
    exact_mod_cast cardStabilizerOnOrbit_ne_zero o
  have hc₂ : (cardStabilizerOnOrbit (effectiveOrbitEquiv Γ o) : ℚ) ≠ 0 := by
    exact_mod_cast cardStabilizerOnOrbit_effective_ne_zero (effectiveOrbitEquiv Γ o)
  rw [weightedOrderOfVanishingOnSubgroupOrbit_def, weightedOrderOfVanishingOnEffectiveOrbit_def,
    orderOfVanishingOnEffectiveOrbit_effectiveOrbitEquiv]
  field_simp
  linear_combination -(orderOfVanishingOnSubgroupOrbit f o : ℚ) * hstab

lemma weightedOrderOfVanishingOnEffectiveOrbit_nonneg
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    0 ≤ weightedOrderOfVanishingOnEffectiveOrbit f P := by
  rw [weightedOrderOfVanishingOnEffectiveOrbit_def]
  exact div_nonneg (by exact_mod_cast orderOfVanishingOnEffectiveOrbit_nonneg f P) (by positivity)

theorem weightedOrderOfVanishingOnEffectiveOrbit_eq_add_of_coe_eq_mul {k₁ k₂ k₃ : ℤ}
    {F₁ F₂ F₃ : Type*} [FunLike F₁ ℍ ℂ] [FunLike F₂ ℍ ℂ] [FunLike F₃ ℍ ℂ]
    [ModularFormClass F₁ (Γ : Subgroup (GL (Fin 2) ℝ)) k₁]
    [ModularFormClass F₂ (Γ : Subgroup (GL (Fin 2) ℝ)) k₂]
    [SlashInvariantFormClass F₃ (Γ : Subgroup (GL (Fin 2) ℝ)) k₃]
    {f : F₁} {g : F₂} {fg : F₃} (hf : (⇑f : ℍ → ℂ) ≠ 0) (hg : (⇑g : ℍ → ℂ) ≠ 0)
    (hfg : (⇑fg : ℍ → ℂ) = ⇑f * ⇑g) (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    weightedOrderOfVanishingOnEffectiveOrbit fg P =
      weightedOrderOfVanishingOnEffectiveOrbit f P +
        weightedOrderOfVanishingOnEffectiveOrbit g P := by
  rw [weightedOrderOfVanishingOnEffectiveOrbit_def, weightedOrderOfVanishingOnEffectiveOrbit_def,
    weightedOrderOfVanishingOnEffectiveOrbit_def,
    orderOfVanishingOnEffectiveOrbit_eq_add_of_coe_eq_mul hf hg hfg P]
  push_cast
  ring

theorem weightedOrderOfVanishingOnEffectiveOrbit_mul {k₁ k₂ : ℤ}
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₁)
    (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₂)
    (hf : (⇑f : ℍ → ℂ) ≠ 0) (hg : (⇑g : ℍ → ℂ) ≠ 0)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    weightedOrderOfVanishingOnEffectiveOrbit (f.mul g) P =
      weightedOrderOfVanishingOnEffectiveOrbit f P +
        weightedOrderOfVanishingOnEffectiveOrbit g P :=
  weightedOrderOfVanishingOnEffectiveOrbit_eq_add_of_coe_eq_mul hf hg
    (_root_.ModularForm.coe_mul f g) P

theorem hasFiniteSupport_weightedOrderOfVanishingOnEffectiveOrbit [Γ.FiniteIndex]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) :
    (weightedOrderOfVanishingOnEffectiveOrbit (Γ := Γ) f).HasFiniteSupport := by
  refine (hasFiniteSupport_orderOfVanishingOnEffectiveOrbit f).subset fun P hP ↦ ?_
  simp only [Function.mem_support, ne_eq] at hP ⊢
  exact fun h0 ↦ hP (by rw [weightedOrderOfVanishingOnEffectiveOrbit_def, h0]; simp)

end TauCeti.ModularForm

end
