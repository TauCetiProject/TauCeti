/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
public import TauCeti.NumberTheory.ModularForms.Order.SubgroupOrbits
import Mathlib.Algebra.FiniteSupport.Basic
import TauCeti.Analysis.Complex.Fuchsian.ProperAction
import TauCeti.Topology.Algebra.ConstMulAction
import TauCeti.Topology.Algebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# Vanishing orders on the effective quotient `Γ \ ℍ`

For `Γ ≤ SL(2, ℤ)`, `(Γ : Subgroup (GL (Fin 2) ℝ))` and `Γ.map sl2zToPSL2R ≤ PSL(2, ℝ)` share
orbits on `ℍ`, with stabilisers differing by `{±I} ∩ Γ`. Since `[±Γ : Γ] · |{±I} ∩ Γ| = 2`, the
projective weighted order `ord_P f / e_P` on `(Γ.map sl2zToPSL2R) \ ℍ` divides the matrix weighted
order `2 · ord_P f / |Stab_Γ P|` by `[±Γ : Γ]`.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], §§3.2–3.3.
-/

public noncomputable section

open MulAction UpperHalfPlane
open scoped MatrixGroups ModularForm Modular

namespace TauCeti.ModularForm

variable {Γ : Subgroup SL(2, ℤ)} {k k₁ k₂ k₃ : ℤ}
variable {F F₁ F₂ F₃ : Type*} [FunLike F ℍ ℂ] [FunLike F₁ ℍ ℂ] [FunLike F₂ ℍ ℂ] [FunLike F₃ ℍ ℂ]

section Slash

variable [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]

/-- The vanishing order of a slash-invariant form on `Γ`, descended to `(Γ.map sl2zToPSL2R) \ ℍ`. -/
def orderOfVanishingOnEffectiveOrbit (f : F) (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) : ℤ :=
  orderOfVanishingOnSubgroupOrbit f (Γ.subgroupOrbitEquivEffectiveOrbit.symm P)

/-- Unfolding `orderOfVanishingOnEffectiveOrbit` across module boundaries. -/
theorem orderOfVanishingOnEffectiveOrbit_def (f : F) (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    orderOfVanishingOnEffectiveOrbit f P =
      orderOfVanishingOnSubgroupOrbit f (Γ.subgroupOrbitEquivEffectiveOrbit.symm P) := (rfl)

/-- Evaluating `orderOfVanishingOnEffectiveOrbit` on the orbit of `z` gives `orderOfVanishingAt`. -/
@[simp]
theorem orderOfVanishingOnEffectiveOrbit_mk (f : F) (z : ℍ) :
    orderOfVanishingOnEffectiveOrbit f
        (Quotient.mk'' z : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) = orderOfVanishingAt f z := by
  simp [orderOfVanishingOnEffectiveOrbit_def]

/-- Transporting a matrix orbit along `subgroupOrbitEquivEffectiveOrbit` preserves its order. -/
@[simp]
theorem orderOfVanishingOnEffectiveOrbit_subgroupOrbitEquivEffectiveOrbit (f : F)
    (o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    orderOfVanishingOnEffectiveOrbit f (Γ.subgroupOrbitEquivEffectiveOrbit o) =
      orderOfVanishingOnSubgroupOrbit f o := by
  rw [orderOfVanishingOnEffectiveOrbit_def, Equiv.symm_apply_apply]

/-- The zero form has vanishing order `0` on every effective orbit. -/
@[simp]
theorem orderOfVanishingOnEffectiveOrbit_zero [Zero F] [IsZeroApply F]
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    orderOfVanishingOnEffectiveOrbit (0 : F) P = 0 :=
  Quotient.inductionOn' P fun _ ↦ by simp [FunLike.coe_zero]

/-- Nonzero complex scalar multiples have the same vanishing order on each effective orbit. -/
@[simp]
theorem orderOfVanishingOnEffectiveOrbit_smul [SMul ℂ F] [IsSMulApply ℂ F] {c : ℂ} (hc : c ≠ 0)
    (f : F) (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    orderOfVanishingOnEffectiveOrbit (c • f) P = orderOfVanishingOnEffectiveOrbit f P :=
  Quotient.inductionOn' P fun _ ↦ by simp [FunLike.coe_smul, hc]

/-- **Projective weighted vanishing order on an effective orbit**: `ord_P f / e_P`. -/
def weightedOrderOfVanishingOnEffectiveOrbit (f : F) (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    ℚ := (orderOfVanishingOnEffectiveOrbit f P : ℚ) / (cardStabilizerOnOrbit P : ℚ)

/-- Unfolding `weightedOrderOfVanishingOnEffectiveOrbit` across module boundaries. -/
theorem weightedOrderOfVanishingOnEffectiveOrbit_def (f : F)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) : weightedOrderOfVanishingOnEffectiveOrbit f P =
      (orderOfVanishingOnEffectiveOrbit f P : ℚ) / (cardStabilizerOnOrbit P : ℚ) := (rfl)

/-- Evaluating `weightedOrderOfVanishingOnEffectiveOrbit` on the orbit of `z`. -/
@[simp]
theorem weightedOrderOfVanishingOnEffectiveOrbit_mk (f : F) (z : ℍ) :
    weightedOrderOfVanishingOnEffectiveOrbit f
        (Quotient.mk'' z : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) =
      (orderOfVanishingAt ⇑f z : ℚ) / (Nat.card (stabilizer (Γ.map sl2zToPSL2R) z) : ℚ) := by
  simp [weightedOrderOfVanishingOnEffectiveOrbit_def, cardStabilizerOnOrbit_mk]

/-- Multiplying the projective weighted order by `e_P` recovers the plain vanishing order on `P`. -/
theorem cardStabilizerOnOrbit_mul_weightedOrderOfVanishingOnEffectiveOrbit (f : F)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    (cardStabilizerOnOrbit P : ℚ) * weightedOrderOfVanishingOnEffectiveOrbit f P =
      (orderOfVanishingOnEffectiveOrbit f P : ℚ) :=
  mul_div_cancel₀ _ (by exact_mod_cast TauCeti.cardStabilizerOnOrbit_ne_zero P)

/-- The zero form has projective weighted vanishing order `0` on every effective orbit. -/
@[simp]
theorem weightedOrderOfVanishingOnEffectiveOrbit_zero [Zero F] [IsZeroApply F]
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    weightedOrderOfVanishingOnEffectiveOrbit (0 : F) P = 0 := by
  simp [weightedOrderOfVanishingOnEffectiveOrbit_def]

/-- Nonzero complex scalar multiples have the same projective weighted order. -/
@[simp]
theorem weightedOrderOfVanishingOnEffectiveOrbit_smul [SMul ℂ F] [IsSMulApply ℂ F] {c : ℂ}
    (hc : c ≠ 0) (f : F) (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    weightedOrderOfVanishingOnEffectiveOrbit (c • f) P =
      weightedOrderOfVanishingOnEffectiveOrbit f P := by
  simp [weightedOrderOfVanishingOnEffectiveOrbit_def, hc]

/-- **Local comparison**: `2 · ord f / |Stab_Γ o| = [±Γ : Γ] · (ord f / e_P)`. -/
theorem weightedOrderOfVanishingOnSubgroupOrbit_eq_relIndex_withCenter_mul (f : F)
    (o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    weightedOrderOfVanishingOnSubgroupOrbit f o =
      (Γ.relIndex Γ.withCenter : ℚ) *
        weightedOrderOfVanishingOnEffectiveOrbit f (Γ.subgroupOrbitEquivEffectiveOrbit o) := by
  have he : (cardStabilizerOnOrbit (Γ.subgroupOrbitEquivEffectiveOrbit o) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (TauCeti.cardStabilizerOnOrbit_ne_zero _)
  have hstab : (cardStabilizerOnOrbit o : ℚ) =
      Nat.card ((Subgroup.center SL(2, ℤ)).subgroupOf Γ) *
        cardStabilizerOnOrbit (Γ.subgroupOrbitEquivEffectiveOrbit o) := by
    exact_mod_cast TauCeti.ModularGroup.cardStabilizerOnOrbit_eq_card_center_mul_effective o
  have hprod : (Γ.relIndex Γ.withCenter : ℚ) *
      Nat.card ((Subgroup.center SL(2, ℤ)).subgroupOf Γ) = 2 := by
    exact_mod_cast Γ.relIndex_withCenter_mul_card_center_subgroupOf_eq_two
  have hcz := right_ne_zero_of_mul (hprod.symm ▸ two_ne_zero)
  rw [weightedOrderOfVanishingOnSubgroupOrbit_def, weightedOrderOfVanishingOnEffectiveOrbit_def,
    orderOfVanishingOnEffectiveOrbit_subgroupOrbitEquivEffectiveOrbit, hstab, ← hprod]
  field_simp

/-- **Global comparison**: the matrix interior sum is `[±Γ : Γ]` times the projective sum. -/
theorem finsum_weightedOrderOfVanishingOnSubgroupOrbit_eq_relIndex_withCenter_mul (f : F) :
    (∑ᶠ o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ,
        weightedOrderOfVanishingOnSubgroupOrbit f o) =
      (Γ.relIndex Γ.withCenter : ℚ) *
        ∑ᶠ P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ,
          weightedOrderOfVanishingOnEffectiveOrbit f P := by
  simp_rw [weightedOrderOfVanishingOnSubgroupOrbit_eq_relIndex_withCenter_mul f]
  rw [← finsum_comp_equiv Γ.subgroupOrbitEquivEffectiveOrbit, mul_finsum]

end Slash

section Modular

variable [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]

/-- The vanishing order of a modular form on an effective orbit is nonnegative. -/
theorem orderOfVanishingOnEffectiveOrbit_nonneg (f : F)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) : 0 ≤ orderOfVanishingOnEffectiveOrbit f P :=
  orderOfVanishingOnSubgroupOrbit_nonneg f _

/-- The projective weighted vanishing order of a modular form is nonnegative. -/
theorem weightedOrderOfVanishingOnEffectiveOrbit_nonneg (f : F)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    0 ≤ weightedOrderOfVanishingOnEffectiveOrbit f P :=
  div_nonneg (by exact_mod_cast orderOfVanishingOnEffectiveOrbit_nonneg f P) (by positivity)

/-- For nonzero modular `f`, vanishing order on `P` is `0` iff `f` is nonvanishing on `P`. -/
theorem orderOfVanishingOnEffectiveOrbit_eq_zero_iff {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    orderOfVanishingOnEffectiveOrbit f P = 0 ↔
      ∀ z : ℍ, (Quotient.mk'' z : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) = P → f z ≠ 0 := by
  induction P using Quotient.inductionOn' with | h z₀ =>
    have hiff (z : ℍ) := orderOfVanishingAt_eq_zero_iff (ModularFormClass.holo f) hf (z := z)
    rw [orderOfVanishingOnEffectiveOrbit_mk, hiff]
    refine ⟨fun hz₀ z hz ↦ (hiff z).mp ?_, fun h ↦ h z₀ rfl⟩
    rw [← orderOfVanishingOnEffectiveOrbit_mk (Γ := Γ), hz, orderOfVanishingOnEffectiveOrbit_mk]
    exact (hiff z₀).mpr hz₀

/-- For nonzero modular `f`, vanishing order on `P` is positive iff `f` vanishes at some `z ∈ P`. -/
theorem orderOfVanishingOnEffectiveOrbit_pos_iff {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    0 < orderOfVanishingOnEffectiveOrbit f P ↔
      ∃ z : ℍ, (Quotient.mk'' z : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) = P ∧ f z = 0 := by
  rw [(orderOfVanishingOnEffectiveOrbit_nonneg f P).lt_iff_ne, ne_comm]
  simpa only [not_forall, Classical.not_not, exists_prop] using
    (orderOfVanishingOnEffectiveOrbit_eq_zero_iff hf P).not

/-- A modular form on finite-index `Γ` has nonzero vanishing order on finitely many orbits. -/
theorem hasFiniteSupport_orderOfVanishingOnEffectiveOrbit [Γ.FiniteIndex] (f : F) :
    Function.HasFiniteSupport (orderOfVanishingOnEffectiveOrbit (Γ := Γ) (k := k) f) :=
  (hasFiniteSupport_orderOfVanishingOnSubgroupOrbit f).preimage
    Γ.subgroupOrbitEquivEffectiveOrbit.symm.injective.injOn

/-- Only finitely many effective orbits carry nonzero projective weighted order. -/
theorem hasFiniteSupport_weightedOrderOfVanishingOnEffectiveOrbit [Γ.FiniteIndex] (f : F) :
    Function.HasFiniteSupport (weightedOrderOfVanishingOnEffectiveOrbit (Γ := Γ) (k := k) f) := by
  change Function.HasFiniteSupport fun P ↦
    weightedOrderOfVanishingOnEffectiveOrbit (Γ := Γ) (k := k) f P
  simpa only [weightedOrderOfVanishingOnEffectiveOrbit_def, div_eq_mul_inv] using
    ((hasFiniteSupport_orderOfVanishingOnEffectiveOrbit f).of_eq_zero_iff fun _ ↦
      Int.cast_eq_zero.symm).fun_mul_left _

end Modular

section Mul

variable [ModularFormClass F₁ (Γ : Subgroup (GL (Fin 2) ℝ)) k₁]
  [ModularFormClass F₂ (Γ : Subgroup (GL (Fin 2) ℝ)) k₂]
  [SlashInvariantFormClass F₃ (Γ : Subgroup (GL (Fin 2) ℝ)) k₃]

/-- **Additivity on products (`ModularFormClass` form)** on effective orbits. -/
theorem orderOfVanishingOnEffectiveOrbit_eq_add_of_coe_eq_mul (f : F₁) (g : F₂) (fg : F₃)
    (hfg : ⇑fg = ⇑f * ⇑g) (hf : (⇑f : ℍ → ℂ) ≠ 0) (hg : (⇑g : ℍ → ℂ) ≠ 0)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    orderOfVanishingOnEffectiveOrbit fg P =
      orderOfVanishingOnEffectiveOrbit f P + orderOfVanishingOnEffectiveOrbit g P :=
  Quotient.inductionOn' P fun z ↦ by
    simpa [hfg] using orderOfVanishingAt_mul (ModularFormClass.holo f) (ModularFormClass.holo g)
      hf hg z

/-- Additivity of the projective weighted order on products (`ModularFormClass` form). -/
theorem weightedOrderOfVanishingOnEffectiveOrbit_eq_add_of_coe_eq_mul (f : F₁) (g : F₂) (fg : F₃)
    (hfg : ⇑fg = ⇑f * ⇑g) (hf : (⇑f : ℍ → ℂ) ≠ 0) (hg : (⇑g : ℍ → ℂ) ≠ 0)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    weightedOrderOfVanishingOnEffectiveOrbit fg P =
      weightedOrderOfVanishingOnEffectiveOrbit f P +
        weightedOrderOfVanishingOnEffectiveOrbit g P := by
  simp only [weightedOrderOfVanishingOnEffectiveOrbit_def,
    orderOfVanishingOnEffectiveOrbit_eq_add_of_coe_eq_mul f g fg hfg hf hg P, Int.cast_add, add_div]

end Mul

/-- Additivity of `orderOfVanishingOnEffectiveOrbit` on products of nonzero modular forms. -/
theorem _root_.ModularForm.orderOfVanishingOnEffectiveOrbit_mul
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₁)
    (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₂) (hf : f ≠ 0) (hg : g ≠ 0)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    orderOfVanishingOnEffectiveOrbit (f.mul g) P =
      orderOfVanishingOnEffectiveOrbit f P + orderOfVanishingOnEffectiveOrbit g P :=
  orderOfVanishingOnEffectiveOrbit_eq_add_of_coe_eq_mul f g (f.mul g)
    (_root_.ModularForm.coe_mul f g) (FunLike.coe_zero_iff.not.mpr hf)
    (FunLike.coe_zero_iff.not.mpr hg) P

/-- Additivity of the projective weighted order on products of nonzero modular forms. -/
theorem _root_.ModularForm.weightedOrderOfVanishingOnEffectiveOrbit_mul
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₁)
    (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₂) (hf : f ≠ 0) (hg : g ≠ 0)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    weightedOrderOfVanishingOnEffectiveOrbit (f.mul g) P =
      weightedOrderOfVanishingOnEffectiveOrbit f P +
        weightedOrderOfVanishingOnEffectiveOrbit g P := by
  simp only [weightedOrderOfVanishingOnEffectiveOrbit_def,
    _root_.ModularForm.orderOfVanishingOnEffectiveOrbit_mul f g hf hg P, Int.cast_add, add_div]

end TauCeti.ModularForm

end
