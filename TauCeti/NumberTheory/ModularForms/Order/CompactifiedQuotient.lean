/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Order.CuspOrbits
public import TauCeti.NumberTheory.ModularForms.Order.EffectiveOrbits
import Mathlib.Algebra.FiniteSupport.Basic
import TauCeti.Algebra.BigOperators.Finprod

/-!
# Vanishing orders on the compactified quotient `X(Γ)`

For `Γ ≤ SL(2, ℤ)`, this file defines the unified geometric vanishing order
`orderOnCompactifiedQuotient` and weighted geometric order `weightedOrderOnCompactifiedQuotient` on
`(Γ.map sl2zToPSL2R).CompactifiedQuotient`, uniting `orderOfVanishingOnEffectiveOrbit` on interior
orbits with `orderAtCuspOrbit` at cusps. It records basic properties (nonnegativity, scalar
invariance, zero/positivity characterization), finite support, decomposition of the divisor sum into
interior and cusp sums (`finsum_weightedOrderOnCompactifiedQuotient_eq_add`), and additivity on
products.

## Main definitions

* `TauCeti.ModularForm.orderOnCompactifiedQuotient`: geometric vanishing order on
  `(Γ.map sl2zToPSL2R).CompactifiedQuotient`.
* `TauCeti.ModularForm.weightedOrderOnCompactifiedQuotient`: weighted geometric order
  `ord_x f / e_x` on `(Γ.map sl2zToPSL2R).CompactifiedQuotient`.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], §§3.2–3.3.
-/

public noncomputable section

open Filter Function Matrix Matrix.SpecialLinearGroup MulAction UpperHalfPlane
open scoped MatrixGroups ModularForm Pointwise

namespace TauCeti.ModularForm

variable {Γ : Subgroup SL(2, ℤ)} {k k₁ k₂ : ℤ}
variable {F F₁ F₂ F₃ : Type*} [FunLike F ℍ ℂ] [FunLike F₁ ℍ ℂ] [FunLike F₂ ℍ ℂ] [FunLike F₃ ℍ ℂ]

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
  exact (hg.preimage e.injective.injOn).subset fun x hx ↦ by simpa [e] using hx

/-- Only finitely many points of the compactified quotient carry nonzero weighted order. -/
theorem hasFiniteSupport_weightedOrderOnCompactifiedQuotient (f : F) :
    Function.HasFiniteSupport (weightedOrderOnCompactifiedQuotient (Γ := Γ) (k := k) f) := by
  change Function.HasFiniteSupport fun x ↦ weightedOrderOnCompactifiedQuotient (Γ := Γ) (k := k) f x
  simpa only [weightedOrderOnCompactifiedQuotient_def, div_eq_mul_inv] using
    (hasFiniteSupport_orderOnCompactifiedQuotient f).fun_mul_left _

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
