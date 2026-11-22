/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.Colon
public import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Colon
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.FinitePresentation

/-!
# Cartier separation

Let `X` be an arbitrary scheme and `D₁`, `D₂` be two effective Cartier divisors on `X`, represented
as `Scheme.IdealSheafData` satisfying `IsEffectiveCartier`. Blowing up the sum ideal sheaf
`I = D₁ ⊔ D₂` yields a proper morphism `p : Bl_{D₁ ⊔ D₂} X ⟶ X`
(`IsEffectiveCartier.isProper_blowupToBase_sup`),
which is an isomorphism away from `V(D₁) ∩ V(D₂)`, together with its invertible exceptional divisor
`F = (D₁ ⊔ D₂).comap p`.

Because `F` is always an effective Cartier divisor on `Bl_{D₁ ⊔ D₂} X`, the residual ideal sheaves
`D'₁ = (D₁.comap p : F)` (`blowupSupResidualLeft`) and `D'₂ = (D₂.comap p : F)`
(`blowupSupResidualRight`) are defined for arbitrary ideal sheaves `D₁` and `D₂` and satisfy:

* `F * D'₁ = D₁.comap p` and `F * D'₂ = D₂.comap p` (`p* Dᵢ = F + D'ᵢ`),
* `K ≤ D'ᵢ ↔ K * F ≤ p* Dᵢ` (`le_blowupSupResidualLeft_iff`, `le_blowupSupResidualRight_iff`),
* `D'₁ ⊔ D'₂ = ⊤`, equivalently `Disjoint D'₁.support D'₂.support`,
* `D₁.comap p * D'₂ = D₂.comap p * D'₁` (`p* D₁ + D'₂ = p* D₂ + D'₁`).

When `D₁` and `D₂` are effective Cartier divisors, so are `D'₁` and `D'₂`, and their line-bundle
classes satisfy `[D'₁] * [D'₂]⁻¹ = p* ([D₁] * [D₂]⁻¹)` in the Picard group. Locally on an affine
open `U` where `D₁(U) = (x₁)` and `D₂(U) = (x₂)`, the residual ideals on the chart
`Spec Γ(X, U)[(x₁, x₂)/x₁]` are `(1)` and `(x₂ / x₁)` (and symmetrically on the `x₂`-chart).

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.blowupSupResidualLeft`,
  `AlgebraicGeometry.Scheme.IdealSheafData.blowupSupResidualRight`: the residual ideal sheaves
  `D'₁ = (p* D₁ : F)` and `D'₂ = (p* D₂ : F)` on `Bl_{D₁ ⊔ D₂} X`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.comap_blowupToBase_sup_mul_blowupSupResidualLeft`,
  `AlgebraicGeometry.Scheme.IdealSheafData.comap_blowupToBase_sup_mul_blowupSupResidualRight`:
  `F * D'ᵢ = p* Dᵢ`.
* `AlgebraicGeometry.Scheme.IdealSheafData.le_blowupSupResidualLeft_iff`,
  `AlgebraicGeometry.Scheme.IdealSheafData.le_blowupSupResidualRight_iff`: universal property
  `K ≤ D'ᵢ ↔ K * F ≤ p* Dᵢ`.
* `AlgebraicGeometry.Scheme.IdealSheafData.blowupSupResidualLeft_sup_right`,
  `AlgebraicGeometry.Scheme.IdealSheafData.disjoint_support_blowupSupResidual`: `D'₁ ⊔ D'₂ = ⊤`
  and `D'₁`, `D'₂` have disjoint supports.
* `AlgebraicGeometry.Scheme.IdealSheafData.comap_mul_blowupSupResidualRight_eq`:
  `p* D₁ * D'₂ = p* D₂ * D'₁`.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier.blowupSupResidualLeft`,
  `AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier.blowupSupResidualRight`:
  the residual ideal sheaves of effective Cartier divisors are effective Cartier.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier.isProper_blowupToBase_sup`,
  `AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier.isIso_blowupToBase_sup_of_le`:
  properness of `Bl_{D₁ ⊔ D₂} X ⟶ X` and triviality when `D₂ ≤ D₁`.
* `TauCeti.AlgebraicGeometry.LineBundleClass.mk_toInvertibleSheaf_blowupSupResidual_mul_inv`:
  `[D'₁] * [D'₂]⁻¹ = p* ([D₁] * [D₂]⁻¹)`.

## References

* G. Boxer and V. Pilloni, *Higher Hida theory for Siegel modular forms*, §4.1.10,
  Proposition-construction 4.1.11, p. 42.
* [The Stacks Project, Section 31.32 / Tag 01OF](https://stacks.math.columbia.edu/tag/01OF):
  blowing up along a quasi-coherent sheaf of ideals.
-/

public section

noncomputable section

open CategoryTheory Opposite TopologicalSpace reesAlgebra

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

open TauCeti.AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The blowup of the sum of two effective Cartier divisors is proper over `X`, without any
Noetherian assumption. -/
theorem IsEffectiveCartier.isProper_blowupToBase_sup {D₁ D₂ : X.IdealSheafData}
    (hD₁ : D₁.IsEffectiveCartier) (hD₂ : D₂.IsEffectiveCartier) :
    IsProper (D₁ ⊔ D₂).blowupToBase :=
  (D₁ ⊔ D₂).isProper_blowupToBase fun U ↦ Submodule.FG.sup (hD₁.fg_ideal U) (hD₂.fg_ideal U)

/-- If `D₁` is effective Cartier and `D₂ ≤ D₁`, the blowup along `D₁ ⊔ D₂ = D₁` is an
isomorphism. -/
theorem IsEffectiveCartier.isIso_blowupToBase_sup_of_le {D₁ D₂ : X.IdealSheafData}
    (hD₁ : D₁.IsEffectiveCartier) (h : D₂ ≤ D₁) : IsIso (D₁ ⊔ D₂).blowupToBase := by
  rw [isIso_blowupToBase_iff, sup_eq_left.mpr h]
  exact hD₁

/-- The **left residual ideal sheaf** `D'₁ = (p* D₁ : F)` on the blowup `Bl_{D₁ ⊔ D₂} X`, where
`p = (D₁ ⊔ D₂).blowupToBase` and `F = (D₁ ⊔ D₂).comap p` is the invertible exceptional divisor.
When `D₁` and `D₂` are effective Cartier divisors, `D'₁` is the effective Cartier divisor
`p* D₁ - F`. -/
def blowupSupResidualLeft (D₁ D₂ : X.IdealSheafData) : (D₁ ⊔ D₂).blowup.IdealSheafData :=
  (D₁.comap (D₁ ⊔ D₂).blowupToBase).colon ((D₁ ⊔ D₂).comap (D₁ ⊔ D₂).blowupToBase)

/-- The **right residual ideal sheaf** `D'₂ = (p* D₂ : F)` on the blowup `Bl_{D₁ ⊔ D₂} X`, where
`p = (D₁ ⊔ D₂).blowupToBase` and `F = (D₁ ⊔ D₂).comap p` is the invertible exceptional divisor.
When `D₁` and `D₂` are effective Cartier divisors, `D'₂` is the effective Cartier divisor
`p* D₂ - F`. -/
def blowupSupResidualRight (D₁ D₂ : X.IdealSheafData) : (D₁ ⊔ D₂).blowup.IdealSheafData :=
  (D₂.comap (D₁ ⊔ D₂).blowupToBase).colon ((D₁ ⊔ D₂).comap (D₁ ⊔ D₂).blowupToBase)

/-- Definitional unfolding of `blowupSupResidualLeft`. -/
theorem blowupSupResidualLeft_def (D₁ D₂ : X.IdealSheafData) :
    D₁.blowupSupResidualLeft D₂ =
      (D₁.comap (D₁ ⊔ D₂).blowupToBase).colon ((D₁ ⊔ D₂).comap (D₁ ⊔ D₂).blowupToBase) :=
  (rfl)

/-- Definitional unfolding of `blowupSupResidualRight`. -/
theorem blowupSupResidualRight_def (D₁ D₂ : X.IdealSheafData) :
    D₁.blowupSupResidualRight D₂ =
      (D₂.comap (D₁ ⊔ D₂).blowupToBase).colon ((D₁ ⊔ D₂).comap (D₁ ⊔ D₂).blowupToBase) :=
  (rfl)

/-- **Universal property of `blowupSupResidualLeft`.** An ideal sheaf `K` on `Bl_{D₁ ⊔ D₂} X` is
contained in `D'₁` exactly when `K * F ≤ p* D₁`. -/
theorem le_blowupSupResidualLeft_iff (D₁ D₂ : X.IdealSheafData)
    (K : (D₁ ⊔ D₂).blowup.IdealSheafData) :
    K ≤ D₁.blowupSupResidualLeft D₂ ↔
      K * (D₁ ⊔ D₂).comap (D₁ ⊔ D₂).blowupToBase ≤ D₁.comap (D₁ ⊔ D₂).blowupToBase :=
  le_colon_iff

/-- **Universal property of `blowupSupResidualRight`.** An ideal sheaf `K` on `Bl_{D₁ ⊔ D₂} X` is
contained in `D'₂` exactly when `K * F ≤ p* D₂`. -/
theorem le_blowupSupResidualRight_iff (D₁ D₂ : X.IdealSheafData)
    (K : (D₁ ⊔ D₂).blowup.IdealSheafData) :
    K ≤ D₁.blowupSupResidualRight D₂ ↔
      K * (D₁ ⊔ D₂).comap (D₁ ⊔ D₂).blowupToBase ≤ D₂.comap (D₁ ⊔ D₂).blowupToBase :=
  le_colon_iff

/-- **Left factorization `p* D₁ = F + D'₁`.** On `Bl_{D₁ ⊔ D₂} X`, the product of the exceptional
ideal `F` with the left residual ideal `D'₁` is the pulled-back ideal `p* D₁`. -/
@[simp]
theorem comap_blowupToBase_sup_mul_blowupSupResidualLeft (D₁ D₂ : X.IdealSheafData) :
    (D₁.comap (D₁ ⊔ D₂).blowupToBase ⊔ D₂.comap (D₁ ⊔ D₂).blowupToBase) *
        D₁.blowupSupResidualLeft D₂ =
      D₁.comap (D₁ ⊔ D₂).blowupToBase :=
  (congrArg (· * _)
    (comap_sup (J₁ := D₁) (J₂ := D₂) (f := (D₁ ⊔ D₂).blowupToBase)).symm).trans
    ((mul_comm _ _).trans
      ((D₁.comap (D₁ ⊔ D₂).blowupToBase).eq_colon_mul ((D₁ ⊔ D₂).comap (D₁ ⊔ D₂).blowupToBase)
        (D₁ ⊔ D₂).isEffectiveCartier_comap_blowupToBase.locallyPrincipal
        (comap_mono _ le_sup_left)).symm)

/-- **Right factorization `p* D₂ = F + D'₂`.** On `Bl_{D₁ ⊔ D₂} X`, the product of the exceptional
ideal `F` with the right residual ideal `D'₂` is the pulled-back ideal `p* D₂`. -/
@[simp]
theorem comap_blowupToBase_sup_mul_blowupSupResidualRight (D₁ D₂ : X.IdealSheafData) :
    (D₁.comap (D₁ ⊔ D₂).blowupToBase ⊔ D₂.comap (D₁ ⊔ D₂).blowupToBase) *
        D₁.blowupSupResidualRight D₂ =
      D₂.comap (D₁ ⊔ D₂).blowupToBase :=
  (congrArg (· * _)
    (comap_sup (J₁ := D₁) (J₂ := D₂) (f := (D₁ ⊔ D₂).blowupToBase)).symm).trans
    ((mul_comm _ _).trans
      ((D₂.comap (D₁ ⊔ D₂).blowupToBase).eq_colon_mul ((D₁ ⊔ D₂).comap (D₁ ⊔ D₂).blowupToBase)
        (D₁ ⊔ D₂).isEffectiveCartier_comap_blowupToBase.locallyPrincipal
        (comap_mono _ le_sup_right)).symm)

/-- **Coprimality of residual ideals.** On `Bl_{D₁ ⊔ D₂} X`, the sum of the two residual ideals
`D'₁` and `D'₂` is the unit ideal sheaf. -/
@[simp]
theorem blowupSupResidualLeft_sup_right (D₁ D₂ : X.IdealSheafData) :
    D₁.blowupSupResidualLeft D₂ ⊔ D₁.blowupSupResidualRight D₂ = ⊤ := by
  refine (D₁ ⊔ D₂).isEffectiveCartier_comap_blowupToBase.mul_left_cancel ?_
  rw [mul_inf, comap_sup, comap_blowupToBase_sup_mul_blowupSupResidualLeft,
    comap_blowupToBase_sup_mul_blowupSupResidualRight, ← comap_sup, mul_top]

/-- **Cartier separation of supports.** On `Bl_{D₁ ⊔ D₂} X`, the two residual subschemes `V(D'₁)`
and `V(D'₂)` have disjoint supports. -/
theorem disjoint_support_blowupSupResidual (D₁ D₂ : X.IdealSheafData) :
    Disjoint (D₁.blowupSupResidualLeft D₂).support (D₁.blowupSupResidualRight D₂).support := by
  rw [disjoint_iff, ← support_sup, blowupSupResidualLeft_sup_right, support_top]

/-- **Cross-sum identity `p* D₁ + D'₂ = p* D₂ + D'₁`.** On `Bl_{D₁ ⊔ D₂} X`, the ideal products
`p* D₁ * D'₂` and `p* D₂ * D'₁` coincide. -/
theorem comap_mul_blowupSupResidualRight_eq (D₁ D₂ : X.IdealSheafData) :
    D₁.comap (D₁ ⊔ D₂).blowupToBase * D₁.blowupSupResidualRight D₂ =
      D₂.comap (D₁ ⊔ D₂).blowupToBase * D₁.blowupSupResidualLeft D₂ := by
  conv_lhs => rw [← comap_blowupToBase_sup_mul_blowupSupResidualLeft]
  conv_rhs => rw [← comap_blowupToBase_sup_mul_blowupSupResidualRight]
  rw [mul_assoc, mul_assoc, mul_comm (D₁.blowupSupResidualLeft D₂)]

/-- If `D₁` is an effective Cartier divisor, its residual `D'₁ = p* D₁ - F` on `Bl_{D₁ ⊔ D₂} X`
is an effective Cartier divisor (for any ideal sheaf `D₂`). -/
theorem IsEffectiveCartier.blowupSupResidualLeft {D₁ : X.IdealSheafData}
    (hD₁ : D₁.IsEffectiveCartier) (D₂ : X.IdealSheafData) :
    (D₁.blowupSupResidualLeft D₂).IsEffectiveCartier :=
  (hD₁.comap_blowupToBase (D₁ ⊔ D₂)).colon
    (D₁ ⊔ D₂).isEffectiveCartier_comap_blowupToBase.locallyPrincipal (comap_mono _ le_sup_left)

/-- If `D₂` is an effective Cartier divisor, its residual `D'₂ = p* D₂ - F` on `Bl_{D₁ ⊔ D₂} X`
is an effective Cartier divisor (for any ideal sheaf `D₁`). -/
theorem IsEffectiveCartier.blowupSupResidualRight {D₂ : X.IdealSheafData}
    (hD₂ : D₂.IsEffectiveCartier) (D₁ : X.IdealSheafData) :
    (D₁.blowupSupResidualRight D₂).IsEffectiveCartier :=
  (hD₂.comap_blowupToBase (D₁ ⊔ D₂)).colon
    (D₁ ⊔ D₂).isEffectiveCartier_comap_blowupToBase.locallyPrincipal (comap_mono _ le_sup_right)

/-! ### Degenerate and comparable cases -/

/-- The left residual ideal is the unit ideal sheaf if and only if `p* D₂ ≤ p* D₁`. -/
@[simp]
theorem blowupSupResidualLeft_eq_top_iff (D₁ D₂ : X.IdealSheafData) :
    D₁.blowupSupResidualLeft D₂ = ⊤ ↔
      D₂.comap (D₁ ⊔ D₂).blowupToBase ≤ D₁.comap (D₁ ⊔ D₂).blowupToBase := by
  rw [blowupSupResidualLeft_def, colon_eq_top_iff, comap_sup, sup_le_iff, and_iff_right le_rfl]

/-- The right residual ideal is the unit ideal sheaf if and only if `p* D₁ ≤ p* D₂`. -/
@[simp]
theorem blowupSupResidualRight_eq_top_iff (D₁ D₂ : X.IdealSheafData) :
    D₁.blowupSupResidualRight D₂ = ⊤ ↔
      D₁.comap (D₁ ⊔ D₂).blowupToBase ≤ D₂.comap (D₁ ⊔ D₂).blowupToBase := by
  rw [blowupSupResidualRight_def, colon_eq_top_iff, comap_sup, sup_le_iff, and_iff_left le_rfl]

/-- If `D₂ ≤ D₁` (geometrically `D₁ ≤ D₂`), the left residual ideal is the unit ideal sheaf. -/
theorem blowupSupResidualLeft_eq_top_of_le {D₁ D₂ : X.IdealSheafData} (h : D₂ ≤ D₁) :
    D₁.blowupSupResidualLeft D₂ = ⊤ :=
  (blowupSupResidualLeft_eq_top_iff D₁ D₂).mpr (comap_mono _ h)

/-- If `D₁ ≤ D₂` (geometrically `D₂ ≤ D₁`), the right residual ideal is the unit ideal sheaf. -/
theorem blowupSupResidualRight_eq_top_of_le {D₁ D₂ : X.IdealSheafData} (h : D₁ ≤ D₂) :
    D₁.blowupSupResidualRight D₂ = ⊤ :=
  (blowupSupResidualRight_eq_top_iff D₁ D₂).mpr (comap_mono _ h)

/-- If `D₁` is locally principal and `D₂ ≤ D₁`, the right residual ideal on `Bl_{D₁ ⊔ D₂} X` is
the pullback of the quotient `(D₂ : D₁)`. -/
theorem blowupSupResidualRight_of_le {D₁ D₂ : X.IdealSheafData}
    (hD₁ : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.val ∧
      ∃ a : Γ(X, U), D₁.ideal U = Ideal.span {a})
    (h : D₂ ≤ D₁) :
    D₁.blowupSupResidualRight D₂ = (D₂.colon D₁).comap (D₁ ⊔ D₂).blowupToBase := by
  have hsup : (D₁ ⊔ D₂).comap (D₁ ⊔ D₂).blowupToBase =
      D₁.comap (D₁ ⊔ D₂).blowupToBase :=
    congrArg (·.comap (D₁ ⊔ D₂).blowupToBase) (sup_eq_left.mpr h)
  rw [blowupSupResidualRight_def, hsup]
  exact (comap_colon D₂ D₁ hD₁ h (D₁ ⊔ D₂).blowupToBase
    (hsup ▸ (D₁ ⊔ D₂).isEffectiveCartier_comap_blowupToBase)).symm

/-- If `D₂` is locally principal and `D₁ ≤ D₂`, the left residual ideal on `Bl_{D₁ ⊔ D₂} X` is
the pullback of the quotient `(D₁ : D₂)`. -/
theorem blowupSupResidualLeft_of_le {D₁ D₂ : X.IdealSheafData}
    (hD₂ : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.val ∧
      ∃ a : Γ(X, U), D₂.ideal U = Ideal.span {a})
    (h : D₁ ≤ D₂) :
    D₁.blowupSupResidualLeft D₂ = (D₁.colon D₂).comap (D₁ ⊔ D₂).blowupToBase := by
  have hsup : (D₁ ⊔ D₂).comap (D₁ ⊔ D₂).blowupToBase =
      D₂.comap (D₁ ⊔ D₂).blowupToBase :=
    congrArg (·.comap (D₁ ⊔ D₂).blowupToBase) (sup_eq_right.mpr h)
  rw [blowupSupResidualLeft_def, hsup]
  exact (comap_colon D₁ D₂ hD₂ h (D₁ ⊔ D₂).blowupToBase
    (hsup ▸ (D₁ ⊔ D₂).isEffectiveCartier_comap_blowupToBase)).symm

/-- For identical ideal sheaves `D`, the left residual ideal on `Bl_{D ⊔ D} X` is `⊤`. -/
@[simp]
theorem blowupSupResidualLeft_self (D : X.IdealSheafData) : D.blowupSupResidualLeft D = ⊤ :=
  blowupSupResidualLeft_eq_top_of_le le_rfl

/-- For identical ideal sheaves `D`, the right residual ideal on `Bl_{D ⊔ D} X` is `⊤`. -/
@[simp]
theorem blowupSupResidualRight_self (D : X.IdealSheafData) : D.blowupSupResidualRight D = ⊤ :=
  blowupSupResidualRight_eq_top_of_le le_rfl

/-- When `D₁ = ⊤`, the left residual ideal is `⊤`. -/
@[simp]
theorem blowupSupResidualLeft_top_left (D₂ : X.IdealSheafData) :
    (⊤ : X.IdealSheafData).blowupSupResidualLeft D₂ = ⊤ :=
  blowupSupResidualLeft_eq_top_of_le le_top

/-- When `D₁ = ⊤`, the right residual ideal is the pullback of `D₂`. -/
@[simp]
theorem blowupSupResidualRight_top_left (D₂ : X.IdealSheafData) :
    (⊤ : X.IdealSheafData).blowupSupResidualRight D₂ =
      D₂.comap ((⊤ : X.IdealSheafData) ⊔ D₂).blowupToBase := by
  simpa only [colon_top] using
    blowupSupResidualRight_of_le (isEffectiveCartier_top X).locallyPrincipal le_top

/-- When `D₂ = ⊤`, the left residual ideal is the pullback of `D₁`. -/
@[simp]
theorem blowupSupResidualLeft_top_right (D₁ : X.IdealSheafData) :
    D₁.blowupSupResidualLeft ⊤ = D₁.comap (D₁ ⊔ ⊤).blowupToBase := by
  simpa only [colon_top] using
    blowupSupResidualLeft_of_le (isEffectiveCartier_top X).locallyPrincipal le_top

/-- When `D₂ = ⊤`, the right residual ideal is `⊤`. -/
@[simp]
theorem blowupSupResidualRight_top_right (D₁ : X.IdealSheafData) :
    D₁.blowupSupResidualRight ⊤ = ⊤ :=
  blowupSupResidualRight_eq_top_of_le le_top

end AlgebraicGeometry.Scheme.IdealSheafData

/-! ### Picard-group identity for Cartier separation -/

namespace TauCeti.AlgebraicGeometry.LineBundleClass

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- **Picard-group difference identity `D'₁ - D'₂ = p* (D₁ - D₂)`.** In the Picard group of
`Bl_{D₁ ⊔ D₂} X`, the ratio of the line-bundle classes of the residual effective Cartier divisors
equals the pullback of the ratio of the classes of `D₁` and `D₂`. -/
theorem mk_toInvertibleSheaf_blowupSupResidual_mul_inv {D₁ D₂ : X.IdealSheafData}
    (hD₁ : D₁.IsEffectiveCartier) (hD₂ : D₂.IsEffectiveCartier) :
    mk (hD₁.blowupSupResidualLeft D₂).toInvertibleSheaf *
        (mk (hD₂.blowupSupResidualRight D₁).toInvertibleSheaf)⁻¹ =
      pullback (D₁ ⊔ D₂).blowupToBase
        (mk hD₁.toInvertibleSheaf * (mk hD₂.toInvertibleSheaf)⁻¹) := by
  have hF := (D₁ ⊔ D₂).isEffectiveCartier_comap_blowupToBase
  have h1 := hD₁.comap_blowupToBase (D₁ ⊔ D₂)
  have h2 := hD₂.comap_blowupToBase (D₁ ⊔ D₂)
  have hL : mk (hD₁.blowupSupResidualLeft D₂).toInvertibleSheaf =
      mk h1.toInvertibleSheaf * (mk hF.toInvertibleSheaf)⁻¹ :=
    (mk_toInvertibleSheaf_congr _
        (h1.colon hF.locallyPrincipal (comap_mono _ le_sup_left)) rfl).trans
      (mk_toInvertibleSheaf_colon h1 hF (comap_mono _ le_sup_left))
  have hR : mk (hD₂.blowupSupResidualRight D₁).toInvertibleSheaf =
      mk h2.toInvertibleSheaf * (mk hF.toInvertibleSheaf)⁻¹ :=
    (mk_toInvertibleSheaf_congr _
        (h2.colon hF.locallyPrincipal (comap_mono _ le_sup_right)) rfl).trans
      (mk_toInvertibleSheaf_colon h2 hF (comap_mono _ le_sup_right))
  rw [hL, hR, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left,
    pullback_mul, pullback_inv,
    hD₁.pullback_mk_toInvertibleSheaf h1, hD₂.pullback_mk_toInvertibleSheaf h2]

end TauCeti.AlgebraicGeometry.LineBundleClass
