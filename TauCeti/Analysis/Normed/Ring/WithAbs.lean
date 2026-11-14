/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# Metric and uniform properties of rings with an absolute value

A scalar action on a ring `A` that commutes with right multiplication,
`m • (x * y) = (m • x) * y` (`IsScalarTower M A A`), such as the algebra action of a commutative
semiring, induces a uniformly continuous action on `WithAbs v` for every fixed scalar. This lets
the scalar action extend to the completion; Mathlib's corresponding instance covers only algebra
actions of a commutative ring on a field.

In addition, a ring isomorphism `σ : R ≃+* T` that intertwines real absolute values `v` on `R` and
`w` on `T` (`w (σ x) = v x`) induces an isometry `WithAbs.congr v w σ : WithAbs v ≃+* WithAbs w`
(`WithAbs.isometry_congr`), bundled as `WithAbs.isometryEquivCongr : WithAbs v ≃ᵢ WithAbs w`.
-/

public section

namespace WithAbs

section SMul

variable {M A : Type*} [Ring A] [SMul M A] [IsScalarTower M A A]

/-- A scalar action on a ring with an absolute value that commutes with right multiplication, such
as an algebra action, is uniformly continuous in its argument. -/
instance (priority := 100) uniformContinuousConstSMul (v : AbsoluteValue A ℝ) :
    UniformContinuousConstSMul M (WithAbs v) where
  -- An action commuting with right multiplication is left multiplication by `m • 1`.
  uniformContinuous_const_smul m := by
    simpa only [smul_eq_mul, smul_one_mul] using
      uniformContinuous_const_smul (X := WithAbs v) (m • 1 : WithAbs v)

end SMul

section Congr

variable {R T : Type*} [Ring R] [Ring T] {v : AbsoluteValue R ℝ} {w : AbsoluteValue T ℝ}

/-- A ring isomorphism carrying the real absolute value `v` to `w` is an isometry from `WithAbs v`
to `WithAbs w`. -/
theorem isometry_congr (σ : R ≃+* T) (hσ : ∀ x, w (σ x) = v x) :
    Isometry (WithAbs.congr v w σ) :=
  AddMonoidHomClass.isometry_of_norm _ fun x ↦ by
    rw [norm_eq_apply_ofAbs, norm_eq_apply_ofAbs, congr_apply, ofAbs_toAbs, hσ]

/-- A ring isomorphism carrying the real absolute value `v` to `w`, bundled as an isometric
equivalence `WithAbs v ≃ᵢ WithAbs w`. -/
noncomputable def isometryEquivCongr (σ : R ≃+* T) (hσ : ∀ x, w (σ x) = v x) :
    WithAbs v ≃ᵢ WithAbs w where
  toEquiv := (WithAbs.congr v w σ).toEquiv
  isometry_toFun := isometry_congr σ hσ

/-- The underlying map of `isometryEquivCongr σ hσ` is `WithAbs.congr v w σ`. -/
@[simp]
theorem coe_isometryEquivCongr (σ : R ≃+* T) (hσ : ∀ x, w (σ x) = v x) :
    ⇑(isometryEquivCongr σ hσ) = WithAbs.congr v w σ :=
  (rfl)

/-- The inverse of `isometryEquivCongr σ hσ` is `isometryEquivCongr` of `σ.symm`. -/
@[simp]
theorem isometryEquivCongr_symm (σ : R ≃+* T) (hσ : ∀ x, w (σ x) = v x) :
    (isometryEquivCongr σ hσ).symm =
      isometryEquivCongr σ.symm (fun y ↦ by rw [← hσ, σ.apply_symm_apply]) :=
  IsometryEquiv.ext fun _ ↦ rfl

end Congr

end WithAbs
