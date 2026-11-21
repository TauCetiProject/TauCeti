/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Homeomorphism between `(0, 1)` and `ℝ`

Composing the affine order isomorphism `t ↦ π(t - 1/2)` from `(0, 1)` onto `(-π/2, π/2)` with
Mathlib's `Real.tanOrderIso` yields an orientation-preserving homeomorphism `(0, 1) ≃ₜ ℝ`.

## Main definitions

* `TauCeti.iooZeroOneOrderIsoPiHalf`: orientation-preserving order isomorphism
  `Set.Ioo (0 : ℝ) 1 ≃o Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)` given by `t ↦ π(t - 1/2)`.
* `TauCeti.iooZeroOneHomeomorphReal`: orientation-preserving homeomorphism
  `Set.Ioo (0 : ℝ) 1 ≃ₜ ℝ` given by `t ↦ tan(π(t - 1/2))`.
-/

public section

open Set

namespace TauCeti

/-- Orientation-preserving order isomorphism `(0, 1) ≃o (-π/2, π/2)` given by `t ↦ π(t - 1/2)`. -/
noncomputable def iooZeroOneOrderIsoPiHalf :
    Ioo (0 : ℝ) 1 ≃o Ioo (-(Real.pi / 2)) (Real.pi / 2) where
  toFun x := ⟨Real.pi * ((x : ℝ) - 2⁻¹),
    by constructor <;> nlinarith [Real.pi_pos, x.property.1, x.property.2]⟩
  invFun y := ⟨(y : ℝ) / Real.pi + 2⁻¹, by
    have hpi := Real.pi_pos
    exact ⟨by rw [div_add' _ _ _ hpi.ne', lt_div_iff₀ hpi]; linarith [y.property.1],
      by rw [div_add' _ _ _ hpi.ne', div_lt_iff₀ hpi]; linarith [y.property.2]⟩⟩
  left_inv x := by ext; simp [mul_div_cancel_left₀ _ Real.pi_ne_zero]
  right_inv y := by ext; simp [mul_div_cancel₀ _ Real.pi_ne_zero]
  map_rel_iff' := by
    simp only [Equiv.coe_fn_mk, ← Subtype.coe_le_coe]
    exact ⟨fun _ => by nlinarith [Real.pi_pos], fun _ => by nlinarith [Real.pi_pos]⟩

@[simp]
theorem coe_iooZeroOneOrderIsoPiHalf (x : Ioo (0 : ℝ) 1) :
    (iooZeroOneOrderIsoPiHalf x : ℝ) = Real.pi * ((x : ℝ) - 2⁻¹) := (rfl)

@[simp]
theorem coe_iooZeroOneOrderIsoPiHalf_symm (y : Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    (iooZeroOneOrderIsoPiHalf.symm y : ℝ) = (y : ℝ) / Real.pi + 2⁻¹ := (rfl)

/-- Orientation-preserving homeomorphism `(0, 1) ≃ₜ ℝ` given by `t ↦ tan(π(t - 1/2))`. -/
noncomputable def iooZeroOneHomeomorphReal : Ioo (0 : ℝ) 1 ≃ₜ ℝ :=
  (iooZeroOneOrderIsoPiHalf.trans Real.tanOrderIso).toHomeomorph

@[simp]
theorem iooZeroOneHomeomorphReal_apply (x : Ioo (0 : ℝ) 1) :
    iooZeroOneHomeomorphReal x = Real.tan (Real.pi * ((x : ℝ) - 2⁻¹)) := (rfl)

@[simp]
theorem coe_iooZeroOneHomeomorphReal_symm (y : ℝ) :
    (iooZeroOneHomeomorphReal.symm y : ℝ) = Real.arctan y / Real.pi + 2⁻¹ := (rfl)

end TauCeti
