/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
public import Mathlib.NumberTheory.ModularForms.BoundedAtCusp

/-!
# Bounds for the weight-two Eisenstein series at cusps

Mathlib's normalized `EisensteinSeries.E2` is bounded at infinity. Its anomalous transformation
term is also bounded there, so every integral weight-two slash of `E₂` is bounded at infinity.
Consequently, `E₂` is bounded in weight two at every cusp of the modular group.

## Main results

* `TauCeti.EisensteinSeries.isBoundedAtImInfty_D2`: the anomalous transformation term is bounded
  at infinity.
* `TauCeti.EisensteinSeries.isBoundedAtImInfty_E2_slash`: every integral weight-two slash of `E₂`
  is bounded at infinity.
* `TauCeti.EisensteinSeries.isBoundedAt_E2`: `E₂` is bounded at every cusp of the modular group.
-/

public noncomputable section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup Filter Complex ModularForm

open scoped MatrixGroups ModularForm

namespace TauCeti.EisensteinSeries

open _root_.EisensteinSeries

/-- The anomalous term in the weight-two transformation law is bounded at infinity. -/
lemma isBoundedAtImInfty_D2 (γ : SL(2, ℤ)) : IsBoundedAtImInfty (D2 γ) := by
  refine isBoundedAtImInfty_iff.mpr ⟨‖(2 * Real.pi * Complex.I : ℂ)‖, 1, fun z hz ↦ ?_⟩
  have hd : 0 < ‖denom γ z‖ := norm_pos_iff.mpr (denom_ne_zero γ z)
  have hci : ‖(γ 1 0 : ℂ)‖ * z.im ≤ ‖denom γ z‖ := by
    simpa [ModularGroup.denom_apply, Complex.mul_im, Complex.add_im,
      abs_mul, abs_of_pos z.im_pos] using Complex.abs_im_le_norm (denom γ z)
  have hc : ‖(γ 1 0 : ℂ)‖ ≤ ‖denom γ z‖ :=
    (le_mul_of_one_le_right (norm_nonneg _) hz).trans hci
  simpa [D2, norm_div, norm_mul] using
    (div_le_iff₀ hd).mpr (mul_le_mul_of_nonneg_left hc (norm_nonneg (2 * Real.pi * Complex.I : ℂ)))

/-- Although `E₂` is not modular, each of its integral weight-two slashes is bounded
at infinity. -/
lemma isBoundedAtImInfty_E2_slash (γ : SL(2, ℤ)) : IsBoundedAtImInfty (E2 ∣[(2 : ℤ)] γ) := by
  rw [E2_slash_action]
  exact isBoundedAtImInfty_E2.sub ((isBoundedAtImInfty_D2 γ).smul _)

/-- `E₂` is bounded in weight two at every cusp of the modular group. -/
lemma isBoundedAt_E2 {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) : c.IsBoundedAt E2 2 :=
  (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr fun γ _ ↦ isBoundedAtImInfty_E2_slash γ

end TauCeti.EisensteinSeries
