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
term tends to zero there, so every integral weight-two slash of `E₂` tends to `1` at infinity.
Consequently, `E₂` is bounded in weight two at every cusp of the modular group.

## Main results

* `TauCeti.EisensteinSeries.tendsto_D2_atImInfty`: the anomalous term tends to zero.
* `TauCeti.EisensteinSeries.tendsto_E2_slash_atImInfty`: every integral translate tends to `1`.
* `TauCeti.EisensteinSeries.isBoundedAtImInfty_D2`: the anomalous transformation term is bounded
  at infinity.
* `TauCeti.EisensteinSeries.isBoundedAtImInfty_E2_slash`: every integral weight-two slash of `E₂`
  is bounded at infinity.
* `TauCeti.EisensteinSeries.isBoundedAt_E2`: `E₂` is bounded at every cusp of the modular group.
-/

public noncomputable section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup Filter Complex ModularForm

open scoped MatrixGroups ModularForm Topology

namespace TauCeti.EisensteinSeries

open _root_.EisensteinSeries

/-- The anomalous term in the weight-two transformation law tends to zero at infinity. -/
lemma tendsto_D2_atImInfty (γ : SL(2, ℤ)) : Tendsto (D2 γ) atImInfty (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hinv : Tendsto (fun z : ℍ ↦ z.im⁻¹) atImInfty (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp tendsto_comap
  refine squeeze_zero (fun _ ↦ norm_nonneg _) ?_
    (by simpa only [mul_zero] using hinv.const_mul (‖(2 * Real.pi * Complex.I : ℂ)‖))
  intro z
  have hd : 0 < ‖denom γ z‖ := norm_pos_iff.mpr (denom_ne_zero γ z)
  have hci : ‖(γ 1 0 : ℂ)‖ * z.im ≤ ‖denom γ z‖ := by
    simpa [ModularGroup.denom_apply, Complex.mul_im, Complex.add_im,
      abs_mul, abs_of_pos z.im_pos] using Complex.abs_im_le_norm (denom γ z)
  rw [D2, norm_div, norm_mul, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ hd z.im_pos).mpr
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hci
    (norm_nonneg (2 * Real.pi * Complex.I : ℂ))

/-- Every integral weight-two translate of `E₂` has limit `1` at infinity. -/
lemma tendsto_E2_slash_atImInfty (γ : SL(2, ℤ)) :
    Tendsto (E2 ∣[(2 : ℤ)] γ) atImInfty (𝓝 1) := by
  rw [E2_slash_action]
  simpa only [Pi.sub_def, Pi.smul_def, smul_eq_mul, mul_zero, sub_zero] using
    tendsto_E2_atImInfty.sub ((tendsto_D2_atImInfty γ).const_smul
      (1 / (2 * riemannZeta 2)))

/-- The anomalous term in the weight-two transformation law is bounded at infinity. -/
lemma isBoundedAtImInfty_D2 (γ : SL(2, ℤ)) : IsBoundedAtImInfty (D2 γ) :=
  (tendsto_D2_atImInfty γ).isBigO_one ℝ

/-- Although `E₂` is not modular, each of its integral weight-two slashes is bounded
at infinity. -/
lemma isBoundedAtImInfty_E2_slash (γ : SL(2, ℤ)) : IsBoundedAtImInfty (E2 ∣[(2 : ℤ)] γ) :=
  (tendsto_E2_slash_atImInfty γ).isBigO_one ℝ

/-- `E₂` is bounded in weight two at every cusp of the modular group. -/
lemma isBoundedAt_E2 {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) : c.IsBoundedAt E2 2 :=
  (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr fun γ _ ↦ isBoundedAtImInfty_E2_slash γ

end TauCeti.EisensteinSeries
