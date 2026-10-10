/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Basic
public import TauCeti.NumberTheory.ModularForms.Cusps.LevelRaise

/-!
# Constant terms of the corrected weight-two Eisenstein series

For `t > 0`, the constant term of `E₂(z) - t E₂(tz)` at the cusp represented by
`γ = [a,b;c,d] ∈ SL₂(ℤ)` is `1 - gcd(c,t)²/t`. This gives the constant-term vectors of the
corrected series used in the weight-two Eisenstein subspace. The formula includes infinity
(`c = 0`) and holds without a squarefree-level assumption.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, Chapter 4.
-/

public noncomputable section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup Filter Complex ModularForm
open scoped MatrixGroups ModularForm Topology

namespace TauCeti.EisensteinSeries

open _root_.EisensteinSeries

variable (t : ℕ) [NeZero t]

/-- The scaled weight-two translate of `E₂` has limit `gcd(c,t)²/t` at infinity, where `c`
is the lower-left entry of the integral cusp representative. -/
lemma tendsto_E2_slash_scaleGL_slash_atImInfty (γ : SL(2, ℤ)) :
    Tendsto ((E2 ∣[(2 : ℤ)] scaleGL t) ∣[(2 : ℤ)] mapGL ℝ γ) atImInfty
      (𝓝 ((Int.gcd (γ 1 0) t : ℂ) ^ 2 / t)) := by
  obtain ⟨δ, ha, hc⟩ := γ.exists_scaled_cusp_reduction (t := t)
  let β := (mapGL ℝ δ)⁻¹ * (scaleGL t * mapGL ℝ γ)
  obtain ⟨h10, h11⟩ := γ.scaled_cusp_upperTriangular δ ha hc
  have hdet : (β.det : ℝ) = t := by simp [β]
  have hdetpos : 0 < (β : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rw [← GeneralLinearGroup.val_det_apply, hdet]
    exact_mod_cast NeZero.pos t
  have _ : (t : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne t)
  have _ : (Int.gcd (γ 1 0) t : ℂ) ≠ 0 := by
    exact_mod_cast (Int.gcd_pos_of_ne_zero_right (γ 1 0)
      (Nat.cast_ne_zero.mpr (NeZero.ne t))).ne'
  have hlim := tendsto_slash_atImInfty_of_upperTriangular 2 β h10
    (tendsto_E2_slash_atImInfty δ)
  rw [SL_slash, TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL] at hlim
  have hmul : mapGL ℝ δ * β = scaleGL t * mapGL ℝ γ := by
    simp [β]
  rw [← SlashAction.slash_mul, hmul] at hlim
  rw [← SlashAction.slash_mul]
  convert hlim using 1
  rw [σ_eq_refl_of_det_pos hdetpos, ContinuousAlgEquiv.refl_apply,
    hdet, abs_of_pos (by exact_mod_cast NeZero.pos t), h11]
  push_cast
  simp only [one_mul, _root_.zpow_neg, zpow_ofNat]
  field_simp

/-- At the cusp represented by `γ = [a,b;c,d]`, the corrected series tends to
`1 - gcd(c,t)²/t` after slashing by `γ`. -/
lemma tendsto_correctedE2_slash_atImInfty (γ : SL(2, ℤ)) :
    Tendsto (⇑(correctedE2 t) ∣[(2 : ℤ)] mapGL ℝ γ) atImInfty
      (𝓝 (1 - (Int.gcd (γ 1 0) t : ℂ) ^ 2 / t)) := by
  rw [coe_correctedE2, sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash,
    ← sub_eq_add_neg]
  have h := (tendsto_E2_slash_atImInfty γ).sub
    (tendsto_E2_slash_scaleGL_slash_atImInfty t γ)
  rw [SL_slash, TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL] at h
  simpa only [Pi.sub_def] using h

/-- **The constant term of the corrected weight-two Eisenstein series at every cusp.**
For `γ = [a,b;c,d]`, it is `1 - gcd(c,t)²/t`, including infinity (`c = 0`). -/
@[simp high]
theorem constantTermAt_correctedE2 (γ : SL(2, ℤ)) :
    constantTermAt γ (correctedE2 t) =
      1 - (Int.gcd (γ 1 0) t : ℂ) ^ 2 / t := by
  rw [constantTermAt_eq_valueAtInfty, coe_translate]
  exact (tendsto_correctedE2_slash_atImInfty t γ).limUnder_eq

end TauCeti.EisensteinSeries
