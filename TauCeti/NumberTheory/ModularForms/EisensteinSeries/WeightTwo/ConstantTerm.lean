/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Basic
public import TauCeti.NumberTheory.ModularForms.Cusps.ConstantTerm

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

/- The proof uses Mathlib's `EisensteinSeries.E2_slash_action`. Reduce the first column of
`diag(t,1) γ` by its gcd and complete the primitive column using `IsCoprime.exists_SL2_col`.
The remaining upper-triangular slash has constant automorphy factor `gcd(c,t)²/t`. -/

private lemma exists_scaled_cusp_reduction (γ : SL(2, ℤ)) :
    ∃ δ : SL(2, ℤ), (t : ℤ) * γ 0 0 = δ 0 0 * Int.gcd (γ 1 0) t ∧
      γ 1 0 = δ 1 0 * Int.gcd (γ 1 0) t := by
  have hcop := Int.isCoprime_iff_gcd_eq_one.mp (γ.isCoprime_col 0)
  have hgcd : Int.gcd ((t : ℤ) * γ 0 0) (γ 1 0) = Int.gcd (γ 1 0) t := by
    rw [Int.gcd_mul_left_left_of_gcd_eq_one hcop, Int.gcd_comm]
  have hpos : 0 < Int.gcd ((t : ℤ) * γ 0 0) (γ 1 0) := by
    rw [hgcd]
    exact Int.gcd_pos_of_ne_zero_right _ (Nat.cast_ne_zero.mpr (NeZero.ne t))
  obtain ⟨a, c, hac, ha, hc⟩ := Int.exists_gcd_one hpos
  obtain ⟨δ, hδa, hδc⟩ := (Int.isCoprime_iff_gcd_eq_one.mpr hac).exists_SL2_col 0
  exact ⟨δ, by simpa [hδa, hgcd] using ha, by simpa [hδc, hgcd] using hc⟩

private lemma scaled_cusp_upperTriangular (γ δ : SL(2, ℤ))
    (ha : (t : ℤ) * γ 0 0 = δ 0 0 * Int.gcd (γ 1 0) t)
    (hc : γ 1 0 = δ 1 0 * Int.gcd (γ 1 0) t) :
    let β := (mapGL ℝ δ)⁻¹ * (scaleGL t * mapGL ℝ γ)
    β 1 0 = 0 ∧ β 1 1 = (t : ℝ) / Int.gcd (γ 1 0) t := by
  intro β
  have ha' : (t : ℝ) * γ 0 0 = (δ 0 0 : ℝ) * Int.gcd (γ 1 0) t := by
    exact_mod_cast ha
  have hc' : (γ 1 0 : ℝ) = (δ 1 0 : ℝ) * Int.gcd (γ 1 0) t := by
    exact_mod_cast hc
  have hentries : β 0 0 = (δ 1 1 : ℝ) * ((t : ℝ) * γ 0 0) - δ 0 1 * γ 1 0 ∧
      β 1 0 = -(δ 1 0 : ℝ) * ((t : ℝ) * γ 0 0) + δ 0 0 * γ 1 0 := by
    simp [β, ← map_inv, mapGL_coe_matrix,
      adjugate_fin_two, coe_scaleGL, Matrix.mul_apply,
      Fin.sum_univ_two, vecMul, dotProduct, sub_eq_add_neg]
  have hδ : (δ 0 0 : ℝ) * δ 1 1 - δ 0 1 * δ 1 0 = 1 := by
    exact_mod_cast (δ.det_coe ▸ Matrix.det_fin_two (δ : Matrix (Fin 2) (Fin 2) ℤ)).symm
  have h00 : β 0 0 = (Int.gcd (γ 1 0) t : ℝ) := by
    rw [hentries.1, ha', hc']
    nlinarith [hδ]
  have h10 : β 1 0 = 0 := by rw [hentries.2, ha', hc']; ring
  have hdet : (β.det : ℝ) = t := by
    simp [β]
  have hprod : (Int.gcd (γ 1 0) t : ℝ) * β 1 1 = t := by
    rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h00, h10] at hdet
    simpa using hdet
  have hg : (Int.gcd (γ 1 0) t : ℝ) ≠ 0 := by
    exact_mod_cast (Int.gcd_pos_of_ne_zero_right (γ 1 0)
      (Nat.cast_ne_zero.mpr (NeZero.ne t))).ne'
  exact ⟨h10, (eq_div_iff hg).mpr (by simpa [mul_comm] using hprod)⟩

/-- The scaled weight-two translate of `E₂` has limit `gcd(c,t)²/t` at infinity, where `c`
is the lower-left entry of the integral cusp representative. -/
lemma tendsto_E2_slash_scaleGL_slash_atImInfty (γ : SL(2, ℤ)) :
    Tendsto ((E2 ∣[(2 : ℤ)] scaleGL t) ∣[(2 : ℤ)] mapGL ℝ γ) atImInfty
      (𝓝 ((Int.gcd (γ 1 0) t : ℂ) ^ 2 / t)) := by
  obtain ⟨δ, ha, hc⟩ := exists_scaled_cusp_reduction t γ
  let β := (mapGL ℝ δ)⁻¹ * (scaleGL t * mapGL ℝ γ)
  obtain ⟨h10, h11⟩ := scaled_cusp_upperTriangular t γ δ ha hc
  have hdet : (β.det : ℝ) = t := by simp [β]
  have hdetpos : 0 < (β : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rw [← GeneralLinearGroup.val_det_apply, hdet]
    exact_mod_cast NeZero.pos t
  have ht : (t : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne t)
  have hg : (Int.gcd (γ 1 0) t : ℂ) ≠ 0 := by
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
