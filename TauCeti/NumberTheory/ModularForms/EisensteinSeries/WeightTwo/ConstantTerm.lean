/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Basic
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Character
public import TauCeti.NumberTheory.ModularForms.Cusps.LevelRaise
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.ConstantTerm

/-!
# Constant terms of weight-two Eisenstein series at the cusps

This file computes the constant terms at every cusp of the weight-two Eisenstein series that
generate the Eisenstein part of `M₂(N, χ)`: the corrected series `E₂(z) - t E₂(tz)`, which
replaces the trivial pair of characters, and the series with characters `G₂^{ψ,φ}` and their level
raises `G₂^{ψ,φ,t}` for the other pairs.

For `t > 0`, the constant term of `E₂(z) - t E₂(tz)` at the cusp represented by
`γ = [a,b;c,d] ∈ SL₂(ℤ)` is `1 - gcd(c,t)²/t`. The formula includes infinity (`c = 0`) and holds
without a squarefree-level assumption.

For a weight `W : (Fin 2 → ZMod N) → ℂ`, the weighted weight-two series `G₂^W` has, at the cusp
`a / c`, the constant term `∑_{n ∈ ℤ} W(-n c, n a) n⁻² - N⁻² (∑_x W(x)) · 2 ζ(2)`
(`TauCeti.EisensteinSeries.valueAtInfty_weightedG2_slash`): the formula of weight `k ≥ 3`
(`TauCeti.EisensteinSeries.constantTermAt_weightedEisensteinSeriesMF`) corrected by the
regularization. For a pair `ψ` modulo `u`, `φ` modulo `v` of characters that are not both trivial
the weight has total mass zero, and the constant term of `G₂^{ψ,φ}` at `a / c` is, as in weight
`k ≥ 3`, `ψ(-c / v) φ⁻¹(a) ∑_{n ∈ ℤ} ψ(n) φ⁻¹(n) n⁻²` if `v ∣ c` and `0` otherwise. These are
the boundary vectors to be compared with the image of the constant-term map on `M₂(N, χ)`, which
satisfies the weight-two residue relation.

## Main results

* `TauCeti.EisensteinSeries.constantTermAt_correctedE2`: the constant terms of the corrected
  series.
* `TauCeti.EisensteinSeries.constantTermAt_weightedG2MF`: the constant terms of `G₂^W`.
* `TauCeti.EisensteinSeries.constantTermAt_charG2MF`: the constant terms of `G₂^{ψ,φ}`.
* `TauCeti.EisensteinSeries.constantTermAt_charG2MFRaise`: the constant terms of `G₂^{ψ,φ,t}`,
  with the scaling factor `(gcd(c,t)/t)²`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §4.2, §4.5
  and §4.6.
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

/-! ### The series with character -/

section Character

variable {N : ℕ} [NeZero N]

/-- **The constant term of a weighted weight-two series at every cusp.** At the cusp
represented by `γ = !![a, b; c, d] ∈ SL₂(ℤ)`, the constant term of `G₂^W` is
`∑_{n ∈ ℤ} W(-n c, n a) n⁻² - N⁻² (∑_x W(x)) · 2 ζ(2)`. -/
theorem constantTermAt_weightedG2MF (W : (Fin 2 → ZMod N) → ℂ) (γ : SL(2, ℤ)) :
    constantTermAt γ (weightedG2MF W) =
      ∑' n : ℤ, W ((↑) ∘ ![-(n * γ 1 0), n * γ 0 0]) * (n : ℂ) ^ (-2 : ℤ) -
        ((N : ℂ) ^ 2)⁻¹ * (∑ a, W a) * (2 * riemannZeta 2) := by
  have h : weightedG2 W ∣[(2 : ℤ)] mapGL ℝ γ = weightedG2 W ∣[(2 : ℤ)] γ := (SL_slash _ γ).symm
  rw [constantTermAt_eq_valueAtInfty, coe_translate, coe_weightedG2MF, h,
    valueAtInfty_weightedG2_slash]

variable {u v : ℕ} (ψ : DirichletCharacter ℂ u) (φ : DirichletCharacter ℂ v)

/-- **The constant term of the weight-two Eisenstein series with character at every cusp.** For
`ψ` modulo `u` and `φ` modulo `v`, not both trivial, with `u v ∣ N`, and
`γ = !![a, b; c, d] ∈ SL₂(ℤ)`, the constant term of `G₂^{ψ,φ}` at the cusp `a / c` is
`ψ(-c / v) φ⁻¹(a) ∑_{n ∈ ℤ} ψ(n) φ⁻¹(n) n⁻²` if `v ∣ c`, and `0` otherwise. -/
theorem constantTermAt_charG2MF (huv : u * v ∣ N) (h : ψ ≠ 1 ∨ φ ≠ 1) (γ : SL(2, ℤ)) :
    constantTermAt γ (charG2MF ψ φ huv) =
      if (v : ℤ) ∣ γ 1 0 then
        ψ ((-(γ 1 0 / v) : ℤ) : ZMod u) * φ⁻¹ (γ 0 0 : ZMod v) *
          ∑' n : ℤ, ψ (n : ZMod u) * φ⁻¹ (n : ZMod v) * (n : ℂ) ^ (-2 : ℤ)
      else 0 := by
  have h' : weightedG2 (charWeight N ψ φ) ∣[(2 : ℤ)] mapGL ℝ γ =
      weightedG2 (charWeight N ψ φ) ∣[(2 : ℤ)] γ :=
    (SL_slash _ γ).symm
  rw [constantTermAt_eq_valueAtInfty, coe_translate, coe_charG2MF, h',
    valueAtInfty_weightedG2_slash, sum_charWeight_eq_zero ψ φ huv h, mul_zero, zero_mul, sub_zero,
    tsum_charWeight_mul_zpow ψ φ huv]

/-- **The constant term of a raised weight-two Eisenstein series with character at every cusp.**
For `ψ` and `φ` not both trivial, at the cusp `a / c` put `g = gcd(c, t)`. The constant term of
`G₂^{ψ,φ}(tz)` is `(g/t)²` times `ψ(-c/(gv)) φ⁻¹(ta/g) ∑ₙ ψ(n) φ⁻¹(n) n⁻²` when `v ∣ c/g`, and
is zero otherwise. The integer divisions are exact in the nonvanishing branch. -/
theorem constantTermAt_charG2MFRaise {t : ℕ} (htuv : t * (u * v) ∣ N) (h : ψ ≠ 1 ∨ φ ≠ 1)
    (γ : SL(2, ℤ)) :
    constantTermAt γ (charG2MFRaise ψ φ t htuv) =
      ((Int.gcd (γ 1 0) t : ℂ) / t) ^ (2 : ℤ) *
        (if (v : ℤ) ∣ γ 1 0 / Int.gcd (γ 1 0) t then
          ψ ((-(γ 1 0 / Int.gcd (γ 1 0) t / v) : ℤ) : ZMod u) *
            φ⁻¹ (((t : ℤ) * γ 0 0 / Int.gcd (γ 1 0) t : ℤ) : ZMod v) *
            ∑' n : ℤ, ψ (n : ZMod u) * φ⁻¹ (n : ZMod v) * (n : ℂ) ^ (-2 : ℤ)
        else 0) := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  obtain ⟨δ, ha, hc⟩ := γ.exists_scaled_cusp_reduction (t := t)
  have hg : (Int.gcd (γ 1 0) t : ℤ) ≠ 0 := by
    exact_mod_cast (Int.gcd_pos_of_ne_zero_right (γ 1 0)
      (Nat.cast_ne_zero.mpr (NeZero.ne t))).ne'
  have hδa : δ 0 0 = (t : ℤ) * γ 0 0 / Int.gcd (γ 1 0) t := by
    rw [ha, Int.mul_ediv_cancel _ hg]
  have hδc : δ 1 0 = γ 1 0 / Int.gcd (γ 1 0) t := by
    exact ((congrArg (fun c : ℤ ↦ c / Int.gcd (γ 1 0) t) hc).trans
      (Int.mul_ediv_cancel _ hg)).symm
  rw [charG2MFRaise_eq_levelRaise, _root_.ModularForm.constantTermAt_levelRaise _ _ γ δ ha hc,
    constantTermAt_charG2MF ψ φ dvd_rfl h, hδa, hδc]

end Character

end TauCeti.EisensteinSeries
