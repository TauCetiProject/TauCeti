/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Basic

import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Expansion
import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Diagonal.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# Diagonal asymptotics of the regularized incomplete Gamma function

Combining the four-term reciprocal Stirling expansion
`TauCeti.isBigO_inv_mul_Gamma_sub_stirling` from
`TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Expansion` with the pure integer-power expansion
`TauCeti.isBigO_mul_lowerIncompleteGamma_diag_sub_half_Gamma` yields the four-term diagonal
asymptotic expansions of `P(a, a)` and `P(a + 1, a)` to `O(a^{-9/2})` together with their
diagonal limits `1 / 2` (DLMF 8.11.13).

## Main results

* `TauCeti.isBigO_regularizedGamma_diag_sub` and `TauCeti.isBigO_regularizedGamma_add_one_diag_sub`:
  four-term diagonal expansions of `P(a, a)` and `P(a + 1, a)` to `O(a^{-9/2})`.
* `TauCeti.tendsto_regularizedGamma_diag_atTop`,
  `TauCeti.tendsto_sub_regularizedGamma_diag_atTop`, and
  `TauCeti.tendsto_regularizedGamma_add_one_diag_atTop`: the diagonal limits `P(a, a) → 1 / 2`,
  `1 - P(a, a) → 1 / 2`, and `P(a + 1, a) → 1 / 2` as `a → +∞` (DLMF 8.11.13).

## References

* *NIST Digital Library of Mathematical Functions*, [§8.11(v)](https://dlmf.nist.gov/8.11.v),
  Eq. 8.11.13.
* F. G. Tricomi, *Asymptotische Eigenschaften der unvollständigen Gammafunktion*, Math. Z. **53**
  (1950), 136–148.
-/

public section

noncomputable section

open Asymptotics Filter
open scoped Topology

namespace TauCeti

private theorem isBigO_diag_diff_mul_inv_stirling :
    (fun a : ℝ => a ^ (1 - a) * Real.exp a * (lowerIncompleteGamma a a - Real.Gamma a / 2) *
        (a ^ (1 / 2 - a) * Real.exp a * Real.Gamma a)⁻¹ -
      (Real.sqrt (2 * Real.pi))⁻¹ *
        (1 / 3 + 1 / (540 * a) - 25 / (6048 * a ^ 2) - 101 / (155520 * a ^ 3)))
      =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) := by
  let P_D : ℝ → ℝ := fun a => 1 / 3 + 4 / (135 * a) - 8 / (2835 * a ^ 2) - 16 / (8505 * a ^ 3)
  let P_S : ℝ → ℝ := fun a => (Real.sqrt (2 * Real.pi))⁻¹ *
    (1 - 1 / (12 * a) + 1 / (288 * a ^ 2) + 139 / (51840 * a ^ 3))
  let P_out : ℝ → ℝ := fun a => (Real.sqrt (2 * Real.pi))⁻¹ *
    (1 / 3 + 1 / (540 * a) - 25 / (6048 * a ^ 2) - 101 / (155520 * a ^ 3))
  have hPD : P_D =O[atTop] fun _ : ℝ => (1 : ℝ) :=
    ((((by fun_prop : Continuous fun t : ℝ =>
        1 / 3 + 4 * t / 135 - 8 * t ^ 2 / 2835 - 16 * t ^ 3 / 8505).tendsto 0).comp
        tendsto_inv_atTop_zero).congr fun a => by
      simp only [Function.comp_apply, P_D, div_eq_mul_inv, mul_inv, inv_pow]; ring).isBigO_one ℝ
  have hS_inv_one : (fun a : ℝ => (a ^ (1 / 2 - a) * Real.exp a * Real.Gamma a)⁻¹)
      =O[atTop] fun _ : ℝ => (1 : ℝ) := by
    have herr := isBigO_inv_mul_Gamma_sub_stirling.trans_tendsto
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 4))
    have hPS := (((by fun_prop : Continuous fun t : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
        (1 - t / 12 + t ^ 2 / 288 + 139 * t ^ 3 / 51840)).tendsto 0).comp
        tendsto_inv_atTop_zero).congr (f₂ := P_S) fun a => by
      simp only [Function.comp_apply, P_S, div_eq_mul_inv, mul_inv, inv_pow]; ring
    exact ((herr.add hPS).congr fun a => sub_add_cancel _ (P_S a)).isBigO_one ℝ
  have hpoly : (fun a : ℝ => P_D a * P_S a - P_out a) =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) := by
    have hq := (((by fun_prop : Continuous fun t : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
        (2773 / 12247200 - 37 * t / 2624400 - 139 * t ^ 2 / 27556200)).tendsto 0).comp
        tendsto_inv_atTop_zero).isBigO_one ℝ
    refine ((isBigO_refl (fun a : ℝ => a ^ (-4 : ℝ)) atTop).mul hq).congr' ?_
      (Eventually.of_forall fun _ => mul_one _)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    have ha4 : a ^ (-4 : ℝ) = (a ^ 4)⁻¹ := by
      have hneg : (-4 : ℝ) = -((4 : ℕ) : ℝ) := by norm_num
      rw [hneg, Real.rpow_neg ha.le, Real.rpow_natCast]
    have : a ≠ 0 := ha.ne'
    rw [ha4]; dsimp only [Function.comp_apply, P_D, P_S, P_out]; field_simp; ring
  exact ((((isBigO_mul_lowerIncompleteGamma_diag_sub_half_Gamma.mul
      hS_inv_one).congr_right fun _ => mul_one _).add
      ((hPD.mul isBigO_inv_mul_Gamma_sub_stirling).congr_right fun _ => one_mul _)).add
      hpoly).congr_left fun a => by dsimp only [P_D, P_S, P_out]; ring

/-- Four-term asymptotic expansion of the diagonal regularized lower incomplete Gamma function
`TauCeti.regularizedGamma a a` as `a → +∞`, with remainder `O(a^{-9/2})`. -/
theorem isBigO_regularizedGamma_diag_sub :
    (fun a : ℝ => regularizedGamma a a -
      (1 / 2 + (Real.sqrt (2 * Real.pi * a))⁻¹ *
        (1 / 3 + 1 / (540 * a) - 25 / (6048 * a ^ 2) - 101 / (155520 * a ^ 3))))
      =O[atTop] fun a : ℝ => a ^ (-9 / 2 : ℝ) := by
  refine ((isBigO_refl (fun a : ℝ => a ^ (-1 / 2 : ℝ)) atTop).mul
    isBigO_diag_diff_mul_inv_stirling).congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    rw [regularizedGamma_eq_div, Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi) a,
      mul_inv (a := Real.sqrt (2 * Real.pi)), Real.inv_sqrt_eq_rpow a]
    have hG : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
    have he : Real.exp a ≠ 0 := (Real.exp_pos a).ne'
    have hp : a ^ (-1 / 2 : ℝ) * a ^ (1 - a) = a ^ (1 / 2 - a) := by
      rw [← Real.rpow_add ha]; congr 1; ring
    have hrel : a ^ (-1 / 2 : ℝ) *
        (a ^ (1 - a) * Real.exp a * (lowerIncompleteGamma a a - Real.Gamma a / 2)) *
        (a ^ (1 / 2 - a) * Real.exp a * Real.Gamma a)⁻¹ =
        lowerIncompleteGamma a a / Real.Gamma a - 1 / 2 := by
      rw [← mul_assoc, ← mul_assoc, hp]
      field_simp [hG, he, (Real.rpow_pos_of_pos ha (1 / 2 - a)).ne']
    linear_combination hrel
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    rw [← Real.rpow_add ha]; congr 1; ring

/-- Four-term asymptotic expansion of `TauCeti.regularizedGamma (a + 1) a` as `a → +∞`, with
remainder `O(a^{-9/2})`. -/
theorem isBigO_regularizedGamma_add_one_diag_sub :
    (fun a : ℝ => regularizedGamma (a + 1) a -
      (1 / 2 - (Real.sqrt (2 * Real.pi * a))⁻¹ *
        (2 / 3 - 23 / (270 * a) + 23 / (3024 * a ^ 2) + 259 / (77760 * a ^ 3))))
      =O[atTop] fun a : ℝ => a ^ (-9 / 2 : ℝ) := by
  have hterm : (fun a : ℝ => -(a ^ a * Real.exp (-a) / Real.Gamma (a + 1)) +
      (Real.sqrt (2 * Real.pi * a))⁻¹ *
        (1 - 1 / (12 * a) + 1 / (288 * a ^ 2) + 139 / (51840 * a ^ 3)))
      =O[atTop] fun a : ℝ => a ^ (-9 / 2 : ℝ) := by
    refine (((isBigO_refl (fun a : ℝ => a ^ (-1 / 2 : ℝ)) atTop).mul
      isBigO_inv_mul_Gamma_sub_stirling).neg_left).congr' ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
      rw [Real.Gamma_add_one ha.ne', Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi) a,
        mul_inv (a := Real.sqrt (2 * Real.pi)), Real.inv_sqrt_eq_rpow a]
      have hG : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
      have hp : a ^ (-1 / 2 : ℝ) * (a ^ (1 / 2 - a))⁻¹ = a ^ a / a := by
        have hexp : (-1 / 2 : ℝ) + -(1 / 2 - a) = a + (-1) := by ring
        rw [← Real.rpow_neg ha.le, ← Real.rpow_add ha, hexp, Real.rpow_add ha,
          Real.rpow_neg_one, div_eq_mul_inv]
      have hid : a ^ (-1 / 2 : ℝ) * (a ^ (1 / 2 - a) * Real.exp a * Real.Gamma a)⁻¹ =
          a ^ a * Real.exp (-a) / (a * Real.Gamma a) :=
        calc a ^ (-1 / 2 : ℝ) * (a ^ (1 / 2 - a) * Real.exp a * Real.Gamma a)⁻¹
            = (a ^ (-1 / 2 : ℝ) * (a ^ (1 / 2 - a))⁻¹) * Real.exp (-a) * (Real.Gamma a)⁻¹ := by
                rw [Real.exp_neg, mul_inv, mul_inv]; ring
          _ = a ^ a * Real.exp (-a) / (a * Real.Gamma a) := by rw [hp]; field_simp [ha.ne', hG]
      linear_combination -hid
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
      rw [← Real.rpow_add ha]; congr 1; ring
  refine (isBigO_regularizedGamma_diag_sub.add hterm).congr' ?_ .rfl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  rw [regularizedGamma_add_one ha ha.le]; ring

/-- **DLMF 8.11.13** on `(0, ∞)`: `P(a, a) → 1 / 2` as `a → +∞`. -/
theorem tendsto_regularizedGamma_diag_atTop :
    Tendsto (fun a : ℝ => regularizedGamma a a) atTop (𝓝 (1 / 2)) := by
  have hexp : (-9 / 2 : ℝ) = -(9 / 2) := by norm_num
  have herr := isBigO_regularizedGamma_diag_sub.trans_tendsto
    (hexp ▸ tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 9 / 2))
  have hmain : Tendsto (fun a : ℝ => 1 / 2 + (Real.sqrt (2 * Real.pi * a))⁻¹ *
      (1 / 3 + 1 / (540 * a) - 25 / (6048 * a ^ 2) - 101 / (155520 * a ^ 3)))
      atTop (𝓝 (1 / 2)) := by
    have h := ((by fun_prop : Continuous fun t : ℝ => 1 / 2 + (Real.sqrt (2 * Real.pi))⁻¹ * t *
      (1 / 3 + t ^ 2 / 540 - 25 * (t ^ 2) ^ 2 / 6048 - 101 * (t ^ 2) ^ 3 / 155520)).tendsto
      0).comp Real.tendsto_sqrt_atTop.inv_tendsto_atTop
    have h0 : (1 / 2 : ℝ) + (Real.sqrt (2 * Real.pi))⁻¹ * 0 *
        (1 / 3 + 0 ^ 2 / 540 - 25 * (0 ^ 2) ^ 2 / 6048 - 101 * (0 ^ 2) ^ 3 / 155520) = 1 / 2 := by
      ring
    rw [h0] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    simp only [Function.comp_apply, Pi.inv_apply, Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi) a,
      mul_inv, inv_pow, Real.sq_sqrt ha.le, div_eq_mul_inv]
    ring
  have hsum := (herr.add hmain).congr fun a => sub_add_cancel _ _
  rwa [zero_add] at hsum

/-- **DLMF 8.11.13** on `(0, ∞)`: `1 - P(a, a) → 1 / 2` as `a → +∞`. -/
theorem tendsto_sub_regularizedGamma_diag_atTop :
    Tendsto (fun a : ℝ => 1 - regularizedGamma a a) atTop (𝓝 (1 / 2)) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_regularizedGamma_diag_atTop
  norm_num at h; exact h

/-- `P(a + 1, a) → 1 / 2` as `a → +∞`. -/
theorem tendsto_regularizedGamma_add_one_diag_atTop :
    Tendsto (fun a : ℝ => regularizedGamma (a + 1) a) atTop (𝓝 (1 / 2)) := by
  have hexp : (-9 / 2 : ℝ) = -(9 / 2) := by norm_num
  have herr := isBigO_regularizedGamma_add_one_diag_sub.trans_tendsto
    (hexp ▸ tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 9 / 2))
  have hmain : Tendsto (fun a : ℝ => 1 / 2 - (Real.sqrt (2 * Real.pi * a))⁻¹ *
      (2 / 3 - 23 / (270 * a) + 23 / (3024 * a ^ 2) + 259 / (77760 * a ^ 3)))
      atTop (𝓝 (1 / 2)) := by
    have h := ((by fun_prop : Continuous fun t : ℝ => 1 / 2 - (Real.sqrt (2 * Real.pi))⁻¹ * t *
      (2 / 3 - 23 * t ^ 2 / 270 + 23 * (t ^ 2) ^ 2 / 3024 + 259 * (t ^ 2) ^ 3 / 77760)).tendsto
      0).comp Real.tendsto_sqrt_atTop.inv_tendsto_atTop
    have h0 : (1 / 2 : ℝ) - (Real.sqrt (2 * Real.pi))⁻¹ * 0 *
        (2 / 3 - 23 * 0 ^ 2 / 270 + 23 * (0 ^ 2) ^ 2 / 3024 + 259 * (0 ^ 2) ^ 3 / 77760) =
        1 / 2 := by ring
    rw [h0] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    simp only [Function.comp_apply, Pi.inv_apply, Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi) a,
      mul_inv, inv_pow, Real.sq_sqrt ha.le, div_eq_mul_inv]
    ring
  have hsum := (herr.add hmain).congr fun a => sub_add_cancel _ _
  rwa [zero_add] at hsum

end TauCeti

end
