/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Diagonal.Basic

/-!
# Four-term Stirling expansion of the real Gamma function

Adding the normalized lower and upper diagonal incomplete Gamma expansions from
`TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Diagonal.Basic`
(`TauCeti.isBigO_mul_lowerIncompleteGamma_diag_sub` and
`TauCeti.isBigO_mul_Gamma_sub_lowerIncompleteGamma_diag_sub`) cancels every odd-order term and
recovers the four-term Poincaré-type Stirling expansion of `a^{1/2 - a} e^a Γ(a)` as `a → +∞` with
remainder `O(a^{-4})` (DLMF 5.11.3–5.11.4). Inverting the truncated asymptotic series yields the
companion four-term expansion of `(a^{1/2 - a} e^a Γ(a))⁻¹` with remainder `O(a^{-4})`.

## Main results

* `TauCeti.isBigO_mul_Gamma_sub_stirling`: four-term Stirling expansion
  `a^{1/2 - a} e^a Γ(a) = √(2π) (1 + 1/(12 a) + 1/(288 a²) - 139/(51840 a³)) + O(a^{-4})`
  as `a → +∞` (DLMF 5.11.3–5.11.4).
* `TauCeti.isBigO_inv_mul_Gamma_sub_stirling`: four-term reciprocal Stirling expansion
  `(a^{1/2 - a} e^a Γ(a))⁻¹ = (√(2π))⁻¹ (1 - 1/(12 a) + 1/(288 a²) + 139/(51840 a³)) + O(a^{-4})`
  as `a → +∞`.

## References

* *NIST Digital Library of Mathematical Functions*, [§5.11(i)](https://dlmf.nist.gov/5.11.i),
  Eqs. 5.11.3–5.11.4.
-/

public section

noncomputable section

open Asymptotics Filter
open scoped Topology

namespace TauCeti

/-- **DLMF 5.11.3–5.11.4**: four-term Stirling asymptotic expansion of `a^{1/2 - a} e^a Γ(a)` as
`a → +∞`, with remainder `O(a^{-4})`. -/
theorem isBigO_mul_Gamma_sub_stirling :
    (fun a : ℝ => a ^ (1 / 2 - a) * Real.exp a * Real.Gamma a -
      Real.sqrt (2 * Real.pi) * (1 + 1 / (12 * a) + 1 / (288 * a ^ 2) - 139 / (51840 * a ^ 3)))
      =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) := by
  have htot := isBigO_mul_lowerIncompleteGamma_diag_sub.add
    isBigO_mul_Gamma_sub_lowerIncompleteGamma_diag_sub
  refine ((isBigO_refl (fun a : ℝ => a ^ (-1 / 2 : ℝ)) atTop).mul htot).congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    have hp (p : ℝ) : a ^ (-1 / 2 : ℝ) * a ^ p = a ^ (p - 1 / 2) := by
      rw [← Real.rpow_add ha]; congr 1; ring
    have hn (k : ℕ) : a ^ (-(k : ℝ)) = 1 / a ^ k := by
      rw [Real.rpow_neg ha.le, Real.rpow_natCast, one_div]
    have hp0 : a ^ (-1 / 2 : ℝ) * a ^ (1 - a) = a ^ (1 / 2 - a) := by
      rw [hp]; congr 1; ring
    have hp1 : a ^ (-1 / 2 : ℝ) * a ^ (1 / 2 : ℝ) = 1 := by rw [hp]; norm_num
    have hp2 : a ^ (-1 / 2 : ℝ) * a ^ (-1 / 2 : ℝ) = 1 / a := by
      have heq : (-1 / 2 : ℝ) - 1 / 2 = -((1 : ℕ) : ℝ) := by norm_num
      rw [hp, heq, hn 1, pow_one]
    have hp3 : a ^ (-1 / 2 : ℝ) * a ^ (-3 / 2 : ℝ) = 1 / a ^ 2 := by
      have heq : (-3 / 2 : ℝ) - 1 / 2 = -((2 : ℕ) : ℝ) := by norm_num
      rw [hp, heq, hn 2]
    have hp4 : a ^ (-1 / 2 : ℝ) * a ^ (-5 / 2 : ℝ) = 1 / a ^ 3 := by
      have heq : (-5 / 2 : ℝ) - 1 / 2 = -((3 : ℕ) : ℝ) := by norm_num
      rw [hp, heq, hn 3]
    have hpi : 2 * Real.sqrt (Real.pi / 2) = Real.sqrt (2 * Real.pi) := by
      rw [Real.sqrt_div Real.pi_pos.le, Real.sqrt_mul zero_le_two]
      have : (2 : ℝ) / Real.sqrt 2 = Real.sqrt 2 := by
        rw [div_eq_iff (Real.sqrt_pos.mpr two_pos).ne', Real.mul_self_sqrt zero_le_two]
      linear_combination Real.sqrt Real.pi * this
    linear_combination
      Real.exp a * Real.Gamma a * hp0 - Real.sqrt (2 * Real.pi) * hp1 - hpi * (a ^ (-1 / 2 : ℝ) *
        a ^ (1 / 2 : ℝ)) - (Real.sqrt (2 * Real.pi) / 12) * hp2 -
        (Real.sqrt (2 * Real.pi) / 288) * hp3 + (139 * Real.sqrt (2 * Real.pi) / 51840) * hp4
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    rw [← Real.rpow_add ha]; congr 1; ring

private theorem eventually_one_le_stirling :
    ∀ᶠ a : ℝ in atTop, 1 ≤ a ^ (1 / 2 - a) * Real.exp a * Real.Gamma a := by
  obtain ⟨C, hC⟩ := isBigO_mul_Gamma_sub_stirling.bound
  filter_upwards [eventually_ge_atTop (max 2 (2 * |C| + 1)), hC] with a ha hCa
  have ha2 : 2 ≤ a := le_trans (le_max_left _ _) ha
  have haC : 2 * |C| + 1 ≤ a := le_trans (le_max_right _ _) ha
  have hA : 3 / 4 ≤ 1 + 1 / (12 * a) + 1 / (288 * a ^ 2) - 139 / (51840 * a ^ 3) := by
    have h1 : 0 ≤ 1 / (12 * a) := by positivity
    have h2 : 0 ≤ 1 / (288 * a ^ 2) := by positivity
    have h3 : 139 / (51840 * a ^ 3) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg a]
    linarith
  have hpi : 2 ≤ Real.sqrt (2 * Real.pi) :=
    calc (2 : ℝ) = Real.sqrt (2 ^ 2) := (Real.sqrt_sq zero_le_two).symm
      _ ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_le_sqrt (by linarith [Real.two_le_pi])
  have ha4 : a ^ (-4 : ℝ) ≤ (2 * |C| + 1)⁻¹ :=
    calc a ^ (-4 : ℝ) ≤ a ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = a⁻¹ := Real.rpow_neg_one a
      _ ≤ (2 * |C| + 1)⁻¹ := inv_anti₀ (by positivity) haC
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)] at hCa
  have herr : |a ^ (1 / 2 - a) * Real.exp a * Real.Gamma a - Real.sqrt (2 * Real.pi) *
      (1 + 1 / (12 * a) + 1 / (288 * a ^ 2) - 139 / (51840 * a ^ 3))| ≤ 1 / 2 :=
    calc _ ≤ C * a ^ (-4 : ℝ) := hCa
      _ ≤ |C| * (2 * |C| + 1)⁻¹ := mul_le_mul (le_abs_self C) ha4 (by positivity) (abs_nonneg C)
      _ ≤ 1 / 2 := by rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]; linarith [abs_nonneg C]
  nlinarith [(abs_le.mp herr).1]

private theorem isBigO_inv_stirling_one :
    (fun a : ℝ => (a ^ (1 / 2 - a) * Real.exp a * Real.Gamma a)⁻¹)
      =O[atTop] fun _ : ℝ => (1 : ℝ) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_one_le_stirling] with a ha
  rw [Real.norm_of_nonneg (by positivity), norm_one, one_mul]
  exact inv_le_one_of_one_le₀ ha

/-- Four-term reciprocal Stirling asymptotic expansion of `(a^{1/2 - a} e^a Γ(a))⁻¹` as `a → +∞`,
with remainder `O(a^{-4})`, obtained by inverting `TauCeti.isBigO_mul_Gamma_sub_stirling`. -/
theorem isBigO_inv_mul_Gamma_sub_stirling :
    (fun a : ℝ => (a ^ (1 / 2 - a) * Real.exp a * Real.Gamma a)⁻¹ -
      (Real.sqrt (2 * Real.pi))⁻¹ *
        (1 - 1 / (12 * a) + 1 / (288 * a ^ 2) + 139 / (51840 * a ^ 3)))
      =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) := by
  let S : ℝ → ℝ := fun a => a ^ (1 / 2 - a) * Real.exp a * Real.Gamma a
  let A : ℝ → ℝ := fun a => 1 + 1 / (12 * a) + 1 / (288 * a ^ 2) - 139 / (51840 * a ^ 3)
  let B : ℝ → ℝ := fun a => 1 - 1 / (12 * a) + 1 / (288 * a ^ 2) + 139 / (51840 * a ^ 3)
  have hB_bdd : B =O[atTop] fun _ : ℝ => (1 : ℝ) :=
    ((((by fun_prop :
        Continuous fun t : ℝ => 1 - t / 12 + t ^ 2 / 288 + 139 * t ^ 3 / 51840).tendsto 0).comp
        tendsto_inv_atTop_zero).congr fun a => by
      simp only [Function.comp_apply, B, div_eq_mul_inv, mul_inv, inv_pow]; ring).isBigO_one ℝ
  have hAB : (fun a : ℝ => 1 - A a * B a) =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) := by
    have hq := (((by fun_prop :
        Continuous fun t : ℝ => -571 / 1244160 + 19321 * t ^ 2 / 2687385600).tendsto 0).comp
        tendsto_inv_atTop_zero).isBigO_one ℝ
    refine ((isBigO_refl (fun a : ℝ => a ^ (-4 : ℝ)) atTop).mul hq).congr' ?_
      (Eventually.of_forall fun _ => mul_one _)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    have ha4 : a ^ (-4 : ℝ) = (a ^ 4)⁻¹ := by
      have hneg : (-4 : ℝ) = -((4 : ℕ) : ℝ) := by norm_num
      rw [hneg, Real.rpow_neg ha.le, Real.rpow_natCast]
    have : a ≠ 0 := ha.ne'
    rw [ha4]; dsimp only [Function.comp_apply, A, B]; field_simp; ring
  have h1 : (fun a : ℝ => -(Real.sqrt (2 * Real.pi))⁻¹ * ((S a)⁻¹ *
      ((S a - Real.sqrt (2 * Real.pi) * A a) * B a))) =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) :=
    ((isBigO_inv_stirling_one.mul (isBigO_mul_Gamma_sub_stirling.mul hB_bdd)).const_mul_left
      _).congr_right fun _ => by ring
  have h2 : (fun a : ℝ => (S a)⁻¹ * (1 - A a * B a)) =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) :=
    (isBigO_inv_stirling_one.mul hAB).congr_right fun _ => by ring
  refine (h1.add h2).congr' ?_ .rfl
  filter_upwards [eventually_one_le_stirling] with a ha
  have hS0 : a ^ (1 / 2 - a) * Real.exp a * Real.Gamma a ≠ 0 := by linarith
  have hpi0 : Real.sqrt (2 * Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  dsimp only [S, B]
  linear_combination
    -(Real.sqrt (2 * Real.pi))⁻¹ *
        (1 - 1 / (12 * a) + 1 / (288 * a ^ 2) + 139 / (51840 * a ^ 3)) * inv_mul_cancel₀ hS0 +
      (a ^ (1 / 2 - a) * Real.exp a * Real.Gamma a)⁻¹ * A a *
        (1 - 1 / (12 * a) + 1 / (288 * a ^ 2) + 139 / (51840 * a ^ 3)) * inv_mul_cancel₀ hpi0

end TauCeti

end
