/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Basic

import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Diagonal.Basic

/-!
# Diagonal asymptotics of the regularized incomplete Gamma function

Adding the normalized lower and upper diagonal expansions
`TauCeti.isBigO_mul_lowerIncompleteGamma_diag_sub` and
`TauCeti.isBigO_mul_Gamma_sub_lowerIncompleteGamma_diag_sub` cancels every odd-order term and
recovers the four-term Stirling expansion of `a^{1/2 - a} e^a Γ(a)` to `O(a^{-4})`. Inverting
this series and multiplying by the pure integer-power expansion
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

/-- Four-term Stirling expansion of `a^{1/2 - a} e^a Γ(a)` obtained by adding the lower and upper
diagonal expansions. -/
private theorem isBigO_stirling_four :
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
    have hp0 := hp (1 - a)
    have hp1 : a ^ (-1 / 2 : ℝ) * a ^ (1 / 2 : ℝ) = 1 := by rw [hp]; norm_num
    have hp2 : a ^ (-1 / 2 : ℝ) * a ^ (-1 / 2 : ℝ) = 1 / a := by
      rw [hp, show (-1 / 2 : ℝ) - 1 / 2 = -((1 : ℕ) : ℝ) by norm_num, hn 1, pow_one]
    have hp3 : a ^ (-1 / 2 : ℝ) * a ^ (-3 / 2 : ℝ) = 1 / a ^ 2 := by
      rw [hp, show (-3 / 2 : ℝ) - 1 / 2 = -((2 : ℕ) : ℝ) by norm_num, hn 2]
    have hp4 : a ^ (-1 / 2 : ℝ) * a ^ (-5 / 2 : ℝ) = 1 / a ^ 3 := by
      rw [hp, show (-5 / 2 : ℝ) - 1 / 2 = -((3 : ℕ) : ℝ) by norm_num, hn 3]
    have hpi : 2 * Real.sqrt (Real.pi / 2) = Real.sqrt (2 * Real.pi) := by
      rw [Real.sqrt_div Real.pi_pos.le, Real.sqrt_mul zero_le_two]
      have : (2 : ℝ) / Real.sqrt 2 = Real.sqrt 2 := by
        rw [div_eq_iff (Real.sqrt_pos.mpr two_pos).ne', Real.mul_self_sqrt zero_le_two]
      linear_combination Real.sqrt Real.pi * this
    rw [show (1 - a) - 1 / 2 = 1 / 2 - a by ring] at hp0
    linear_combination
      Real.exp a * Real.Gamma a * hp0 - Real.sqrt (2 * Real.pi) * hp1 - hpi * (a ^ (-1 / 2 : ℝ) *
        a ^ (1 / 2 : ℝ)) - (Real.sqrt (2 * Real.pi) / 12) * hp2 -
        (Real.sqrt (2 * Real.pi) / 288) * hp3 + (139 * Real.sqrt (2 * Real.pi) / 51840) * hp4
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    rw [← Real.rpow_add ha]; congr 1; ring

private theorem eventually_one_le_stirling :
    ∀ᶠ a : ℝ in atTop, 1 ≤ a ^ (1 / 2 - a) * Real.exp a * Real.Gamma a := by
  obtain ⟨C, hC⟩ := isBigO_stirling_four.bound
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

private theorem isBigO_inv_stirling_four :
    (fun a : ℝ => (a ^ (1 / 2 - a) * Real.exp a * Real.Gamma a)⁻¹ -
      (Real.sqrt (2 * Real.pi))⁻¹ * (1 - 1 / (12 * a) + 1 / (288 * a ^ 2) + 139 / (51840 * a ^ 3)))
      =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) := by
  let S : ℝ → ℝ := fun a => a ^ (1 / 2 - a) * Real.exp a * Real.Gamma a
  let A : ℝ → ℝ := fun a => 1 + 1 / (12 * a) + 1 / (288 * a ^ 2) - 139 / (51840 * a ^ 3)
  let B : ℝ → ℝ := fun a => 1 - 1 / (12 * a) + 1 / (288 * a ^ 2) + 139 / (51840 * a ^ 3)
  have hdiv (c d : ℝ) (hd : 0 < d) (k : ℕ) (hk : k ≠ 0) :
      Tendsto (fun a : ℝ => c / (d * a ^ k)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop hk).const_mul_atTop hd)
  have hB_lim : Tendsto B atTop (𝓝 1) := by
    simpa [B, pow_one] using (((tendsto_const_nhds (x := (1 : ℝ))).sub
      (hdiv 1 12 (by norm_num) 1 one_ne_zero)).add
      (hdiv 1 288 (by norm_num) 2 (by norm_num))).add
      (hdiv 139 51840 (by norm_num) 3 (by norm_num))
  have hB_bdd : B =O[atTop] fun _ : ℝ => (1 : ℝ) := hB_lim.isBigO_one ℝ
  have hAB : (fun a : ℝ => 1 - A a * B a) =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) := by
    have hq_lim : Tendsto (fun a : ℝ => -571 / 1244160 + 19321 / (2687385600 * a ^ 2))
        atTop (𝓝 (-571 / 1244160)) := by
      simpa using (tendsto_const_nhds (x := (-571 / 1244160 : ℝ))).add
        (hdiv 19321 2687385600 (by norm_num) 2 (by norm_num))
    refine ((isBigO_refl (fun a : ℝ => a ^ (-4 : ℝ)) atTop).mul (hq_lim.isBigO_one ℝ)).congr' ?_
      (Eventually.of_forall fun _ => mul_one _)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    have ha4 : a ^ (-4 : ℝ) = (a ^ 4)⁻¹ := by
      rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg ha.le, Real.rpow_natCast]
    have : a ≠ 0 := ha.ne'
    rw [ha4]; dsimp only [A, B]; field_simp; ring
  have h1 : (fun a : ℝ => -(Real.sqrt (2 * Real.pi))⁻¹ * ((S a)⁻¹ *
      ((S a - Real.sqrt (2 * Real.pi) * A a) * B a))) =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) :=
    ((isBigO_inv_stirling_one.mul (isBigO_stirling_four.mul hB_bdd)).const_mul_left _).congr_right
      fun _ => by ring
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
  have hdiv (c d : ℝ) (hd : 0 < d) (k : ℕ) (hk : k ≠ 0) :
      Tendsto (fun a : ℝ => c / (d * a ^ k)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop hk).const_mul_atTop hd)
  have hPD_lim : Tendsto P_D atTop (𝓝 (1 / 3)) := by
    simpa [P_D, pow_one] using (((tendsto_const_nhds (x := (1 / 3 : ℝ))).add
      (hdiv 4 135 (by norm_num) 1 one_ne_zero)).sub
      (hdiv 8 2835 (by norm_num) 2 (by norm_num))).sub
      (hdiv 16 8505 (by norm_num) 3 (by norm_num))
  have hPD : P_D =O[atTop] fun _ : ℝ => (1 : ℝ) := hPD_lim.isBigO_one ℝ
  have hpoly : (fun a : ℝ => P_D a * P_S a - P_out a) =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) := by
    have hq_lim : Tendsto (fun a : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
        (2773 / 12247200 - 37 / (2624400 * a) - 139 / (27556200 * a ^ 2)))
        atTop (𝓝 ((Real.sqrt (2 * Real.pi))⁻¹ * (2773 / 12247200))) := by
      simpa [pow_one] using (((tendsto_const_nhds (x := (2773 / 12247200 : ℝ))).sub
        (hdiv 37 2624400 (by norm_num) 1 one_ne_zero)).sub
        (hdiv 139 27556200 (by norm_num) 2 (by norm_num))).const_mul (Real.sqrt (2 * Real.pi))⁻¹
    refine ((isBigO_refl (fun a : ℝ => a ^ (-4 : ℝ)) atTop).mul (hq_lim.isBigO_one ℝ)).congr' ?_
      (Eventually.of_forall fun _ => mul_one _)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    have ha4 : a ^ (-4 : ℝ) = (a ^ 4)⁻¹ := by
      rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg ha.le, Real.rpow_natCast]
    have : a ≠ 0 := ha.ne'
    rw [ha4]; dsimp only [P_D, P_S, P_out]; field_simp; ring
  exact ((((isBigO_mul_lowerIncompleteGamma_diag_sub_half_Gamma.mul
      isBigO_inv_stirling_one).congr_right fun _ => mul_one _).add
      ((hPD.mul isBigO_inv_stirling_four).congr_right fun _ => one_mul _)).add
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
    rw [regularizedGamma_eq_div]
    have hG : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
    have he : Real.exp a ≠ 0 := (Real.exp_pos a).ne'
    have hp : a ^ (-1 / 2 : ℝ) * a ^ (1 - a) = a ^ (1 / 2 - a) := by
      rw [← Real.rpow_add ha]; congr 1; ring
    have hsqrt : a ^ (-1 / 2 : ℝ) * (Real.sqrt (2 * Real.pi))⁻¹ =
        (Real.sqrt (2 * Real.pi * a))⁻¹ := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi) a, mul_inv, mul_comm,
        show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg ha.le, ← Real.sqrt_eq_rpow]
    have hrel : a ^ (-1 / 2 : ℝ) *
        (a ^ (1 - a) * Real.exp a * (lowerIncompleteGamma a a - Real.Gamma a / 2)) *
        (a ^ (1 / 2 - a) * Real.exp a * Real.Gamma a)⁻¹ =
        lowerIncompleteGamma a a / Real.Gamma a - 1 / 2 := by
      rw [← mul_assoc, ← mul_assoc, hp]
      field_simp [hG, he, (Real.rpow_pos_of_pos ha (1 / 2 - a)).ne']
    linear_combination hrel -
      (1 / 3 + 1 / (540 * a) - 25 / (6048 * a ^ 2) - 101 / (155520 * a ^ 3)) * hsqrt
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
      isBigO_inv_stirling_four).neg_left).congr' ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
      rw [Real.Gamma_add_one ha.ne']
      have hG : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
      have hp : a ^ (-1 / 2 : ℝ) * (a ^ (1 / 2 - a))⁻¹ = a ^ a / a := by
        rw [← Real.rpow_neg ha.le, ← Real.rpow_add ha,
          show (-1 / 2 : ℝ) + -(1 / 2 - a) = a + (-1) by ring,
          Real.rpow_add ha, Real.rpow_neg_one, div_eq_mul_inv]
      have hsqrt : a ^ (-1 / 2 : ℝ) * (Real.sqrt (2 * Real.pi))⁻¹ =
          (Real.sqrt (2 * Real.pi * a))⁻¹ := by
        rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi) a, mul_inv, mul_comm,
          show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg ha.le, ← Real.sqrt_eq_rpow]
      have hid : a ^ (-1 / 2 : ℝ) * (a ^ (1 / 2 - a) * Real.exp a * Real.Gamma a)⁻¹ =
          a ^ a * Real.exp (-a) / (a * Real.Gamma a) :=
        calc a ^ (-1 / 2 : ℝ) * (a ^ (1 / 2 - a) * Real.exp a * Real.Gamma a)⁻¹
            = (a ^ (-1 / 2 : ℝ) * (a ^ (1 / 2 - a))⁻¹) * Real.exp (-a) * (Real.Gamma a)⁻¹ := by
                rw [Real.exp_neg, mul_inv, mul_inv]; ring
          _ = a ^ a * Real.exp (-a) / (a * Real.Gamma a) := by rw [hp]; field_simp [ha.ne', hG]
      linear_combination -hid +
        (1 - 1 / (12 * a) + 1 / (288 * a ^ 2) + 139 / (51840 * a ^ 3)) * hsqrt
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
      rw [← Real.rpow_add ha]; congr 1; ring
  refine (isBigO_regularizedGamma_diag_sub.add hterm).congr' ?_ .rfl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  rw [regularizedGamma_add_one ha ha.le]; ring

/-- **DLMF 8.11.13** on `(0, ∞)`: `P(a, a) → 1 / 2` as `a → +∞`. -/
theorem tendsto_regularizedGamma_diag_atTop :
    Tendsto (fun a : ℝ => regularizedGamma a a) atTop (𝓝 (1 / 2)) := by
  have herr := isBigO_regularizedGamma_diag_sub.trans_tendsto (by
    simpa only [show (-9 / 2 : ℝ) = -(9 / 2) by norm_num] using
      tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 9 / 2))
  have hsq : Tendsto (fun a : ℝ => (Real.sqrt (2 * Real.pi * a))⁻¹) atTop (𝓝 0) :=
    (Real.tendsto_sqrt_atTop.comp
      (tendsto_id.const_mul_atTop (by positivity))).inv_tendsto_atTop
  have hdiv (c d : ℝ) (hd : 0 < d) (k : ℕ) (hk : k ≠ 0) :
      Tendsto (fun a : ℝ => c / (d * a ^ k)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop hk).const_mul_atTop hd)
  have hpoly : Tendsto (fun a : ℝ => 1 / 3 + 1 / (540 * a) - 25 / (6048 * a ^ 2) -
      101 / (155520 * a ^ 3)) atTop (𝓝 (1 / 3)) := by
    simpa [pow_one] using (((tendsto_const_nhds (x := (1 / 3 : ℝ))).add
      (hdiv 1 540 (by norm_num) 1 one_ne_zero)).sub
      (hdiv 25 6048 (by norm_num) 2 (by norm_num))).sub
      (hdiv 101 155520 (by norm_num) 3 (by norm_num))
  simpa using herr.add ((tendsto_const_nhds (x := (1 / 2 : ℝ))).add (hsq.mul hpoly))

/-- **DLMF 8.11.13** on `(0, ∞)`: `1 - P(a, a) → 1 / 2` as `a → +∞`. -/
theorem tendsto_sub_regularizedGamma_diag_atTop :
    Tendsto (fun a : ℝ => 1 - regularizedGamma a a) atTop (𝓝 (1 / 2)) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_regularizedGamma_diag_atTop
  norm_num at h; exact h

/-- `P(a + 1, a) → 1 / 2` as `a → +∞`. -/
theorem tendsto_regularizedGamma_add_one_diag_atTop :
    Tendsto (fun a : ℝ => regularizedGamma (a + 1) a) atTop (𝓝 (1 / 2)) := by
  have herr := isBigO_regularizedGamma_add_one_diag_sub.trans_tendsto (by
    simpa only [show (-9 / 2 : ℝ) = -(9 / 2) by norm_num] using
      tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 9 / 2))
  have hsq : Tendsto (fun a : ℝ => (Real.sqrt (2 * Real.pi * a))⁻¹) atTop (𝓝 0) :=
    (Real.tendsto_sqrt_atTop.comp
      (tendsto_id.const_mul_atTop (by positivity))).inv_tendsto_atTop
  have hdiv (c d : ℝ) (hd : 0 < d) (k : ℕ) (hk : k ≠ 0) :
      Tendsto (fun a : ℝ => c / (d * a ^ k)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop hk).const_mul_atTop hd)
  have hpoly : Tendsto (fun a : ℝ => 2 / 3 - 23 / (270 * a) + 23 / (3024 * a ^ 2) +
      259 / (77760 * a ^ 3)) atTop (𝓝 (2 / 3)) := by
    simpa [pow_one] using (((tendsto_const_nhds (x := (2 / 3 : ℝ))).sub
      (hdiv 23 270 (by norm_num) 1 one_ne_zero)).add
      (hdiv 23 3024 (by norm_num) 2 (by norm_num))).add
      (hdiv 259 77760 (by norm_num) 3 (by norm_num))
  simpa using herr.add ((tendsto_const_nhds (x := (1 / 2 : ℝ))).sub (hsq.mul hpoly))

end TauCeti

end
