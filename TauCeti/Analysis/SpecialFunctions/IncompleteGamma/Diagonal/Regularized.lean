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

private theorem isBigO_div_pow (k m : ℕ) (hkm : m ≤ k) (c : ℝ) :
    (fun a : ℝ => c / a ^ k) =O[atTop] fun a : ℝ => a ^ (-(m : ℝ)) := by
  refine IsBigO.of_bound |c| ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
  have ha0 : 0 < a := by linarith
  rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos ha0,
    Real.norm_of_nonneg (Real.rpow_nonneg ha0.le _), div_eq_mul_inv,
    ← Real.rpow_natCast a k, ← Real.rpow_neg ha0.le]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le ha (neg_le_neg (Nat.cast_le.mpr hkm))) (abs_nonneg c)

private theorem isBigO_cubic_inv_one (c0 c1 c2 c3 : ℝ) :
    (fun a : ℝ => c0 + c1 / a + c2 / a ^ 2 + c3 / a ^ 3) =O[atTop] fun _ : ℝ => (1 : ℝ) := by
  have h (k : ℕ) (c : ℝ) : (fun a : ℝ => c / a ^ k) =O[atTop] fun _ : ℝ => (1 : ℝ) :=
    (isBigO_div_pow k 0 (Nat.zero_le k) c).congr_right fun _ => by simp
  exact ((((h 0 c0).add (h 1 c1)).add (h 2 c2)).add (h 3 c3)).congr_left fun a => by ring

private theorem rpow_neg_half_mul_inv_sqrt_two_pi {a : ℝ} (ha : 0 < a) :
    a ^ (-1 / 2 : ℝ) * (Real.sqrt (2 * Real.pi))⁻¹ = (Real.sqrt (2 * Real.pi * a))⁻¹ := by
  rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi) a, mul_inv, mul_comm,
    show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg ha.le, ← Real.sqrt_eq_rpow]

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
  have hB_bdd : B =O[atTop] fun _ : ℝ => (1 : ℝ) :=
    (isBigO_cubic_inv_one 1 (-1 / 12) (1 / 288) (139 / 51840)).congr_left fun a => by
      dsimp only [B]; ring
  have hAB : (fun a : ℝ => 1 - A a * B a) =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) := by
    refine ((isBigO_div_pow 4 4 le_rfl (-571 / 1244160)).add
      (isBigO_div_pow 6 4 (by omega) (19321 / 2687385600))).congr' ?_
      (Eventually.of_forall fun _ => by norm_num)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    have : a ≠ 0 := ha.ne'; dsimp only [A, B]; field_simp; ring
  have h1 : (fun a : ℝ => -(Real.sqrt (2 * Real.pi))⁻¹ * ((S a)⁻¹ *
      ((S a - Real.sqrt (2 * Real.pi) * A a) * B a))) =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) :=
    ((isBigO_inv_stirling_one.mul (isBigO_stirling_four.mul hB_bdd)).const_mul_left _).congr_right
      fun _ => by ring
  have h2 : (fun a : ℝ => (S a)⁻¹ * (1 - A a * B a)) =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) :=
    (isBigO_inv_stirling_one.mul hAB).congr_right fun _ => by ring
  refine (h1.add h2).congr' ?_ .rfl
  filter_upwards [eventually_one_le_stirling] with a ha
  have hS0 : S a ≠ 0 := by dsimp only [S]; linarith
  have hpi0 : Real.sqrt (2 * Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  change _ = (S a)⁻¹ - (Real.sqrt (2 * Real.pi))⁻¹ * B a
  field_simp [hS0, hpi0]; ring

/-- Four-term asymptotic expansion of the diagonal regularized lower incomplete Gamma function
`TauCeti.regularizedGamma a a` as `a → +∞`, with remainder `O(a^{-9/2})`. -/
theorem isBigO_regularizedGamma_diag_sub :
    (fun a : ℝ => regularizedGamma a a -
      (1 / 2 + (Real.sqrt (2 * Real.pi * a))⁻¹ *
        (1 / 3 + 1 / (540 * a) - 25 / (6048 * a ^ 2) - 101 / (155520 * a ^ 3))))
      =O[atTop] fun a : ℝ => a ^ (-9 / 2 : ℝ) := by
  let D : ℝ → ℝ := fun a => a ^ (1 - a) * Real.exp a * (lowerIncompleteGamma a a - Real.Gamma a / 2)
  let P_D : ℝ → ℝ := fun a => 1 / 3 + 4 / (135 * a) - 8 / (2835 * a ^ 2) - 16 / (8505 * a ^ 3)
  let S_inv : ℝ → ℝ := fun a => (a ^ (1 / 2 - a) * Real.exp a * Real.Gamma a)⁻¹
  let P_S : ℝ → ℝ := fun a => (Real.sqrt (2 * Real.pi))⁻¹ *
    (1 - 1 / (12 * a) + 1 / (288 * a ^ 2) + 139 / (51840 * a ^ 3))
  let P_out : ℝ → ℝ := fun a => (Real.sqrt (2 * Real.pi))⁻¹ *
    (1 / 3 + 1 / (540 * a) - 25 / (6048 * a ^ 2) - 101 / (155520 * a ^ 3))
  have hPD : P_D =O[atTop] fun _ : ℝ => (1 : ℝ) :=
    (isBigO_cubic_inv_one (1 / 3) (4 / 135) (-8 / 2835) (-16 / 8505)).congr_left fun a => by
      dsimp only [P_D]; ring
  have hpoly : (fun a : ℝ => P_D a * P_S a - P_out a) =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) := by
    refine ((((isBigO_div_pow 4 4 le_rfl (2773 / 12247200)).sub
      (isBigO_div_pow 5 4 (by omega) (37 / 2624400))).sub
      (isBigO_div_pow 6 4 (by omega) (139 / 27556200))).const_mul_left
      (Real.sqrt (2 * Real.pi))⁻¹).congr' ?_ (Eventually.of_forall fun _ => by norm_num)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    have : a ≠ 0 := ha.ne'; dsimp only [P_D, P_S, P_out]; field_simp; ring
  have hprod : (fun a : ℝ => D a * S_inv a - P_out a) =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) :=
    ((((isBigO_mul_lowerIncompleteGamma_diag_sub_half_Gamma.mul isBigO_inv_stirling_one).congr_right
      fun _ => mul_one _).add ((hPD.mul isBigO_inv_stirling_four).congr_right
      fun _ => one_mul _)).add hpoly).congr_left fun a => by ring
  refine ((isBigO_refl (fun a : ℝ => a ^ (-1 / 2 : ℝ)) atTop).mul hprod).congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    rw [regularizedGamma_eq_div]
    have hG : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
    have he : Real.exp a ≠ 0 := (Real.exp_pos a).ne'
    have hp : a ^ (-1 / 2 : ℝ) * a ^ (1 - a) = a ^ (1 / 2 - a) := by
      rw [← Real.rpow_add ha]; congr 1; ring
    have hrel : a ^ (-1 / 2 : ℝ) * D a * S_inv a =
        lowerIncompleteGamma a a / Real.Gamma a - 1 / 2 := by
      dsimp only [D, S_inv]; rw [← mul_assoc, ← mul_assoc, hp]
      field_simp [hG, he, (Real.rpow_pos_of_pos ha (1 / 2 - a)).ne']
    dsimp only [P_out]
    linear_combination hrel -
      (1 / 3 + 1 / (540 * a) - 25 / (6048 * a ^ 2) - 101 / (155520 * a ^ 3)) *
        rpow_neg_half_mul_inv_sqrt_two_pi ha
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
      have hid : a ^ (-1 / 2 : ℝ) * (a ^ (1 / 2 - a) * Real.exp a * Real.Gamma a)⁻¹ =
          a ^ a * Real.exp (-a) / (a * Real.Gamma a) :=
        calc a ^ (-1 / 2 : ℝ) * (a ^ (1 / 2 - a) * Real.exp a * Real.Gamma a)⁻¹
            = (a ^ (-1 / 2 : ℝ) * (a ^ (1 / 2 - a))⁻¹) * Real.exp (-a) * (Real.Gamma a)⁻¹ := by
                rw [Real.exp_neg, mul_inv, mul_inv]; ring
          _ = a ^ a * Real.exp (-a) / (a * Real.Gamma a) := by rw [hp]; field_simp [ha.ne', hG]
      linear_combination -hid +
        (1 - 1 / (12 * a) + 1 / (288 * a ^ 2) + 139 / (51840 * a ^ 3)) *
          rpow_neg_half_mul_inv_sqrt_two_pi ha
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
      rw [← Real.rpow_add ha]; congr 1; ring
  refine (isBigO_regularizedGamma_diag_sub.add hterm).congr' ?_ .rfl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  rw [regularizedGamma_add_one ha ha.le]; ring

private theorem tendsto_of_sub_regularized_isBigO {f : ℝ → ℝ} (c0 c1 c2 c3 : ℝ)
    (hf : (fun a : ℝ => f a - (1 / 2 + (Real.sqrt (2 * Real.pi * a))⁻¹ *
      (c0 + c1 / a + c2 / a ^ 2 + c3 / a ^ 3))) =O[atTop] fun a : ℝ => a ^ (-9 / 2 : ℝ)) :
    Tendsto f atTop (𝓝 (1 / 2)) := by
  have herr : Tendsto (fun a : ℝ => f a - (1 / 2 + (Real.sqrt (2 * Real.pi * a))⁻¹ *
      (c0 + c1 / a + c2 / a ^ 2 + c3 / a ^ 3))) atTop (𝓝 0) :=
    hf.trans_tendsto (by
      simpa only [show (-9 / 2 : ℝ) = -(9 / 2) by norm_num] using
        tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 9 / 2))
  have hsq : Tendsto (fun a : ℝ => (Real.sqrt (2 * Real.pi * a))⁻¹) atTop (𝓝 0) :=
    (Real.tendsto_sqrt_atTop.comp (tendsto_id.const_mul_atTop (by positivity))).inv_tendsto_atTop
  have hdiv (c : ℝ) (k : ℕ) (hk : 1 ≤ k) : Tendsto (fun a : ℝ => c / a ^ k) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by omega))
  have hpoly : Tendsto (fun a : ℝ => c0 + c1 / a + c2 / a ^ 2 + c3 / a ^ 3) atTop (𝓝 c0) := by
    simpa [pow_one] using (((tendsto_const_nhds (x := c0)).add (hdiv c1 1 le_rfl)).add
      (hdiv c2 2 (by omega))).add (hdiv c3 3 (by omega))
  have hmain : Tendsto (fun a : ℝ => 1 / 2 + (Real.sqrt (2 * Real.pi * a))⁻¹ *
      (c0 + c1 / a + c2 / a ^ 2 + c3 / a ^ 3)) atTop (𝓝 (1 / 2)) := by
    simpa using tendsto_const_nhds.add (hsq.mul hpoly)
  simpa using herr.add hmain

/-- **DLMF 8.11.13** on `(0, ∞)`: `P(a, a) → 1 / 2` as `a → +∞`. -/
theorem tendsto_regularizedGamma_diag_atTop :
    Tendsto (fun a : ℝ => regularizedGamma a a) atTop (𝓝 (1 / 2)) :=
  tendsto_of_sub_regularized_isBigO (1 / 3) (1 / 540) (-25 / 6048) (-101 / 155520)
    (isBigO_regularizedGamma_diag_sub.congr_left fun a => by ring)

/-- **DLMF 8.11.13** on `(0, ∞)`: `1 - P(a, a) → 1 / 2` as `a → +∞`. -/
theorem tendsto_sub_regularizedGamma_diag_atTop :
    Tendsto (fun a : ℝ => 1 - regularizedGamma a a) atTop (𝓝 (1 / 2)) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_regularizedGamma_diag_atTop
  norm_num at h; exact h

/-- `P(a + 1, a) → 1 / 2` as `a → +∞`. -/
theorem tendsto_regularizedGamma_add_one_diag_atTop :
    Tendsto (fun a : ℝ => regularizedGamma (a + 1) a) atTop (𝓝 (1 / 2)) :=
  tendsto_of_sub_regularized_isBigO (-2 / 3) (23 / 270) (-23 / 3024) (-259 / 77760)
    (isBigO_regularizedGamma_add_one_diag_sub.congr_left fun a => by ring)

end TauCeti

end
