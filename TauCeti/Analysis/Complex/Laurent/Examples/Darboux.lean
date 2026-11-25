/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Laurent.Darboux
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.Complex.Laurent.Expansion

/-!
# Checks for Darboux's method

This file checks Darboux's comparison theorem `TauCeti.tendsto_zpow_smul_circleLaurentCoeff_sub`
(DLMF 2.10.29) on explicit simple poles, using the Laurent coefficients of `(a - z)⁻¹` from
`TauCeti.circleLaurentCoeff_inv_sub_of_lt_norm`.

* On every circle `|z| = ρ` with `0 < ρ < 1`, the Laurent coefficients of `1 / (1 - z)` are `1`
  in every nonnegative degree and `0` in every negative degree.
* For `f(z) = 1 / (1 - z) + 1 / (2 - z)` and `g(z) = 1 / (1 - z)`, the coefficient difference
  `f_n - g_n` is computed exactly and shown to tend to `0` by Darboux's method with `r = 1`.

It also checks the form with boundary singularities,
`TauCeti.tendsto_zpow_smul_circleLaurentCoeff_of_isBigO_rpow`, on which DLMF 2.10.30 rests:

* the principal branch of `(1 - z) ^ (-1/2)` has no continuous extension to the unit circle, but it
  is `O(|z - 1| ^ (1/2 - 1))` near `z = 1` and continuous elsewhere on the closed disc, so its
  Laurent coefficients tend to `0`.
-/

public section

open Complex Set Metric Filter Asymptotics
open scoped Topology

namespace TauCeti

/-- On every circle `|z| = ρ` with `0 < ρ < 1`, the Laurent coefficients of `1 / (1 - z)` are `1`
in every nonnegative degree and `0` in every negative degree. -/
example {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (n : ℤ) :
    circleLaurentCoeff (fun z ↦ (1 - z)⁻¹) 0 ρ n = if 0 ≤ n then 1 else 0 := by
  simpa using circleLaurentCoeff_inv_sub_of_lt_norm (a := 1) (c := 0) hρ (by simpa using hρ1) n

/-- Darboux's method with `f(z) = 1 / (1 - z) + 1 / (2 - z)`, `g(z) = 1 / (1 - z)` and `r = 1`:
`f - g = 1 / (2 - z)` is continuous on `|z| ≤ 1`, and `f_n - g_n = 2 ^ (-n - 1)` for `n ≥ 0` and
`0` for `n < 0`, which is `o(1)` as `n → ±∞`. -/
example {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    (∀ n : ℤ, circleLaurentCoeff (fun z ↦ (1 - z)⁻¹ + (2 - z)⁻¹) 0 ρ n -
        circleLaurentCoeff (fun z ↦ (1 - z)⁻¹) 0 ρ n = if 0 ≤ n then 2 ^ (-n - 1) else 0) ∧
      Tendsto (fun n : ℤ ↦ (1 : ℝ) ^ n • (circleLaurentCoeff (fun z ↦ (1 - z)⁻¹ + (2 - z)⁻¹) 0 ρ n -
        circleLaurentCoeff (fun z ↦ (1 - z)⁻¹) 0 ρ n)) cofinite (𝓝 0) := by
  have hball : ∀ a : ℂ, 1 ≤ ‖a‖ → ∀ z ∈ ball (0 : ℂ) 1 \ {0}, a - z ≠ 0 := fun a ha z hz h ↦ by
    rw [← sub_eq_zero.1 h, Set.mem_sdiff, mem_ball_zero_iff] at hz
    exact (ha.trans_lt hz.1).false
  have hdiff : ∀ a : ℂ, 1 ≤ ‖a‖ → DifferentiableOn ℂ (fun z : ℂ ↦ (a - z)⁻¹) (ball 0 1 \ {0}) :=
    fun a ha ↦ ((differentiableOn_const a).sub differentiableOn_id).inv (hball a ha)
  refine ⟨fun n ↦ ?_, tendsto_zpow_smul_circleLaurentCoeff_sub (h := fun z ↦ (2 - z)⁻¹) le_rfl hρ
    hρ1 (by rw [closedBall_zero]; exact (hdiff 1 (by simp)).add (hdiff 2 (by simp)))
    (by rw [closedBall_zero]; exact hdiff 1 (by simp)) ?_ fun z _ ↦ ?_⟩
  · have hsph : ∀ a : ℂ, 1 ≤ ‖a‖ → CircleIntegrable (fun z : ℂ ↦ (a - z)⁻¹) 0 ρ := fun a ha ↦
      ((hdiff a ha).continuousOn.mono (subset_sdiff_singleton (sphere_subset_ball hρ1)
        fun h0 ↦ ne_of_mem_sphere h0 hρ.ne' rfl)).circleIntegrable hρ.le
    rw [circleLaurentCoeff_add (hsph 1 (by simp)) (hsph 2 (by simp)), add_sub_cancel_left,
      circleLaurentCoeff_inv_sub_of_lt_norm hρ (by simpa using hρ1.trans one_lt_two), sub_zero]
  · refine (continuousOn_const.sub continuousOn_id).inv₀ fun z hz h ↦ ?_
    simp only [Pi.sub_apply, id_eq, sub_eq_zero] at h
    subst h
    norm_num at hz
  · simp

/-- The principal branch of `(1 - z) ^ (-1/2)` is unbounded near `z = 1`, where it is
`O(|z - 1| ^ (1/2 - 1))`, and continuous elsewhere on the closed unit disc. So its Laurent
coefficients on every circle `|z| = ρ` with `0 < ρ < 1` tend to `0` as `n → ±∞`. -/
example {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    Tendsto (fun n : ℤ ↦ circleLaurentCoeff (fun z : ℂ ↦ (1 - z) ^ ((-1 / 2 : ℝ) : ℂ)) 0 ρ n)
      cofinite (𝓝 0) := by
  -- On the closed unit disc, `1 - z` lies in the slit plane except at `z = 1`.
  have hslit : ∀ z ∈ closedBall (0 : ℂ) 1, z ≠ 1 → 1 - z ∈ slitPlane := fun z hz hz1 ↦ by
    rw [mem_closedBall_zero_iff] at hz
    refine Or.inl ?_
    rw [sub_re, one_re, sub_pos]
    refine (re_le_norm z).trans hz |>.lt_of_ne fun h ↦ hz1 (Complex.ext h ?_)
    have h2 : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by rw [← normSq_eq_norm_sq, normSq_apply]
    rw [one_im]
    nlinarith [sq_nonneg z.im, norm_nonneg z]
  simpa using tendsto_zpow_smul_circleLaurentCoeff_of_isBigO_rpow
    (f := fun z : ℂ ↦ (1 - z) ^ ((-1 / 2 : ℝ) : ℂ)) (r := 1) hρ hρ1.le
    countable_empty (finite_singleton 1) (by simp)
    ((continuousOn_const.sub continuousOn_id).cpow_const fun z hz ↦
      hslit z hz.1.1 hz.2)
    (fun z hz ↦ ((differentiableAt_const _).sub differentiableAt_id).cpow_const
      (hslit z (ball_subset_closedBall hz.1.1) fun h ↦ by simp [h] at hz))
    (fun w hw ↦ ⟨1 / 2, by norm_num, IsBigO.of_bound 1 (Eventually.of_forall fun z ↦ by
      rw [mem_singleton_iff.1 hw, norm_cpow_real, norm_sub_rev, Real.norm_of_nonneg
        (Real.rpow_nonneg (norm_nonneg _) _)]
      norm_num)⟩)

end TauCeti
