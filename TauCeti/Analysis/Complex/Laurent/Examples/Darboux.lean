/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Laurent.Darboux
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
-/

public section

open Complex Set Metric Filter
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

end TauCeti
