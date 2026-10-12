/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5, Claude Opus 4.8, Claude Opus 5
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Square-root displacement estimates

Two estimates comparing the real square-root and inverse-square-root functions
with the identity near `1`. These bounds control scalar spectral factors of
positive operators close to the identity.

## Main results

* `Real.abs_sqrt_sub_one_le_abs_sub_one`: for every real `μ`,
  `|√μ - 1| ≤ |μ - 1|`.
* `Real.abs_one_sub_inv_sqrt_le`: if `|μ - 1| ≤ δ ≤ 1/2`,
  `|1 - (√μ)⁻¹| ≤ δ`.

## References

[AIQ DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization),
`ForTauCeti/Analysis/SpecialFunctions/Sqrt.lean`.
-/

public section

namespace Real

/-- For every real `μ`, the square root is no farther from `1` than `μ` is:
`|√μ - 1| ≤ |μ - 1|`. -/
theorem abs_sqrt_sub_one_le_abs_sub_one {μ : ℝ} :
    |Real.sqrt μ - 1| ≤ |μ - 1| := by
  rcases le_total 0 μ with hμ | hμ
  · have hs : 0 ≤ Real.sqrt μ := Real.sqrt_nonneg μ
    have hsq : Real.sqrt μ * Real.sqrt μ = μ := Real.mul_self_sqrt hμ
    have key : |Real.sqrt μ - 1| * (Real.sqrt μ + 1) = |μ - 1| := by
      rw [← abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.sqrt μ + 1), ← abs_mul]
      congr 1
      nlinarith [hsq]
    nlinarith [key, mul_nonneg (abs_nonneg (Real.sqrt μ - 1)) hs]
  · have hsqrt : Real.sqrt μ = 0 := Real.sqrt_eq_zero_of_nonpos hμ
    calc
      |Real.sqrt μ - 1| = 1 := by rw [hsqrt]; norm_num
      _ ≤ |μ - 1| := by
        rw [abs_of_nonpos (by linarith : μ - 1 ≤ 0)]
        linarith

/-- If `|μ - 1| ≤ δ ≤ 1 / 2`, then `|1 - (√μ)⁻¹| ≤ δ`.

The hypotheses force `μ` to be positive and keep the inverse square root
bounded near `1`. -/
theorem abs_one_sub_inv_sqrt_le {μ δ : ℝ} (hδ : δ ≤ 1 / 2) (hμ : |μ - 1| ≤ δ) :
    |1 - (Real.sqrt μ)⁻¹| ≤ δ := by
  have hμlb : 1 - δ ≤ μ := by rw [abs_le] at hμ; linarith
  have hμpos : (0 : ℝ) < μ := by linarith
  set s := Real.sqrt μ
  have hs0 : 0 < s := Real.sqrt_pos.mpr hμpos
  have hssq : s ^ 2 = μ := Real.sq_sqrt (le_of_lt hμpos)
  -- `s ≥ 1/2` (since `s² = μ ≥ 1/2`)
  have hssqlb : (1 : ℝ) / 2 ≤ s ^ 2 := by rw [hssq]; linarith
  have hsge : (1 : ℝ) / 2 ≤ s := by nlinarith [hs0, hssqlb]
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) hμ
  rw [abs_le] at hμ ⊢
  obtain ⟨hμ1, hμ2⟩ := hμ
  have hssq' : s * s = μ := by nlinarith [hssq]
  -- Lower bound `1 ≤ (1 + δ) * s`: its square is `(1 + δ)² μ ≥ (1 + δ)² (1 - δ) ≥ 1`.
  have hlow : 1 ≤ (1 + δ) * s := by
    have hpos : 0 < (1 + δ) * s := by positivity
    nlinarith [hpos, hssq', hμ1, hμ2, hδ0, hsge, mul_nonneg hδ0 hδ0,
      mul_nonneg (mul_nonneg hδ0 hδ0) hδ0]
  -- Upper bound `(1 - δ) * s ≤ 1`: equivalently `(1 - δ)² μ ≤ 1` when `1 - δ ≥ 0`.
  have hhigh : (1 - δ) * s ≤ 1 := by
    rcases le_or_gt (1 - δ) 0 with h | h
    · nlinarith [hs0, h]
    · nlinarith [hssq', hμ1, hμ2, hδ0, hsge, h, mul_nonneg hδ0 hδ0]
  -- Translate the two multiplicative bounds into bounds on `s⁻¹`.
  have hinv_le : s⁻¹ ≤ 1 + δ := by
    rw [inv_eq_one_div, div_le_iff₀ hs0]; linarith [hlow]
  have hle_inv : 1 - δ ≤ s⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hs0]; linarith [hhigh]
  exact ⟨by linarith [hinv_le], by linarith [hle_inv]⟩

end Real

end
