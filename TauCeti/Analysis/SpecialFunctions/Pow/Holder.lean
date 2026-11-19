/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Hölder continuity of real powers

For `0 ≤ p ≤ 1` the power `t ↦ t ^ p` is `p`-Hölder on `[0, ∞)` with constant one:
`|a ^ p - b ^ p| ≤ |a - b| ^ p` for `a, b ≥ 0`. This is the subadditivity
`(a + b) ^ p ≤ a ^ p + b ^ p` of Mathlib's `Real.rpow_add_le_add_rpow`, applied to `b` and
`a - b`. It is the estimate showing that cone-point functions such as `‖z‖ ^ p` are `p`-Hölder.

The square root also satisfies a weighted form of its `1/2`-Hölder bound: for `0 ≤ γ ≤ 1`,
`|√t - √s| max (√t) (√s) ^ γ ≤ |t - s| ^ ((1 + γ) / 2)`. This is the time increment of a
parabolic rescaling `x - √t y` against a `γ`-Hölder modulus, as in the temporal Hölder estimate
of heat potentials of `C^{1,γ}` data.
-/

public section

namespace Real

/-- On `[0, ∞)` the power `t ↦ t ^ p` is `p`-Hölder with constant one, for `0 ≤ p ≤ 1`. -/
theorem abs_rpow_sub_rpow_le {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 0 ≤ p)
    (hp1 : p ≤ 1) : |a ^ p - b ^ p| ≤ |a - b| ^ p := by
  wlog hab : b ≤ a generalizing a b
  · rw [abs_sub_comm, abs_sub_comm a]
    exact this hb ha (le_of_not_ge hab)
  have h := rpow_add_le_add_rpow (sub_nonneg.mpr hab) hb hp hp1
  rw [sub_add_cancel] at h
  rw [abs_of_nonneg (sub_nonneg.mpr (rpow_le_rpow hb hab hp)),
    abs_of_nonneg (sub_nonneg.mpr hab)]
  linarith

/-- **A weighted Hölder bound for the square root.** For all reals `t` and `s` and `0 ≤ γ ≤ 1`,
`|√t - √s| max (√t) (√s) ^ γ ≤ |t - s| ^ ((1 + γ) / 2)`. At `γ = 0` this is the `1/2`-Hölder
bound of the square root. -/
theorem abs_sqrt_sub_sqrt_mul_max_rpow_le (t s : ℝ) {γ : ℝ} (hγ₀ : 0 ≤ γ) (hγ₁ : γ ≤ 1) :
    |√t - √s| * max √t √s ^ γ ≤ |t - s| ^ ((1 + γ) / 2) := by
  -- First the bound `|a - b| max a b ^ γ ≤ |a² - b²| ^ ((1 + γ) / 2)` for `a, b ≥ 0`.
  have key : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b →
      |a - b| * max a b ^ γ ≤ |a ^ 2 - b ^ 2| ^ ((1 + γ) / 2) := by
    intro a b ha hb
    wlog hab : b ≤ a generalizing a b
    · simpa [abs_sub_comm, max_comm] using this hb ha (le_of_not_ge hab)
    rcases (add_nonneg ha hb).eq_or_lt with hs | hs
    · obtain rfl : a = 0 := by linarith
      obtain rfl : b = 0 := by linarith
      simp only [sub_self, abs_zero, zero_mul]
      positivity
    have hd : 0 ≤ a - b := sub_nonneg.2 hab
    rw [abs_of_nonneg hd, max_eq_left hab, show a ^ 2 - b ^ 2 = (a - b) * (a + b) by ring,
      abs_of_nonneg (mul_nonneg hd hs.le), mul_rpow hd hs.le]
    -- Split `a - b = (a - b) ^ ((1 + γ) / 2) (a - b) ^ ((1 - γ) / 2)` and use `a - b ≤ a + b`.
    have h₁ : a - b ≤ (a - b) ^ ((1 + γ) / 2) * (a + b) ^ ((1 - γ) / 2) := by
      calc a - b = (a - b) ^ ((1 + γ) / 2) * (a - b) ^ ((1 - γ) / 2) := by
            rw [← rpow_add' hd (by ring_nf; norm_num)]
            ring_nf
            rw [rpow_one]
        _ ≤ _ := by gcongr; linarith
    have h₂ : a ^ γ ≤ (a + b) ^ γ := by gcongr; linarith
    calc (a - b) * a ^ γ
        ≤ (a - b) ^ ((1 + γ) / 2) * (a + b) ^ ((1 - γ) / 2) * (a + b) ^ γ := by gcongr
      _ = (a - b) ^ ((1 + γ) / 2) * (a + b) ^ ((1 + γ) / 2) := by
          rw [mul_assoc, ← rpow_add hs]
          ring_nf
  refine (key (sqrt_nonneg t) (sqrt_nonneg s)).trans
    (rpow_le_rpow (abs_nonneg _) ?_ (by positivity))
  rw [sq_sqrt', sq_sqrt']
  exact abs_max_sub_max_le_abs t s 0

end Real
