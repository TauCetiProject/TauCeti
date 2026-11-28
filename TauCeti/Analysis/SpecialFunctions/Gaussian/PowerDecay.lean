/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds

/-!
# Power bounds for Gaussian weights

On the positive ray a Gaussian with a real power weight is bounded by a constant times any
power whose exponent is at most that of the weight. This gives a single bound usable both
near zero and at infinity. Multiplying two such comparisons separates the powers of the
arguments from a common scale.
-/

public section

open Real

namespace TauCeti

/-- On the positive ray, `x ^ a * exp (-c * x²)` is bounded by a constant times `x ^ b`
whenever `b ≤ a` and `c > 0`. -/
theorem exists_rpow_mul_exp_neg_mul_sq_le_mul_rpow {a b c : ℝ} (hab : b ≤ a) (hc : 0 < c) :
    ∃ C ≥ 0, ∀ x : ℝ, 0 < x → x ^ a * exp (-c * x ^ 2) ≤ C * x ^ b := by
  obtain ⟨C, hC, h⟩ := exists_rpow_mul_exp_neg_mul_le
    (σ := (a - b) / 2) (by linarith) hc
  refine ⟨C, hC, fun x hx ↦ ?_⟩
  have hpow : (x ^ 2) ^ ((a - b) / 2) = x ^ (a - b) := by
    rw [← rpow_two, ← rpow_mul hx.le, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  have hbound := h (x ^ 2) (sq_nonneg x)
  rw [hpow, ← neg_mul] at hbound
  calc
    x ^ a * exp (-c * x ^ 2) = (x ^ (a - b) * exp (-c * x ^ 2)) * x ^ b := by
      rw [mul_right_comm, ← rpow_add hx, sub_add_cancel]
    _ ≤ C * x ^ b := mul_le_mul_of_nonneg_right hbound (rpow_nonneg hx.le _)

/-- A pointwise Gaussian power comparison bounds the product at `m * u` and `n * u`, weighted
by `u`, with separate powers of `m * n` and the common scale `u`. -/
theorem mul_gaussian_pair_le {a C c : ℝ} {j : ℕ}
    (h : ∀ x : ℝ, 0 < x → x ^ j * exp (-c * x ^ 2) ≤ C * x ^ (-a))
    {u m n : ℝ} (hu : 0 ≤ u) (hm : 0 < m) (hn : 0 < n) :
    u * (((m * u) ^ j * exp (-c * (m * u) ^ 2)) * ((n * u) ^ j * exp (-c * (n * u) ^ 2))) ≤
      C ^ 2 * (m * n) ^ (-a) * u ^ (1 - 2 * a) := by
  rcases hu.eq_or_lt with rfl | hu
  · simp only [zero_mul]
    positivity
  have hm' := h _ (mul_pos hm hu)
  have hn' := h _ (mul_pos hn hu)
  have hm₀ : 0 ≤ (m * u) ^ j * exp (-c * (m * u) ^ 2) := by positivity
  calc
    _ ≤ u * ((C * (m * u) ^ (-a)) * (C * (n * u) ^ (-a))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hm' hn' (by positivity) (hm₀.trans hm')) hu.le
    _ = _ := by
      rw [mul_rpow hm.le hu.le, mul_rpow hn.le hu.le, mul_rpow hm.le hn.le,
        sub_eq_add_neg, rpow_add hu, rpow_one,
        (by ring : -(2 * a) = -a + -a), rpow_add hu]
      ring

end TauCeti
