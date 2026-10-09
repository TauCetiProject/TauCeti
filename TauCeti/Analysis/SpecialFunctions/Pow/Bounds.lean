/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Elementary bounds on real powers

A base at least `2` raised to a negative exponent of size at least `1` is at most `1 / 2`. This
is the shape in which the local ratio of an Euler factor is bounded away from `1`, so that the
denominator `1 - y ^ (-s)` stays bounded below.

For any `θ < 1` and any exponent `β`, some base `τ ∈ (0, 1)` has `θ < τ ^ β`. This is how a
geometric ratio is chosen in iteration arguments, such as the absorption lemma.

For `1 ≤ p`, the graph of `u ↦ u ^ p` on `[0, ∞)` lies above each of its tangent lines:
`v ^ p + p * v ^ (p - 1) * (u - v) ≤ u ^ p`, strictly so when `1 < p` and `u ≠ v`. This is
Bernoulli's inequality made homogeneous, and it is the first-order optimality test for weighted
sums of powers.

## Main results

* `Real.rpow_neg_le_half`: `y ^ (-s) ≤ 1 / 2` for `2 ≤ y` and `1 ≤ s`.
* `Real.exists_pos_lt_one_lt_rpow`: for `θ < 1` and any `β`, some `τ ∈ (0, 1)` has `θ < τ ^ β`.
* `Real.rpow_add_mul_rpow_sub_one_mul_sub_le_rpow` and
  `Real.rpow_add_mul_rpow_sub_one_mul_sub_lt_rpow`: the tangent-line inequalities for `u ↦ u ^ p`.
-/

public section

namespace Real

/-- If `2 ≤ y` and `1 ≤ s`, then `y ^ (-s) ≤ 1 / 2`. -/
theorem rpow_neg_le_half {y s : ℝ} (hy : 2 ≤ y) (hs : 1 ≤ s) : y ^ (-s) ≤ 1 / 2 :=
  calc y ^ (-s) ≤ (2 : ℝ) ^ (-s) := rpow_le_rpow_of_nonpos two_pos hy (by linarith)
    _ ≤ (2 : ℝ) ^ (-(1 : ℝ)) := rpow_le_rpow_of_exponent_le one_le_two (by linarith)
    _ = 1 / 2 := by norm_num

/-- For `θ < 1` and any exponent `β`, some ratio `τ ∈ (0, 1)` has `θ < τ ^ β`. -/
theorem exists_pos_lt_one_lt_rpow {θ : ℝ} (hθ : θ < 1) (β : ℝ) :
    ∃ τ : ℝ, 0 < τ ∧ τ < 1 ∧ θ < τ ^ β := by
  rcases le_or_gt β 0 with hβ | hβ
  · exact ⟨1 / 2, by norm_num, by norm_num,
      hθ.trans_le (one_le_rpow_of_pos_of_le_one_of_nonpos (by norm_num) (by norm_num) hβ)⟩
  · set c := max ((1 + θ) / 2) (1 / 2)
    have hc0 : 0 < c := lt_max_of_lt_right (by norm_num)
    have hc1 : c < 1 := max_lt (by linarith) (by norm_num)
    refine ⟨c ^ β⁻¹, rpow_pos_of_pos hc0 _, rpow_lt_one hc0.le hc1 (inv_pos.2 hβ), ?_⟩
    rw [← rpow_mul hc0.le, inv_mul_cancel₀ hβ.ne', rpow_one]
    exact lt_max_of_lt_left (by linarith)

/-- **The strict tangent-line inequality for real powers.** For `1 < p` and distinct `u, v ≥ 0`,
`u ↦ u ^ p` lies strictly above its tangent line at `v`. -/
theorem rpow_add_mul_rpow_sub_one_mul_sub_lt_rpow {p u v : ℝ} (hp : 1 < p) (hu : 0 ≤ u)
    (hv : 0 ≤ v) (huv : u ≠ v) : v ^ p + p * v ^ (p - 1) * (u - v) < u ^ p := by
  rcases hv.eq_or_lt with rfl | hv
  · rw [zero_rpow (by linarith), zero_rpow (by linarith)]
    simpa using rpow_pos_of_pos (hu.lt_of_ne' huv) p
  · have hs : -1 ≤ (u - v) / v := by
      rw [le_div_iff₀ hv]
      linarith
    have h := one_add_mul_self_lt_rpow_one_add hs (div_ne_zero (sub_ne_zero.2 huv) hv.ne') hp
    have hu_div : 1 + (u - v) / v = u / v := by
      field_simp
      ring
    rw [hu_div, div_rpow hu hv.le, lt_div_iff₀ (rpow_pos_of_pos hv p)] at h
    rw [rpow_sub_one hv.ne']
    calc v ^ p + p * (v ^ p / v) * (u - v) = (1 + p * ((u - v) / v)) * v ^ p := by
          field_simp
      _ < u ^ p := h

/-- **The tangent-line inequality for real powers.** For `1 ≤ p` and `u, v ≥ 0`, `u ↦ u ^ p` lies
above its tangent line at `v`. This is Bernoulli's inequality
`one_add_mul_self_le_rpow_one_add` made homogeneous. -/
theorem rpow_add_mul_rpow_sub_one_mul_sub_le_rpow {p u v : ℝ} (hp : 1 ≤ p) (hu : 0 ≤ u)
    (hv : 0 ≤ v) : v ^ p + p * v ^ (p - 1) * (u - v) ≤ u ^ p := by
  rcases hp.eq_or_lt with rfl | hp
  · simp
  rcases eq_or_ne u v with rfl | huv
  · simp
  exact (rpow_add_mul_rpow_sub_one_mul_sub_lt_rpow hp hu hv huv).le

end Real
