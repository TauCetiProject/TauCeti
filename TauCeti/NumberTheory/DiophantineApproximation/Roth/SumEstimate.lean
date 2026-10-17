/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# A lower bound for a sum of truncated linear terms

For `k : ℕ` and `δ : ℝ` we prove

`(k + 1) * min (δ / 2) (δ ^ 2 / 2) ≤ ∑ i ∈ Finset.range (k + 1), max (δ - i / k) 0`,

where `i / k` is real division, so that `i / 0 = 0`. The left-hand side is `(k + 1) δ / 2` for
`δ ≥ 1` and `(k + 1) δ² / 2` for `0 ≤ δ ≤ 1`.

This is the numerical estimate in the inductive step of Roth's lemma, which bounds the index
of a multivariate polynomial at a point of large height. A Hasse derivative of order `l` in a
variable of weight `k` lowers the index by at most `l / k`, so it keeps index at least
`max (δ - l / k) 0` when the polynomial has index `δ`. The estimate bounds the sum of these
lower bounds over `l = 0, …, k` from below by a quantity that is quadratic in `δ` for small `δ`.

## Main results

* `TauCeti.mul_min_le_sum_max_sub_div`: the lower bound above.

## References

* L. Pottmeyer, [*Diophantine Approximation*](https://esaga.uni-due.de/f/lukas.pottmeyer/DioApp.pdf)
  (2022), §3.4, Lemma 3.4.8 and Exercise 3.7.
-/

public section

namespace TauCeti

open Finset

/-- The partial sum of the terms `δ - i / k` over `i ≤ N` bounds from below the full sum of
their positive parts over `i ≤ k`, for every `N ≤ k`. -/
private lemma succ_mul_sub_le_sum_max_sub_div {k N : ℕ} (hN : N ≤ k) (δ : ℝ) :
    (N + 1) * δ - N * (N + 1) / (2 * k) ≤ ∑ i ∈ range (k + 1), max (δ - i / k) 0 := by
  have hgauss : ∑ i ∈ range (N + 1), (i : ℝ) = N * (N + 1) / 2 := by
    rw [eq_div_iff two_ne_zero, mul_comm (N : ℝ), ← Nat.cast_sum]
    exact_mod_cast (Nat.add_sub_cancel N 1 ▸ sum_range_id_mul_two (N + 1))
  calc (N + 1) * δ - N * (N + 1) / (2 * k) = ∑ i ∈ range (N + 1), (δ - i / k) := by
        rw [sum_sub_distrib, ← sum_div, hgauss, sum_const, card_range, nsmul_eq_mul, div_div]
        push_cast
        ring
    _ ≤ ∑ i ∈ range (N + 1), max (δ - i / k) 0 := sum_le_sum fun _ _ ↦ le_max_left _ _
    _ ≤ ∑ i ∈ range (k + 1), max (δ - i / k) 0 :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega))
          fun _ _ _ ↦ le_max_right _ _

/-- **Pottmeyer, Lemma 3.4.8.** For `k : ℕ` and `δ : ℝ`, the positive parts of
`δ - i / k` for `i = 0, …, k` sum to at least `(k + 1) * min (δ / 2) (δ ^ 2 / 2)`. Here `i / k`
is real division, so for `k = 0` the sum is `max δ 0`. -/
theorem mul_min_le_sum_max_sub_div (k : ℕ) (δ : ℝ) :
    (k + 1) * min (δ / 2) (δ ^ 2 / 2) ≤ ∑ i ∈ range (k + 1), max (δ - i / k) 0 := by
  rcases le_or_gt δ 0 with hδ | hδ
  · -- For `δ ≤ 0` the left-hand side is nonpositive and the sum is nonnegative.
    calc (k + 1) * min (δ / 2) (δ ^ 2 / 2) ≤ (k + 1) * (δ / 2) := by
          gcongr
          exact min_le_left _ _
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
      _ ≤ _ := sum_nonneg fun _ _ ↦ le_max_right _ _
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using (min_le_left _ _).trans ((half_le_self hδ.le).trans (le_max_left δ 0))
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rcases le_or_gt 1 δ with hδ₁ | hδ₁
  · -- For `δ ≥ 1` all `k + 1` terms are at least `δ - i / k`.
    refine le_trans ?_ (succ_mul_sub_le_sum_max_sub_div le_rfl δ)
    have : (k : ℝ) * (k + 1) / (2 * k) = (k + 1) / 2 := by field_simp
    rw [this]
    nlinarith [min_le_left (δ / 2) (δ ^ 2 / 2)]
  · -- For `0 < δ < 1` keep the terms with `i ≤ ⌊δ k⌋`, which are exactly the positive ones.
    set N := ⌊δ * k⌋₊
    have hδk : 0 ≤ δ * k := by positivity
    have hN₁ : (N : ℝ) ≤ δ * k := Nat.floor_le hδk
    have hN₂ : δ * k < N + 1 := Nat.lt_floor_add_one _
    have hNk : N ≤ k := by
      have : (N : ℝ) < k := hN₁.trans_lt (by nlinarith)
      exact_mod_cast this.le
    refine le_trans ?_ (succ_mul_sub_le_sum_max_sub_div hNk δ)
    have hdiv : (N : ℝ) * (N + 1) / (2 * k) ≤ (N + 1) * δ - (k + 1) * (δ ^ 2 / 2) := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg (sub_nonneg.2 hN₂.le) (sub_nonneg.2 hN₁),
        mul_nonneg hδk (sub_nonneg.2 hδ₁.le)]
    nlinarith [min_le_right (δ / 2) (δ ^ 2 / 2)]

end TauCeti
