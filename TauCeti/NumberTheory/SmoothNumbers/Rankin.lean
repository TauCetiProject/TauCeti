/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.NumberTheory.SmoothNumbers.Count
import TauCeti.NumberTheory.SmoothNumbers.Basic

/-!
# Rankin's upper bound for the number of smooth integers

Rankin's trick bounds the number `Ψ(x, y)` of `y`-smooth positive integers up to `x` by a finite
Euler product: for every real `x ≥ 0` and every `σ > 0`,

  `Ψ(x, y) ≤ x ^ σ * ∏_{p ≤ y} (1 - p ^ (-σ))⁻¹`.

The exponent `σ` is a free parameter, and the bound is valid for every `σ > 0`, with no condition
`σ > 1`, because only the finitely many primes `p ≤ y` occur (the Euler product is
`TauCeti.hasSum_rpow_neg_smoothNumbers`). Decreasing `σ` makes `x ^ σ` smaller and every factor
of the product larger, so to use the bound one chooses `σ` to balance the two. At `σ = 1` the
right side is `x ∏_{p ≤ y} (1 - 1 / p)⁻¹ ≥ x`, which is no better than `Ψ(x, y) ≤ x`; the bound
only helps for `σ < 1`. For `σ = 1 - c / log y` with a constant `c > 0`, one has
`p ^ (-σ) ≤ e ^ c / p` for all primes `p ≤ y`, which controls the factors of the product, while
`x ^ σ = x * exp (-c log x / log y)` for `x > 0` gains a factor exponentially small in
`log x / log y`.

## Main results

* `Nat.smoothNumbersUpTo_card_le_rpow_mul_prod`: Rankin's bound for `Nat.smoothNumbersUpTo N k`,
  at natural cutoffs.
* `TauCeti.smoothCount_le_rpow_mul_prod`: Rankin's bound for `Ψ(x, y)`, at real cutoffs.

## References

* A. Hildebrand, G. Tenenbaum, *Integers without large prime factors*, J. Théor. Nombres
  Bordeaux 5 (1993), 411–484, equation (1.3).
-/

public section

open Finset

/-- **Rankin's bound at natural cutoffs.** For `σ > 0`, the number of positive integers up to `N`
all of whose prime factors are less than `k` is at most `N ^ σ * ∏_{p < k} (1 - p ^ (-σ))⁻¹`. -/
theorem Nat.smoothNumbersUpTo_card_le_rpow_mul_prod (N k : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    (#(Nat.smoothNumbersUpTo N k) : ℝ) ≤
      (N : ℝ) ^ σ * ∏ p ∈ k.primesBelow, (1 - (p : ℝ) ^ (-σ))⁻¹ := by
  have hmem : ∀ n ∈ Nat.smoothNumbersUpTo N k, n ∈ k.smoothNumbers :=
    fun n hn ↦ (Nat.mem_smoothNumbersUpTo.1 hn).2
  -- Each counted `n` satisfies `1 ≤ N ^ σ * n ^ (-σ)`.
  have hterm : ∀ n ∈ Nat.smoothNumbersUpTo N k, (1 : ℝ) ≤ (N : ℝ) ^ σ * (n : ℝ) ^ (-σ) := by
    intro n hn
    have hn0 : (0 : ℝ) < n :=
      Nat.cast_pos.2 (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers (hmem n hn)))
    have hnN : (n : ℝ) ≤ N := Nat.cast_le.2 (Nat.mem_smoothNumbersUpTo.1 hn).1
    rw [Real.rpow_neg hn0.le, ← div_eq_mul_inv, ← Real.div_rpow N.cast_nonneg hn0.le]
    exact Real.one_le_rpow ((one_le_div hn0).2 hnN) hσ.le
  -- The sum over the counted `n` is at most the full sum over the smooth numbers.
  have hsum : ∑ n ∈ Nat.smoothNumbersUpTo N k, (n : ℝ) ^ (-σ) ≤
      ∏ p ∈ k.primesBelow, (1 - (p : ℝ) ^ (-σ))⁻¹ := by
    rw [← sum_subtype_of_mem (fun n : ℕ ↦ (n : ℝ) ^ (-σ)) hmem]
    exact sum_le_hasSum _ (fun n _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (TauCeti.hasSum_rpow_neg_smoothNumbers hσ k)
  calc (#(Nat.smoothNumbersUpTo N k) : ℝ)
      ≤ ∑ n ∈ Nat.smoothNumbersUpTo N k, (N : ℝ) ^ σ * (n : ℝ) ^ (-σ) := by
        simpa only [nsmul_one] using card_nsmul_le_sum _ _ (1 : ℝ) hterm
    _ = (N : ℝ) ^ σ * ∑ n ∈ Nat.smoothNumbersUpTo N k, (n : ℝ) ^ (-σ) := (mul_sum _ _ _).symm
    _ ≤ (N : ℝ) ^ σ * ∏ p ∈ k.primesBelow, (1 - (p : ℝ) ^ (-σ))⁻¹ :=
        mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg N.cast_nonneg σ)

namespace TauCeti

/-- **Rankin's bound.** For `x ≥ 0` and `σ > 0`, the number `Ψ(x, y)` of `y`-smooth positive
integers up to `x` is at most `x ^ σ * ∏_{p ≤ y} (1 - p ^ (-σ))⁻¹`, the product being over the
primes `p < ⌊y⌋₊ + 1`. -/
theorem smoothCount_le_rpow_mul_prod {x σ : ℝ} (hx : 0 ≤ x) (hσ : 0 < σ) (y : ℝ) :
    (smoothCount x y : ℝ) ≤
      x ^ σ * ∏ p ∈ (⌊y⌋₊ + 1).primesBelow, (1 - (p : ℝ) ^ (-σ))⁻¹ := by
  rw [smoothCount_def]
  refine (Nat.smoothNumbersUpTo_card_le_rpow_mul_prod ⌊x⌋₊ (⌊y⌋₊ + 1) hσ).trans
    (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hx) hσ.le)
      (prod_nonneg fun p hp ↦ inv_nonneg.2 (sub_nonneg.2 ?_)))
  have hp1 : (1 : ℝ) ≤ p := mod_cast (Nat.prime_of_mem_primesBelow hp).one_le
  exact Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)

end TauCeti
