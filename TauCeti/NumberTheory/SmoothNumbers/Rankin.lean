/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.SmoothNumbers
public import TauCeti.NumberTheory.SmoothNumbers.Count

/-!
# Rankin's upper bound for the number of smooth integers

Rankin's trick bounds the number `Ψ(x, y)` of `y`-smooth positive integers up to `x` by a finite
Euler product: for every `σ > 0`,

  `Ψ(x, y) ≤ x ^ σ * ∏_{p ≤ y} (1 - p ^ (-σ))⁻¹`.

Each counted `n` satisfies `1 ≤ (x / n) ^ σ`, so `Ψ(x, y) ≤ x ^ σ ∑ n ^ (-σ)`, the sum being over
the `y`-smooth `n ≤ x`; enlarging it to all `y`-smooth integers gives the Euler product
(`TauCeti.hasSum_rpow_neg_smoothNumbers`). The bound holds for every `σ > 0`, with no condition
`σ > 1`, because only the finitely many primes `p ≤ y` occur.

## Main results

* `TauCeti.smoothCount_le_rpow_mul_prod`: Rankin's bound.

## References

* A. Hildebrand, G. Tenenbaum, *Integers without large prime factors*, J. Théor. Nombres
  Bordeaux 5 (1993), 411–484, equation (1.3).
-/

public section

open Finset

namespace TauCeti

/-- **Rankin's bound.** For `x ≥ 0` and `σ > 0`, the number `Ψ(x, y)` of `y`-smooth positive
integers up to `x` is at most `x ^ σ * ∏_{p ≤ y} (1 - p ^ (-σ))⁻¹`, the product being over the
primes `p < ⌊y⌋₊ + 1`. -/
theorem smoothCount_le_rpow_mul_prod {x σ : ℝ} (hx : 0 ≤ x) (hσ : 0 < σ) (y : ℝ) :
    (smoothCount x y : ℝ) ≤
      x ^ σ * ∏ p ∈ (⌊y⌋₊ + 1).primesBelow, (1 - (p : ℝ) ^ (-σ))⁻¹ := by
  have hmem : ∀ n ∈ Nat.smoothNumbersUpTo ⌊x⌋₊ (⌊y⌋₊ + 1), n ∈ (⌊y⌋₊ + 1).smoothNumbers :=
    fun n hn ↦ (Nat.mem_smoothNumbersUpTo.1 hn).2
  -- Each counted `n` satisfies `1 ≤ x ^ σ * n ^ (-σ)`.
  have hterm : ∀ n ∈ Nat.smoothNumbersUpTo ⌊x⌋₊ (⌊y⌋₊ + 1), (1 : ℝ) ≤ x ^ σ * (n : ℝ) ^ (-σ) := by
    intro n hn
    have hn0 : (0 : ℝ) < n :=
      Nat.cast_pos.2 (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers (hmem n hn)))
    have hnx : (n : ℝ) ≤ x :=
      (Nat.cast_le.2 (Nat.mem_smoothNumbersUpTo.1 hn).1).trans (Nat.floor_le hx)
    rw [Real.rpow_neg hn0.le, ← div_eq_mul_inv, ← Real.div_rpow hx hn0.le]
    exact Real.one_le_rpow ((one_le_div hn0).2 hnx) hσ.le
  -- The sum over the counted `n` is at most the full sum over the smooth numbers.
  have hsum : ∑ n ∈ Nat.smoothNumbersUpTo ⌊x⌋₊ (⌊y⌋₊ + 1), (n : ℝ) ^ (-σ) ≤
      ∏ p ∈ (⌊y⌋₊ + 1).primesBelow, (1 - (p : ℝ) ^ (-σ))⁻¹ := by
    rw [← sum_subtype_of_mem (fun n : ℕ ↦ (n : ℝ) ^ (-σ)) hmem]
    exact sum_le_hasSum _ (fun n _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (hasSum_rpow_neg_smoothNumbers hσ (⌊y⌋₊ + 1))
  calc (smoothCount x y : ℝ)
      = ∑ _n ∈ Nat.smoothNumbersUpTo ⌊x⌋₊ (⌊y⌋₊ + 1), (1 : ℝ) := by
        rw [smoothCount_def, sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ n ∈ Nat.smoothNumbersUpTo ⌊x⌋₊ (⌊y⌋₊ + 1), x ^ σ * (n : ℝ) ^ (-σ) := sum_le_sum hterm
    _ = x ^ σ * ∑ n ∈ Nat.smoothNumbersUpTo ⌊x⌋₊ (⌊y⌋₊ + 1), (n : ℝ) ^ (-σ) := (mul_sum _ _ _).symm
    _ ≤ x ^ σ * ∏ p ∈ (⌊y⌋₊ + 1).primesBelow, (1 - (p : ℝ) ^ (-σ))⁻¹ :=
        mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hx σ)

end TauCeti
