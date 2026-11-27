/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Counting shifted squares

For a natural number `c`, the natural numbers `k ≤ N` for which the integer `k - c` is a perfect
square are the numbers `u² + c` with `u ≤ ⌊√(N - c)⌋`. There are `⌊√(N - c)⌋ + 1` of them when
`c ≤ N`, the square `0` included, and none otherwise. For a real cutoff `K` this gives the bound
`1 + √(max (K - c) 0)`.

Such counts bound thin exceptional sets of parameters. The shift `c = 4` occurs for the Markoff
type cubic surfaces `x₁² + x₂² + x₃² - x₁ x₂ x₃ = k`.

## Main results

* `Nat.isSquare_natCast_sub_iff`: the integer `k - c` is a square exactly when `k = u² + c` for a
  natural number `u`.
* `Nat.card_filter_Iic_isSquare_sub`: the number of `k ≤ N` with `k - c` a square is
  `⌊√(N - c)⌋ + 1` if `c ≤ N` and `0` otherwise; `Nat.card_filter_Icc_one_isSquare_sub` is the
  same count over `1 ≤ k ≤ N`, for `c ≥ 1`.
* `Nat.card_filter_Iic_natFloor_isSquare_sub_le`: with a real cutoff `K`, the count is at most
  `1 + √(max (K - c) 0)`.

## References

* A. Ghosh, P. Sarnak, *Integral points on Markoff type cubic surfaces*, arXiv:1706.06712.
-/

public section

open Finset

namespace Nat

variable {c k N : ℕ}

/-- For natural numbers `k` and `c`, the integer `k - c` is a square exactly when `k = u² + c` for
a natural number `u`. -/
theorem isSquare_natCast_sub_iff : IsSquare ((k : ℤ) - c) ↔ ∃ u : ℕ, u ^ 2 + c = k := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z.natAbs, ?_⟩
    have h : ((z.natAbs ^ 2 + c : ℕ) : ℤ) = k := by
      rw [Nat.cast_add, Nat.cast_pow, Int.natCast_natAbs, sq_abs, sq]
      linarith
    exact_mod_cast h
  · rintro ⟨u, rfl⟩
    exact ⟨u, by push_cast; ring⟩

/-- The `k ≤ N` with `k - c` a square, for `c ≤ N`, are the numbers `u² + c` with
`u ≤ ⌊√(N - c)⌋`. -/
theorem filter_Iic_isSquare_sub (hc : c ≤ N) :
    {k ∈ Iic N | IsSquare (((k : ℕ) : ℤ) - c)} = (Iic (N - c).sqrt).image fun u ↦ u ^ 2 + c := by
  ext k
  simp only [mem_filter, mem_Iic, mem_image, Nat.le_sqrt', isSquare_natCast_sub_iff]
  constructor
  · rintro ⟨hk, u, rfl⟩
    exact ⟨u, by omega, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨by omega, u, rfl⟩

/-- The number of `k ≤ N` with `k - c` a square is `⌊√(N - c)⌋ + 1` if `c ≤ N`, and `0`
otherwise. The square `0` is counted: `k = c` contributes. -/
theorem card_filter_Iic_isSquare_sub (c N : ℕ) :
    #{k ∈ Iic N | IsSquare (((k : ℕ) : ℤ) - c)} = if c ≤ N then (N - c).sqrt + 1 else 0 := by
  split_ifs with hc
  · rw [filter_Iic_isSquare_sub hc, Finset.card_image_of_injective _
      fun u v (h : u ^ 2 + c = v ^ 2 + c) ↦
        Nat.pow_left_injective two_ne_zero (Nat.add_right_cancel h), Nat.card_Iic]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro k hk hsq
    obtain ⟨u, rfl⟩ := isSquare_natCast_sub_iff.1 hsq
    exact hc ((Nat.le_add_left c (u ^ 2)).trans (mem_Iic.1 hk))

/-- For `c ≥ 1`, the number of `1 ≤ k ≤ N` with `k - c` a square is `⌊√(N - c)⌋ + 1` if `c ≤ N`,
and `0` otherwise: `0` is not of the form `u² + c`. -/
theorem card_filter_Icc_one_isSquare_sub (hc : 0 < c) (N : ℕ) :
    #{k ∈ Icc 1 N | IsSquare (((k : ℕ) : ℤ) - c)} = if c ≤ N then (N - c).sqrt + 1 else 0 := by
  rw [← card_filter_Iic_isSquare_sub]
  congr 1
  ext k
  simp only [mem_filter, mem_Icc, mem_Iic]
  refine ⟨fun ⟨⟨_, h⟩, hs⟩ ↦ ⟨h, hs⟩, fun ⟨h, hs⟩ ↦ ⟨⟨?_, h⟩, hs⟩⟩
  obtain ⟨u, rfl⟩ := isSquare_natCast_sub_iff.1 hs
  omega

/-- For a real cutoff `K`, the number of natural numbers `k ≤ K` with `k - c` a square is at most
`1 + √(max (K - c) 0)`. -/
theorem card_filter_Iic_natFloor_isSquare_sub_le (c : ℕ) (K : ℝ) :
    (#{k ∈ Iic ⌊K⌋₊ | IsSquare (((k : ℕ) : ℤ) - c)} : ℝ) ≤ 1 + √(max (K - c) 0) := by
  rw [card_filter_Iic_isSquare_sub]
  split_ifs with hc
  · have h₁ : ((⌊K⌋₊ - c).sqrt : ℝ) ≤ √((⌊K⌋₊ - c : ℕ) : ℝ) := Real.nat_sqrt_le_real_sqrt
    have h₂ : ((⌊K⌋₊ - c : ℕ) : ℝ) ≤ max (K - c) 0 := by
      rw [Nat.cast_sub hc]
      rcases le_or_gt 0 K with hK | hK
      · exact (sub_le_sub_right (Nat.floor_le hK) _).trans (le_max_left _ _)
      · have h0 : ⌊K⌋₊ = 0 := Nat.floor_of_nonpos hK.le
        have hc0 : c = 0 := by omega
        simp [h0, hc0]
    push_cast
    linarith [Real.sqrt_le_sqrt h₂]
  · rw [Nat.cast_zero]
    positivity

/-! ### Examples: the shift `c = 4` -/

example : #{k ∈ Icc 1 3 | IsSquare (((k : ℕ) : ℤ) - 4)} = 0 := by decide

example : #{k ∈ Icc 1 4 | IsSquare (((k : ℕ) : ℤ) - 4)} = 1 := by decide

example : #{k ∈ Icc 1 5 | IsSquare (((k : ℕ) : ℤ) - 4)} = 2 := by decide

example : #{k ∈ Icc 1 13 | IsSquare (((k : ℕ) : ℤ) - 4)} = 4 := by decide +kernel

end Nat
