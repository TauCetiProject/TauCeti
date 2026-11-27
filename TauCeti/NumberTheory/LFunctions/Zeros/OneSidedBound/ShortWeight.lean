/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Interval.Set.Defs

/-!
# The short weight in a two-cutoff prime sum

The short weight `x * b / x₁` must be large on the initial scale `x` but small relative to the
long weight `b`. A power separation between `x` and `x₁` gives the upper bound, and a square
separation between `x₁` and `b` already suffices for the lower bound, even for rounded weights.
This is the comparison in `New.Data.a_div_x₁_mem_Icc` in lsernau/grh-lean (commit `72fead1`).
-/

public section

namespace TauCeti.OneSidedBound

/-- For separated cutoffs, the short weight stays above `x ^ k` and at most the long weight
`b` divided by `x ^ k`. All quotients are natural-number quotients; no divisibility premise is
needed. At `k = 999` this applies to the cutoffs with `x ^ 1000000 ≤ x₁` and `x₁ ^ 1000000 ≤ b`.
-/
theorem shortWeight_mem_Icc {x x₁ b k : ℕ} (hx : 0 < x) (h₁ : x ^ (k + 1) ≤ x₁)
    (hb : x₁ ^ 2 ≤ b) : x * b / x₁ ∈ Set.Icc (x ^ k) (b / x ^ k) := by
  rw [Nat.pow_succ] at h₁
  have hk : 0 < x ^ k := Nat.pow_pos hx
  have hpow : x ^ k ≤ x₁ := Nat.le_trans (Nat.le_mul_of_pos_right _ hx) h₁
  have hx₁ : 0 < x₁ := Nat.lt_of_lt_of_le hk hpow
  refine ⟨(Nat.le_div_iff_mul_le hx₁).2 ?_, (Nat.le_div_iff_mul_le hk).2 ?_⟩
  · calc
      x ^ k * x₁ ≤ x₁ ^ 2 := by rw [Nat.pow_two]; exact Nat.mul_le_mul_right _ hpow
      _ ≤ b := hb
      _ ≤ x * b := Nat.le_mul_of_pos_left _ hx
  · apply Nat.le_of_mul_le_mul_right _ hx
    rw [Nat.mul_assoc, Nat.mul_comm b x]
    exact Nat.le_trans (Nat.mul_le_mul_left _ h₁) (Nat.div_mul_le_self _ _)

end TauCeti.OneSidedBound
