/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Ring

/-!
# Integer floors of quotients by a step

For a step `δ > 0` in a linearly ordered field with an integer floor, the multiples of `δ` cut
the line into the closed intervals `[δ m, δ (m + 1)]` with `m ∈ ℤ`. Every point `x` lies in the
interval indexed by `⌊x / δ⌋`.

## Main results

* `TauCeti.mem_Icc_mul_floor_div`: `x ∈ [δ ⌊x / δ⌋, δ (⌊x / δ⌋ + 1)]`.
-/

public section

namespace TauCeti

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K] {δ : K}

/-- For a step `δ > 0`, the point `x` lies in the interval `[δ m, δ (m + 1)]` with
`m = ⌊x / δ⌋`. -/
theorem mem_Icc_mul_floor_div (hδ : 0 < δ) (x : K) :
    x ∈ Set.Icc (δ * ⌊x / δ⌋) (δ * (⌊x / δ⌋ + 1)) := by
  constructor
  · rw [mul_comm, ← le_div_iff₀ hδ]
    exact Int.floor_le _
  · rw [mul_comm, ← div_le_iff₀ hδ]
    exact (Int.lt_floor_add_one _).le

end TauCeti
