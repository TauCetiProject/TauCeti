/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.CardIntervalMod

/-!
# An upper bound for the integers of an interval with given residue

Mathlib's `Int.Ico_filter_modEq_card` counts the integers of `[a, b)` congruent to `v` modulo
`r > 0` exactly, as a difference of two ceilings. For estimates, the useful consequence is the
uniform bound `(b - a) / r + 1`, independent of the residue `v`: a box of side `L` in `ℤ^n`
contains at most `(L / r + 1) ^ n` points of any one residue class modulo `r`.
-/

public section

open Finset

namespace Int

/-- An interval `[a, b)` of integers with `a ≤ b` contains at most `(b - a) / r + 1` integers
congruent to `v` modulo `r > 0`, whatever the residue `v`. -/
theorem card_Ico_filter_modEq_le {r : ℤ} (hr : 0 < r) {a b : ℤ} (hab : a ≤ b) (v : ℤ) :
    (#{x ∈ Ico a b | x ≡ v [ZMOD r]} : ℚ) ≤ (b - a) / r + 1 := by
  have hr' : (0 : ℚ) < r := by exact_mod_cast hr
  have hcard : ((#{x ∈ Ico a b | x ≡ v [ZMOD r]} : ℤ) : ℚ) =
      ((max (⌈(b - v) / (r : ℚ)⌉ - ⌈(a - v) / (r : ℚ)⌉) 0 : ℤ) : ℚ) := by
    rw [Ico_filter_modEq_card _ _ hr]
  rw [Int.cast_natCast] at hcard
  rw [hcard, Int.cast_max, Int.cast_zero, max_le_iff]
  have hba : (0 : ℚ) ≤ (b - a) / r := div_nonneg (by exact_mod_cast sub_nonneg.mpr hab) hr'.le
  refine ⟨?_, by linarith⟩
  have h₁ := Int.ceil_lt_add_one ((b - v) / (r : ℚ))
  have h₂ := Int.le_ceil ((a - v) / (r : ℚ))
  have hsplit : ((b : ℚ) - a) / r = (b - v) / r - (a - v) / r := by ring
  push_cast
  linarith

end Int
