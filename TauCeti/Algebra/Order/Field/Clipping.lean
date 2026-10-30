/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A fourth-power bound for clipping

For `M > 0`, clipping an element of a linearly ordered field to `[-M, M]` has squared
error at most its fourth power divided by `16 M²`. The constant `1/16` is sharp, with
equality at `x = 2M`.
Integrating this pointwise estimate gives the fourth-moment clipping bound used in the
Gaussian truncation proof of Grothendieck's inequality.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §8.1.
-/

public section

namespace TauCeti

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

/-- The pointwise fourth-moment estimate for clipping, with the sharp constant `1/16`. -/
theorem sq_sub_max_min_le_pow_four_div {M : α} (hM : 0 < M) (x : α) :
    (x - max (-M) (min M x)) ^ 2 ≤ x ^ 4 / (16 * M ^ 2) := by
  have tail (t : α) (ht : M ≤ t) : (t - M) ^ 2 ≤ t ^ 4 / (16 * M ^ 2) := by
    apply (le_div_iff₀ (by positivity : 0 < 16 * M ^ 2)).2
    have h : 4 * M * (t - M) ≤ t ^ 2 := by nlinarith [sq_nonneg (t - 2 * M)]
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 4 * M * (t - M)) h 2
    nlinarith only [hh]
  rcases le_total x (-M) with hx | hx
  · rw [min_eq_right (by linarith), max_eq_left hx]
    convert tail (-x) (by linarith) using 1 <;> ring
  · rcases le_total x M with hx' | hx'
    · simp only [min_eq_right hx', max_eq_right hx, sub_self, zero_pow (by decide : 2 ≠ 0)]
      positivity
    · rw [min_eq_left hx', max_eq_right (by linarith)]
      exact tail x hx'

end TauCeti
