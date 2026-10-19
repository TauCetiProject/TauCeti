/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Ceilings of quotients by a time step

For a step `τ > 0` in a linearly ordered division semiring, the multiples `n τ` of the step
lying in a half-open interval `[s, t)` are those with `n ∈ [⌈s / τ⌉₊, ⌈t / τ⌉₊)`. With ordered
subtraction and `s ≤ t`, there are strictly fewer than `(t - s) / τ + 1` of them. These are the
index counts of time discretizations with step `τ`. The counting bound also holds for `τ = 0`.

## Main results

* `TauCeti.natCast_ceil_div_sub_ceil_div_lt`: `⌈t / τ⌉₊ - ⌈s / τ⌉₊ < (t - s) / τ + 1`.
* `TauCeti.mem_Ico_ceil_div_iff`: `n ∈ [⌈s / τ⌉₊, ⌈t / τ⌉₊)` if and only if `n τ ∈ [s, t)`.
-/

public section

namespace TauCeti

variable {K : Type*} [DivisionSemiring K] [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K]
  {τ s t : K}

/-- For a nonnegative step `τ` and `s ≤ t`, the indices in `[⌈s / τ⌉₊, ⌈t / τ⌉₊)` number
strictly less than `(t - s) / τ + 1`. This holds for both ordinary and truncated subtraction. -/
theorem natCast_ceil_div_sub_ceil_div_lt [Sub K] [OrderedSub K] [ExistsAddOfLE K]
    (hτ : 0 ≤ τ) (hst : s ≤ t) :
    ((⌈t / τ⌉₊ - ⌈s / τ⌉₊ : ℕ) : K) < (t - s) / τ + 1 := by
  -- For `t < 0` both ceilings vanish.
  rcases lt_or_ge t 0 with ht | ht
  · rw [Nat.ceil_eq_zero.2 (div_nonpos_of_nonpos_of_nonneg ht.le hτ), Nat.zero_sub,
      Nat.cast_zero]
    exact add_pos_of_nonneg_of_pos
      (div_nonneg (le_tsub_of_add_le_left ((add_zero s).trans_le hst)) hτ) zero_lt_one
  have hle : ⌈s / τ⌉₊ ≤ ⌈t / τ⌉₊ := Nat.ceil_mono (div_le_div_of_nonneg_right hst hτ)
  have hdiv : (t - s) / τ + s / τ = t / τ := by
    rw [← add_div, tsub_add_cancel_of_le hst]
  apply (add_lt_add_iff_right (⌈s / τ⌉₊ : K)).mp
  calc
    ((⌈t / τ⌉₊ - ⌈s / τ⌉₊ : ℕ) : K) + ⌈s / τ⌉₊ = (⌈t / τ⌉₊ : K) := by
      rw [← Nat.cast_add, Nat.sub_add_cancel hle]
    _ < t / τ + 1 := Nat.ceil_lt_add_one (div_nonneg ht hτ)
    _ ≤ (t - s) / τ + 1 + ⌈s / τ⌉₊ := by
      rw [← hdiv, add_right_comm]
      gcongr
      exact Nat.le_ceil _

/-- For a step `τ > 0`, an index `n` lies in `[⌈s / τ⌉₊, ⌈t / τ⌉₊)` exactly when the multiple
`n τ` lies in `[s, t)`. -/
theorem mem_Ico_ceil_div_iff (hτ : 0 < τ) {n : ℕ} :
    n ∈ Finset.Ico ⌈s / τ⌉₊ ⌈t / τ⌉₊ ↔ n * τ ∈ Set.Ico s t := by
  rw [Finset.mem_Ico, Nat.ceil_le, Nat.lt_ceil, div_le_iff₀ hτ, lt_div_iff₀ hτ, Set.mem_Ico]

end TauCeti
