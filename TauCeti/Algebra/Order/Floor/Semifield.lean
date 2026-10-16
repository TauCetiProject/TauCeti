/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith

/-!
# Ceilings of quotients by a time step

For a step `τ > 0` in an ordered field, the multiples `n τ` of the step lying in a half-open
interval `[s, t)` are those with `n ∈ [⌈s / τ⌉₊, ⌈t / τ⌉₊)`, and for `s ≤ t` there are at most
`(t - s) / τ + 1` of them. These are the index counts of time discretizations with step `τ`.

## Main results

* `TauCeti.natCast_ceil_div_sub_ceil_div_le`: `⌈t / τ⌉₊ - ⌈s / τ⌉₊ ≤ (t - s) / τ + 1`.
* `TauCeti.mem_Ico_ceil_div_iff`: `n ∈ [⌈s / τ⌉₊, ⌈t / τ⌉₊)` if and only if `n τ ∈ [s, t)`.
-/

public section

namespace TauCeti

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K]
  {τ s t : K}

/-- For a step `τ > 0` and `s ≤ t`, the indices in `[⌈s / τ⌉₊, ⌈t / τ⌉₊)` number at most
`(t - s) / τ + 1`. -/
theorem natCast_ceil_div_sub_ceil_div_le (hτ : 0 < τ) (hst : s ≤ t) :
    ((⌈t / τ⌉₊ - ⌈s / τ⌉₊ : ℕ) : K) ≤ (t - s) / τ + 1 := by
  -- For `t < 0` both ceilings vanish.
  rcases lt_or_ge t 0 with ht | ht
  · rw [Nat.ceil_eq_zero.2 (div_nonpos_of_nonpos_of_nonneg ht.le hτ.le), Nat.zero_sub,
      Nat.cast_zero]
    have := div_nonneg (sub_nonneg.2 hst) hτ.le
    linarith
  have hle : ⌈s / τ⌉₊ ≤ ⌈t / τ⌉₊ := Nat.ceil_mono (div_le_div_of_nonneg_right hst hτ.le)
  rw [Nat.cast_sub hle, sub_div]
  linarith [Nat.ceil_lt_add_one (div_nonneg ht hτ.le), Nat.le_ceil (s / τ)]

/-- For a step `τ > 0`, an index `n` lies in `[⌈s / τ⌉₊, ⌈t / τ⌉₊)` exactly when the multiple
`n τ` lies in `[s, t)`. -/
theorem mem_Ico_ceil_div_iff (hτ : 0 < τ) {n : ℕ} :
    n ∈ Finset.Ico ⌈s / τ⌉₊ ⌈t / τ⌉₊ ↔ n * τ ∈ Set.Ico s t := by
  rw [Finset.mem_Ico, Nat.ceil_le, Nat.lt_ceil, div_le_iff₀ hτ, lt_div_iff₀ hτ, Set.mem_Ico]

end TauCeti
