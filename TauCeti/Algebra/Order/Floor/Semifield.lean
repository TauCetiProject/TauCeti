/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Order.Interval.Finset.Nat

import Mathlib.Data.Rat.Floor

/-!
# Ceilings and floors of quotients by a step

For a step `τ > 0` in a linearly ordered division semiring, the multiples `n τ` of the step
lying in a half-open interval `[s, t)` are those with `n ∈ [⌈s / τ⌉₊, ⌈t / τ⌉₊)`. With ordered
subtraction and `s ≤ t`, there are strictly fewer than `(t - s) / τ + 1` of them. These are the
index counts of time discretizations with step `τ`. The counting bound also holds for `τ = 0`.

Dually, for `B > 0` and any natural degree bound `n`, multiplying `B < ⌊B⌋₊ + 1` by
`n / B < ⌊n / B⌋₊ + 1` gives `n < (⌊B⌋₊ + 1) * (⌊n / B⌋₊ + 1)`, and in particular
`n < (2 * ⌊B⌋₊ + 1) * (⌊n / B⌋₊ + 1)`. This includes `n = 0` and `B < 1`, and counts the available
jet conditions on an integer interval of radius `B`.

## Main results

* `TauCeti.natCast_ceil_div_sub_ceil_div_lt`: `⌈t / τ⌉₊ - ⌈s / τ⌉₊ < (t - s) / τ + 1`.
* `TauCeti.mem_Ico_ceil_div_iff`: `n ∈ [⌈s / τ⌉₊, ⌈t / τ⌉₊)` if and only if `n τ ∈ [s, t)`.
* `TauCeti.exists_pos_nat_mul_bounds`: a positive multiple `N a` lies in `(t, t + a]`.
* `TauCeti.lt_floor_add_one_mul_floor_div_add_one`: `n < (⌊B⌋₊ + 1) * (⌊n / B⌋₊ + 1)` for `B > 0`.
* `TauCeti.lt_two_mul_floor_add_one_mul_floor_div_add_one`:
  `n < (2 * ⌊B⌋₊ + 1) * (⌊n / B⌋₊ + 1)` for `B > 0`.
-/

public section

namespace TauCeti

variable {K : Type*} [DivisionSemiring K] [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K]
  {τ s t B : K}

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

/-- For `B > 0` and any `n : ℕ`, `(⌊B⌋₊ + 1) * (⌊n / B⌋₊ + 1)` strictly exceeds `n`, including
when `n = 0` or `B < 1`. -/
theorem lt_floor_add_one_mul_floor_div_add_one (hB : 0 < B) (n : ℕ) :
    n < (⌊B⌋₊ + 1) * (⌊(n : K) / B⌋₊ + 1) := by
  have h1 : (n : K) / B < ((⌊(n : K) / B⌋₊ + 1 : ℕ) : K) := by
    simpa using Nat.lt_floor_add_one ((n : K) / B)
  have h2 : B < ((⌊B⌋₊ + 1 : ℕ) : K) := by
    simpa using Nat.lt_floor_add_one B
  refine Nat.cast_lt (α := K).1 ?_
  calc (n : K)
      = (n : K) / B * B := (div_mul_cancel₀ (n : K) hB.ne').symm
    _ < ((⌊(n : K) / B⌋₊ + 1 : ℕ) : K) * B := mul_lt_mul_of_pos_right h1 hB
    _ < ((⌊(n : K) / B⌋₊ + 1 : ℕ) : K) * ((⌊B⌋₊ + 1 : ℕ) : K) :=
        mul_lt_mul_of_pos_left h2 (Nat.cast_pos.2 (Nat.succ_pos _))
    _ = (((⌊B⌋₊ + 1) * (⌊(n : K) / B⌋₊ + 1) : ℕ) : K) := by
        rw [← Nat.cast_mul, Nat.mul_comm]

/-- For `B > 0` and any `n : ℕ`, `(2 * ⌊B⌋₊ + 1) * (⌊n / B⌋₊ + 1)` strictly exceeds `n`: an
integer interval `[-⌊B⌋₊, ⌊B⌋₊]` with derivative orders up to `⌊n / B⌋₊` has more than `n`
point-order pairs, also when `n = 0` or `B < 1`. -/
theorem lt_two_mul_floor_add_one_mul_floor_div_add_one (hB : 0 < B) (n : ℕ) :
    n < (2 * ⌊B⌋₊ + 1) * (⌊(n : K) / B⌋₊ + 1) :=
  (lt_floor_add_one_mul_floor_div_add_one hB n).trans_le (Nat.mul_le_mul_right _ (by omega))

/-- For a nonnegative `t` and positive `a`, some positive multiple `N a` lies in `(t, t + a]`. -/
theorem exists_pos_nat_mul_bounds {t a : K} (ht : 0 ≤ t) (ha : 0 < a) :
    ∃ N : ℕ, 1 ≤ N ∧ t < N * a ∧ N * a ≤ t + a := by
  have htdiv : 0 ≤ t / a := div_nonneg ht ha.le
  refine ⟨⌊t / a⌋₊ + 1, by omega, ?_, ?_⟩
  · have h := Nat.lt_floor_add_one (t / a)
    exact (div_lt_iff₀ ha).mp (by simpa only [Nat.cast_add, Nat.cast_one] using h)
  · push_cast
    rw [add_mul, one_mul]
    exact add_le_add_left ((le_div_iff₀ ha).mp (Nat.floor_le htdiv)) a

/-- For `n = 3` and `B = 1 / 2`, `⌊B⌋₊ = 0` and `⌊n / B⌋₊ = 6`, giving `1 * 7 > 3`; for `n = 2`
and `B = 3`, `⌊B⌋₊ = 3` and `⌊n / B⌋₊ = 0`, giving `7 * 1 > 2`. -/
example : ⌊(1 / 2 : ℚ)⌋₊ = 0 ∧ ⌊(3 : ℚ) / (1 / 2)⌋₊ = 6 ∧
    3 < (2 * ⌊(1 / 2 : ℚ)⌋₊ + 1) * (⌊(3 : ℚ) / (1 / 2)⌋₊ + 1) ∧
    ⌊(3 : ℚ)⌋₊ = 3 ∧ ⌊(2 : ℚ) / 3⌋₊ = 0 ∧
    2 < (2 * ⌊(3 : ℚ)⌋₊ + 1) * (⌊(2 : ℚ) / 3⌋₊ + 1) := by
  refine ⟨?_, ?_, lt_two_mul_floor_add_one_mul_floor_div_add_one (by norm_num) 3, ?_, ?_,
    lt_two_mul_floor_add_one_mul_floor_div_add_one (by norm_num) 2⟩ <;> norm_num

end TauCeti
