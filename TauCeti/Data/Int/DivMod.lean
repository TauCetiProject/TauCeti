/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Unbundled.Int

/-!
# Quotient and remainder of a successor in `ℤ`

For `n ≠ 0` the remainder `m % n` lies in `[0, |n|)`, so passing from `m` to `m + 1` either
increases the remainder by one, keeping the quotient `m / n`, or, when `m % n + 1 = |n|`, resets
the remainder to `0` and moves the quotient by the sign of `n`. These are the integer counterparts
of `Nat.succ_div_of_not_dvd` and `Nat.succ_div_of_dvd`, phrased by the remainder so that they apply
to the periodic indexing `m ↦ (m / n, m % n)`. Each of the four formulas below holds for every `n`,
including `n = 0`; the two cases are exhaustive only for `n ≠ 0`, where `Int.add_one_natMod_cases`
states the resulting dichotomy for the natural remainder `m.natMod n`.

## Main results

* `Int.add_one_ediv_of_emod_add_one_lt`, `Int.add_one_emod_of_emod_add_one_lt`: if
  `m % n + 1 < |n|` then `(m + 1) / n = m / n` and `(m + 1) % n = m % n + 1`.
* `Int.add_one_ediv_of_emod_add_one_eq`, `Int.add_one_emod_of_emod_add_one_eq`: if
  `m % n + 1 = |n|` then `(m + 1) / n = m / n + n.sign` and `(m + 1) % n = 0`.
* `Int.add_one_natMod_cases`: for `n ≠ 0`, either `(m + 1).natMod n = m.natMod n + 1` with the
  same quotient, or `m.natMod n + 1 = |n|`, `(m + 1).natMod n = 0` and the quotient moves by
  `n.sign`.
-/

public section

namespace Int

variable {m n : ℤ}

/-- If `m % n + 1 < |n|`, then `m + 1` has the same quotient as `m` on division by `n`. -/
theorem add_one_ediv_of_emod_add_one_lt (h : m % n + 1 < |n|) : (m + 1) / n = m / n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have := emod_nonneg m hn
  have hm : m + 1 = m % n + 1 + n * (m / n) := by have := emod_add_mul_ediv m n; omega
  rw [hm, add_mul_ediv_left _ _ hn, ediv_eq_zero_of_lt_abs (by omega) h, zero_add]

/-- If `m % n + 1 < |n|`, then the remainder of `m + 1` on division by `n` is `m % n + 1`. -/
theorem add_one_emod_of_emod_add_one_lt (h : m % n + 1 < |n|) : (m + 1) % n = m % n + 1 := by
  rw [emod_def, add_one_ediv_of_emod_add_one_lt h, emod_def]
  omega

/-- If `m % n + 1 = |n|`, then the quotient of `m + 1` on division by `n` is `m / n + n.sign`. -/
theorem add_one_ediv_of_emod_add_one_eq (h : m % n + 1 = |n|) : (m + 1) / n = m / n + n.sign := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  refine Int.ediv_eq_of_eq_mul_right hn ?_
  rw [Int.mul_add, mul_comm n n.sign, sign_mul_self_eq_abs, ← h]
  have := emod_add_mul_ediv m n
  omega

/-- If `m % n + 1 = |n|`, then `m + 1` is divisible by `n`. -/
theorem add_one_emod_of_emod_add_one_eq (h : m % n + 1 = |n|) : (m + 1) % n = 0 := by
  refine emod_eq_zero_of_dvd ⟨m / n + n.sign, ?_⟩
  rw [Int.mul_add, mul_comm n n.sign, sign_mul_self_eq_abs, ← h]
  have := emod_add_mul_ediv m n
  omega

/-- For `n ≠ 0`, passing from `m` to `m + 1` either moves the natural remainder `m.natMod n` up by
one and keeps the quotient `m / n`, or moves it from its last value `|n| - 1` back to `0` and moves
the quotient by the sign of `n`. -/
theorem add_one_natMod_cases (m : ℤ) (hn : n ≠ 0) :
    (m + 1).natMod n = m.natMod n + 1 ∧ (m + 1) / n = m / n ∨
      (m + 1).natMod n = 0 ∧ m.natMod n + 1 = n.natAbs ∧ (m + 1) / n = m / n + n.sign := by
  have := emod_nonneg m hn
  have := emod_lt m hn
  have := abs_eq_natAbs n
  obtain h | h : m % n + 1 < |n| ∨ m % n + 1 = |n| := by omega
  · refine .inl ⟨?_, add_one_ediv_of_emod_add_one_lt h⟩
    rw [natMod, natMod, add_one_emod_of_emod_add_one_lt h]
    omega
  · refine .inr ⟨by rw [natMod, add_one_emod_of_emod_add_one_eq h]; rfl, ?_,
      add_one_ediv_of_emod_add_one_eq h⟩
    rw [natMod]
    omega

end Int
