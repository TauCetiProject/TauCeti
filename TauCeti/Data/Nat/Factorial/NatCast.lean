/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Divisibility
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Casts and inverses of factorials

If a positive natural number `m` vanishes in a semiring `R`, then so does the factorial of every
natural number `k ≥ m`, since `m ∣ k !`. In a characteristic-zero division semiring, the inverse of
`m !` steps to that of `(m + 1)!` via `(m !)⁻¹ = (m + 1) * ((m + 1)!)⁻¹`.

## Main results

* `Nat.cast_factorial_eq_zero_of_le`: `(m : R) = 0` with `0 < m ≤ k` gives `(k ! : R) = 0`.
* `Nat.inv_factorial_eq_add_one_mul_inv_factorial_succ`:
  `(m ! : K)⁻¹ = ((m : K) + 1) * ((m + 1)! : K)⁻¹` in a characteristic-zero division semiring.
-/

public section

namespace Nat

variable {R : Type*} [Semiring R]

/-- If `m` is positive and vanishes in `R`, so does the factorial of every `k ≥ m`. -/
theorem cast_factorial_eq_zero_of_le {m k : ℕ} (hm : 0 < m) (hmR : (m : R) = 0) (hk : m ≤ k) :
    (k.factorial : R) = 0 := by
  simpa only [hmR, zero_dvd_iff] using
    (Nat.cast_dvd_cast (Nat.dvd_factorial hm hk) : (m : R) ∣ (k.factorial : R))

/-- In a characteristic-zero division semiring, `(m ! : K)⁻¹ = (m + 1) * ((m + 1)! : K)⁻¹`. -/
theorem inv_factorial_eq_add_one_mul_inv_factorial_succ {K : Type*} [DivisionSemiring K]
    [CharZero K] (m : ℕ) :
    (m.factorial : K)⁻¹ = ((m : K) + 1) * ((m + 1).factorial : K)⁻¹ := by
  rw [factorial_succ, Nat.mul_comm, cast_mul, cast_add, cast_one, mul_inv_rev, ← mul_assoc,
    mul_inv_cancel₀ (cast_add_one_ne_zero m), one_mul]

end Nat
