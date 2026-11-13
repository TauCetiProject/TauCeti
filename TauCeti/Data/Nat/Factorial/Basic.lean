/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Nonvanishing factorials and falling-factorial bounds

The factorial of a natural number is nonzero. Registering this fact as an instance
also lets `NeZero.charZero` infer nonvanishing of factorials cast to characteristic-zero
scalars, so constructions requiring an invertible factorial apply automatically there.

The file also records `Nat.sq_eq_descFactorial_two_add`, the expansion `n ^ 2 = (n)₂ + n` of a
square into falling factorials, which converts second factorial moments into second moments;
`Nat.pow_succ_le_descFactorial_succ_add`, `n ^ (k + 1) ≤ (n)_{k + 1} + ((k + 1).choose 2) * n ^ k`,
the pairwise-collision upper bound on `n ^ (k + 1) - (n)_{k + 1}`;
`Nat.six_pow_mul_factorial_le_factorial_two_mul_add_one`, `6 ^ n * n ! ≤ (2 * n + 1)!`, the
termwise comparison of the power series of `x * exp (x ^ 2 / 6)` and `sinh x`; and
`Nat.factorial_succ_sq_le_four_pow_mul_factorial_two_mul`, `((n + 1)!)² ≤ 4 ^ n * (2 * n)!`, the
termwise comparison that sums moment bounds `((n + 1)!)² aⁿ` against the series of `cosh`.
-/

public section

namespace TauCeti

/-- Natural factorials are nonzero, also enabling automatic nonvanishing of their
casts to characteristic-zero scalars. -/
instance instNeZeroFactorial {n : ℕ} : NeZero n.factorial :=
  ⟨Nat.factorial_ne_zero n⟩

end TauCeti

namespace Nat

/-- A square is the second falling factorial plus the number itself: `n ^ 2 = (n)₂ + n`. -/
theorem sq_eq_descFactorial_two_add (n : ℕ) : n ^ 2 = n.descFactorial 2 + n := by
  rcases n with _ | n
  · simp
  · rw [succ_descFactorial_succ, descFactorial_one, Nat.pow_two, succ_mul, Nat.mul_comm]

/-- A natural power exceeds the corresponding falling factorial by at most the pairwise-collision
bound `((k + 1).choose 2) * n ^ k`: `n ^ (k + 1) ≤ (n)_{k + 1} + ((k + 1).choose 2) * n ^ k`,
with equality for `k ≤ 1`. -/
theorem pow_succ_le_descFactorial_succ_add (n k : ℕ) :
    n ^ (k + 1) ≤ n.descFactorial (k + 1) + (k + 1).choose 2 * n ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc n ^ (k + 1 + 1) = n ^ (k + 1) * n := Nat.pow_succ n (k + 1)
      _ ≤ (n.descFactorial (k + 1) + (k + 1).choose 2 * n ^ k) * n := Nat.mul_le_mul_right n ih
      _ = n.descFactorial (k + 1 + 1) + (k + 1) * n.descFactorial (k + 1) +
            (k + 1).choose 2 * n ^ (k + 1) := by
          rw [Nat.add_mul, descFactorial_mul_self, Nat.mul_assoc, ← Nat.pow_succ]
      _ ≤ n.descFactorial (k + 1 + 1) + (k + 1) * n ^ (k + 1) +
            (k + 1).choose 2 * n ^ (k + 1) :=
          Nat.add_le_add_right
            (Nat.add_le_add_left (Nat.mul_le_mul_left _ (descFactorial_le_pow n (k + 1))) _) _
      _ = n.descFactorial (k + 1 + 1) + (k + 1 + 1).choose 2 * n ^ (k + 1) := by
          rw [choose_succ_succ (k + 1) 1, choose_one_right, Nat.add_mul (k + 1), ← Nat.add_assoc]

/-- `6 ^ n * n ! ≤ (2 * n + 1)!`, with equality at `n = 0` and `n = 1`. -/
theorem six_pow_mul_factorial_le_factorial_two_mul_add_one (n : ℕ) :
    6 ^ n * n ! ≤ (2 * n + 1)! := by
  induction n with
  | zero => simp
  | succ n ih =>
    -- The last term `(2 * n + 1 + 1 + 1)!` is `(2 * (n + 1) + 1)!` by unfolding.
    calc 6 ^ (n + 1) * (n + 1)! = 6 * (n + 1) * (6 ^ n * n !) := by
          rw [Nat.pow_succ, factorial_succ]; ac_rfl
      _ ≤ (2 * n + 1 + 1 + 1) * (2 * n + 1 + 1) * (2 * n + 1)! := by
          refine Nat.mul_le_mul ?_ ih
          calc 6 * (n + 1) = 3 * (2 * n + 1 + 1) := by omega
            _ ≤ (2 * n + 1 + 1 + 1) * (2 * n + 1 + 1) := Nat.mul_le_mul_right _ (by omega)
      _ = (2 * n + 1 + 1 + 1)! := by
          rw [factorial_succ (2 * n + 1 + 1), factorial_succ (2 * n + 1), Nat.mul_assoc]

/-- `((n + 1)!)² ≤ 4 ^ n * (2 * n)!`, with equality at `n = 0`. -/
theorem factorial_succ_sq_le_four_pow_mul_factorial_two_mul (n : ℕ) :
    (n + 1)! ^ 2 ≤ 4 ^ n * (2 * n)! := by
  have hn : (n + 1) ^ 2 ≤ 4 ^ n := by
    induction n with
    | zero => simp
    | succ k ih =>
      calc (k + 1 + 1) ^ 2 ≤ (2 * (k + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ = 4 * (k + 1) ^ 2 := by rw [Nat.mul_pow]
        _ ≤ 4 * 4 ^ k := Nat.mul_le_mul_left 4 ih
        _ = 4 ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  have hc : n ! * n ! ≤ (2 * n)! := by
    rw [Nat.two_mul]
    exact le_of_dvd (factorial_pos _) (factorial_mul_factorial_dvd_factorial_add n n)
  rw [factorial_succ, Nat.mul_pow, Nat.pow_two n !]
  exact Nat.mul_le_mul hn hc

end Nat
