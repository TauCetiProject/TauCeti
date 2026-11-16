/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Basic

/-!
# Nonvanishing factorials

The factorial of a natural number is nonzero. Registering this fact as an instance
also lets `NeZero.charZero` infer nonvanishing of factorials cast to characteristic-zero
scalars, so constructions requiring an invertible factorial apply automatically there.

The file also records `Nat.sq_eq_descFactorial_two_add`, the expansion `n ^ 2 = (n)₂ + n` of a
square into falling factorials, which converts second factorial moments into second moments;
`Nat.pow_le_two_mul_descFactorial`, the falling-factorial lower bound `n ^ k ≤ 2 * (n)_k` whenever
`k * (k - 1) ≤ n`; `Nat.six_pow_mul_factorial_le_factorial_two_mul_add_one`,
`6 ^ n * n ! ≤ (2 * n + 1)!`, the termwise comparison of the power series of `x * exp (x ^ 2 / 6)`
and `sinh x`; and `Nat.factorial_succ_sq_le_four_pow_mul_factorial_two_mul`,
`((n + 1)!)² ≤ 4 ^ n * (2 * n)!`, the termwise comparison that sums moment bounds `((n + 1)!)² aⁿ`
against the series of `cosh`.
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

/-- If `k * (k - 1) ≤ n`, then `n ^ k ≤ 2 * n.descFactorial k`. In particular, `n ^ 3 ≤ 2 * (n)₃`
for `n ≥ 6`. -/
theorem pow_le_two_mul_descFactorial {n k : ℕ} (h : k * (k - 1) ≤ n) :
    n ^ k ≤ 2 * n.descFactorial k := by
  have hkey : ∀ m, (2 * n - m * (m - 1)) * n ^ m ≤ 2 * n * n.descFactorial m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      simp only [Nat.add_sub_cancel]
      by_cases hlt : (m + 1) * m < 2 * n
      · have hstep : (m + 1) * m = m * (m - 1) + 2 * m := by
          cases m with
          | zero => simp
          | succ j =>
            simp only [Nat.add_sub_cancel]
            rw [Nat.mul_comm (j + 1) j, ← Nat.add_mul]
        have hmn : m ≤ n := by omega
        have hsub : 2 * n - m * (m - 1) = (2 * n - (m + 1) * m) + 2 * m := by omega
        have hle1 : (2 * n - (m + 1) * m) * n ≤ (n - m) * (2 * n - m * (m - 1)) := by
          set a := 2 * n - (m + 1) * m
          have ha : a ≤ 2 * (n - m) := by omega
          calc a * n = a * ((n - m) + m) := by rw [Nat.sub_add_cancel hmn]
            _ = a * (n - m) + a * m := Nat.mul_add a (n - m) m
            _ ≤ a * (n - m) + (2 * (n - m)) * m :=
                Nat.add_le_add_left (Nat.mul_le_mul_right m ha) _
            _ = (n - m) * (a + 2 * m) := by
                rw [Nat.mul_add, Nat.mul_comm a (n - m)]
                congr 1
                ac_rfl
            _ = (n - m) * (2 * n - m * (m - 1)) := by rw [hsub]
        calc (2 * n - (m + 1) * m) * n ^ (m + 1)
            = (2 * n - (m + 1) * m) * n * n ^ m := by
                rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm (n ^ m) n, ← Nat.mul_assoc]
          _ ≤ (n - m) * (2 * n - m * (m - 1)) * n ^ m := Nat.mul_le_mul_right _ hle1
          _ = (n - m) * ((2 * n - m * (m - 1)) * n ^ m) := Nat.mul_assoc _ _ _
          _ ≤ (n - m) * (2 * n * n.descFactorial m) := Nat.mul_le_mul_left _ ih
          _ = 2 * n * ((n - m) * n.descFactorial m) := by
                rw [← Nat.mul_assoc, Nat.mul_comm (n - m), Nat.mul_assoc]
          _ = 2 * n * n.descFactorial (m + 1) := by rw [descFactorial_succ]
      · have hzero : 2 * n - (m + 1) * m = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_lt hlt)
        simp [hzero]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rcases k with _ | _ | k
    · simp
    · simp
    · exact absurd h (Nat.not_le_of_lt (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)))
  · have hle : n * n ^ k ≤ n * (2 * n.descFactorial k) := by
      calc n * n ^ k ≤ (2 * n - k * (k - 1)) * n ^ k := Nat.mul_le_mul_right _ (by omega)
        _ ≤ 2 * n * n.descFactorial k := hkey k
        _ = n * (2 * n.descFactorial k) := by rw [Nat.mul_comm 2 n, Nat.mul_assoc]
    exact Nat.le_of_mul_le_mul_left hle hn

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
