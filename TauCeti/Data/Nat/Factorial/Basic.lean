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
`Nat.pow_le_mul_descFactorial`, the falling-factorial lower bound `n ^ k ≤ c * (n)_k` whenever
`c * k.choose 2 ≤ (c - 1) * n` (including `Nat.pow_le_two_mul_descFactorial`, `n ^ k ≤ 2 * (n)_k`
whenever `k * (k - 1) ≤ n`); `Nat.six_pow_mul_factorial_le_factorial_two_mul_add_one`,
`6 ^ n * n ! ≤ (2 * n + 1)!`, the termwise comparison of the power series of `x * exp (x ^ 2 / 6)`
and `sinh x`; `Nat.factorial_succ_sq_le_four_pow_mul_factorial_two_mul`,
`((n + 1)!)² ≤ 4 ^ n * (2 * n)!`, the termwise comparison that sums moment bounds `((n + 1)!)² aⁿ`
against the series of `cosh`; `Nat.factorial_add_mul_factorial_add_le`,
`(s + j)! * (s + j)! ≤ (2 * s + j)! * j !`, which bounds products of factorials in double
hypergeometric series; and `Nat.factorial_div_mul_factorial_div_dvd`,
`(i / d)! * (j / d)! ∣ ((i + j) / d)!`.
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
  cases n <;> simp [Nat.pow_two, succ_mul]

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

/-- If `0 < c` and `c * k.choose 2 ≤ (c - 1) * n`, then `n ^ k ≤ c * n.descFactorial k`. -/
theorem pow_le_mul_descFactorial {n k c : ℕ} (hc : 0 < c) (h : c * k.choose 2 ≤ (c - 1) * n) :
    n ^ k ≤ c * n.descFactorial k := by
  cases k with
  | zero => simpa using Nat.succ_le_of_lt hc
  | succ m =>
    have hpow := Nat.mul_le_mul_left c (pow_succ_le_descFactorial_succ_add n m)
    have herr : c * ((m + 1).choose 2 * n ^ m) ≤ (c - 1) * n ^ (m + 1) := by
      calc c * ((m + 1).choose 2 * n ^ m)
          = (c * (m + 1).choose 2) * n ^ m := by rw [Nat.mul_assoc]
        _ ≤ ((c - 1) * n) * n ^ m := Nat.mul_le_mul_right _ h
        _ = (c - 1) * n ^ (m + 1) := by rw [Nat.mul_assoc, Nat.mul_comm n, ← Nat.pow_succ]
    have hsum : c * n ^ (m + 1) ≤ c * n.descFactorial (m + 1) + (c - 1) * n ^ (m + 1) :=
      hpow.trans (Nat.mul_add _ _ _ ▸ Nat.add_le_add_left herr _)
    have hsplit : c * n ^ (m + 1) = n ^ (m + 1) + (c - 1) * n ^ (m + 1) := by
      calc c * n ^ (m + 1) = (1 + (c - 1)) * n ^ (m + 1) := by congr 1; omega
        _ = n ^ (m + 1) + (c - 1) * n ^ (m + 1) := by rw [Nat.add_mul, Nat.one_mul]
    omega

/-- If `k * (k - 1) ≤ n`, then `n ^ k ≤ 2 * n.descFactorial k`. In particular, `n ^ 3 ≤ 2 * (n)₃`
for `n ≥ 6`. -/
theorem pow_le_two_mul_descFactorial {n k : ℕ} (h : k * (k - 1) ≤ n) :
    n ^ k ≤ 2 * n.descFactorial k := by
  refine pow_le_mul_descFactorial (c := 2) Nat.two_pos ?_
  rw [Nat.choose_two_right, Nat.one_mul]
  exact (Nat.mul_div_le (k * (k - 1)) 2).trans h

/-- `6 ^ n * n ! ≤ (2 * n + 1)!`, with equality at `n = 0` and `n = 1`. -/
theorem six_pow_mul_factorial_le_factorial_two_mul_add_one (n : ℕ) :
    6 ^ n * n ! ≤ (2 * n + 1)! := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_add_one]
    calc 6 ^ (n + 1) * (n + 1)! = 6 * (n + 1) * (6 ^ n * n !) := by
          rw [Nat.pow_succ, factorial_succ]; ac_rfl
      _ ≤ (2 * n + 2 + 1) * (2 * n + 2) * (2 * n + 1)! := by
          refine Nat.mul_le_mul ?_ ih
          calc 6 * (n + 1) = 3 * (2 * n + 2) := by omega
            _ ≤ (2 * n + 2 + 1) * (2 * n + 2) := Nat.mul_le_mul_right _ (by omega)
      _ = (2 * n + 2 + 1)! := by
          rw [factorial_succ (2 * n + 2), factorial_succ (2 * n + 1), Nat.mul_assoc]

/-- `((n + 1)!)² ≤ 4 ^ n * (2 * n)!`, with equality at `n = 0`. -/
theorem factorial_succ_sq_le_four_pow_mul_factorial_two_mul (n : ℕ) :
    (n + 1)! ^ 2 ≤ 4 ^ n * (2 * n)! := by
  -- Square `n + 1 ≤ 2 ^ n`.
  have hn : (n + 1) ^ 2 ≤ 4 ^ n :=
    calc (n + 1) ^ 2 ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left n.lt_two_pow_self 2
      _ = 4 ^ n := by rw [← Nat.pow_mul, Nat.mul_comm, Nat.pow_mul]
  have hc : n ! * n ! ≤ (2 * n)! := by
    rw [Nat.two_mul]
    exact le_of_dvd (factorial_pos _) (factorial_mul_factorial_dvd_factorial_add n n)
  rw [factorial_succ, Nat.mul_pow, Nat.pow_two n !]
  exact Nat.mul_le_mul hn hc

/-- `(s + j)! * (s + j)! ≤ (2 * s + j)! * j !`, with equality at `s = 0`: equivalently,
`C(s + j, s) ≤ C(2 * s + j, s)`. -/
theorem factorial_add_mul_factorial_add_le (s j : ℕ) :
    (s + j)! * (s + j)! ≤ (2 * s + j)! * j ! := by
  have e₁ := add_choose_mul_factorial_mul_factorial j s
  have e₂ := add_choose_mul_factorial_mul_factorial (s + j) s
  have e₃ : (j + s).choose s ≤ (s + j + s).choose s := choose_le_choose s (by omega)
  rw [Nat.add_comm j s] at e₁ e₃
  rw [show 2 * s + j = s + j + s by omega]
  calc (s + j)! * (s + j)! = (s + j).choose s * j ! * s ! * (s + j)! := by rw [e₁]
    _ ≤ (s + j + s).choose s * j ! * s ! * (s + j)! :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ e₃))
    _ = (s + j + s).choose s * (s + j)! * s ! * j ! := by ac_rfl
    _ = (s + j + s)! * j ! := by rw [e₂]

/-- Factorial divisibility under Euclidean division: `(i / d)! * (j / d)! ∣ ((i + j) / d)!`. -/
theorem factorial_div_mul_factorial_div_dvd (d i j : ℕ) :
    (i / d)! * (j / d)! ∣ ((i + j) / d)! :=
  Nat.dvd_trans (factorial_mul_factorial_dvd_factorial_add (i / d) (j / d))
    (factorial_dvd_factorial div_add_div_le_add_div)

end Nat
