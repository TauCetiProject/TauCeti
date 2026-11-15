/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Nat.Choose.Basic

import Mathlib.Algebra.Group.Nat.Even

/-!
# Powers of products of scalar-semiconjugate elements

For a monoid `R` acting compatibly on a monoid `A` (`[IsScalarTower R A A]` and
`[SMulCommClass R A A]`), if `x * u = c • (u * x)` then straightening `(u * x) ^ n` into
`u ^ n * x ^ n` moves each factor of `x` across the preceding factors of `u`, accumulating
`1 + 2 + ⋯ + (n - 1) = n.choose 2` powers of `c`. When the commutation scalar is a square `q ^ 2`,
the exponent `2 * n.choose 2` simplifies to `n * (n - 1)`.

## Main results

* `TauCeti.mul_pow_of_mul_eq_smul_mul`: if `x * u = c • (u * x)`, then
  `(u * x) ^ n = c ^ n.choose 2 • (u ^ n * x ^ n)`.
* `TauCeti.mul_pow_of_mul_eq_sq_smul_mul`: if `x * u = q ^ 2 • (u * x)`, then
  `(u * x) ^ n = q ^ (n * (n - 1)) • (u ^ n * x ^ n)`.
-/

public section

namespace TauCeti

/-- If `x * u = c • (u * x)` for a compatible monoid action of `R` on `A`, then
`(u * x) ^ n = c ^ n.choose 2 • (u ^ n * x ^ n)`. -/
theorem mul_pow_of_mul_eq_smul_mul {R A : Type*} [Monoid R] [Monoid A] [MulAction R A]
    [IsScalarTower R A A] [SMulCommClass R A A] {c : R} {u x : A} (h : x * u = c • (u * x))
    (n : ℕ) : (u * x) ^ n = c ^ n.choose 2 • (u ^ n * x ^ n) := by
  have hpow (m : ℕ) : x ^ m * u = c ^ m • (u * x ^ m) := by
    have hsc : SemiconjBy u (c • x) x := by rw [SemiconjBy, mul_smul_comm, h]
    rw [← (hsc.pow_right m).eq, smul_pow, mul_smul_comm]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, smul_mul_assoc, mul_assoc, ← mul_assoc (x ^ n) u, hpow n, smul_mul_assoc,
      mul_smul_comm, smul_smul, ← pow_add, Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
    simp only [pow_succ, mul_assoc]

/-- If `x * u = q ^ 2 • (u * x)` for a compatible monoid action of `R` on `A`, then
`(u * x) ^ n = q ^ (n * (n - 1)) • (u ^ n * x ^ n)`. -/
theorem mul_pow_of_mul_eq_sq_smul_mul {R A : Type*} [Monoid R] [Monoid A] [MulAction R A]
    [IsScalarTower R A A] [SMulCommClass R A A] {q : R} {u x : A} (h : x * u = q ^ 2 • (u * x))
    (n : ℕ) : (u * x) ^ n = q ^ (n * (n - 1)) • (u ^ n * x ^ n) := by
  rw [mul_pow_of_mul_eq_smul_mul h, ← pow_mul, Nat.choose_two_right,
    Nat.two_mul_div_two_of_even n.even_mul_pred_self]

end TauCeti
