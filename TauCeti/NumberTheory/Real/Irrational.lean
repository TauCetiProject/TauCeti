/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Real.Irrational

/-!
# Irrationality of squares of real fourth roots

For a nonnegative real number `x`, the square of the fourth root `x ^ (1 / 4 : ℝ)` is `√x`, so
`(x ^ (1 / 4 : ℝ)) ^ 2` is irrational if and only if `√x` is irrational
(`TauCeti.irrational_rpow_one_quarter_sq_iff`). In particular, for any prime `p` — and specifically
for `p = 2` (`TauCeti.irrational_two_rpow_one_quarter_sq`) — the square of `(p : ℝ) ^ (1 / 4 : ℝ)`
is irrational. This supplies the irrational-square condition `Irrational (c ^ 2)` for rank-one
non-integral lattices `c ℤ ⊆ ℝ` such as `2 ^ (1 / 4) ℤ`.

## Main statements

* `TauCeti.irrational_rpow_one_quarter_sq_iff`: for `0 ≤ x`,
  `Irrational ((x ^ (1 / 4 : ℝ)) ^ 2) ↔ Irrational √x`.
* `Nat.Prime.irrational_rpow_one_quarter_sq`: for prime `p`,
  `Irrational (((p : ℝ) ^ (1 / 4 : ℝ)) ^ 2)`.
* `TauCeti.irrational_two_rpow_one_quarter_sq`: `Irrational (((2 : ℝ) ^ (1 / 4 : ℝ)) ^ 2)`.
-/

public section

namespace TauCeti

/-- For a nonnegative real number `x`, the square of `x ^ (1 / 4)` equals `√x` and is therefore
irrational if and only if `√x` is irrational. Nonnegativity cannot be dropped: at `x = -2`,
`((-2) ^ (1 / 4)) ^ 2 = √2 / 2` is irrational whereas `√(-2) = 0` is rational. -/
theorem irrational_rpow_one_quarter_sq_iff {x : ℝ} (hx : 0 ≤ x) :
    Irrational ((x ^ ((1 : ℝ) / 4)) ^ 2) ↔ Irrational √x := by
  have hhalf : (1 : ℝ) / 4 * (2 : ℕ) = 1 / (2 : ℝ) := by norm_num
  have hsq : (x ^ ((1 : ℝ) / 4)) ^ 2 = √x := by
    rw [← Real.rpow_mul_natCast hx, hhalf, ← Real.sqrt_eq_rpow]
  rw [hsq]

/-- For a prime `p`, the square of `(p : ℝ) ^ (1 / 4)` is `√p`, hence irrational. -/
theorem _root_.Nat.Prime.irrational_rpow_one_quarter_sq {p : ℕ} (hp : p.Prime) :
    Irrational (((p : ℝ) ^ ((1 : ℝ) / 4)) ^ 2) :=
  (irrational_rpow_one_quarter_sq_iff p.cast_nonneg).mpr hp.irrational_sqrt

/-- The square of `2 ^ (1 / 4 : ℝ)` is `√2`, hence irrational. -/
theorem irrational_two_rpow_one_quarter_sq :
    Irrational (((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2) :=
  Nat.prime_two.irrational_rpow_one_quarter_sq

end TauCeti
