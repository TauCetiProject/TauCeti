/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Monoid.WithTop
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.NNReal.Basic

/-!
# Finite bounds on natural multiples in `WithTop`

A positive natural multiple bounded by a finite field element can be divided by the
multiplier; the bound excludes infinity. For nonnegative real inputs, finite multiple bounds
can also be read in `ℝ≥0`.

## Main results

* `WithTop.nsmul_le_coe_iff`: divide a finite bound by a positive natural multiplier.
* `WithTop.nsmul_coe_nnreal_le_iff`: express a multiple bound using nonnegative reals.
-/

public section

open scoped NNReal

namespace WithTop

/-- A positive natural multiple is bounded by a finite value exactly when its argument is
bounded by the quotient. In particular such a bound excludes infinity. -/
theorem nsmul_le_coe_iff {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {n : ℕ} (hn : 0 < n) {x : WithTop F} {b : F} :
    n • x ≤ (b : WithTop F) ↔ x ≤ ((b / n : F) : WithTop F) := by
  induction x using WithTop.recTopCoe with
  | top =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    simp [succ_nsmul]
  | coe x =>
    rw [← coe_nsmul, coe_le_coe, coe_le_coe, nsmul_eq_mul,
      le_div_iff₀ (Nat.cast_pos.2 hn), mul_comm]

/-- A natural multiple of a nonnegative real, cast through `ℝ` to `WithTop ℝ`, satisfies
exactly the corresponding finite product bound. -/
theorem nsmul_coe_nnreal_le_iff (n : ℕ) (a b : ℝ≥0) :
    n • ((a : ℝ) : WithTop ℝ) ≤ (b : ℝ) ↔ (n * a : ℝ≥0) ≤ b := by
  rw [← coe_nsmul, coe_le_coe, nsmul_eq_mul, ← NNReal.coe_natCast, ← NNReal.coe_mul,
    NNReal.coe_le_coe]

end WithTop
