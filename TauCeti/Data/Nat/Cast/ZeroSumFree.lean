/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Data.Nat.Cast.Basic

/-!
# Natural-number casts in zero-sum-free additive monoids

For commutative additive monoids, Mathlib expresses zero-sum-freeness as
`Subsingleton (AddUnits R)`, which makes `add_eq_zero` available. This file records that no
positive natural number then casts to zero, when one is nonzero. For semirings, this shows that
`Nat.castRingHom` reflects zero, as needed for evaluating natural-coefficient polynomials.
-/

public section

namespace TauCeti

/-- In a zero-sum-free additive monoid with nonzero one, a natural number casts to zero only if
it is zero. -/
@[simp]
theorem natCast_eq_zero_iff {R : Type*} [AddMonoidWithOne R] [IsDedekindFiniteAddMonoid R]
    [NeZero (1 : R)] [Subsingleton (AddUnits R)] {n : ℕ} : (n : R) = 0 ↔ n = 0 := by
  cases n with
  | zero => simp
  | succ n => simp [Nat.cast_succ, NeZero.ne (1 : R)]

end TauCeti
