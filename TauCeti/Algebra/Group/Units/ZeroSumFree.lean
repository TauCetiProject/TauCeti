/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Data.Nat.Cast.Basic

/-!
# Zero-sum-free addition

A nontrivial semiring whose additive units form a subsingleton has no nonzero natural-number
cast that vanishes.
-/

public section

namespace TauCeti

/-- In a nontrivial semiring with subsingleton additive units, a natural number casts to zero
only if it is zero. -/
@[simp]
theorem natCast_eq_zero_iff {R : Type*} [NonAssocSemiring R] [Nontrivial R]
    [Subsingleton (AddUnits R)] {n : ℕ} : (n : R) = 0 ↔ n = 0 := by
  cases n with
  | zero => simp
  | succ n => simp [Nat.cast_succ]

end TauCeti
