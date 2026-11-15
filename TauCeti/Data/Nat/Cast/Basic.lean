/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Algebra.Group.Units.Basic

/-!
# Casting natural remainders and positive naturals

The remainder identity `n = c * (n / c) + n % c` can be rearranged using subtraction
after casting to a ring, including when `c = 0`.

In a Dedekind-finite `AddMonoidWithOne` with `1 ≠ 0` and trivial additive units (for example, any
nontrivial zero-sum-free semiring, even an idempotent tropical one where `Nat.cast` is not
injective), casting a natural number gives zero if and only if the number is zero.
-/

public section

namespace Nat

/-- A natural remainder cast into a ring is the dividend minus the divisor times the quotient. -/
theorem cast_mod_eq_sub_mul_div {R : Type*} [NonAssocRing R] (n c : ℕ) :
    ((n % c : ℕ) : R) = n - c * (n / c : ℕ) := by
  rw [eq_sub_iff_add_eq, ← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div]

/-- In a Dedekind-finite `AddMonoidWithOne` with `1 ≠ 0` and no nonzero additive units, a natural
number casts to zero if and only if it is zero. No `CharZero` hypothesis is needed. -/
theorem cast_eq_zero_of_subsingleton_addUnits {R : Type*} [AddMonoidWithOne R]
    [IsDedekindFiniteAddMonoid R] [Subsingleton (AddUnits R)] [NeZero (1 : R)] (n : ℕ) :
    (n : R) = 0 ↔ n = 0 := by
  cases n with
  | zero => simp
  | succ k => simp [Nat.cast_succ]

/-- A nonzero natural number casts to a nonzero element of any Dedekind-finite
`AddMonoidWithOne` with `1 ≠ 0` and trivial additive units. -/
theorem cast_ne_zero_of_subsingleton_addUnits {R : Type*} [AddMonoidWithOne R]
    [IsDedekindFiniteAddMonoid R] [Subsingleton (AddUnits R)] [NeZero (1 : R)] {n : ℕ}
    (hn : n ≠ 0) : (n : R) ≠ 0 :=
  mt (cast_eq_zero_of_subsingleton_addUnits n).mp hn

end Nat
