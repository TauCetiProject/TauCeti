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

An additive monoid is zero-sum-free if a sum can vanish only when both summands are zero.
This is Mathlib's condition that the additive units form a subsingleton; in particular,
`add_eq_zero` is available under this hypothesis.
-/

@[expose] public section

namespace TauCeti

/-- The additive monoid `A` has no nonzero additive units, or equivalently
`a + b = 0` implies `a = b = 0`. -/
abbrev ZeroSumFree (A : Type*) [AddMonoid A] := Subsingleton (AddUnits A)

/-- An additive monoid is zero-sum-free if a vanishing sum forces its left summand to vanish. -/
theorem ZeroSumFree.of_add_eq_zero {A : Type*} [AddMonoid A]
    (h : ∀ a b : A, a + b = 0 → a = 0) : ZeroSumFree A :=
  ⟨fun a b => AddUnits.ext ((h _ _ a.val_neg).trans (h _ _ b.val_neg).symm)⟩

/-- In a nontrivial zero-sum-free semiring, a natural number casts to zero only if it is zero. -/
theorem ZeroSumFree.natCast_eq_zero_iff {R : Type*} [NonAssocSemiring R] [Nontrivial R]
    [ZeroSumFree R] (n : ℕ) : (n : R) = 0 ↔ n = 0 := by
  cases n with
  | zero => simp
  | succ n => simp [Nat.cast_succ]

end TauCeti
