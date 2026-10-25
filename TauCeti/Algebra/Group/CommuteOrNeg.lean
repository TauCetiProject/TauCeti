/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Commute.Basic
public import Mathlib.Algebra.Ring.Basic

/-!
# Commutation up to a central sign

The relation `CommuteOrNeg a x` records that `a` commutes with `x` or that it
anticommutes with `x`.  Its closure laws are useful when a group is generated
by elements that pairwise commute or anticommute.
-/

public section

namespace TauCeti

/-- Two elements commute or anticommute. -/
abbrev CommuteOrNeg {M : Type*} [Semigroup M] [HasDistribNeg M] (a x : M) : Prop :=
  Commute a x ∨ SemiconjBy a x (-x)

namespace CommuteOrNeg

/-- Commutation up to a sign is symmetric. -/
theorem symm {M : Type*} [Semigroup M] [HasDistribNeg M] {a x : M} :
    CommuteOrNeg a x → CommuteOrNeg x a := by
  intro h
  rcases h with h | h
  · exact Or.inl h.symm
  · right
    rw [SemiconjBy]
    simpa only [neg_mul, mul_neg, neg_neg] using (congrArg Neg.neg h).symm

/-- Commutation up to a sign is preserved by multiplication on the right. -/
theorem mul_right {M : Type*} [Semigroup M] [HasDistribNeg M] {a x y : M}
    (hx : CommuteOrNeg a x) (hy : CommuteOrNeg a y) :
    CommuteOrNeg a (x * y) := by
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact Or.inl (hx.mul_right hy)
  · right
    simpa only [SemiconjBy, mul_assoc, mul_neg] using hx.semiconjBy.mul_right hy
  · right
    simpa only [SemiconjBy, mul_assoc, neg_mul] using hx.mul_right (hy.semiconjBy)
  · left
    rw [Commute]
    simpa only [SemiconjBy, mul_assoc, neg_mul, mul_neg, neg_neg] using hx.mul_right hy

/-- Commutation up to a sign is preserved by inversion on the right. -/
theorem inv_right {M : Type*} [Group M] [HasDistribNeg M] {a x : M}
    (hx : CommuteOrNeg a x) : CommuteOrNeg a x⁻¹ := by
  rcases hx with hx | hx
  · exact Or.inl hx.inv_right
  · right
    simpa only [inv_neg] using hx.inv_right

/-- The identity commutes or anticommutes with every element. -/
theorem one_left {M : Type*} [Monoid M] [HasDistribNeg M] (x : M) : CommuteOrNeg 1 x :=
  Or.inl (Commute.one_left x)

/-- Every element commutes or anticommutes with the identity. -/
theorem one_right {M : Type*} [Monoid M] [HasDistribNeg M] (x : M) : CommuteOrNeg x 1 :=
  Or.inl (Commute.one_right x)

end CommuteOrNeg

end TauCeti
