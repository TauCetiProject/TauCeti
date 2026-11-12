/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Invertible
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Units and invertible elements in semirings

If `2` is a unit in a semiring, zero is the only element that doubles to zero. The cardinality
of a product of types is invertible in a semiring when both cardinalities are.
-/

public section

/-- If `2` is a unit, only zero doubles to zero. -/
theorem IsUnit.eq_zero_of_add_self_eq_zero {R : Type*} [Semiring R] (h2 : IsUnit (2 : R)) :
    ∀ x : R, x + x = 0 → x = 0 := by
  intro x hx
  exact h2.mul_right_eq_zero.mp (by rwa [two_mul])

namespace TauCeti

/-- The cardinality of a product of types is invertible when both cardinalities are. For groups,
this makes the character table of `G × H` available alongside those of `G` and `H`. -/
noncomputable instance instInvertibleNatCardProd {k G H : Type*} [Semiring k]
    [Invertible (Nat.card G : k)] [Invertible (Nat.card H : k)] :
    Invertible (Nat.card (G × H) : k) :=
  Invertible.copy (invertibleMul (Nat.card G : k) (Nat.card H : k)) _ (by
    rw [Nat.card_prod, Nat.cast_mul])

end TauCeti
