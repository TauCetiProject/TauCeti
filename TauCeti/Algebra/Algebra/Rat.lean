/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Rat

/-!
# Rational algebras from ring homomorphisms

The image of a ring homomorphism `ℚ →+* B` into a semiring is central, because every nonnegative
rational number is a quotient of natural numbers, whose casts commute with everything, and the
additive inverse of a central element is central. Hence such a homomorphism makes `B` a
`ℚ`-algebra, even when `B` is not commutative. This is used, for instance, to view the target of
a ring homomorphism out of a `ℚ`-algebra as a `ℚ`-algebra.

## Main declarations

* `RingHom.commute_apply_rat`: the image of a rational number commutes with every element.
* `RingHom.toRatAlgebra`: the `ℚ`-algebra structure induced by a ring homomorphism `ℚ →+* B`.
* `RingHom.algebraMap_toRatAlgebra`: its algebra map is the given homomorphism.
-/

public section

namespace RingHom

variable {B : Type*} [Semiring B]

/-- The image of a rational number under a ring homomorphism is central. -/
theorem commute_apply_rat (g : ℚ →+* B) (q : ℚ) (y : B) : Commute (g q) y := by
  -- A nonnegative rational is a quotient of natural numbers, whose images are central.
  have key (r : ℚ) (hr : 0 ≤ r) : Commute (g r) y := by
    lift r to ℚ≥0 using hr
    have hd : IsUnit (g (r.den : ℚ)) := (IsUnit.mk0 _ (mod_cast r.den_ne_zero)).map g
    have hc : Commute (g (r.den : ℚ)) y := by simpa using Nat.cast_commute r.den y
    have h : g r * g r.den = (r.num : B) := by
      rw [← map_mul, ← map_natCast g r.num]
      exact congrArg g (mod_cast r.mul_den_eq_num)
    refine hd.mul_left_inj.mp ?_
    rw [mul_assoc, ← hc.eq, ← mul_assoc, h, mul_assoc, h]
    exact Nat.cast_commute _ _
  obtain hq | hq := le_total 0 q
  · exact key q hq
  -- Otherwise `g q` is the additive inverse of the central element `g (-q)`.
  · have h0 : g q + g (-q) = 0 := by simp [← map_add]
    calc g q * y = g q * y + y * (g (-q) + g q) := by simp [add_comm, h0]
      _ = (g q + g (-q)) * y + y * g q := by
        rw [mul_add, add_mul, (key (-q) (neg_nonneg.mpr hq)).eq, add_assoc]
      _ = y * g q := by simp [h0]

/-- A ring homomorphism `ℚ →+* B` makes `B` a `ℚ`-algebra, since its image is central.
See note [reducible non-instances]. -/
abbrev toRatAlgebra (g : ℚ →+* B) : Algebra ℚ B :=
  g.toAlgebra' fun q y ↦ (g.commute_apply_rat q y).eq

/-- The algebra map of `RingHom.toRatAlgebra g` is `g`. -/
theorem algebraMap_toRatAlgebra (g : ℚ →+* B) :
    @algebraMap ℚ B _ _ g.toRatAlgebra = g :=
  rfl

end RingHom
