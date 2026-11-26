/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.Algebra.Order.Ring.Cast

/-!
# The integer cast as an order-preserving additive map

In an ordered additive group with one and `0 ≤ 1`, the integer cast is monotone
(`Int.cast_mono`) and additive, so it bundles as an order-preserving additive monoid
homomorphism `Int.castOrderAddMonoidHom R : ℤ →+o R`. This lets APIs that change coefficients
along a map `K →+o L` read integer data in `R`, for example in `ℚ` or `ℝ`.
-/

public section

namespace Int

variable (R : Type*) [AddCommGroupWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]

/-- The integer cast into an ordered additive group with one and `0 ≤ 1`, as an order-preserving
additive monoid homomorphism. -/
def castOrderAddMonoidHom : ℤ →+o R :=
  .mk' Int.cast cast_mono cast_add

@[simp]
theorem coe_castOrderAddMonoidHom : ⇑(castOrderAddMonoidHom R) = Int.cast :=
  (rfl)

end Int
