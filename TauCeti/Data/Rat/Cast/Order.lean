/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.Data.Rat.Cast.Order

/-!
# The rational cast as an order-preserving additive map

In a linearly ordered field, the rational cast is monotone (`Rat.cast_mono`) and additive, so
it bundles as an order-preserving additive monoid homomorphism
`Rat.castOrderAddMonoidHom K : ℚ →+o K`. This lets APIs that change coefficients along a map
`K →+o L` move rational data to `K`, for example from `ℚ` to `ℝ`.
-/

public section

namespace Rat

variable (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The rational cast into a linearly ordered field, as an order-preserving additive monoid
homomorphism. -/
def castOrderAddMonoidHom : ℚ →+o K :=
  .mk' Rat.cast cast_mono cast_add

@[simp]
theorem coe_castOrderAddMonoidHom : ⇑(castOrderAddMonoidHom K) = Rat.cast :=
  (rfl)

end Rat
