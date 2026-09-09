/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-!
# The order of vanishing of the constant function one

For a locally Noetherian integral scheme `X`, Mathlib defines the order of vanishing
`Scheme.ord f x : ℤ` of a rational function at a point, together with `ord_zero`, `ord_mul` and
`ord_of_isUnit`.

## Main declarations

* `AlgebraicGeometry.Scheme.ord_one`: the constant function `1` has order zero at every
  point. This is the companion of Mathlib's `ord_zero`: at a codimension-one point the order is
  the valuation of a unit of the local ring, and at every other point the order is zero by
  definition.
-/

public section

open AlgebraicGeometry

namespace TauCeti

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- The rational function `1` has order zero at every point. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.ord_one (x : X) : X.ord (1 : X.functionField) x = 0 := by
  rcases eq_or_ne (Order.coheight x) 1 with hx | hx
  · rw [X.ord_eq_iff hx one_ne_zero]
    simp
  · simp [hx]

end TauCeti
