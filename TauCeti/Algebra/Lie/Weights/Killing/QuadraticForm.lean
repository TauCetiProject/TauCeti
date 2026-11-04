/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Weights.RootSystem
public import TauCeti.Algebra.Lie.SkewAdjoint

/-!
# The Killing quadratic form on root spaces

Root spaces pair to zero under the Killing form unless their weights cancel. Read through the
Killing quadratic form `x ↦ κ(x, x)`, whose polar form is `2 • κ`, this says that the root spaces of
weights that do not cancel are orthogonal, and that the root space of a nonzero weight is isotropic
when `2 ≠ 0` in the base field.

## Main results

* `TauCeti.LieAlgebra.polar_killingQuadraticForm_eq_zero_of_mem_rootSpace`: root spaces of weights
  that do not cancel are orthogonal for the Killing quadratic form.
* `TauCeti.LieAlgebra.killingQuadraticForm_eq_zero_of_mem_rootSpace`: when `2 ≠ 0` in the base
  field, the root space of a nonzero weight is isotropic for the Killing quadratic form.
-/

public section

namespace TauCeti.LieAlgebra

open _root_.LieAlgebra LieModule

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- Root spaces of weights that do not cancel are orthogonal for the Killing quadratic form. -/
theorem polar_killingQuadraticForm_eq_zero_of_mem_rootSpace {α β : H → K} {x y : L}
    (hx : x ∈ rootSpace H α) (hy : y ∈ rootSpace H β) (h : α + β ≠ 0) :
    QuadraticMap.polar (killingQuadraticForm K L) x y = 0 := by
  rw [polar_killingQuadraticForm,
    killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero K L H hx hy h, mul_zero]

/-- The root space of a nonzero weight is isotropic for the Killing quadratic form: when `2 ≠ 0`
in `K`, a nonzero weight does not cancel itself. -/
theorem killingQuadraticForm_eq_zero_of_mem_rootSpace [NeZero (2 : K)] {χ : H → K}
    (hχ : χ ≠ 0) {x : L} (hx : x ∈ rootSpace H χ) : killingQuadraticForm K L x = 0 := by
  rw [killingQuadraticForm_apply]
  exact killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero K L H hx hx fun hc ↦
    hχ <| funext fun u ↦ by simpa [← two_mul, two_ne_zero] using congrFun hc u

end TauCeti.LieAlgebra
