/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Bivector.Basic

import Mathlib.Tactic.NoncommRing

/-!
# The square of a bivector

The Clifford bivector `β(a, b) = ½ ⁅ι a, ι b⁆` of any two vectors squares to the scalar
`(½ polar(a, b))² - Q a * Q b`. In particular, the bivector of a hyperbolic pair, with
`Q a = Q b = 0` and `polar(a, b) = 2`, is an involution. This generalizes
`CliffordAlgebra.bivector_mul_self_of_isOrtho`, the square of the bivector of an orthogonal pair.

## Main results

* `CliffordAlgebra.bivector_mul_self`: the square of a bivector.
-/

public section

namespace CliffordAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Invertible (2 : R)]
  {Q : QuadraticForm R M}

/-- **The square of a bivector** is the scalar `(½ polar(a, b))² - Q a * Q b`. In particular the
bivector of a hyperbolic pair, with `Q a = Q b = 0` and `polar(a, b) = 2`, is an involution. -/
theorem bivector_mul_self (a b : M) :
    bivector Q a b * bivector Q a b =
      algebraMap R (CliffordAlgebra Q) ((⅟(2 : R) * QuadraticMap.polar Q a b) ^ 2 - Q a * Q b) := by
  set s := algebraMap R (CliffordAlgebra Q) (⅟(2 : R) * QuadraticMap.polar Q a b) with hs
  have hscomm : s * (ι Q a * ι Q b) = ι Q a * ι Q b * s := Algebra.commutes _ _
  have hpolar : algebraMap R (CliffordAlgebra Q) (QuadraticMap.polar Q a b) = s + s := by
    rw [hs, ← map_add, ← add_mul, invOf_two_add_invOf_two, one_mul]
  have hbiv : bivector Q a b = ι Q a * ι Q b - s := by
    rw [ι_mul_ι_eq_bivector_add, hs, map_mul, ← Algebra.smul_def, add_sub_cancel_right]
  have habab : ι Q a * ι Q b * (ι Q a * ι Q b) =
      (s + s) * (ι Q a * ι Q b) - algebraMap R (CliffordAlgebra Q) (Q a * Q b) := by
    rw [← mul_assoc, ι_mul_ι_mul_ι]
    simp [sub_mul, mul_assoc, Algebra.smul_def, hpolar]
  rw [map_sub, map_pow, sq, hbiv]
  noncomm_ring [habab, hscomm]

end CliffordAlgebra
