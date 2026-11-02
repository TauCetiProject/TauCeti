/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Bivector.Basic

import Mathlib.Tactic.NoncommRing

/-!
# The bivector of an isotropic pair

The Clifford bivector `β(a, b) = ½ ⁅ι a, ι b⁆` of two isotropic vectors squares to the scalar
`(½ polar(a, b))²`. In particular, the bivector of a hyperbolic pair, with `polar(a, b) = 2`, is an
involution. This complements `CliffordAlgebra.bivector_mul_self_of_isOrtho`, the square of the
bivector of an orthogonal pair.

## Main results

* `CliffordAlgebra.bivector_mul_self_of_isotropic`: the square of the bivector of an isotropic pair.
-/

public section

namespace CliffordAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Invertible (2 : R)]
  {Q : QuadraticForm R M}

/-- **The square of the bivector of an isotropic pair** is the scalar `(½ polar(a, b))²`. In
particular the bivector of a hyperbolic pair, with `polar(a, b) = 2`, is an involution. -/
theorem bivector_mul_self_of_isotropic {a b : M} (ha : Q a = 0) (hb : Q b = 0) :
    bivector Q a b * bivector Q a b =
      algebraMap R (CliffordAlgebra Q) ((⅟(2 : R) * QuadraticMap.polar Q a b) ^ 2) := by
  have haa : ι Q a * ι Q a = 0 := by rw [ι_sq_scalar, ha, map_zero]
  have hbb : ι Q b * ι Q b = 0 := by rw [ι_sq_scalar, hb, map_zero]
  set s := algebraMap R (CliffordAlgebra Q) (⅟(2 : R) * QuadraticMap.polar Q a b) with hs
  have hscomm (x : CliffordAlgebra Q) : s * x = x * s := Algebra.commutes _ x
  have hpolar : algebraMap R (CliffordAlgebra Q) (QuadraticMap.polar Q a b) = s + s := by
    rw [hs, ← map_add, ← add_mul, invOf_two_add_invOf_two, one_mul]
  have hba : ι Q b * ι Q a = s + s - ι Q a * ι Q b := by
    rw [← hpolar]
    exact eq_sub_of_add_eq' (ι_mul_ι_add_swap a b)
  have hbiv : bivector Q a b = ι Q a * ι Q b - s := by
    rw [ι_mul_ι_eq_bivector_add, hs, map_mul, ← Algebra.smul_def, add_sub_cancel_right]
  have habab : ι Q a * ι Q b * (ι Q a * ι Q b) = (s + s) * (ι Q a * ι Q b) := by
    calc ι Q a * ι Q b * (ι Q a * ι Q b) = ι Q a * (ι Q b * ι Q a) * ι Q b := by noncomm_ring
      _ = ι Q a * (s + s) * ι Q b - ι Q a * ι Q a * (ι Q b * ι Q b) := by
        rw [hba]; noncomm_ring
      _ = (s + s) * (ι Q a * ι Q b) := by
        rw [haa, zero_mul, sub_zero, mul_add, ← hscomm, ← add_mul, mul_assoc]
  rw [map_pow, sq, hbiv, sub_mul, mul_sub, mul_sub, habab, ← hscomm (ι Q a * ι Q b)]
  noncomm_ring

end CliffordAlgebra
