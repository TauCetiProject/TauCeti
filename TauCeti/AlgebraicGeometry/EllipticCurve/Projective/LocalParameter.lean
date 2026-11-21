/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Point

/-!
# The local parameter at the origin of a projective Weierstrass curve

For a point of a Weierstrass curve with homogeneous coordinates `[X : Y : Z]`, the ratio `-X / Y`
does not depend on the choice of coordinates (`WeierstrassCurve.Projective.Point.localParameter`).
It vanishes at the origin `O = [0 : 1 : 0]`, and near `O` it is the standard local parameter
`z = -x / y` of the curve, in which the invariant differential `dx / (2y + a₁x + a₃)` is
`(1 + O(z)) dz`. It is the coordinate of the formal group of the curve. On the points with `Y = 0`
the formula takes the junk value `0`.

Unlike a chart of the complex manifold `E(ℂ)` at `O`, the parameter `-X / Y` is intrinsic to the
Weierstrass equation. Over `ℂ` it is holomorphic near `O`
(`WeierstrassCurve.Projective.Point.contMDiffAt_localParameter_zero`), and its differential at `O`
is a coordinate on the tangent space there. The tangent-space exponential of `E(ℂ)` is canonical,
but expressing its domain as `ℂ` requires such a tangent coordinate; this one normalizes the
exponential `WeierstrassCurve.Projective.exp`.

## Main definitions

* `WeierstrassCurve.Projective.Point.localParameter`: the function `[X : Y : Z] ↦ -X / Y`.

## Main results

* `WeierstrassCurve.Projective.Point.localParameter_mk`: its value on homogeneous coordinates.
* `WeierstrassCurve.Projective.Point.localParameter_addEquivVariableChange_mk` and
  `WeierstrassCurve.Projective.Point.localParameter_addEquivVariableChange_symm_mk`: its value
  after a change of variables.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts in Mathematics
  106, Springer, 2009, §IV.1.
-/

public section

open Matrix

namespace WeierstrassCurve.Projective.Point

variable {F : Type*} [Field F] {W : Projective F}

/-- The ratio `-X / Y` of the homogeneous coordinates `[X : Y : Z]` of a point of a Weierstrass
curve; it does not depend on the choice of coordinates. At the origin `[0 : 1 : 0]` it vanishes,
and near the origin it is the standard local parameter `z = -x / y` of the curve. Points with
`Y = 0` have the junk value `0`. -/
def localParameter (P : W.Point) : F :=
  P.point.lift (fun v ↦ -(v 0 / v 1)) <| by
    rintro _ v ⟨u, rfl⟩
    simp only [Units.smul_def, Pi.smul_apply, smul_eq_mul, mul_div_mul_left _ _ u.ne_zero]

/-- The local parameter of the point with homogeneous coordinates `P` is `-P 0 / P 1`. -/
@[simp]
theorem localParameter_mk {P : Fin 3 → F} (hP : W.NonsingularLift ⟦P⟧) :
    (Point.mk hP).localParameter = -(P 0 / P 1) :=
  (rfl)

/-- The local parameter vanishes at the origin. -/
@[simp]
theorem localParameter_zero : (0 : W.Point).localParameter = 0 := by
  simp [zero_def]

variable {W : WeierstrassCurve F} {C : VariableChange F} {P : Fin 3 → F}

/-- After the change of variables `C = (u, r, s, t)`, the point with homogeneous coordinates
`[X : Y : Z]` has local parameter `-(u²X + rZ) / (u²sX + u³Y + tZ)`. -/
theorem localParameter_addEquivVariableChange_mk (hP : (C • W).toProjective.NonsingularLift ⟦P⟧) :
    (addEquivVariableChange W C (Point.mk hP)).localParameter =
      -(((C.u : F) ^ 2 * P 0 + C.r * P 2) /
        ((C.u : F) ^ 2 * C.s * P 0 + (C.u : F) ^ 3 * P 1 + C.t * P 2)) := by
  simp [addEquivVariableChange_mk, VariableChange.toMatrix_def, dotProduct,
    Fin.sum_univ_three]

/-- The inverse of the change of variables `C` acts on homogeneous coordinates by the matrix of
`C⁻¹ = (u', r', s', t')`, so it gives the point with homogeneous coordinates `[X : Y : Z]` the
local parameter `-(u'²X + r'Z) / (u'²s'X + u'³Y + t'Z)`. -/
theorem localParameter_addEquivVariableChange_symm_mk (hP : W.toProjective.NonsingularLift ⟦P⟧) :
    ((addEquivVariableChange W C).symm (Point.mk hP)).localParameter =
      -(((C⁻¹.u : F) ^ 2 * P 0 + C⁻¹.r * P 2) /
        ((C⁻¹.u : F) ^ 2 * C⁻¹.s * P 0 + (C⁻¹.u : F) ^ 3 * P 1 + C⁻¹.t * P 2)) := by
  simp [addEquivVariableChange_symm_mk, VariableChange.toMatrix_def, dotProduct,
    Fin.sum_univ_three]

end WeierstrassCurve.Projective.Point
