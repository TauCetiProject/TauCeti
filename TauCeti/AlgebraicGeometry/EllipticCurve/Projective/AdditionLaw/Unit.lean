/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.AdditionLaw.Basic

/-!
# The Bosma–Lenstra addition laws at infinity

This file evaluates the two Bosma–Lenstra addition laws when their second argument is the point at
infinity `[0 : 1 : 0]`. The law attached to `Z = 0` returns `-P₂ • P`, while the law attached to
`Y = 0` returns `P₁ • P`. Consequently the first law represents `P` wherever `P₂` is a unit and the
second does so wherever `P₁` is a unit. These two loci cover a Weierstrass cubic and give the
scheme-theoretic right unit law for its addition morphism.

## Main results

* `WeierstrassCurve.Projective.addXYZ_zero_right`: the law attached to `Z = 0` at `(P, 0)`.
* `WeierstrassCurve.Projective.dblAddXYZ_zero_right`: the law attached to `Y = 0` at `(P, 0)`.

## References

* W. Bosma and H. W. Lenstra, Jr., *Complete systems of two addition laws for elliptic curves*,
  J. Number Theory 53 (1995), 229–240.
-/

public section

universe u

namespace WeierstrassCurve.Projective

variable {R : Type u} [CommRing R] (W : Projective R)

/-- The Bosma–Lenstra addition law attached to `Z = 0`, evaluated at `P` and the point at infinity
`[0 : 1 : 0]`, is the scalar multiple `-P₂ • P`. -/
@[simp]
theorem addXYZ_zero_right (P : Fin 3 → R) :
    W.addXYZ P ![0, 1, 0] = -P 2 • P := by
  funext i
  fin_cases i <;> simp [addXYZ, addX, addY, negAddY, addZ, negY] <;> ring

/-- The Bosma–Lenstra addition law attached to `Y = 0`, evaluated at `P` and the point at infinity
`[0 : 1 : 0]`, is the scalar multiple `P₁ • P`. -/
@[simp]
theorem dblAddXYZ_zero_right (P : Fin 3 → R) :
    W.dblAddXYZ P ![0, 1, 0] = P 1 • P := by
  funext i
  fin_cases i <;> simp [dblAddX, dblAddY, dblAddZ] <;> ring

end WeierstrassCurve.Projective
