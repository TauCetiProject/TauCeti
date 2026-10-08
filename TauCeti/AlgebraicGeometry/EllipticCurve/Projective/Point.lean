/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point

/-!
# Commutativity of the addition of point representatives on a projective Weierstrass curve

For a Weierstrass curve `W'` over a commutative ring, Mathlib's addition
`WeierstrassCurve.Projective.add` of two point representatives `P` and `Q` is the doubling formula
`dblXYZ P` if `P` and `Q` are equivalent, and the addition formula `addXYZ P Q` otherwise. Mathlib
shows that over a field it induces a commutative group law on the nonsingular point classes. This
file shows that over any commutative ring, and for all point representatives, `add P Q` and
`add Q P` are equivalent: each coordinate of `addXYZ` changes sign when `P` and `Q` are swapped.

## Main results

* `WeierstrassCurve.Projective.addXYZ_swap`: swapping the two point representatives changes the
  sign of the addition formula, `addXYZ P Q = -addXYZ Q P`.
* `WeierstrassCurve.Projective.add_comm_equiv`: the sums `add P Q` and `add Q P` of two point
  representatives are equivalent.
-/

public section

namespace WeierstrassCurve.Projective

variable {R : Type*} [CommRing R] {W' : Projective R}

/-- Swapping the two point representatives changes the sign of the `X`-coordinate `addX` of the
addition formula. -/
theorem addX_swap (P Q : Fin 3 → R) : W'.addX P Q = -W'.addX Q P := by
  rw [addX, addX]
  ring1

/-- Swapping the two point representatives changes the sign of the `Z`-coordinate `addZ` of the
addition formula. -/
theorem addZ_swap (P Q : Fin 3 → R) : W'.addZ P Q = -W'.addZ Q P := by
  rw [addZ, addZ]
  ring1

/-- Swapping the two point representatives changes the sign of the negated `Y`-coordinate
`negAddY` of the addition formula. -/
theorem negAddY_swap (P Q : Fin 3 → R) : W'.negAddY P Q = -W'.negAddY Q P := by
  rw [negAddY, negAddY]
  ring1

/-- Swapping the two point representatives changes the sign of the `Y`-coordinate `addY` of the
addition formula. -/
theorem addY_swap (P Q : Fin 3 → R) : W'.addY P Q = -W'.addY Q P := by
  rw [addY, addY, negY_eq, negY_eq, addX_swap P Q, negAddY_swap P Q, addZ_swap P Q]
  ring1

/-- Swapping the two point representatives changes the sign of the addition formula `addXYZ`. -/
theorem addXYZ_swap (P Q : Fin 3 → R) : W'.addXYZ P Q = -W'.addXYZ Q P := by
  rw [addXYZ, addXYZ, addX_swap P Q, addY_swap P Q, addZ_swap P Q, Matrix.neg_cons,
    Matrix.neg_cons, Matrix.neg_cons, Matrix.neg_empty]

/-- The sums `W'.add P Q` and `W'.add Q P` of two point representatives on a Weierstrass curve
over a commutative ring are equivalent. -/
theorem add_comm_equiv (P Q : Fin 3 → R) : W'.add P Q ≈ W'.add Q P := by
  by_cases h : P ≈ Q
  · -- both sums are equivalent to `add Q Q`
    exact Setoid.trans (add_equiv h (Setoid.refl Q)) (Setoid.symm (add_equiv (Setoid.refl Q) h))
  · -- both sums are the addition formula, which changes sign when `P` and `Q` are swapped
    rw [add_of_not_equiv h, add_of_not_equiv (mt Setoid.symm h), addXYZ_swap P Q,
      ← neg_one_smul R (W'.addXYZ Q P)]
    exact smul_equiv _ isUnit_one.neg

end WeierstrassCurve.Projective
