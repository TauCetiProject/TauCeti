/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point

/-!
# The group law on point representatives of a projective Weierstrass curve

For a Weierstrass curve `W'` over a commutative ring, Mathlib's addition
`WeierstrassCurve.Projective.add` of two point representatives `P` and `Q` is the doubling formula
`dblXYZ P` if `P` and `Q` are equivalent, and the addition formula `addXYZ P Q` otherwise. Mathlib
shows that over a field it induces a commutative group law on the nonsingular point classes. This
file states laws of that group for point representatives, where they hold up to equivalence.

Commutativity holds over any commutative ring and for all point representatives: `add P Q` and
`add Q P` are equivalent, because each coordinate of `addXYZ` changes sign when `P` and `Q` are
swapped. Associativity and the inverse law are those of Mathlib's group, for nonsingular point
representatives over a field.

## Main results

* `WeierstrassCurve.Projective.addXYZ_swap`: swapping the two point representatives changes the
  sign of the addition formula, `addXYZ P Q = -addXYZ Q P`.
* `WeierstrassCurve.Projective.add_comm_equiv`: the sums `add P Q` and `add Q P` of two point
  representatives are equivalent.
* `WeierstrassCurve.Projective.add_assoc_equiv`: over a field, the sums `add (add P Q) T` and
  `add P (add Q T)` of three nonsingular point representatives are equivalent.
* `WeierstrassCurve.Projective.neg_add_cancel_equiv`: over a field, the sum `add (neg P) P` of the
  negation of a nonsingular point representative `P` and `P` is equivalent to the point at
  infinity `![0, 1, 0]`.
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

section Field

variable {F : Type*} [Field F] {W : Projective F} {P Q T : Fin 3 → F}

/-- Over a field, the sums `W.add (W.add P Q) T` and `W.add P (W.add Q T)` of three nonsingular
point representatives are equivalent. -/
theorem add_assoc_equiv (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) (hT : W.Nonsingular T) :
    W.add (W.add P Q) T ≈ W.add P (W.add Q T) :=
  Quotient.exact <| by
    simpa only [Point.add_point, addMap_eq] using congrArg Point.point
      (add_assoc (⟨(nonsingularLift_iff P).mpr hP⟩ : W.Point) ⟨(nonsingularLift_iff Q).mpr hQ⟩
        ⟨(nonsingularLift_iff T).mpr hT⟩)

/-- Over a field, the sum `W.add (W.neg P) P` of the negation of a nonsingular point representative
`P` and `P` itself is equivalent to the point at infinity `![0, 1, 0]`. -/
theorem neg_add_cancel_equiv (hP : W.Nonsingular P) : W.add (W.neg P) P ≈ ![0, 1, 0] :=
  Quotient.exact <| by
    simpa only [Point.add_point, Point.neg_point, Point.zero_point, negMap_eq, addMap_eq] using
      congrArg Point.point (neg_add_cancel (⟨(nonsingularLift_iff P).mpr hP⟩ : W.Point))

end Field

end WeierstrassCurve.Projective
