/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.VariableChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.VariableChange

/-!
# The group law on point representatives of a projective Weierstrass curve

For a Weierstrass curve `W'` over a commutative ring, Mathlib's addition
`WeierstrassCurve.Projective.add` of two point representatives `P` and `Q` is the doubling formula
`dblXYZ P` if `P` and `Q` are equivalent, and the addition formula `addXYZ P Q` otherwise. Mathlib
shows that over a field it induces a commutative group law on the nonsingular point classes. This
file states laws of that group for point representatives, where they hold up to equivalence.

Commutativity holds over any commutative ring and for all point representatives: `add P Q` and
`add Q P` are equivalent, because each coordinate of `addXYZ` changes sign when `P` and `Q` are
swapped. Associativity is the one of Mathlib's group, for nonsingular point representatives over a
field. Over a field, the group law also commutes with a change of variables `C`: the homogeneous
coordinate map `P ↦ C.toMatrix *ᵥ P` from `C • W` to `W` carries `add P Q`, for nonsingular point
representatives `P` and `Q` of `C • W`, to a representative of
`add (C.toMatrix *ᵥ P) (C.toMatrix *ᵥ Q)`. This is read off the affine point groups, where the
change of variables is the group isomorphism `WeierstrassCurve.Affine.Point.addEquivVariableChange`.

## Main results

* `WeierstrassCurve.Projective.addXYZ_swap`: swapping the two point representatives changes the
  sign of the addition formula, `addXYZ P Q = -addXYZ Q P`.
* `WeierstrassCurve.Projective.add_comm_equiv`: the sums `add P Q` and `add Q P` of two point
  representatives are equivalent.
* `WeierstrassCurve.Projective.add_assoc_equiv`: over a field, the sums `add (add P Q) T` and
  `add P (add Q T)` of three nonsingular point representatives are equivalent.
* `WeierstrassCurve.Projective.Point.toAffine_eq_toAffine_iff`: over a field, two nonsingular point
  representatives have the same affine point exactly when they are equivalent.
* `WeierstrassCurve.Projective.Point.toAffine_toMatrix_mulVec`: over a field, the affine point of
  `C.toMatrix *ᵥ P` is the image of the affine point of `P` under the change of variables `C`.
* `WeierstrassCurve.Projective.toMatrix_mulVec_add_equiv`: over a field, for nonsingular point
  representatives `P` and `Q` of `C • W`, the image of `add P Q` under `C.toMatrix` is equivalent
  to the sum `add (C.toMatrix *ᵥ P) (C.toMatrix *ᵥ Q)` on `W`.
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

/-- Over a field, two nonsingular point representatives have the same affine point exactly when
they are equivalent. -/
theorem Point.toAffine_eq_toAffine_iff (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) :
    Point.toAffine W P = Point.toAffine W Q ↔ P ≈ Q := by
  classical
  refine ⟨fun h ↦ Quotient.exact (congrArg Point.point ((Point.toAffineAddEquiv W).injective
    (a₁ := ⟨(nonsingularLift_iff P).mpr hP⟩) (a₂ := ⟨(nonsingularLift_iff Q).mpr hQ⟩) ?_)),
    Point.toAffine_of_equiv⟩
  rwa [Point.toAffineAddEquiv_apply, Point.toAffineAddEquiv_apply, Point.toAffineLift_eq,
    Point.toAffineLift_eq]

end Field

section VariableChange

variable {F : Type*} [Field F] {W : WeierstrassCurve F} (C : VariableChange F) {P Q : Fin 3 → F}

open Matrix

/-- Over a field, the affine point of the image `C.toMatrix *ᵥ P` on `W` of a point representative
`P` of `C • W` is the image of the affine point of `P` under the change of variables
`(x, y) ↦ (u²x + r, u³y + u²sx + t)`. Both sides are `0` when `P` is singular. -/
@[simp]
theorem Point.toAffine_toMatrix_mulVec (P : Fin 3 → F) :
    Point.toAffine W.toProjective (C.toMatrix *ᵥ P) =
      Affine.Point.equivVariableChange W C (Point.toAffine (C • W).toProjective P) := by
  have hz := VariableChange.toMatrix_mulVec_two C P
  by_cases hP : (C • W).toProjective.Nonsingular P
  · by_cases hPz : P 2 = 0
    · rw [Point.toAffine_of_Z_eq_zero hPz, Point.toAffine_of_Z_eq_zero (hz.trans hPz),
        Affine.Point.equivVariableChange_zero]
    · rw [Point.toAffine_of_Z_ne_zero hP hPz,
        Point.toAffine_of_Z_ne_zero ((nonsingular_variableChange W C P).mp hP) (hz ▸ hPz),
        Affine.Point.equivVariableChange_some, Affine.Point.some.injEq, hz]
      exact ⟨VariableChange.toMatrix_mulVec_zero_div C hPz,
        VariableChange.toMatrix_mulVec_one_div C hPz⟩
  · rw [Point.toAffine_of_singular hP,
      Point.toAffine_of_singular (mt (nonsingular_variableChange W C P).mpr hP),
      Affine.Point.equivVariableChange_zero]

/-- **The group law commutes with a change of variables.** Over a field, let `P` and `Q` be
nonsingular point representatives of `C • W`. The image under `C.toMatrix` of their sum
`add P Q` on `C • W` is equivalent to the sum `add (C.toMatrix *ᵥ P) (C.toMatrix *ᵥ Q)` of their
images on `W`. -/
theorem toMatrix_mulVec_add_equiv (hP : (C • W).toProjective.Nonsingular P)
    (hQ : (C • W).toProjective.Nonsingular Q) :
    C.toMatrix *ᵥ (C • W).toProjective.add P Q ≈
      W.toProjective.add (C.toMatrix *ᵥ P) (C.toMatrix *ᵥ Q) := by
  classical
  have hP' := (nonsingular_variableChange W C P).mp hP
  have hQ' := (nonsingular_variableChange W C Q).mp hQ
  -- both sides are nonsingular, so it suffices that they have the same affine point
  rw [← Point.toAffine_eq_toAffine_iff
    ((nonsingular_variableChange W C _).mp (nonsingular_add hP hQ)) (nonsingular_add hP' hQ'),
    Point.toAffine_add hP' hQ', Point.toAffine_toMatrix_mulVec, Point.toAffine_toMatrix_mulVec,
    Point.toAffine_toMatrix_mulVec, Point.toAffine_add hP hQ,
    ← Affine.Point.coe_addEquivVariableChange, map_add]

end VariableChange

end WeierstrassCurve.Projective
