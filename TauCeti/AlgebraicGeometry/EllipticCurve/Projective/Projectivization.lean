/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Nonsingular

/-!
# Nonsingular Weierstrass points in projective space

The native projective point classes allow the zero vector, whereas projective space consists
of lines represented by nonzero vectors. Nonsingularity excludes the zero vector, so the
native nonsingular points embed in projective space. The image consists exactly of the lines
with nonsingular representatives. This comparison lets the native point type inherit the
analytic topology of projective space.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, III.1.
-/

public section

open scoped LinearAlgebra.Projectivization

namespace WeierstrassCurve.Projective.Point

variable {F : Type*} [Field F] {W : Projective F}

/-- A native nonsingular projective point, viewed as a line in the coordinate vector space. -/
noncomputable def toProjectivization (P : W.Point) : ℙ F (Fin 3 → F) :=
  Projectivization.mk F P.point.out (ne_zero_of_nonsingular (by
    simpa only [← nonsingularLift_iff, Quotient.out_eq] using P.nonsingular))

/-- The comparison with projective space sends a nonsingular representative to its line. -/
@[simp]
theorem toProjectivization_mk {P : Fin 3 → F} (hP : W.NonsingularLift ⟦P⟧) :
    (Point.mk hP).toProjectivization =
      Projectivization.mk F P (ne_zero_of_nonsingular ((nonsingularLift_iff P).mp hP)) := by
  rw [toProjectivization, Projectivization.mk_eq_mk_iff]
  exact Quotient.mk_out P

/-- Distinct native nonsingular points define distinct lines. -/
theorem toProjectivization_injective :
    Function.Injective (toProjectivization : W.Point → ℙ F (Fin 3 → F)) := by
  intro P Q h
  apply Point.ext
  exact Quotient.out_equiv_out.mp
    ((Projectivization.mk_eq_mk_iff F _ _ _ _).mp h)

/-- A line represented by `P` comes from a native nonsingular point exactly when `P` is
nonsingular. -/
@[simp]
theorem exists_toProjectivization_eq_mk_iff (P : Fin 3 → F) (hP : P ≠ 0) :
    (∃ Q : W.Point, Q.toProjectivization = Projectivization.mk F P hP) ↔
      W.Nonsingular P := by
  constructor
  · rintro ⟨Q, hQ⟩
    have he : Q.point = ⟦P⟧ := by
      rw [← Quotient.out_eq Q.point]
      exact Quotient.sound ((Projectivization.mk_eq_mk_iff F _ _ _ _).mp hQ)
    simpa only [he, nonsingularLift_iff] using Q.nonsingular
  · intro h
    exact ⟨Point.mk ((nonsingularLift_iff P).mpr h), toProjectivization_mk _⟩

/-- Membership in the image can be checked on the chosen nonzero representative of a line. -/
theorem mem_range_toProjectivization_iff (P : ℙ F (Fin 3 → F)) :
    P ∈ Set.range (toProjectivization : W.Point → _) ↔ W.Nonsingular P.rep := by
  simpa only [Set.mem_range, Projectivization.mk_rep] using
    exists_toProjectivization_eq_mk_iff (W := W) P.rep P.rep_ne_zero

/-- The identity point is the line through `[0, 1, 0]`. -/
@[simp]
theorem toProjectivization_zero :
    (0 : W.Point).toProjectivization =
      Projectivization.mk F ![0, 1, 0] (ne_zero_of_nonsingular (nonsingular_zero (W' := W))) :=
  toProjectivization_mk _

/-- An affine point has projective coordinates `[x, y, 1]`. -/
@[simp]
theorem toProjectivization_fromAffine_some {x y : F} (h : W.toAffine.Nonsingular x y) :
    (Point.fromAffine (.some x y h)).toProjectivization =
      Projectivization.mk F ![x, y, 1]
        (ne_zero_of_nonsingular ((nonsingular_some x y).mpr h)) :=
  toProjectivization_mk _

end WeierstrassCurve.Projective.Point
