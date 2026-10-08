/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
public import TauCeti.LinearAlgebra.Unimodular
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Nonsingular

/-!
# Unimodular solutions of the projective Weierstrass equation

For a Weierstrass curve `W` over a commutative ring `R`, a projective point class `[X : Y : Z]` is
*unimodular* if it is represented by a solution of the projective Weierstrass equation whose
coordinates are unimodular, that is, generate the unit ideal of `R`. Over a local ring these are
exactly the solutions one of whose coordinates is a unit, and they describe the `R`-points of the
projective Weierstrass model.

Mathlib's `WeierstrassCurve.Projective.NonsingularLift` is the corresponding condition with
nonsingularity in place of unimodularity, and it is only meaningful over a field. Over a field and
for an elliptic curve the two conditions agree, which identifies the unimodular classes with
Mathlib's nonsingular projective points `WeierstrassCurve.Projective.Point`.

## Main definitions

* `WeierstrassCurve.Projective.UnimodularLift`: the proposition that a projective point class is
  represented by a solution of the projective Weierstrass equation with unimodular coordinates.
* `WeierstrassCurve.Projective.Point.equivUnimodularLift`: on an elliptic curve over a field, the
  nonsingular projective points are the unimodular point classes.

## Main results

* `WeierstrassCurve.Projective.unimodularLift_iff`: the condition on a representative.
* `WeierstrassCurve.Projective.unimodularLift_iff_nonsingularLift`: on an elliptic curve over a
  field, a point class is unimodular if and only if it is nonsingular.
-/

public section

namespace WeierstrassCurve.Projective

section CommRing

variable {R : Type*} [CommRing R] (W' : Projective R)

/-- The proposition that a projective point class on a Weierstrass curve `W` is represented by a
solution of the projective Weierstrass equation with unimodular coordinates, that is, coordinates
generating the unit ideal.

If `P` is a projective point representative on `W`, then `W.UnimodularLift ⟦P⟧` is equivalent to
`W.Equation P ∧ Module.IsUnimodular R P` (`unimodularLift_iff`). Over a local ring these classes
correspond to the `R`-points of the projective Weierstrass model. -/
def UnimodularLift (P : PointClass R) : Prop :=
  P.lift (fun Q ↦ W'.Equation Q ∧ Module.IsUnimodular R Q) fun _ Q h ↦ by
    obtain ⟨u, rfl⟩ := h
    refine propext <| and_congr (W'.equation_of_equiv ⟨u, rfl⟩)
      ⟨fun hu ↦ ?_, TauCeti.Module.isUnimodular_units_smul u⟩
    simpa using TauCeti.Module.isUnimodular_units_smul u⁻¹ hu

variable {W'}

/-- The class of a representative `P` is unimodular if and only if `P` solves the projective
Weierstrass equation and its coordinates are unimodular. -/
theorem unimodularLift_iff (P : Fin 3 → R) :
    W'.UnimodularLift ⟦P⟧ ↔ W'.Equation P ∧ Module.IsUnimodular R P :=
  Iff.rfl

variable (W')

/-- The class of `(0, 1, 0)`, the point at infinity `[0 : 1 : 0]`, is unimodular. -/
@[simp]
theorem unimodularLift_zero : W'.UnimodularLift ⟦![0, 1, 0]⟧ :=
  (unimodularLift_iff _).mpr
    ⟨W'.equation_zero, TauCeti.Module.isUnimodular_of_isUnit_apply (i := 1) (by simp)⟩

/-- The class of `(a, b, 1)` is unimodular if and only if `(a, b)` solves the affine Weierstrass
equation: the coordinate `1` makes the coordinates unimodular. -/
@[simp]
theorem unimodularLift_some (a b : R) :
    W'.UnimodularLift ⟦![a, b, 1]⟧ ↔ W'.toAffine.Equation a b := by
  rw [unimodularLift_iff, equation_some, and_iff_left_iff_imp]
  exact fun _ ↦ TauCeti.Module.isUnimodular_of_isUnit_apply (i := 2) (by simp)

end CommRing

section Field

variable {F : Type*} [Field F] {W : Projective F}

/-- On an elliptic curve over a field, a projective point class is unimodular if and only if it is
nonsingular: both conditions say that a nonzero representative solves the equation. -/
theorem unimodularLift_iff_nonsingularLift [W.IsElliptic] {P : PointClass F} :
    W.UnimodularLift P ↔ W.NonsingularLift P := by
  induction P using Quotient.inductionOn with | _ P => ?_
  rw [unimodularLift_iff, nonsingularLift_iff, TauCeti.Module.isUnimodular_iff_exists_isUnit]
  simp_rw [isUnit_iff_ne_zero, ← Function.ne_iff]
  exact ⟨fun h ↦ (equation_iff_nonsingular_of_ne_zero h.2).mp h.1,
    fun h ↦ ⟨h.1, ne_zero_of_nonsingular h⟩⟩

variable (W) [W.IsElliptic]

/-- On an elliptic curve over a field, the nonsingular projective points are the unimodular
projective point classes. -/
def Point.equivUnimodularLift : W.Point ≃ {P : PointClass F // W.UnimodularLift P} where
  toFun P := ⟨P.point, unimodularLift_iff_nonsingularLift.mpr P.nonsingular⟩
  invFun P := ⟨unimodularLift_iff_nonsingularLift.mp P.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem Point.coe_equivUnimodularLift (P : W.Point) :
    (Point.equivUnimodularLift W P : PointClass F) = P.point :=
  (rfl)

@[simp]
theorem Point.equivUnimodularLift_symm_point (P : {P : PointClass F // W.UnimodularLift P}) :
    ((Point.equivUnimodularLift W).symm P).point = P :=
  (rfl)

end Field

end WeierstrassCurve.Projective
