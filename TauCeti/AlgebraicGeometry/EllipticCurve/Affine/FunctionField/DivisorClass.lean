/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.PointPlace
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.ToClass
public import TauCeti.FieldTheory.FunctionField.Divisor.AffineModel

/-!
# The points of a Weierstrass curve are the degree-zero divisor classes of its function field

The coordinate ring of an affine Weierstrass curve is an affine model of its function field whose
only place at infinity is `TauCeti.Place.infinity`, and that place is rational. The general
affine-model bridge therefore identifies the ideal class group of the coordinate ring with the
degree-zero divisor class group of the function field. Composing with the identification of the
points with that ideal class group gives the points as degree-zero divisor classes.

## Main results

* `WeierstrassCurve.Affine.setOf_exists_notMem_integers_eq_singleton_infinity`: the place at
  infinity is the only place infinite on the coordinate ring.
* `WeierstrassCurve.Affine.pointEquivDegreeZeroDivisorClass`: **the points of `W` are the
  degree-zero divisor classes of `F(W)`.**
* `WeierstrassCurve.Affine.val_pointEquivDegreeZeroDivisorClass_some`: that equivalence sends an
  affine point `P` to the class of `(P) - (O)`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.3.4.
* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], I.4.
-/

public section

namespace WeierstrassCurve.Affine

open TauCeti AlgebraicGeometry IsDedekindDomain Polynomial

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)
  [IsDedekindDomain W.CoordinateRing]

/-- **The place at infinity is the only place infinite on the coordinate ring.** Every other place
is the place of a height-one prime, and such a place contains the whole coordinate ring; the place
at infinity is infinite on it because `x` has a pole there. -/
theorem setOf_exists_notMem_integers_eq_singleton_infinity :
    {Q : Place F W.FunctionField | ∃ r : W.CoordinateRing,
        algebraMap W.CoordinateRing W.FunctionField r ∉ Q.integers} = {Place.infinity W} := by
  ext Q
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨r, hr⟩
    rcases Place.eq_infinity_or_existsUnique_eq_ofPrime (W := W) Q with h | ⟨𝔭, h𝔭, -⟩
    · exact h
    · exact absurd ((Place.exists_eq_ofPrime_iff F W.FunctionField Q).mp ⟨𝔭, h𝔭⟩ r) hr
  · rintro rfl
    refine ⟨algebraMap F[X] W.CoordinateRing X, ?_⟩
    rw [Place.mem_integers_iff, Place.valuation_infinity,
      ← IsScalarTower.algebraMap_apply F[X] W.CoordinateRing W.FunctionField]
    exact not_le.mpr W.one_lt_infinityPlace_X

/-- **The ideal class of a point's place is the class Mathlib's `toClass` takes.** The place of a
point has the point's ideal `⟨X - x, Y - y⟩` underneath it, and `XYIdeal'` is that ideal as an
invertible fractional ideal. -/
@[simp]
theorem classGroupMk_pointPlace {x y : F} (h : W.Nonsingular x y) :
    (CoordinateRing.pointPlace h.left).classGroupMk =
      ClassGroup.mk W.FunctionField (CoordinateRing.XYIdeal' h) := by
  rw [IsDedekindDomain.HeightOneSpectrum.classGroupMk_eq_mk W.FunctionField]
  congr 1
  exact Units.ext (by rw [Units.val_mk0, CoordinateRing.XYIdeal'_eq,
    CoordinateRing.pointPlace_asIdeal])

/-- The class of `(P) - (O)` has degree zero: both places are rational. -/
-- Not `@[simp]`, unlike `classGroupMk_pointPlace` above: `Divisor.degreeClass_divisorClass` and
-- `Divisor.degree_ofPoint` are themselves `@[simp]` and rewrite this left-hand side to a
-- difference of place degrees, so the rule would not be in simp normal form.
theorem degreeClass_divisorClass_pointPlace_sub_infinity {x y : F} (h : W.Equation x y) :
    Divisor.degreeClass W.isFunctionField
        ((Place.orderSystem W.isFunctionField).divisorClass
          (WeilDivisor.ofPoint (Place.ofPrime F W.FunctionField (CoordinateRing.pointPlace h)) -
            WeilDivisor.ofPoint (Place.infinity W))) = 0 := by
  simp [Place.degree_ofPrime, CoordinateRing.pointPlace.finrank_residueField_eq_one]

variable [DecidableEq F]

/-- **The points of `W` are the degree-zero divisor classes of `F(W)`.** The point at infinity is
the trivial class and an affine point `P` is the class of `(P) - (O)`. -/
noncomputable def pointEquivDegreeZeroDivisorClass :
    W.Point ≃+ (Divisor.degreeClass W.isFunctionField).ker :=
  (Point.toClassEquiv (W := W)).trans
    (Divisor.degreeZeroClassGroupEquiv W.CoordinateRing W.isFunctionField
      W.setOf_exists_notMem_integers_eq_singleton_infinity (Place.degree_infinity (W := W))).symm

/-- **An affine point goes to the class of `(P) - (O)`.** This is the computation rule for
`pointEquivDegreeZeroDivisorClass`, whose value is otherwise opaque. -/
@[simp]
theorem val_pointEquivDegreeZeroDivisorClass_some {x y : F} (h : W.Nonsingular x y) :
    (W.pointEquivDegreeZeroDivisorClass (Point.some x y h) :
        (Place.orderSystem W.isFunctionField).ClassGroup) =
      (Place.orderSystem W.isFunctionField).divisorClass
        (WeilDivisor.ofPoint (Place.ofPrime F W.FunctionField (CoordinateRing.pointPlace h.left)) -
          WeilDivisor.ofPoint (Place.infinity W)) := by
  have hsingle := W.setOf_exists_notMem_integers_eq_singleton_infinity
  have hinf : ∃ r : W.CoordinateRing,
      algebraMap W.CoordinateRing W.FunctionField r ∉ (Place.infinity W).integers := by
    rw [Set.ext_iff] at hsingle
    exact (hsingle (Place.infinity W)).mpr rfl
  refine sub_eq_zero.mp (Divisor.eq_zero_of_classGroupHom_eq_zero_of_degreeClass_eq_zero
    W.CoordinateRing W.isFunctionField hsingle (Place.degree_infinity (W := W)) ?_ ?_)
  · rw [map_sub, W.degreeClass_divisorClass_pointPlace_sub_infinity h.left, sub_zero]
    exact AddMonoidHom.mem_ker.mp (W.pointEquivDegreeZeroDivisorClass (Point.some x y h)).2
  · rw [map_sub, sub_eq_zero, ← Divisor.degreeZeroClassGroupEquiv_apply W.CoordinateRing
      W.isFunctionField hsingle (Place.degree_infinity (W := W))]
    simp only [pointEquivDegreeZeroDivisorClass, AddEquiv.trans_apply, AddEquiv.apply_symm_apply,
      Point.toClassEquiv_apply, map_sub, Divisor.classGroupHom_divisorClass_ofPoint_ofPrime,
      Divisor.classGroupHom_divisorClass_ofPoint_of_exists_notMem_integers _ hinf, sub_zero]
    exact (W.classGroupMk_pointPlace h).symm

end WeierstrassCurve.Affine

end
