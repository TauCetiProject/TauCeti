/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GenericPoint
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.TautologicalPoint

/-!
# The point formula for relative Frobenius

The relative Frobenius isogeny from an affine Weierstrass curve to its Frobenius twist is
contravariantly defined on coordinate rings. This file records the corresponding formula on its
tautological point: its affine coordinates are the corresponding powers of the generic
coordinates. The same formulas are supplied for the iterated relative Frobenius.

These formulas are the point-level interface of relative Frobenius. They let later arguments
compare a pullback defined on coordinate rings with the usual coordinate description of
Frobenius, without unfolding either the coordinate ring or the tautological point.

## Main results

* `TauCeti.Isogeny.xCoord_tautologicalPoint_relativeFrobeniusIsogeny` and
  `TauCeti.Isogeny.yCoord_tautologicalPoint_relativeFrobeniusIsogeny` give the coordinates of
  relative Frobenius.
* `TauCeti.Isogeny.xCoord_tautologicalPoint_iterateRelativeFrobeniusIsogeny` and
  `TauCeti.Isogeny.yCoord_tautologicalPoint_iterateRelativeFrobeniusIsogeny` give their iterated
  counterparts.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.11.
-/

public section

namespace TauCeti.Isogeny

open Polynomial
open WeierstrassCurve.Affine

variable {F : Type*} [Field F] (p : ℕ) [ExpChar F p] (W : WeierstrassCurve.Affine F)

/-- Substituting `X ^ q` into the affine coordinate and passing to the function field gives the
`q`-th power of the generic `x`-coordinate. -/
private theorem algebraMap_of_expand_X (q : ℕ) :
    algebraMap W.CoordinateRing W.FunctionField (AdjoinRoot.of W.polynomial (expand F q X)) =
      W.genericX ^ q := by
  rw [Polynomial.expand_X, map_pow, map_pow, ← AdjoinRoot.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply F[X] W.CoordinateRing W.FunctionField,
    ← W.genericX_eq_algebraMap]

/-- **Relative Frobenius sends the generic affine `x`-coordinate to its `p`-th power.**

**Deliberately not `@[simp]`.** Its left-hand side is already reduced by the coordinate-pullback
and relative-Frobenius simp lemmas; this named form remains the point-level API. -/
theorem xCoord_tautologicalPoint_relativeFrobeniusIsogeny [W.IsElliptic] :
    Point.xCoord (CoordinatePullback.tautologicalPoint
      (relativeFrobeniusIsogeny p W).pullback) = W.genericX ^ p := by
  rw [CoordinatePullback.xCoord_tautologicalPoint, relativeFrobeniusIsogeny_pullback,
    relativeFrobeniusPullback_apply, CoordinateRing.relativeFrobenius_of,
    algebraMap_of_expand_X]

/-- **Relative Frobenius sends the generic affine `y`-coordinate to its `p`-th power.**

**Deliberately not `@[simp]`.** Its left-hand side is already reduced by the coordinate-pullback
and relative-Frobenius simp lemmas; this named form remains the point-level API. -/
theorem yCoord_tautologicalPoint_relativeFrobeniusIsogeny [W.IsElliptic] :
    Point.yCoord (CoordinatePullback.tautologicalPoint
      (relativeFrobeniusIsogeny p W).pullback) = W.genericY ^ p := by
  rw [CoordinatePullback.yCoord_tautologicalPoint, relativeFrobeniusIsogeny_pullback,
    relativeFrobeniusPullback_apply, CoordinateRing.relativeFrobenius_root]
  rw [WeierstrassCurve.Affine.genericY_def, map_pow, AdjoinRoot.mk_X]

/-- **The `n`-fold relative Frobenius sends the generic affine `x`-coordinate to its
`p ^ n`-th power.**

**Deliberately not `@[simp]`.** Its left-hand side is already reduced by the coordinate-pullback
and iterated-relative-Frobenius simp lemmas; this named form remains the point-level API. -/
theorem xCoord_tautologicalPoint_iterateRelativeFrobeniusIsogeny [W.IsElliptic] (n : ℕ) :
    Point.xCoord (CoordinatePullback.tautologicalPoint
      (iterateRelativeFrobeniusIsogeny p W n).pullback) =
      W.genericX ^ p ^ n := by
  rw [CoordinatePullback.xCoord_tautologicalPoint, iterateRelativeFrobeniusIsogeny_pullback,
    iterateRelativeFrobeniusPullback_apply, CoordinateRing.iterateRelativeFrobenius_of,
    algebraMap_of_expand_X]

/-- **The `n`-fold relative Frobenius sends the generic affine `y`-coordinate to its
`p ^ n`-th power.**

**Deliberately not `@[simp]`.** Its left-hand side is already reduced by the coordinate-pullback
and iterated-relative-Frobenius simp lemmas; this named form remains the point-level API. -/
theorem yCoord_tautologicalPoint_iterateRelativeFrobeniusIsogeny [W.IsElliptic] (n : ℕ) :
    Point.yCoord (CoordinatePullback.tautologicalPoint
      (iterateRelativeFrobeniusIsogeny p W n).pullback) =
      W.genericY ^ p ^ n := by
  rw [CoordinatePullback.yCoord_tautologicalPoint, iterateRelativeFrobeniusIsogeny_pullback,
    iterateRelativeFrobeniusPullback_apply, CoordinateRing.iterateRelativeFrobenius_root]
  rw [WeierstrassCurve.Affine.genericY_def, map_pow, AdjoinRoot.mk_X]

end TauCeti.Isogeny

end
