/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GenericPoint.Reduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.TautologicalPoint
-- Proof-only: the pulled-back `x` has a pole at the place at infinity.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InfinityPlace

/-!
# The image of a point under an isogeny

Let `φ : W₁ → W₂` be an isogeny of elliptic curves over a field `F`. Its pullback carries the
generic point of `W₂` to the **tautological point** `t_φ`, a point of `W₂` over the function field
`F(W₁)` (`TauCeti.Isogeny.tautologicalPoint_eq_map_genericPoint`). Every point `P` of `W₁` has a
place of `F(W₁)` of degree one, and `φ(P)` is the reduction of `t_φ` there: the unique point `Q` of
`W₂` over `F` with `t_φ - Q` in the kernel of reduction at the place of `P`
(`WeierstrassCurve.Affine.reductionOfDegreeEqOne`).

Geometrically, `t_φ` is `φ` evaluated at the generic point of `W₁`, and reducing it at the place of
`P` evaluates `φ` at `P`. For the identity isogeny this is the statement that the generic point
reduces to `P` at the place of `P` (`WeierstrassCurve.Affine.reductionOfDegreeEqOne_genericPoint`).
The action of `[n]` is in `Isogeny/MulByInt/PointImage.lean`, and that of the Frobenius in
`Isogeny/Frobenius/PointImage.lean`.

The map here is read off the function field of `W₁` through reduction, and it needs nothing about
the isogeny beyond its tautological point, inseparable isogenies included.
`TauCeti.Isogeny.toPointHom` (`Isogeny/PointHom.lean`) is the class-group construction of the
induced map of points.

## Main definitions

* `TauCeti.Isogeny.pointImage`: the image `φ(P) ∈ W₂(F)` of a point `P ∈ W₁(F)`.

## Main results

* `TauCeti.Isogeny.pointImage_eq_iff`: `φ(P) = Q` exactly when `t_φ - Q` lies in the kernel of
  reduction at the place of `P`.
* `TauCeti.Isogeny.pointImage_zero`: `φ(O) = O`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4, VII.2.1.
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine

namespace TauCeti.Isogeny

variable {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve.Affine F}
  [W₁.IsElliptic] [W₂.IsElliptic]

/-- **The image of a point under an isogeny**: the reduction of the tautological point of `φ` at
the place of `P`. -/
noncomputable def pointImage (φ : Isogeny W₁ W₂) (P : W₁.Point) : W₂.Point :=
  (Point.equivBaseChangeSelf W₂).symm
    (reductionOfDegreeEqOne W₂ (W₁.pointEquivDegreeOnePlace P).2 φ.pullback.tautologicalPoint)

/-- **`φ(P)` is the point `Q` with `t_φ - Q` in the kernel of reduction at the place of `P`.** -/
theorem pointImage_eq_iff {φ : Isogeny W₁ W₂} {P : W₁.Point} {Q : W₂.Point} :
    φ.pointImage P = Q ↔ φ.pullback.tautologicalPoint -
      Point.baseChange (W' := W₂) F W₁.FunctionField (Point.equivBaseChangeSelf W₂ Q) ∈
        polePoints W₂ (W₁.pointEquivDegreeOnePlace P).1 := by
  rw [pointImage, AddEquiv.symm_apply_eq, reductionOfDegreeEqOne_eq_iff]

/-- **An isogeny sends `O` to `O`.** -/
@[simp]
theorem pointImage_zero (φ : Isogeny W₁ W₂) : φ.pointImage 0 = 0 := by
  rw [pointImage_eq_iff, map_zero (Point.equivBaseChangeSelf W₂),
    map_zero (Point.baseChange (W' := W₂) F W₁.FunctionField), sub_zero, Point.zero_def,
    coe_pointEquivDegreeOnePlace_zero, mem_polePoints_iff, Place.valuation_infinity,
    CoordinatePullback.xCoord_tautologicalPoint, ← AdjoinRoot.algebraMap_eq]
  exact Or.inr (one_lt_infinityPlace_pullback_X φ)

end TauCeti.Isogeny

end
