/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Iteration
public import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount
import TauCeti.FieldTheory.Finite.FrobeniusFixed

/-!
# Frobenius fixed points and finite extensions

Let `W` be an elliptic curve over a finite field `F` with `q` elements, and let `E/F` be a finite
extension of degree `n` embedded in a field `K`. The points of `W` over `E` map bijectively onto
the points over `K` fixed by the `n`th iterate of the `q`-power Frobenius. Thus the fixed-point
model for points over `𝔽_{qⁿ}` has the same count as base change to any chosen such extension.

If `K` is separably closed, this identifies `#W(E)` with `deg (1 - π ^ n)`. No algebraicity
assumption on `K/F` is needed. The extension degree is automatically positive, so the zero
iterate, whose fixed locus need not be finite, never occurs.

## Main results

* `TauCeti.Isogeny.Hom.pow_ofIsogeny_baseChangeFrobenius_pointMap_eq_self_iff_mem_range_map`:
  the fixed points are precisely the images of the points over the finite extension.
* `TauCeti.Isogeny.Hom.ncard_fixedPoints_pow_ofIsogeny_baseChangeFrobenius_eq_pointCount`:
  the fixed-point count agrees with the chosen-extension count.
* `TauCeti.Isogeny.Hom.degree_one_sub_pow_ofIsogeny_baseChangeFrobenius_eq_pointCount`:
  over separably closed constants the degree is the chosen-extension count.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], V.2.3.
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine

namespace TauCeti.Isogeny.Hom

variable {F E K : Type*} [Field F] [Finite F] [Field E] [Finite E] [Field K]
  [Algebra F E] [Algebra F K] [Algebra E K] [IsScalarTower F E K]
  [DecidableEq E] [DecidableEq K]
  (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-- The points fixed by Frobenius to the extension degree are exactly the points coming from
that finite extension. This holds in any ambient field containing the extension. -/
theorem pow_ofIsogeny_baseChangeFrobenius_pointMap_eq_self_iff_mem_range_map
    (P : (W⁄K).toAffine.Point) :
    ((ofIsogeny (baseChangeFrobenius K W)) ^ Module.finrank F E).pointMap P = P ↔
      P ∈ Set.range (Point.map (W' := W) (IsScalarTower.toAlgHom F E K)) := by
  rw [pow_ofIsogeny_baseChangeFrobenius_pointMap_eq_self_iff,
    ← Module.natCard_eq_pow_finrank (K := F) (V := E), Set.mem_range, Point.exists_map_eq_iff,
    IsScalarTower.coe_toAlgHom']
  exact and_congr
    (FiniteField.pow_natCard_eq_self_iff_mem_range_algebraMap (Point.xCoord P))
    (FiniteField.pow_natCard_eq_self_iff_mem_range_algebraMap (Point.yCoord P))

omit [DecidableEq E] in
/-- The number of points fixed by the extension-degree iterate of Frobenius is the point count
of the base change to that extension. The point at infinity is included on both sides. -/
theorem ncard_fixedPoints_pow_ofIsogeny_baseChangeFrobenius_eq_pointCount :
    {P : (W⁄K).toAffine.Point |
      ((ofIsogeny (baseChangeFrobenius K W)) ^ Module.finrank F E).pointMap P = P}.ncard =
        (W⁄E).pointCount := by
  classical
  have hset : {P : (W⁄K).toAffine.Point |
      ((ofIsogeny (baseChangeFrobenius K W)) ^ Module.finrank F E).pointMap P = P} =
      Set.range (Point.map (W' := W) (IsScalarTower.toAlgHom F E K)) :=
    Set.ext (pow_ofIsogeny_baseChangeFrobenius_pointMap_eq_self_iff_mem_range_map W)
  rw [hset, Set.ncard_range_of_injective (Point.map_injective _),
    WeierstrassCurve.pointCount_eq_card_point]

omit [DecidableEq E] [DecidableEq K] in
/-- Over a separably closed ambient field, the degree of `1 - π ^ [E:F]` is `#W(E)`.
This compares the intrinsic isogeny degree with a chosen finite-extension model. -/
theorem degree_one_sub_pow_ofIsogeny_baseChangeFrobenius_eq_pointCount [IsSepClosed K] :
    (1 - (ofIsogeny (baseChangeFrobenius K W)) ^ Module.finrank F E).degree =
      (W⁄E).pointCount := by
  classical
  rw [← ncard_fixedPoints_pow_ofIsogeny_baseChangeFrobenius W _
      (Module.finrank_pos (R := F) (M := E)),
    ncard_fixedPoints_pow_ofIsogeny_baseChangeFrobenius_eq_pointCount (E := E)]

end TauCeti.Isogeny.Hom

end
