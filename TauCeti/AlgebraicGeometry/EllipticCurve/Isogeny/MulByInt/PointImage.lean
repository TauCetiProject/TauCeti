/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.MapsInfinity
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PointImage

/-!
# Multiplication by `n` acts on points as `n •`

The image of a point under the isogeny `[n]` (`TauCeti.Isogeny.pointImage`) is `n • P`
(`TauCeti.Isogeny.pointImage_mulByIntIsogeny`): the point map of an isogeny recovers, for `[n]`,
the group's own multiplication by `n`.

## Main results

* `TauCeti.Isogeny.pointImage_mulByIntIsogeny`: `[n]` sends `P` to `n • P`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine

namespace TauCeti.Isogeny

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F} [W.IsElliptic]

/-- **`[n]` acts on points as multiplication by `n`.** -/
@[simp]
theorem pointImage_mulByIntIsogeny {n : ℤ} (hn : psiFunctionField W n ≠ 0) (P : W.Point) :
    (mulByIntIsogeny W hn).pointImage P = n • P := by
  rw [pointImage_eq_iff, ← reductionOfDegreeEqOne_eq_iff W (W.pointEquivDegreeOnePlace P).2,
    mulByIntIsogeny_pullback, tautologicalPoint_mulByIntPullback, map_zsmul,
    reductionOfDegreeEqOne_genericPoint, map_zsmul]

end TauCeti.Isogeny

end
