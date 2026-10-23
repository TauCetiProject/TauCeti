/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GenericPoint.Reduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.MapsInfinity

/-!
# The tautological point of `[n]` reduces to `n • P`

The tautological point of the isogeny `[n]` is `n` times the generic point
(`TauCeti.Isogeny.tautologicalPoint_mulByIntPullback`), and the generic point reduces to `P` at
the place of `P` (`WeierstrassCurve.Affine.reductionOfDegreeEqOne_genericPoint`). Reduction at a
place of degree one is additive, so the tautological point of `[n]` reduces to `n • P` there. The
tautological point of an isogeny is the isogeny evaluated at the generic point, and its reduction
at the place of `P` is the isogeny evaluated at `P`; read this way, the statement says that `[n]`
is the group's own multiplication by `n`.

## Main results

* `TauCeti.Isogeny.reductionOfDegreeEqOne_tautologicalPoint_mulByIntIsogeny`: at the place of
  `P`, the tautological point of `[n]` reduces to `n • P`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine

namespace TauCeti.Isogeny

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F} [W.IsElliptic]

/-- **`[n]` acts on points as multiplication by `n`**: at the place of `P`, the tautological
point of `[n]` reduces to `n • P`. -/
-- Not `@[simp]`: its left-hand side is not simp-normal, since `mulByIntIsogeny_pullback` rewrites
-- the pullback of `[n]`.
theorem reductionOfDegreeEqOne_tautologicalPoint_mulByIntIsogeny {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) (P : W.Point) :
    reductionOfDegreeEqOne W (W.pointEquivDegreeOnePlace P).2
        (mulByIntIsogeny W hn).pullback.tautologicalPoint =
      Point.equivBaseChangeSelf W (n • P) := by
  rw [mulByIntIsogeny_pullback, tautologicalPoint_mulByIntPullback, map_zsmul,
    reductionOfDegreeEqOne_genericPoint, map_zsmul]

end TauCeti.Isogeny

end
