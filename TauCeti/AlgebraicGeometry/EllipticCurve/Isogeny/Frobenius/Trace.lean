/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Pencil
public import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.FrobeniusFixed
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.PointMap
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PointHom.Fiber

/-!
# The trace of Frobenius over a separably closed extension

Let `W` be an elliptic curve over a finite field `𝔽_q` and `π` its Frobenius over a separably
closed extension `K`. This file proves that `deg (id - π)` over `K` is `#E(𝔽_q)`, the point count of
`W` over its own base, and hence that the degree of the Frobenius pencil `r π - s` is the quadratic
form `q r² - a_q r s + s²` whose middle coefficient is the Frobenius trace `a_q = q + 1 - #E(𝔽_q)`.

## Main results

* `TauCeti.Isogeny.Hom.degree_id_sub_ofIsogeny_baseChangeFrobenius_eq_pointCount`:
  `deg (id - π) = #E(𝔽_q)` over a separably closed extension.
* `TauCeti.Isogeny.Hom.degree_zsmul_ofIsogeny_baseChangeFrobenius_sub_zsmul_id_eq_frobeniusTrace`:
  the degree of `r π - s` is the quadratic form `q r² - a_q r s + s²`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.10 and V.1.1.

## Provenance

The AINTLIB `HasseWeil` project (Chris Birkbeck, Apache-2.0) at commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a` has the corresponding count for its own model of
isogenies, `oneSubFrobeniusIsogBaseChange_degree_eq_pointCount` in
`HasseWeil/HasseBound/WeilPairing/Scaling/OneSubTransport.lean`. Nothing is taken from the source:
the statements here are about TauCeti's morphisms of elliptic curves and their degrees.
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine

namespace TauCeti.Isogeny.Hom

variable {F K : Type*} [Field F] [Finite F] [Field K] [Algebra F K]
  (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-- **`deg (id - π) = #E(𝔽_q)`**: over a separably closed extension of the finite base, the degree
of `id - π` is the number of rational points of `W`, the point at infinity included. Here `π` is
the base-changed Frobenius endomorphism of `W⁄K`; compare
`TauCeti.Isogeny.degree_oneSubFrobeniusIsogeny_eq_pointCount`, the same count for `1 - π_q` as an
isogeny of `W` over `𝔽_q` itself. -/
theorem degree_id_sub_ofIsogeny_baseChangeFrobenius_eq_pointCount [IsSepClosed K] :
    (id (W⁄K).toAffine - ofIsogeny (baseChangeFrobenius K W)).degree = W.pointCount := by
  classical
  have : Fintype F := Fintype.ofFinite F
  -- `id - π` is the pencil `r π - s` at `r = s = -1`, so it is a nonzero separable isogeny; over a
  -- separably closed field its degree is then the number of points it sends to `O`, which are the
  -- points fixed by the `q`-power map, i.e. the base changes of the rational points.
  rw [show id (W⁄K).toAffine - ofIsogeny (baseChangeFrobenius K W) =
      (-1 : ℤ) • ofIsogeny (baseChangeFrobenius K W) - (-1 : ℤ) • id (W⁄K).toAffine by
    rw [neg_one_zsmul, neg_one_zsmul, neg_sub_neg]]
  have hf := zsmul_ofIsogeny_baseChangeFrobenius_sub_zsmul_id_ne_zero (K := K) W (-1) (-1) (by simp)
  have :=
    (isSeparable_toIsogeny_zsmul_ofIsogeny_baseChangeFrobenius_sub_zsmul_id_iff W (-1) (-1) hf).2
      (by simp)
  rw [← ofIsogeny_toIsogeny hf, degree_ofIsogeny, ← ncard_fiber_toPointHom_eq_degree _ 0,
    WeierstrassCurve.pointCount_eq_card_point,
    ← Point.ncard_setOf_map_frobeniusAlgHom_eq_self (L := K) W]
  refine congrArg Set.ncard (Set.ext fun P ↦ ?_)
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, ← pointMap_ofIsogeny_eq_toPointHom,
    ofIsogeny_toIsogeny, neg_one_zsmul, neg_one_zsmul, neg_sub_neg, sub_pointMap, id_pointMap,
    pointMap_ofIsogeny_baseChangeFrobenius, sub_eq_zero, eq_comm]

/-- **The middle coefficient of the Frobenius pencil's degree form is the Frobenius trace.** Over a
separably closed algebraic extension, `deg (r π - s) = q r² - a_q r s + s²` whenever `s` is
nonzero in the field. Compare `degree_zsmul_ofIsogeny_baseChangeFrobenius_sub_zsmul_id`, which has
`q + 1 - deg (id - π)` in place of `a_q`. -/
theorem degree_zsmul_ofIsogeny_baseChangeFrobenius_sub_zsmul_id_eq_frobeniusTrace [IsSepClosed K]
    [Algebra.IsAlgebraic F K] (r s : ℤ) (hs : (s : K) ≠ 0) :
    ((r • ofIsogeny (baseChangeFrobenius K W) - s • id (W⁄K).toAffine).degree : ℤ) =
      (Nat.card F : ℤ) * r ^ 2 - W.frobeniusTrace * (r * s) + s ^ 2 := by
  rw [degree_zsmul_ofIsogeny_baseChangeFrobenius_sub_zsmul_id W r s hs,
    degree_id_sub_ofIsogeny_baseChangeFrobenius_eq_pointCount, WeierstrassCurve.frobeniusTrace_def]

end TauCeti.Isogeny.Hom

end
