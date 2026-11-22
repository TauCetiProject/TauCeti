/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Pencil
public import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.OneSubFrobenius.Degree

/-!
# The trace of Frobenius over a separably closed extension

Let `W` be an elliptic curve over a finite field `𝔽_q` and `π` its Frobenius over an extension
`K`. This file proves that `deg (id - π)` over `K` is `#E(𝔽_q)`, the point count of
`W` over its own base, and hence, when `K` is separably closed, that the degree of the Frobenius
pencil `r π - s` is the quadratic form `q r² - a_q r s + s²` whose middle coefficient is the
Frobenius trace `a_q = q + 1 - #E(𝔽_q)`. As `r π - 1` is then separable, its kernel, the set of
points fixed by `r π`, has `q r² - a_q r + 1` elements.

## Main results

* `TauCeti.Isogeny.Hom.degree_id_sub_ofIsogeny_baseChangeFrobenius_eq_pointCount`:
  `deg (id - π) = #E(𝔽_q)` over an extension.
* `TauCeti.Isogeny.Hom.degree_zsmul_ofIsogeny_baseChangeFrobenius_sub_zsmul_id_eq_frobeniusTrace`:
  the degree of `r π - s` is the quadratic form `q r² - a_q r s + s²`.
* `TauCeti.Isogeny.Hom.ncard_fixedPoints_zsmul_ofIsogeny_baseChangeFrobenius`: over a separably
  closed extension, `#{P | r • π P = P} = q r² - a_q r + 1`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.10, V.1.1 and V.2.3.

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

/-- The degree of `1 - π` computed over the presentation `W.map (algebraMap F K)` of the base
change, with `π` as the `Isogeny.map` of the Frobenius of `W`, equals the degree over `W⁄K` with
`π = baseChangeFrobenius K W`: the two curves agree by unfolding `WeierstrassCurve.baseChange`. -/
private theorem degree_one_sub_ofIsogeny_map_frobeniusIsogeny :
    (1 - ofIsogeny ((frobeniusIsogeny W).map (algebraMap F K))).degree =
      (1 - ofIsogeny (baseChangeFrobenius K W)).degree := by
  rw [baseChangeFrobenius_def]
  rfl

/-- **`deg (id - π) = #E(𝔽_q)`**: over an extension of the finite base, the degree
of `id - π` is the number of rational points of `W`, the point at infinity included. Here `π` is
the base-changed Frobenius endomorphism of `W⁄K`; compare
`TauCeti.Isogeny.degree_oneSubFrobeniusIsogeny_eq_pointCount`, the same count for `1 - π_q` as an
isogeny of `W` over `𝔽_q` itself. -/
theorem degree_id_sub_ofIsogeny_baseChangeFrobenius_eq_pointCount :
    (id (W⁄K).toAffine - ofIsogeny (baseChangeFrobenius K W)).degree = W.pointCount := by
  rw [← one_def, ← degree_oneSubFrobeniusIsogeny_eq_pointCount W, ← degree_ofIsogeny,
    ofIsogeny_oneSubFrobeniusIsogeny, ← degree_map _ (algebraMap F K), map_sub, map_one,
    ofIsogeny_map]
  exact (degree_one_sub_ofIsogeny_map_frobeniusIsogeny (K := K) W).symm

/-- **The middle coefficient of the Frobenius pencil's degree form is the Frobenius trace.** Over a
separably closed extension, `deg (r π - s) = q r² - a_q r s + s²`. Compare
`degree_zsmul_ofIsogeny_baseChangeFrobenius_sub_zsmul_id`, which has `q + 1 - deg (id - π)` in
place of `a_q`. -/
theorem degree_zsmul_ofIsogeny_baseChangeFrobenius_sub_zsmul_id_eq_frobeniusTrace [IsSepClosed K]
    (r s : ℤ) :
    ((r • ofIsogeny (baseChangeFrobenius K W) - s • id (W⁄K).toAffine).degree : ℤ) =
      (Nat.card F : ℤ) * r ^ 2 - W.frobeniusTrace * (r * s) + s ^ 2 := by
  rw [degree_zsmul_ofIsogeny_baseChangeFrobenius_sub_zsmul_id W r s,
    degree_id_sub_ofIsogeny_baseChangeFrobenius_eq_pointCount, WeierstrassCurve.frobeniusTrace_def]

/-- **The points fixed by `r π` over a separably closed extension** number
`q r² - a_q r + 1`, the degree of the separable endomorphism `r π - 1` (Silverman V.2.3). -/
theorem ncard_fixedPoints_zsmul_ofIsogeny_baseChangeFrobenius [DecidableEq K] [IsSepClosed K]
    (r : ℤ) :
    ({P : (W⁄K).toAffine.Point |
      (r • ofIsogeny (baseChangeFrobenius K W)).pointMap P = P}.ncard : ℤ) =
      Nat.card F * r ^ 2 - W.frobeniusTrace * r + 1 := by
  have h := zsmul_ofIsogeny_baseChangeFrobenius_sub_zsmul_id_ne_zero (K := K) W r 1 (by simp)
  have := (isSeparable_toIsogeny_zsmul_ofIsogeny_baseChangeFrobenius_sub_zsmul_id_iff W r 1 h).mpr
    (by simp)
  have hset : {P : (W⁄K).toAffine.Point |
      (r • ofIsogeny (baseChangeFrobenius K W)).pointMap P = P} =
      {P | (r • ofIsogeny (baseChangeFrobenius K W) - (1 : ℤ) • id (W⁄K).toAffine).pointMap P =
        0} := by
    ext P
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, sub_pointMap, one_zsmul, id_pointMap, sub_eq_zero]
  rw [hset, ncard_setOf_pointMap_eq h,
    degree_zsmul_ofIsogeny_baseChangeFrobenius_sub_zsmul_id_eq_frobeniusTrace, mul_one, one_pow]

end TauCeti.Isogeny.Hom

end
