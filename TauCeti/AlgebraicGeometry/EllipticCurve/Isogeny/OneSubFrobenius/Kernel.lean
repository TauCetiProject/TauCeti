/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Translation
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Kernel
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.OneSubFrobenius.TautologicalPoint
public import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount

/-!
# Every rational point lies in the kernel of `1 − π`

Over a finite field the isogeny `1 − π_q` kills every `F`-rational point, so its kernel is all of
them. The reason is the one behind the classical count: `π_q` fixes the rational points, so
`(1 − π_q)(X + P) = (1 − π_q)(X)` for rational `P`, and a function pulled back along `1 − π_q` is
unmoved by translating by `P`.

An isogeny here has no point map, so the argument is carried out on tautological points. A kernel
element is a point whose translation fixes the pulled-back field; translation acts on a pullback by
post-composition, and a pullback is fixed by such an endomorphism exactly when its tautological
point is. The tautological point of `1 − π_q` is `g − π_q(g)`, and translation moves both terms by
the same rational point, so their difference does not move at all.

## Main results

* `TauCeti.Isogeny.ker_oneSubFrobeniusIsogeny`: the kernel of `1 − π_q` is everything.
* `TauCeti.Isogeny.card_ker_oneSubFrobeniusIsogeny`: so its kernel has exactly as many elements
  as there are rational points.
* `TauCeti.Isogeny.pointCount_le_degree_oneSubFrobeniusIsogeny`: consequently `deg (1 − π_q)`
  bounds `pointCount` above.

This is the lower half of `deg (1 − π_q) = #E(𝔽_q)`. The upper half asks in addition that the
kernel cut out the pulled-back field exactly, and is not proved here.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4, V.1.
* The AINTLIB `HasseWeil` project (Chris Birkbeck, Apache 2.0, commit
  `513e83879e2f8cbc626eb9e04d660e92be16ccba`) states the two headline results in
  `Hasse/PointFix.lean` as `kernel_eq_top_of_hom_eq_id_sub_frobenius` and
  `card_kernel_eq_pointCount_of_kernel_eq_top`. Its isogenies carry a point map independent of the
  function-field pullback, and its Frobenius declares that map to be the identity, so there the
  first reduces to `sub_self`. The kernel here is defined from the pullback, so the proof is the
  tautological-point argument above instead.
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [Finite F] [DecidableEq F] (W : WeierstrassCurve.Affine F)
  [W.IsElliptic]

/-- **The kernel of `1 − π_q` is every rational point.** -/
@[simp]
theorem ker_oneSubFrobeniusIsogeny : (oneSubFrobeniusIsogeny W).ker = ⊤ := by
  refine eq_top_iff.2 fun P _ ↦ mem_ker_iff.2 ?_
  -- it is enough that translation fixes the coordinate pullback, the function field being its
  -- fraction field
  have hcoord : (translation W P).toAlgHom.comp (oneSubFrobeniusIsogeny W).pullback =
      (oneSubFrobeniusIsogeny W).pullback := by
    refine CoordinatePullback.tautologicalPoint_injective ?_
    rw [CoordinatePullback.tautologicalPoint_comp,
      tautologicalPoint_oneSubFrobeniusIsogeny, map_sub, map_translation_genericPoint,
      translatedGenericPoint_def, map_translation_tautologicalPoint_frobeniusIsogeny]
    abel
  have hfield : (translation W P).toAlgHom.comp (oneSubFrobeniusIsogeny W).fieldPullback =
      (oneSubFrobeniusIsogeny W).fieldPullback :=
    fieldPullback_unique _ _ fun x ↦ by
      rw [AlgHom.comp_apply, fieldPullback_algebraMap, ← AlgHom.comp_apply, hcoord]
  rintro _ ⟨z, rfl⟩
  simpa using DFunLike.congr_fun hfield z

/-- **The rational points are exactly the kernel of `1 − π_q`**, as a cardinality. -/
theorem card_ker_oneSubFrobeniusIsogeny :
    Nat.card (oneSubFrobeniusIsogeny W).ker = Nat.card (W⁄F).toAffine.Point := by
  rw [ker_oneSubFrobeniusIsogeny, AddSubgroup.card_top]

omit [DecidableEq F] in
/-- **The degree of `1 − π_q` bounds the point count above.** This is the lower half of
`deg (1 − π_q) = #E(𝔽_q)`; the upper half asks in addition that the kernel cut out the pulled-back
field exactly, and is not proved here. -/
theorem pointCount_le_degree_oneSubFrobeniusIsogeny :
    W.pointCount ≤ (oneSubFrobeniusIsogeny W).degree := by
  classical
  rw [WeierstrassCurve.pointCount_eq_card_point]
  exact (card_ker_oneSubFrobeniusIsogeny W).symm.trans_le (card_ker_le_degree _)

end TauCeti.Isogeny

end
