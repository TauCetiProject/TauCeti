/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.BaseChange

/-!
# Transport of elliptic-curve points along an algebra equivalence

Let `W` be a Weierstrass curve over a field `F`. Mathlib's `WeierstrassCurve.Affine.Point.map`
carries the points of `W` over one `F`-algebra to its points over another along an algebra
homomorphism. This file packages that map, for an `F`-algebra equivalence `K ≃ₐ[F] L`, as an
additive equivalence of point groups, and proves its identity, composition and inverse laws.

## Main definitions

* `WeierstrassCurve.Affine.Point.mapEquiv`: transport of points along an algebra equivalence.

## Main results

* `WeierstrassCurve.Affine.Point.mapEquiv_refl`, `mapEquiv_trans` and `mapEquiv_symm`: the
  transport is functorial in the algebra equivalence.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.
-/

public section

open scoped WeierstrassCurve

namespace WeierstrassCurve.Affine.Point

variable {F K L M : Type*} [Field F] [Field K] [Field L] [Field M]
  [DecidableEq K] [DecidableEq L] [DecidableEq M]
  [Algebra F K] [Algebra F L] [Algebra F M] (W : _root_.WeierstrassCurve F) [W.IsElliptic]

/-- **Transport of elliptic-curve points along an algebra equivalence.** This is Mathlib's
additive point map, with inverse induced by the inverse algebra equivalence. -/
noncomputable def mapEquiv (e : K ≃ₐ[F] L) :
    (W⁄K).toAffine.Point ≃+ (W⁄L).toAffine.Point where
  toFun := Point.map e.toAlgHom
  invFun := Point.map e.symm.toAlgHom
  left_inv P := by
    rcases P with _ | ⟨x, y, h⟩
    · rfl
    · simp only [Point.map_some]
      congr <;> exact e.symm_apply_apply _
  right_inv P := by
    rcases P with _ | ⟨x, y, h⟩
    · rfl
    · simp only [Point.map_some]
      congr <;> exact e.apply_symm_apply _
  map_add' := map_add (Point.map e.toAlgHom)

omit [W.IsElliptic] in
/-- `mapEquiv W e` applies Mathlib's point map along `e`. -/
@[simp]
theorem mapEquiv_apply (e : K ≃ₐ[F] L) (P : (W⁄K).toAffine.Point) :
    mapEquiv W e P = Point.map e.toAlgHom P :=
  by rw [mapEquiv]; rfl

omit [W.IsElliptic] in
/-- The inverse of `mapEquiv W e` applies Mathlib's point map along `e.symm`. -/
theorem mapEquiv_symm_apply (e : K ≃ₐ[F] L) (P : (W⁄L).toAffine.Point) :
    (mapEquiv W e).symm P = Point.map e.symm.toAlgHom P :=
  by rw [mapEquiv]; rfl

omit [W.IsElliptic] in
/-- Transport along the identity algebra equivalence is the identity. -/
@[simp]
theorem mapEquiv_refl : mapEquiv W (AlgEquiv.refl : K ≃ₐ[F] K) = AddEquiv.refl _ := by
  ext P
  exact Point.map_id P

omit [W.IsElliptic] in
/-- Transport along a composite algebra equivalence is the composite of the transports. -/
@[simp]
theorem mapEquiv_trans (e : K ≃ₐ[F] L) (f : L ≃ₐ[F] M) :
    mapEquiv W (e.trans f) = (mapEquiv W e).trans (mapEquiv W f) := by
  ext P
  exact (Point.map_map e.toAlgHom f.toAlgHom P).symm

omit [W.IsElliptic] in
/-- The inverse of the transport along `e` is the transport along `e.symm`. -/
@[simp]
theorem mapEquiv_symm (e : K ≃ₐ[F] L) :
    (mapEquiv W e).symm = mapEquiv W e.symm :=
  by
    ext P
    rw [mapEquiv_symm_apply, mapEquiv_apply]

end WeierstrassCurve.Affine.Point

end
