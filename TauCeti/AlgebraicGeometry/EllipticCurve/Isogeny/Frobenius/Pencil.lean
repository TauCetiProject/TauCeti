/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Differential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Torsion
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Differential
import TauCeti.LinearAlgebra.Matrix.QuadraticFormCongruence

/-!
# Degrees of the Frobenius pencil

Let `W` be an elliptic curve over a finite field `F`, and let `π` be its Frobenius over an
extension `K`. The endomorphism `r • π - s • id` pulls the invariant differential back to
`-s • ω`. Consequently it is nonzero and separable whenever `s` is nonzero in `K`.

Over a separably closed extension, the degree of the pencil is the integral quadratic form
`#F * r² - (#F + 1 - deg (id - π)) * r * s + s²`, for all integers `r` and `s`. This is the
degree-form input to the Hasse bound.

## Main results

* `TauCeti.Isogeny.Hom.zsmul_ofIsogeny_baseChangeFrobenius_sub_zsmul_id_ne_zero`:
  the pencil is nonzero when `s` is nonzero in the field.
* `TauCeti.Isogeny.Hom.isSeparable_toIsogeny_zsmul_ofIsogeny_baseChangeFrobenius_sub_zsmul_id_iff`:
  a nonzero pencil is separable exactly when `s` is nonzero in the field.
* `TauCeti.Isogeny.Hom.degree_zsmul_ofIsogeny_baseChangeFrobenius_sub_zsmul_id`:
  the integral quadratic degree formula over a separably closed extension.

## Provenance

The AINTLIB `HasseWeil` project (Chris Birkbeck, Apache 2.0, commit
`513e83879e2f8cbc626eb9e04d660e92be16ccba`) has conditional degree-form counterparts in
`DegreeQuadraticForm.lean` (dual-isogeny witnesses) and `WeilPairing/Reduction.lean`
(`deg_eq_of_frobMatrix_data` / `deg_eq_of_frob_det_data`, assuming per-prime matrix data).
The latter reduction is ported in `TauCeti.LinearAlgebra.Matrix.QuadraticFormCongruence`.
Here the pencil is formed in the morphism group of function-field isogenies, and its
matrix data is proved, so the degree formula needs no additional witness or matrix-data
hypotheses beyond the stated field and coefficient conditions.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.5, III.8 and V.1.
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine

namespace TauCeti.Isogeny

variable {F K : Type*} [Field F] [Finite F] [Field K] [Algebra F K]
  (W : WeierstrassCurve.Affine F)

namespace Hom

variable [W.IsElliptic]

/-- If `s` is nonzero in the field, the Frobenius pencil `r π - s` is nonzero. -/
theorem zsmul_ofIsogeny_baseChangeFrobenius_sub_zsmul_id_ne_zero (r s : ℤ) (hs : (s : K) ≠ 0) :
    r • ofIsogeny (baseChangeFrobenius K W) - s • id (W⁄K).toAffine ≠ 0 := by
  apply zsmul_sub_zsmul_id_ne_zero_of_pullbackDifferential_eq_zero _ r s hs
  rw [pullbackDifferential_ofIsogeny,
    pullbackDifferential_baseChangeFrobenius_invariantDifferential]

/-- A nonzero Frobenius pencil `r π - s` is separable exactly when `s` is nonzero in the field. -/
@[simp]
theorem isSeparable_toIsogeny_zsmul_ofIsogeny_baseChangeFrobenius_sub_zsmul_id_iff (r s : ℤ)
    (h : r • ofIsogeny (baseChangeFrobenius K W) - s • id (W⁄K).toAffine ≠ 0) :
    Algebra.IsSeparable (toIsogeny h).fieldPullback.fieldRange (W⁄K).toAffine.FunctionField ↔
      (s : K) ≠ 0 := by
  apply isSeparable_toIsogeny_zsmul_sub_zsmul_id_iff_of_pullbackDifferential_eq_zero _ r s h
  rw [pullbackDifferential_ofIsogeny,
    pullbackDifferential_baseChangeFrobenius_invariantDifferential]

variable [IsSepClosed K]

/-- Over a separably closed extension of the finite base, the degree of `r π - s`
is the integral quadratic form with middle coefficient `#F + 1 - deg (id - π)`. -/
theorem degree_zsmul_ofIsogeny_baseChangeFrobenius_sub_zsmul_id (r s : ℤ) :
    ((r • ofIsogeny (baseChangeFrobenius K W) - s • id (W⁄K).toAffine).degree : ℤ) =
      (Nat.card F : ℤ) * r ^ 2 -
        ((Nat.card F : ℤ) + 1 - (id (W⁄K).toAffine -
          ofIsogeny (baseChangeFrobenius K W)).degree) * (r * s) + s ^ 2 := by
  classical
  apply TauCeti.Matrix.eq_quadratic_form_of_det_det_one_sub (p := ringChar K)
  intro ℓ hℓ hℓne
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hℓK : (ℓ : K) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime K hℓ hℓne.symm
  obtain ⟨b⟩ := WeierstrassCurve.nonempty_basis_torsionBy (W⁄K) ℓ hℓK
  let π := ofIsogeny (baseChangeFrobenius K W)
  let M := LinearMap.toMatrix b b (π.torsionLinearMap ℓ)
  have hmatrix (a c : ℤ) :
      (a : ZMod ℓ) • M - (c : ZMod ℓ) • 1 =
        LinearMap.toMatrix b b ((a • π - c • id (W⁄K).toAffine).torsionLinearMap ℓ) := by
    simp only [torsionLinearMap_sub, torsionLinearMap_zsmul, torsionLinearMap_id,
      _root_.map_sub, _root_.map_zsmul, LinearMap.toMatrix_id, Int.cast_smul_eq_zsmul, M]
  refine ⟨M, ?_, ?_, ?_⟩
  · rw [LinearMap.det_toMatrix]
    simpa only [Int.cast_natCast, π] using
      det_torsionLinearMap_ofIsogeny_baseChangeFrobenius W hℓK
  · have hone : (1 - M) =
        LinearMap.toMatrix b b ((id (W⁄K).toAffine - π).torsionLinearMap ℓ) := by
      simpa only [Int.cast_neg, Int.cast_one, neg_one_smul, neg_sub_neg] using hmatrix (-1) (-1)
    rw [hone, LinearMap.det_toMatrix, det_torsionLinearMap hℓK]
    simp only [sub_sub_cancel, Int.cast_natCast, π]
  · rw [hmatrix, LinearMap.det_toMatrix, det_torsionLinearMap hℓK, Int.cast_natCast]

end Hom

end TauCeti.Isogeny

end
