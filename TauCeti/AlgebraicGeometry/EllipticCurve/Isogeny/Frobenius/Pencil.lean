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

Over a separably closed algebraic extension, the Weil pairing identifies the determinant of
this pencil on prime-to-characteristic torsion with its degree. Comparing these determinants
at every prime other than the characteristic gives the integral quadratic degree formula,
with middle coefficient `#F + 1 - deg (id - π)`. This is the algebraic input to the Hasse bound;
the identification of `deg (id - π)` with the rational point count is a separate step.

The proof combines `Hom.det_torsionLinearMap_ofIsogeny` with the Frobenius determinant theorem
`Hom.det_torsionLinearMap_ofIsogeny_baseChangeFrobenius`, then applies
`TauCeti.Matrix.eq_quadratic_form_of_det_det_one_sub`. The matrices and their bases remain local
to the proof; the result is stated entirely in terms of the intrinsic endomorphisms and degrees.

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

/-- The Frobenius pencil `r π - s` pulls the invariant differential back to `-s • ω`. -/
theorem pullbackDifferential_zsmul_baseChangeFrobenius_sub_zsmul_id (r s : ℤ) :
    (r • ofIsogeny (baseChangeFrobenius K W) - s • id (W⁄K).toAffine).pullbackDifferential
      (invariantDifferential (W⁄K).toAffine) = -s • invariantDifferential (W⁄K).toAffine := by
  simp only [pullbackDifferential_sub_invariantDifferential,
    pullbackDifferential_zsmul_invariantDifferential, pullbackDifferential_ofIsogeny,
    pullbackDifferential_baseChangeFrobenius_invariantDifferential,
    pullbackDifferential_id, LinearMap.id_apply, smul_zero, zero_sub, neg_smul]

/-- If `s` is nonzero in the field, the Frobenius pencil `r π - s` is nonzero. -/
theorem zsmul_baseChangeFrobenius_sub_zsmul_id_ne_zero (r s : ℤ) (hs : (s : K) ≠ 0) :
    r • ofIsogeny (baseChangeFrobenius K W) - s • id (W⁄K).toAffine ≠ 0 := by
  intro h
  have hω := pullbackDifferential_zsmul_baseChangeFrobenius_sub_zsmul_id (K := K) W r s
  rw [h, pullbackDifferential_zero, LinearMap.zero_apply] at hω
  exact hs ((zsmul_invariantDifferential_eq_zero_iff (W⁄K).toAffine s).mp (by
    simpa using hω.symm))

/-- A nonzero Frobenius pencil `r π - s` is separable exactly when `s` is nonzero in the field. -/
@[simp]
theorem isSeparable_toIsogeny_zsmul_baseChangeFrobenius_sub_zsmul_id_iff (r s : ℤ)
    (h : r • ofIsogeny (baseChangeFrobenius K W) - s • id (W⁄K).toAffine ≠ 0) :
    Algebra.IsSeparable (toIsogeny h).fieldPullback.fieldRange (W⁄K).toAffine.FunctionField ↔
      (s : K) ≠ 0 := by
  rw [isSeparable_iff_pullbackDifferential_ne_zero,
    ← pullbackDifferential_ofIsogeny, ofIsogeny_toIsogeny,
    pullbackDifferential_zsmul_baseChangeFrobenius_sub_zsmul_id]
  simp [zsmul_invariantDifferential_eq_zero_iff]

section Torsion

variable [DecidableEq K] [IsSepClosed K]

/-- The determinant of a Frobenius pencil on invertible torsion is its degree,
when the pencil's identity coefficient is nonzero in the field. -/
theorem det_torsionLinearMap_zsmul_baseChangeFrobenius_sub_zsmul_id
    {N : ℕ} [NeZero N] (hN : (N : K) ≠ 0) (r s : ℤ) (hs : (s : K) ≠ 0) :
    LinearMap.det
      ((r • ofIsogeny (baseChangeFrobenius K W) - s • id (W⁄K).toAffine).torsionLinearMap N) =
        (r • ofIsogeny (baseChangeFrobenius K W) - s • id (W⁄K).toAffine).degree := by
  let h := zsmul_baseChangeFrobenius_sub_zsmul_id_ne_zero W r s hs
  have := (isSeparable_toIsogeny_zsmul_baseChangeFrobenius_sub_zsmul_id_iff W r s h).2 hs
  simpa only [ofIsogeny_toIsogeny, ← degree_ofIsogeny] using
    det_torsionLinearMap_ofIsogeny hN (toIsogeny h)

end Torsion

variable [IsSepClosed K] [Algebra.IsAlgebraic F K]

/-- Over a separably closed algebraic extension of the finite base, the degree of `r π - s`
is the integral quadratic form with middle coefficient `#F + 1 - deg (id - π)`, provided
`s` is nonzero in the field. No preservation-of-degree hypothesis is assumed. -/
theorem degree_zsmul_baseChangeFrobenius_sub_zsmul_id (r s : ℤ) (hs : (s : K) ≠ 0) :
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
      map_sub, map_zsmul, LinearMap.toMatrix_id, Int.cast_smul_eq_zsmul, M]
  refine ⟨M, ?_, ?_, ?_⟩
  · rw [LinearMap.det_toMatrix]
    simpa only [Int.cast_natCast, π] using
      det_torsionLinearMap_ofIsogeny_baseChangeFrobenius W hℓK
  · have hdet := det_torsionLinearMap_zsmul_baseChangeFrobenius_sub_zsmul_id W
      hℓK (-1) (-1) (by simp)
    have hone : (1 - M) =
        LinearMap.toMatrix b b ((id (W⁄K).toAffine - π).torsionLinearMap ℓ) := by
      simpa only [Int.cast_neg, Int.cast_one, neg_one_smul, neg_sub_neg] using hmatrix (-1) (-1)
    rw [hone, LinearMap.det_toMatrix]
    simpa only [neg_one_zsmul, neg_sub_neg, Int.cast_sub, Int.cast_add, Int.cast_one,
      Int.cast_natCast, sub_sub_cancel, π] using hdet
  · rw [hmatrix, LinearMap.det_toMatrix]
    simpa only [Int.cast_natCast, π] using
      det_torsionLinearMap_zsmul_baseChangeFrobenius_sub_zsmul_id W hℓK r s hs

end Hom

end TauCeti.Isogeny

end
