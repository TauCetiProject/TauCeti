/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Smooth.Basic
public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Levi.BaseChange

/-!
# Geometry of general-linear weight Levis

For a weight `w : Fin N → ℤ`, the weight Levi in `GL_N` consists of the invertible matrices
whose entries between distinct weight spaces vanish. Its coordinate algebra is the localization
at the determinant of the polynomial algebra on the entries within equal-weight blocks.

This file constructs that presentation directly. The generic block-diagonal matrix supplies the
map from the determinant localization defining `GL_N`; conversely, its surviving entries in the
weight-Levi quotient supply the inverse map. The presentation proves smoothness over an arbitrary
commutative base ring. Over a field it remains a domain after every scalar extension, and hence
the weight Levi is geometrically connected.

## Main declarations

* `TauCeti.GeneralLinear.WeightLeviIndex`: the matrix entries within equal-weight blocks.
* `TauCeti.GeneralLinear.weightLeviCoordinateAlgEquiv`: the localized polynomial presentation.
* `TauCeti.GeneralLinear.instSmoothWeightLeviCoordinateHopfAlgebra`: every weight Levi is smooth.
* `TauCeti.GeneralLinear.geometricallyConnectedCommHopfAlgProperty_weightLeviCoordinateHopfAlgebra`:
  every weight Levi over a field is geometrically connected.

## References

* G. R. Kempf, *Instability in invariant theory*, Annals of Mathematics 108 (1978), §2.
* J. S. Milne, *Algebraic Groups* (2017), Chapters 12--13.

The quotient/evaluation equivalence and its inverse-map proofs, together with the smoothness,
domain, and geometric-connectedness arguments, are adapted from the construction in
`TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Unipotent.Geometry`.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.GeneralLinear

universe u v

noncomputable section

variable (R : Type u) [CommRing R] {N : ℕ}

/-- Pairs indexing matrix entries within one weight space. -/
abbrev WeightLeviIndex (w : Fin N → ℤ) :=
  {ij : Fin N × Fin N // w ij.1 = w ij.2}

/-- The generic matrix whose free entries are those within equal-weight blocks. -/
def weightLeviPolynomialGenericMatrix (w : Fin N → ℤ) :
    Matrix (Fin N) (Fin N) (MvPolynomial (WeightLeviIndex w) R) :=
  fun i j ↦ if h : w i = w j then MvPolynomial.X ⟨(i, j), h⟩ else 0

/-- An entry within one weight block is its corresponding polynomial variable. -/
@[simp]
theorem weightLeviPolynomialGenericMatrix_apply_of_eq (w : Fin N → ℤ)
    {i j : Fin N} (hij : w i = w j) :
    weightLeviPolynomialGenericMatrix R w i j = MvPolynomial.X ⟨(i, j), hij⟩ := by
  simp only [weightLeviPolynomialGenericMatrix, hij, dite_true]

/-- An entry between distinct weight blocks vanishes. -/
@[simp]
theorem weightLeviPolynomialGenericMatrix_apply_of_ne (w : Fin N → ℤ)
    {i j : Fin N} (hij : w i ≠ w j) :
    weightLeviPolynomialGenericMatrix R w i j = 0 := by
  simp only [weightLeviPolynomialGenericMatrix, hij, dite_false]

/-- The localized polynomial presentation of a weight Levi. -/
abbrev WeightLeviCoordinateRing (w : Fin N → ℤ) :=
  Localization.Away (Matrix.det (weightLeviPolynomialGenericMatrix R w))

/-- The generic weight-Levi matrix in its localized coordinate ring. -/
def weightLeviLocalizedGenericMatrix (w : Fin N → ℤ) :
    Matrix (Fin N) (Fin N) (WeightLeviCoordinateRing R w) :=
  (weightLeviPolynomialGenericMatrix R w).map
    (IsScalarTower.toAlgHom R (MvPolynomial (WeightLeviIndex w) R)
      (WeightLeviCoordinateRing R w))

/-- A localized generic entry within one weight block is the corresponding localized variable. -/
@[simp]
theorem weightLeviLocalizedGenericMatrix_apply_of_eq (w : Fin N → ℤ)
    {i j : Fin N} (hij : w i = w j) :
    weightLeviLocalizedGenericMatrix R w i j =
      IsScalarTower.toAlgHom R (MvPolynomial (WeightLeviIndex w) R)
        (WeightLeviCoordinateRing R w) (MvPolynomial.X ⟨(i, j), hij⟩) := by
  simp [weightLeviLocalizedGenericMatrix,
    weightLeviPolynomialGenericMatrix_apply_of_eq R w hij]

/-- A localized generic entry between distinct weight blocks vanishes. -/
@[simp]
theorem weightLeviLocalizedGenericMatrix_apply_of_ne (w : Fin N → ℤ)
    {i j : Fin N} (hij : w i ≠ w j) :
    weightLeviLocalizedGenericMatrix R w i j = 0 := by
  simp [weightLeviLocalizedGenericMatrix,
    weightLeviPolynomialGenericMatrix_apply_of_ne R w hij]

/-- The determinant of the localized generic weight-Levi matrix is a unit. -/
theorem isUnit_det_weightLeviLocalizedGenericMatrix (w : Fin N → ℤ) :
    IsUnit (Matrix.det (weightLeviLocalizedGenericMatrix R w)) := by
  rw [weightLeviLocalizedGenericMatrix, ← AlgHom.mapMatrix_apply, ← AlgHom.map_det]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- Block-diagonal evaluation on the bundled coordinate algebra of `GL_N`. -/
private def weightLeviAmbientToCoordinateRing (w : Fin N → ℤ) :
    coordinateHopfAlgebra R N →ₐ[R] WeightLeviCoordinateRing R w :=
  (generalLinearToPoint N (Matrix.GeneralLinearGroup.mk''
    (weightLeviLocalizedGenericMatrix R w)
    (isUnit_det_weightLeviLocalizedGenericMatrix R w))).ofConv

private theorem weightLeviAmbientToCoordinateRing_genericMatrix_apply
    (w : Fin N → ℤ) (i j : Fin N) :
    weightLeviAmbientToCoordinateRing R w ((genericMatrix R N) i j) =
      weightLeviLocalizedGenericMatrix R w i j := by
  simp [genericMatrix_apply, weightLeviAmbientToCoordinateRing]

private theorem weightLeviDefiningIdeal_le_ker_ambientToCoordinateRing
    (w : Fin N → ℤ) :
    (weightLeviDefiningHopfIdeal R w).toIdeal ≤
      RingHom.ker (weightLeviAmbientToCoordinateRing R w).toRingHom :=
  weightLeviDefiningHopfIdeal_toIdeal_le_ker R w _ fun i j hij ↦ by
    rw [← genericMatrix_apply, weightLeviAmbientToCoordinateRing_genericMatrix_apply,
      weightLeviLocalizedGenericMatrix_apply_of_ne R w hij]

/-- The weight-Levi quotient maps to its localized block coordinates. -/
private def weightLeviQuotientToCoordinateRing (w : Fin N → ℤ) :
    weightLeviCoordinateHopfAlgebra R w →ₐ[R] WeightLeviCoordinateRing R w :=
  Ideal.Quotient.liftₐ _ (weightLeviAmbientToCoordinateRing R w)
    (weightLeviDefiningIdeal_le_ker_ambientToCoordinateRing R w)

private theorem weightLeviQuotientToCoordinateRing_mk_genericMatrix_apply
    (w : Fin N → ℤ) (i j : Fin N) :
    weightLeviQuotientToCoordinateRing R w
        (Ideal.Quotient.mkₐ R (weightLeviDefiningHopfIdeal R w).toIdeal
          ((genericMatrix R N) i j)) =
      weightLeviLocalizedGenericMatrix R w i j := by
  have hcomp := Ideal.Quotient.liftₐ_comp
    (weightLeviDefiningHopfIdeal R w).toIdeal
    (weightLeviAmbientToCoordinateRing R w)
    (weightLeviDefiningIdeal_le_ker_ambientToCoordinateRing R w)
  exact (DFunLike.congr_fun hcomp ((genericMatrix R N) i j)).trans
    (weightLeviAmbientToCoordinateRing_genericMatrix_apply R w i j)

/-- Send each block coordinate to the corresponding surviving quotient-matrix entry. -/
private def weightLeviPolynomialToQuotient (w : Fin N → ℤ) :
    MvPolynomial (WeightLeviIndex w) R →ₐ[R] weightLeviCoordinateHopfAlgebra R w :=
  MvPolynomial.aeval fun ij ↦
    Ideal.Quotient.mkₐ R (weightLeviDefiningHopfIdeal R w).toIdeal
      ((genericMatrix R N) ij.1.1 ij.1.2)

private theorem weightLeviPolynomialToQuotient_determinant_isUnit (w : Fin N → ℤ) :
    IsUnit (weightLeviPolynomialToQuotient R w
      (Matrix.det (weightLeviPolynomialGenericMatrix R w))) := by
  rw [AlgHom.map_det]
  have hmatrix :
      (weightLeviPolynomialGenericMatrix R w).map
          (weightLeviPolynomialToQuotient R w) =
        (genericMatrix R N).map
          (Ideal.Quotient.mkₐ R (weightLeviDefiningHopfIdeal R w).toIdeal) := by
    ext i j
    by_cases hij : w i = w j
    · simp [weightLeviPolynomialGenericMatrix_apply_of_eq R w hij,
        weightLeviPolynomialToQuotient]
    · rw [Matrix.map_apply, weightLeviPolynomialGenericMatrix_apply_of_ne R w hij,
        map_zero, Matrix.map_apply]
      simpa only [Ideal.Quotient.mkₐ_eq_mk, genericMatrix_apply] using
        (weightLeviQuotient_mk_genericMatrix_apply_of_ne R w hij).symm
  -- `AlgHom.map_det` exposes `mapMatrix`, whereas the pointwise matrix map is the stable form
  -- used by `hmatrix`.
  change IsUnit (Matrix.det ((weightLeviPolynomialGenericMatrix R w).map
    (weightLeviPolynomialToQuotient R w)))
  rw [hmatrix]
  simpa only [← AlgHom.mapMatrix_apply, ← AlgHom.map_det] using
    (isUnit_det_genericMatrix R N).map
      (Ideal.Quotient.mkₐ R (weightLeviDefiningHopfIdeal R w).toIdeal)

/-- Extend the quotient-valued block coordinates across their determinant localization. -/
private def weightLeviCoordinateRingToQuotient (w : Fin N → ℤ) :
    WeightLeviCoordinateRing R w →ₐ[R] weightLeviCoordinateHopfAlgebra R w :=
  IsLocalization.Away.liftAlgHom
    (Matrix.det (weightLeviPolynomialGenericMatrix R w))
    (weightLeviPolynomialToQuotient_determinant_isUnit R w)

private theorem weightLeviCoordinateRingToQuotient_coordinateRingMap
    (w : Fin N → ℤ) (x : MvPolynomial (WeightLeviIndex w) R) :
    weightLeviCoordinateRingToQuotient R w
        (IsScalarTower.toAlgHom R (MvPolynomial (WeightLeviIndex w) R)
          (WeightLeviCoordinateRing R w) x) =
      weightLeviPolynomialToQuotient R w x := by
  simp [weightLeviCoordinateRingToQuotient]

private theorem weightLeviQuotientToCoordinateRing_comp_coordinateRingToQuotient
    (w : Fin N → ℤ) :
    (weightLeviQuotientToCoordinateRing R w).comp
        (weightLeviCoordinateRingToQuotient R w) = AlgHom.id R _ := by
  apply IsLocalization.algHom_ext
    (Submonoid.powers (Matrix.det (weightLeviPolynomialGenericMatrix R w)))
  apply MvPolynomial.algHom_ext
  intro ij
  simp only [AlgHom.comp_apply, AlgHom.id_apply]
  -- Localization extensionality inserts the canonical algebra map; expose it as the scalar-tower
  -- algebra hom before applying the computation theorem.
  change weightLeviQuotientToCoordinateRing R w
      (weightLeviCoordinateRingToQuotient R w
        (IsScalarTower.toAlgHom R (MvPolynomial (WeightLeviIndex w) R)
          (WeightLeviCoordinateRing R w) (MvPolynomial.X ij))) =
    IsScalarTower.toAlgHom R (MvPolynomial (WeightLeviIndex w) R)
      (WeightLeviCoordinateRing R w) (MvPolynomial.X ij)
  rw [weightLeviCoordinateRingToQuotient_coordinateRingMap,
    weightLeviPolynomialToQuotient, MvPolynomial.aeval_X,
    weightLeviQuotientToCoordinateRing_mk_genericMatrix_apply,
    weightLeviLocalizedGenericMatrix, Matrix.map_apply,
    weightLeviPolynomialGenericMatrix_apply_of_eq R w ij.2]

private theorem weightLeviCoordinateRingToQuotient_comp_quotientToCoordinateRing
    (w : Fin N → ℤ) :
    (weightLeviCoordinateRingToQuotient R w).comp
        (weightLeviQuotientToCoordinateRing R w) = AlgHom.id R _ := by
  apply Ideal.Quotient.algHom_ext
  apply coordinateHopfAlgebra_algHom_ext R N
  intro i j
  rw [← genericMatrix_apply]
  simp only [AlgHom.comp_apply, AlgHom.id_apply]
  rw [weightLeviQuotientToCoordinateRing_mk_genericMatrix_apply]
  by_cases hij : w i = w j
  · rw [weightLeviLocalizedGenericMatrix, Matrix.map_apply,
      weightLeviPolynomialGenericMatrix_apply_of_eq R w hij,
      weightLeviCoordinateRingToQuotient_coordinateRingMap,
      weightLeviPolynomialToQuotient, MvPolynomial.aeval_X]
  · rw [weightLeviLocalizedGenericMatrix, Matrix.map_apply,
      weightLeviPolynomialGenericMatrix_apply_of_ne R w hij, map_zero, map_zero]
    simpa only [Ideal.Quotient.mkₐ_eq_mk, genericMatrix_apply] using
      (weightLeviQuotient_mk_genericMatrix_apply_of_ne R w hij).symm

/-- The weight-Levi coordinate algebra is the determinant localization of the polynomial algebra
on entries lying within equal-weight blocks. -/
def weightLeviCoordinateAlgEquiv (w : Fin N → ℤ) :
    weightLeviCoordinateHopfAlgebra R w ≃ₐ[R] WeightLeviCoordinateRing R w :=
  AlgEquiv.ofAlgHom
    (weightLeviQuotientToCoordinateRing R w)
    (weightLeviCoordinateRingToQuotient R w)
    (weightLeviQuotientToCoordinateRing_comp_coordinateRingToQuotient R w)
    (weightLeviCoordinateRingToQuotient_comp_quotientToCoordinateRing R w)

/-- The localized polynomial presentation sends a quotient matrix entry to the corresponding
entry of the generic block-diagonal matrix. -/
@[simp]
theorem weightLeviCoordinateAlgEquiv_mk_genericMatrix_apply
    (w : Fin N → ℤ) (i j : Fin N) :
    weightLeviCoordinateAlgEquiv R w
        (Ideal.Quotient.mk (weightLeviDefiningHopfIdeal R w).toIdeal
          (coordinateHopfAlgebraAlgEquiv R N
            (coordinateRingMap R N (MvPolynomial.X (i, j))))) =
      weightLeviLocalizedGenericMatrix R w i j := by
  -- Unfold the presentation wrapper and normalize the quotient matrix entry.
  simpa only [weightLeviCoordinateAlgEquiv, AlgEquiv.ofAlgHom_apply,
    Ideal.Quotient.mkₐ_eq_mk, genericMatrix_apply] using
    weightLeviQuotientToCoordinateRing_mk_genericMatrix_apply R w i j

/-- The inverse localized-polynomial presentation sends a block variable to its surviving
quotient-matrix entry. -/
@[simp]
theorem weightLeviCoordinateAlgEquiv_symm_algebraMap_X
    (w : Fin N → ℤ) (ij : WeightLeviIndex w) :
    (weightLeviCoordinateAlgEquiv R w).symm
        (algebraMap (MvPolynomial (WeightLeviIndex w) R)
          (WeightLeviCoordinateRing R w) (MvPolynomial.X ij)) =
      Ideal.Quotient.mkₐ R (weightLeviDefiningHopfIdeal R w).toIdeal
        ((genericMatrix R N) ij.1.1 ij.1.2) := by
  apply (weightLeviCoordinateAlgEquiv R w).injective
  rw [AlgEquiv.apply_symm_apply, genericMatrix_apply, Ideal.Quotient.mkₐ_eq_mk,
    weightLeviCoordinateAlgEquiv_mk_genericMatrix_apply,
    weightLeviLocalizedGenericMatrix_apply_of_eq R w ij.2]
  rw [IsScalarTower.toAlgHom_apply]

/-- The weight-Levi coordinate algebra is smooth over its base ring. -/
instance instSmoothWeightLeviCoordinateHopfAlgebra (w : Fin N → ℤ) :
    Algebra.Smooth R (weightLeviCoordinateHopfAlgebra R w) := by
  let _ : Algebra.Smooth R (MvPolynomial (WeightLeviIndex w) R) :=
    ⟨inferInstance, inferInstance⟩
  let _ : Algebra.Smooth R (WeightLeviCoordinateRing R w) :=
    ⟨inferInstance, inferInstance⟩
  exact Algebra.Smooth.of_equiv (weightLeviCoordinateAlgEquiv R w).symm

/-- The determinant of the generic block-diagonal matrix is a nonzero polynomial over a
nontrivial base ring. -/
theorem weightLeviPolynomialGenericMatrix_det_ne_zero
    (R : Type u) [CommRing R] [Nontrivial R] (w : Fin N → ℤ) :
    Matrix.det (weightLeviPolynomialGenericMatrix R w) ≠ 0 := by
  intro hzero
  let e : MvPolynomial (WeightLeviIndex w) R →ₐ[R] R :=
    MvPolynomial.aeval fun ij ↦ if ij.1.1 = ij.1.2 then 1 else 0
  have hmatrix : (weightLeviPolynomialGenericMatrix R w).map e = 1 := by
    ext i j
    by_cases hij : w i = w j
    · rw [Matrix.map_apply, weightLeviPolynomialGenericMatrix_apply_of_eq R w hij]
      simp [e, Matrix.one_apply]
    · rw [Matrix.map_apply, weightLeviPolynomialGenericMatrix_apply_of_ne R w hij,
        map_zero]
      have hne : i ≠ j := fun h ↦ hij (congrArg w h)
      simp [hne]
  have hdet := congrArg e hzero
  rw [map_zero, AlgHom.map_det, AlgHom.mapMatrix_apply, hmatrix, Matrix.det_one] at hdet
  exact one_ne_zero hdet

/-- Over an integral domain, the weight-Levi coordinate algebra is an integral domain. -/
instance instIsDomainWeightLeviCoordinateHopfAlgebra
    (R : Type u) [CommRing R] [IsDomain R] (w : Fin N → ℤ) :
    IsDomain (weightLeviCoordinateHopfAlgebra R w) := by
  let _ : IsDomain (WeightLeviCoordinateRing R w) :=
    Localization.Away.isDomain (weightLeviPolynomialGenericMatrix_det_ne_zero R w)
  exact (weightLeviCoordinateAlgEquiv R w).toRingEquiv.isDomain_iff.mpr inferInstance

/-- The weight Levi is geometrically connected over every field. -/
theorem geometricallyConnectedCommHopfAlgProperty_weightLeviCoordinateHopfAlgebra
    (k : Type u) [Field k] (w : Fin N → ℤ) :
    geometricallyConnectedCommHopfAlgProperty k
      (weightLeviCoordinateHopfAlgebra k w) := by
  rw [geometricallyConnectedCommHopfAlgProperty_iff]
  intro K _ _
  let e := (Algebra.TensorProduct.comm k
    (weightLeviCoordinateHopfAlgebra k w) K).toRingEquiv.trans (CommHopfAlgCat.ofIso
      (weightLeviCoordinateHopfAlgebraBaseChangeIso k K w)).toAlgEquiv.toRingEquiv
  exact (PrimeSpectrum.homeomorphOfRingEquiv e).connectedSpace_iff.mpr inferInstance

end

end TauCeti.GeneralLinear
