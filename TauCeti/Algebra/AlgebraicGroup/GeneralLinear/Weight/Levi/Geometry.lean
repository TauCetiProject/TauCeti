/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Smooth.Basic
public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Levi.Basic

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
* `TauCeti.GeneralLinear.weightLeviCoordinateHopfAlgebraBaseChangeRingEquiv`: compatibility of
  the presentation with scalar extension.
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

/-- In the weight-Levi quotient, an ambient entry between different weight blocks is zero. -/
@[simp]
theorem weightLeviQuotient_mk_genericMatrix_apply_of_ne (w : Fin N → ℤ)
    {i j : Fin N} (hij : w i ≠ w j) :
    Ideal.Quotient.mk (weightLeviDefiningHopfIdeal R w).toIdeal
      (coordinateHopfAlgebraAlgEquiv R N
        (coordinateRingMap R N (MvPolynomial.X (i, j)))) = 0 := by
  rw [← genericMatrix_apply, Ideal.Quotient.eq_zero_iff_mem, weightLeviDefiningHopfIdeal_def,
    HopfIdeal.sup_toIdeal, weightParabolicDefiningHopfIdeal_toIdeal,
    weightParabolicDefiningHopfIdeal_toIdeal]
  rcases lt_or_gt_of_ne hij with hij | hji
  · apply Ideal.mem_sup_left
    rw [genericMatrix_apply]
    exact Ideal.subset_span (X_mem_weightParabolicRelationSet R w hij)
  · apply Ideal.mem_sup_right
    rw [genericMatrix_apply]
    exact Ideal.subset_span (X_mem_weightParabolicRelationSet R (-w) (by simpa using hji))

/-- Evaluate the ambient matrix-polynomial coordinates at the generic block-diagonal matrix. -/
private def weightLeviPolynomialEvaluation (w : Fin N → ℤ) :
    MatrixMonoid.CoordinateRing R N →ₐ[R] WeightLeviCoordinateRing R w :=
  MvPolynomial.aeval fun ij ↦ weightLeviLocalizedGenericMatrix R w ij.1 ij.2

private theorem weightLeviPolynomialEvaluation_determinant_isUnit (w : Fin N → ℤ) :
    IsUnit (weightLeviPolynomialEvaluation R w
      (Matrix.det (Matrix.mvPolynomialX (Fin N) (Fin N) R))) := by
  rw [weightLeviPolynomialEvaluation, AlgHom.map_det,
    Matrix.mvPolynomialX_mapMatrix_aeval]
  exact isUnit_det_weightLeviLocalizedGenericMatrix R w

/-- Extend block-diagonal evaluation across the determinant localization defining `GL_N`. -/
private def weightLeviLocalizedEvaluation (w : Fin N → ℤ) :
    CoordinateRing R N →ₐ[R] WeightLeviCoordinateRing R w :=
  IsLocalization.Away.liftAlgHom
    (Matrix.det (Matrix.mvPolynomialX (Fin N) (Fin N) R))
    (weightLeviPolynomialEvaluation_determinant_isUnit R w)

private theorem weightLeviLocalizedEvaluation_coordinateRingMap
    (w : Fin N → ℤ) (x : MatrixMonoid.CoordinateRing R N) :
    weightLeviLocalizedEvaluation R w (coordinateRingMap R N x) =
      weightLeviPolynomialEvaluation R w x := by
  rw [coordinateRingMap_apply]
  simp [-coordinateRingMap_apply, weightLeviLocalizedEvaluation]

/-- Block-diagonal evaluation on the bundled coordinate algebra of `GL_N`. -/
private def weightLeviAmbientToCoordinateRing (w : Fin N → ℤ) :
    coordinateHopfAlgebra R N →ₐ[R] WeightLeviCoordinateRing R w :=
  (weightLeviLocalizedEvaluation R w).comp
    (coordinateHopfAlgebraAlgEquiv R N).symm.toAlgHom

private theorem weightLeviAmbientToCoordinateRing_genericMatrix_apply
    (w : Fin N → ℤ) (i j : Fin N) :
    weightLeviAmbientToCoordinateRing R w ((genericMatrix R N) i j) =
      weightLeviLocalizedGenericMatrix R w i j := by
  calc
    _ = weightLeviLocalizedEvaluation R w
        ((coordinateHopfAlgebraAlgEquiv R N).symm
          (coordinateHopfAlgebraAlgEquiv R N
            (coordinateRingMap R N (MvPolynomial.X (i, j))))) := by
      rw [genericMatrix_apply]
      rfl
    _ = weightLeviLocalizedEvaluation R w
        (coordinateRingMap R N (MvPolynomial.X (i, j))) := by simp
    _ = weightLeviPolynomialEvaluation R w (MvPolynomial.X (i, j)) :=
      weightLeviLocalizedEvaluation_coordinateRingMap R w _
    _ = _ := by simp [weightLeviPolynomialEvaluation, weightLeviLocalizedGenericMatrix]

private theorem weightLeviDefiningIdeal_le_ker_ambientToCoordinateRing
    (w : Fin N → ℤ) :
    (weightLeviDefiningHopfIdeal R w).toIdeal ≤
      RingHom.ker (weightLeviAmbientToCoordinateRing R w).toRingHom := by
  rw [weightLeviDefiningHopfIdeal_def, HopfIdeal.sup_toIdeal,
    weightParabolicDefiningHopfIdeal_toIdeal,
    weightParabolicDefiningHopfIdeal_toIdeal]
  apply sup_le <;> rw [Ideal.span_le]
  · intro x hx
    obtain ⟨i, j, hij, rfl⟩ := (mem_weightParabolicRelationSet_iff R w _).mp hx
    rw [← genericMatrix_apply]
    rw [SetLike.mem_coe, RingHom.mem_ker]
    -- The kernel goal exposes the underlying ring hom, while the computation theorem is stated
    -- for the bundled algebra hom.
    change weightLeviAmbientToCoordinateRing R w ((genericMatrix R N) i j) = 0
    rw [weightLeviAmbientToCoordinateRing_genericMatrix_apply,
      weightLeviLocalizedGenericMatrix, Matrix.map_apply,
      weightLeviPolynomialGenericMatrix_apply_of_ne R w hij.ne]
    exact map_zero _
  · intro x hx
    obtain ⟨i, j, hij, rfl⟩ := (mem_weightParabolicRelationSet_iff R (-w) _).mp hx
    have hne : w i ≠ w j := by
      intro h
      simp [h] at hij
    rw [← genericMatrix_apply]
    rw [SetLike.mem_coe, RingHom.mem_ker]
    -- As above, cross the ring-hom projection before using the algebra-hom computation theorem.
    change weightLeviAmbientToCoordinateRing R w ((genericMatrix R N) i j) = 0
    rw [weightLeviAmbientToCoordinateRing_genericMatrix_apply,
      weightLeviLocalizedGenericMatrix, Matrix.map_apply,
      weightLeviPolynomialGenericMatrix_apply_of_ne R w hne]
    exact map_zero _

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
  apply AlgHom.ext
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mkₐ_surjective R
    (weightLeviDefiningHopfIdeal R w).toIdeal x
  have hcomp :
      ((weightLeviCoordinateRingToQuotient R w).comp
        (weightLeviQuotientToCoordinateRing R w)).comp
          (Ideal.Quotient.mkₐ R (weightLeviDefiningHopfIdeal R w).toIdeal) =
      (AlgHom.id R _).comp
          (Ideal.Quotient.mkₐ R (weightLeviDefiningHopfIdeal R w).toIdeal) := by
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
  exact DFunLike.congr_fun hcomp y

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

private theorem weightLeviPolynomialGenericMatrix_det_ne_zero
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

/-- Scalar extension of the localized polynomial presentation is the corresponding presentation
over the extended base ring. -/
def weightLeviCoordinateRingBaseChangeAlgEquiv
    (k : Type u) (K : Type v) [CommRing k] [CommRing K] [Algebra k K] (w : Fin N → ℤ) :
    K ⊗[k] WeightLeviCoordinateRing k w ≃ₐ[K] WeightLeviCoordinateRing K w := by
  let p : K ⊗[k] MvPolynomial (WeightLeviIndex w) k ≃ₐ[K]
      MvPolynomial (WeightLeviIndex w) K := MvPolynomial.algebraTensorAlgEquiv k K
  have hp : p (1 ⊗ₜ[k] Matrix.det (weightLeviPolynomialGenericMatrix k w)) =
      Matrix.det (weightLeviPolynomialGenericMatrix K w) := by
    -- The local name `p` is opaque to rewriting; expose the standard polynomial base-change map
    -- so its pure-tensor computation lemma applies.
    change MvPolynomial.algebraTensorAlgEquiv k K
      (1 ⊗ₜ[k] Matrix.det (weightLeviPolynomialGenericMatrix k w)) = _
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul, RingHom.map_det]
    congr 1
    ext i j
    by_cases hij : w i = w j
    · simp [weightLeviPolynomialGenericMatrix_apply_of_eq, hij]
    · simp [weightLeviPolynomialGenericMatrix_apply_of_ne, hij]
  exact (IsLocalization.Away.tensorProductEquivTMulRight k K
    (Matrix.det (weightLeviPolynomialGenericMatrix k w))
      (WeightLeviCoordinateRing k w)).trans <|
    IsLocalization.algEquivOfAlgEquiv _ _ p (by
      rw [Submonoid.map_powers, hp])

/-- Base change sends a scalar tensored with a localized polynomial coordinate to that scalar
times the same polynomial with its coefficients extended to the new base. -/
@[simp]
theorem weightLeviCoordinateRingBaseChangeAlgEquiv_tmul_algebraMap
    (k : Type u) (K : Type v) [CommRing k] [CommRing K] [Algebra k K] (w : Fin N → ℤ)
    (s : K) (p : MvPolynomial (WeightLeviIndex w) k) :
    weightLeviCoordinateRingBaseChangeAlgEquiv k K w
        (s ⊗ₜ[k] algebraMap (MvPolynomial (WeightLeviIndex w) k)
          (WeightLeviCoordinateRing k w) p) =
      s • algebraMap (MvPolynomial (WeightLeviIndex w) K)
        (WeightLeviCoordinateRing K w) (MvPolynomial.map (algebraMap k K) p) := by
  rw [weightLeviCoordinateRingBaseChangeAlgEquiv, AlgEquiv.trans_apply,
    IsLocalization.Away.tensorProductEquivTMulRight_tmul]
  rw [IsLocalization.algEquivOfAlgEquiv_eq]
  -- The localization lift still wraps the polynomial base-change equivalence; expose its
  -- underlying algebra-map application so `algebraTensorAlgEquiv_tmul` can rewrite it.
  change algebraMap _ _
      (MvPolynomial.algebraTensorAlgEquiv k K (s ⊗ₜ[k] p)) = _
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul, Algebra.smul_def, map_mul,
    ← IsScalarTower.algebraMap_apply K (MvPolynomial (WeightLeviIndex w) K)]
  rw [Algebra.smul_def]

/-- Scalar extension of the weight-Levi coordinate Hopf algebra is ring-equivalent to the
weight-Levi coordinate Hopf algebra over the extended base ring. -/
def weightLeviCoordinateHopfAlgebraBaseChangeRingEquiv
    (k : Type u) (K : Type v) [CommRing k] [CommRing K] [Algebra k K] (w : Fin N → ℤ) :
    weightLeviCoordinateHopfAlgebra k w ⊗[k] K ≃+*
      weightLeviCoordinateHopfAlgebra K w :=
  (Algebra.TensorProduct.congr (weightLeviCoordinateAlgEquiv k w)
    (AlgEquiv.refl : K ≃ₐ[k] K)).toRingEquiv.trans <|
  (Algebra.TensorProduct.comm k (WeightLeviCoordinateRing k w) K).toRingEquiv.trans <|
  (weightLeviCoordinateRingBaseChangeAlgEquiv k K w).toRingEquiv.trans <|
  (weightLeviCoordinateAlgEquiv K w).symm.toRingEquiv

/-- Base change carries each quotient generic-matrix entry of the weight Levi to the
corresponding quotient generic-matrix entry over the new base. -/
@[simp]
theorem weightLeviCoordinateHopfAlgebraBaseChangeRingEquiv_tmul_mk_genericMatrix_apply
    (k : Type u) (K : Type v) [CommRing k] [CommRing K] [Algebra k K] (w : Fin N → ℤ)
    (i j : Fin N) :
    weightLeviCoordinateHopfAlgebraBaseChangeRingEquiv k K w
        (Ideal.Quotient.mk (weightLeviDefiningHopfIdeal k w).toIdeal
          (coordinateHopfAlgebraAlgEquiv k N
            (coordinateRingMap k N (MvPolynomial.X (i, j)))) ⊗ₜ[k] (1 : K)) =
      Ideal.Quotient.mk (weightLeviDefiningHopfIdeal K w).toIdeal
        (coordinateHopfAlgebraAlgEquiv K N
          (coordinateRingMap K N (MvPolynomial.X (i, j)))) := by
  rw [← genericMatrix_apply (R := k) (n := N) i j,
    ← genericMatrix_apply (R := K) (n := N) i j,
    ← Ideal.Quotient.mkₐ_eq_mk (R₁ := k),
    ← Ideal.Quotient.mkₐ_eq_mk (R₁ := K)]
  by_cases hij : w i = w j
  · -- Unfold the composed ring equivalence just enough to expose its presentation and
    -- localization base-change stages, whose generator computation lemmas apply below.
    change (weightLeviCoordinateAlgEquiv K w).symm
        (weightLeviCoordinateRingBaseChangeAlgEquiv k K w
          ((1 : K) ⊗ₜ[k] weightLeviCoordinateAlgEquiv k w
            (Ideal.Quotient.mkₐ k (weightLeviDefiningHopfIdeal k w).toIdeal
              ((genericMatrix k N) i j)))) = _
    rw [genericMatrix_apply, Ideal.Quotient.mkₐ_eq_mk,
      weightLeviCoordinateAlgEquiv_mk_genericMatrix_apply,
      weightLeviLocalizedGenericMatrix_apply_of_eq k w hij,
      IsScalarTower.toAlgHom_apply,
      weightLeviCoordinateRingBaseChangeAlgEquiv_tmul_algebraMap,
      MvPolynomial.map_X, one_smul,
      weightLeviCoordinateAlgEquiv_symm_algebraMap_X]
  · simp [weightLeviCoordinateHopfAlgebraBaseChangeRingEquiv,
      weightLeviQuotient_mk_genericMatrix_apply_of_ne k w hij,
      weightLeviQuotient_mk_genericMatrix_apply_of_ne K w hij]

/-- The weight Levi is geometrically connected over every field. -/
theorem geometricallyConnectedCommHopfAlgProperty_weightLeviCoordinateHopfAlgebra
    (k : Type u) [Field k] (w : Fin N → ℤ) :
    geometricallyConnectedCommHopfAlgProperty k
      (weightLeviCoordinateHopfAlgebra k w) := by
  rw [geometricallyConnectedCommHopfAlgProperty_iff]
  intro K _ _
  exact (PrimeSpectrum.homeomorphOfRingEquiv
    (weightLeviCoordinateHopfAlgebraBaseChangeRingEquiv k K w)).connectedSpace_iff.mpr
      inferInstance

end

end TauCeti.GeneralLinear
