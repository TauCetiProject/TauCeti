/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Fin.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Weight.Order
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Equivalence
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.GroupScheme
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.WeightDegree

/-!
# The positive Geck matrices in weight order

The finite Geck coordinate basis is numbered independently of weight height. Reordering it by
`weightDegree` gives an integral permutation matrix `geckWeightOrderingMatrix`. Conjugation by
its image over any commutative ring writes the original Geck root and torus matrices in that
ordered basis. The numbered raising root subgroups become upper unitriangular, and the torus
becomes diagonal with the reordered weight characters.

The cardinality transport in `geckWeightOrderingEquiv` identifies the ordered-weight API's
`Fin (Fintype.card (Fin n))` with the original matrix index `Fin n`. Thus the conjugation acts
on the same ambient general linear group as the positive Geck carrier.
-/

public section

open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType

noncomputable section

-- Use the scalar-extension algebra structure for tensor-product modules.
attribute [local instance high] Algebra.toModule

variable (t : DynkinType) (ht : t.Valid)

/-- The Geck coordinates numbered by decreasing weight degree, with the original matrix size. -/
def geckWeightOrderingEquiv : Fin (t.geckDim ht) ≃ Fin (t.geckDim ht) :=
  (orderedWeightIndexEquiv (t.weightDegree ht) (t.geckWeightFin ht)).trans
    (Fin.castOrderIso (Fintype.card_fin (t.geckDim ht))).toEquiv

/-- The ordered weight basis, transported back to the original finite matrix index. -/
def geckOrderedWeightBasis :
    Module.Basis (Fin (t.geckDim ht)) ℤ (t.geckCoordinateLattice ht).toAddSubgroup :=
  (t.geckCoordinateBasisFin ht).reindex (t.geckWeightOrderingEquiv ht)

/-- The weights of the reordered Geck coordinate basis. -/
def geckOrderedWeight : Fin (t.geckDim ht) → Fin t.rank → ℤ :=
  t.geckWeightFin ht ∘ (t.geckWeightOrderingEquiv ht).symm

/-- The reordered basis is the generic ordered weight basis followed by the cardinality
identification. -/
theorem geckOrderedWeightBasis_eq_orderedWeightBasis :
    t.geckOrderedWeightBasis ht =
      (orderedWeightBasis (t.weightDegree ht) (t.geckWeightFin ht)
        (t.geckCoordinateBasisFin ht)).reindex
          (Fin.castOrderIso (Fintype.card_fin (t.geckDim ht))).toEquiv := by
  ext r
  simp [geckOrderedWeightBasis, geckWeightOrderingEquiv, orderedWeightBasis_apply,
    Module.Basis.reindex_apply]

/-- The reordered weights agree with `orderedWeight` after the cardinality identification. -/
theorem geckOrderedWeight_eq_orderedWeight (r : Fin (t.geckDim ht)) :
    t.geckOrderedWeight ht r =
      orderedWeight (t.weightDegree ht) (t.geckWeightFin ht)
        ((Fin.castOrderIso (Fintype.card_fin (t.geckDim ht))).symm r) := by
  simp [geckOrderedWeight, geckWeightOrderingEquiv]

/-- The integral change of coordinates from the Geck coordinate basis to decreasing weight
order. Its inverse changes coordinates in the opposite direction. -/
def geckWeightOrderingMatrix : Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) ℤ where
  val := (t.geckOrderedWeightBasis ht).toMatrix (t.geckCoordinateBasisFin ht)
  inv := (t.geckCoordinateBasisFin ht).toMatrix (t.geckOrderedWeightBasis ht)
  val_inv := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  inv_val := Module.Basis.toMatrix_mul_toMatrix_flip _ _

/-- The change-of-coordinates matrix is a permutation matrix. -/
theorem coe_geckWeightOrderingMatrix :
    (t.geckWeightOrderingMatrix ht : Matrix (Fin (t.geckDim ht)) (Fin (t.geckDim ht)) ℤ) =
      Equiv.Perm.permMatrix ℤ (t.geckWeightOrderingEquiv ht).symm := by
  simp only [geckWeightOrderingMatrix, geckOrderedWeightBasis]
  rw [Module.Basis.toMatrix_reindex, Module.Basis.toMatrix_self]
  exact (PEquiv.toMatrix_toPEquiv_eq _).symm

variable {A : Type*} [CommRing A]

/-- Scalar extension preserves the same coordinate permutation over every value ring. -/
theorem coe_map_geckWeightOrderingMatrix :
    (Matrix.GeneralLinearGroup.map (algebraMap ℤ A) (t.geckWeightOrderingMatrix ht) :
      Matrix (Fin (t.geckDim ht)) (Fin (t.geckDim ht)) A) =
        Equiv.Perm.permMatrix A (t.geckWeightOrderingEquiv ht).symm := by
  -- `GeneralLinearGroup.map_apply` is entrywise; expose the underlying matrix map
  -- so that `PEquiv.map_toMatrix` applies directly to this matrix equality.
  change ((t.geckWeightOrderingMatrix ht :
    Matrix (Fin (t.geckDim ht)) (Fin (t.geckDim ht)) ℤ).map (algebraMap ℤ A)) = _
  rw [coe_geckWeightOrderingMatrix]
  exact PEquiv.map_toMatrix _ _

/-- Conjugation by the weight-ordering matrix reindexes both matrix coordinates. -/
theorem conj_geckWeightOrderingMatrix_eq_reindexGL
    (g : Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) :
    Matrix.GeneralLinearGroup.map (algebraMap ℤ A) (t.geckWeightOrderingMatrix ht) * g *
        (Matrix.GeneralLinearGroup.map (algebraMap ℤ A) (t.geckWeightOrderingMatrix ht))⁻¹ =
      (t.geckWeightOrderingEquiv ht).reindexGL A g := by
  apply (mul_inv_eq_iff_eq_mul).2
  apply Units.ext
  simp only [Units.val_mul, coe_map_geckWeightOrderingMatrix, Equiv.coe_reindexGL,
    Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext r s
  simp

private theorem geckOrderedWeightBasis_baseChange :
    (t.geckOrderedWeightBasis ht).baseChange A =
      ((t.geckCoordinateBasisFin ht).baseChange A).reindex (t.geckWeightOrderingEquiv ht) := by
  ext r
  simp [geckOrderedWeightBasis, Module.Basis.reindex_apply]

/-- Conjugation writes each original numbered root-subgroup matrix in the ordered basis.
The equality holds for both raising and lowering generators. -/
theorem conj_geckRootSubgroupMatrix_eq_ordered (i : Fin t.rank ⊕ Fin t.rank)
    (q : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    Matrix.GeneralLinearGroup.map (algebraMap ℤ A) (t.geckWeightOrderingMatrix ht) *
        t.geckRootSubgroupMatrix ht i q *
        (Matrix.GeneralLinearGroup.map (algebraMap ℤ A) (t.geckWeightOrderingMatrix ht))⁻¹ =
      kostantRootSubgroupMatrix
        (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
        (t.geckCoordinateLattice ht).toAddSubgroup
        (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht) i
        (t.isNilpotent_geckRepresentation_rootGenerator ht i) (t.geckOrderedWeightBasis ht) q := by
  rw [conj_geckWeightOrderingMatrix_eq_reindexGL]
  ext r s
  simp [Equiv.coe_reindexGL, geckRootSubgroupMatrix, kostantRootSubgroupMatrix_apply,
    geckOrderedWeightBasis_baseChange, Module.Basis.reindex_apply]

/-- Every numbered raising root subgroup becomes upper unitriangular after the fixed integral
weight-basis permutation, over every commutative value ring. -/
theorem isUpperUnitriangular_conj_geckRootSubgroupMatrix_inl (i : Fin t.rank)
    (q : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    ((Matrix.GeneralLinearGroup.map (algebraMap ℤ A) (t.geckWeightOrderingMatrix ht) *
        t.geckRootSubgroupMatrix ht (.inl i) q *
        (Matrix.GeneralLinearGroup.map (algebraMap ℤ A) (t.geckWeightOrderingMatrix ht))⁻¹ :
          Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) :
      Matrix (Fin (t.geckDim ht)) (Fin (t.geckDim ht)) A).IsUpperUnitriangular := by
  rw [conj_geckRootSubgroupMatrix_eq_ordered, geckOrderedWeightBasis_eq_orderedWeightBasis]
  have hpos : 0 < t.weightDegree ht (t.rootGeneratorWeight ht (.inl i)) := by
    have hrow : t.rootGeneratorWeight ht (.inl i) = fun j => t.cartanMatrix i j := by
      funext j
      rw [rootGeneratorWeight_inl]
    rw [hrow, weightDegree_cartanMatrix_row]
    norm_num
  have hordered := isUpperUnitriangular_kostantRootSubgroupMatrix_orderedWeightBasis
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) (t.weightDegree ht)
    (t.isCartanWeightVector_geckCoordinateBasisFin ht)
    (t.isNilpotent_geckRepresentation_rootGenerator ht (.inl i))
    (t.lie_lieBasis_h_rootGenerator ht (.inl i)) hpos q
  let e := Fin.castOrderIso (Fintype.card_fin (t.geckDim ht))
  have hbase :
      ((orderedWeightBasis (t.weightDegree ht) (t.geckWeightFin ht)
        (t.geckCoordinateBasisFin ht)).reindex e.toEquiv).baseChange A =
      ((orderedWeightBasis (t.weightDegree ht) (t.geckWeightFin ht)
        (t.geckCoordinateBasisFin ht)).baseChange A).reindex e.toEquiv := by
    ext r
    simp [Module.Basis.reindex_apply]
  rw [Matrix.isUpperUnitriangular_def]
  constructor
  · intro r s hsr
    simpa [kostantRootSubgroupMatrix_apply, hbase, Module.Basis.reindex_apply, e] using
      hordered.isUpperTriangular (e.symm.lt_iff_lt.mpr hsr)
  · intro r
    simpa [kostantRootSubgroupMatrix_apply, hbase, Module.Basis.reindex_apply, e] using
      hordered.apply_diag (e.symm r)

/-- Each original raising matrix is upper triangular after conjugation by the integral
weight-ordering matrix. -/
theorem isUpperTriangular_conj_geckRootSubgroupMatrix_inl (i : Fin t.rank)
    (q : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    ((Matrix.GeneralLinearGroup.map (algebraMap ℤ A) (t.geckWeightOrderingMatrix ht) *
        t.geckRootSubgroupMatrix ht (.inl i) q *
        (Matrix.GeneralLinearGroup.map (algebraMap ℤ A) (t.geckWeightOrderingMatrix ht))⁻¹ :
          Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) :
      Matrix (Fin (t.geckDim ht)) (Fin (t.geckDim ht)) A).IsUpperTriangular :=
  (t.isUpperUnitriangular_conj_geckRootSubgroupMatrix_inl ht i q).isUpperTriangular

/-- Conjugation writes the original torus matrix in the ordered basis with its reordered weights. -/
theorem conj_geckTorusMatrix_eq_ordered (s : Fin t.rank → Aˣ) :
    Matrix.GeneralLinearGroup.map (algebraMap ℤ A) (t.geckWeightOrderingMatrix ht) *
        t.geckTorusMatrix ht s *
        (Matrix.GeneralLinearGroup.map (algebraMap ℤ A) (t.geckWeightOrderingMatrix ht))⁻¹ =
      kostantTorusMatrix (t.geckCoordinateLattice ht).toAddSubgroup
        (t.geckOrderedWeightBasis ht) (t.geckOrderedWeight ht) s := by
  rw [conj_geckWeightOrderingMatrix_eq_reindexGL]
  ext r c
  simp [Equiv.coe_reindexGL, geckTorusMatrix, kostantTorusMatrix_apply, diagGL_apply,
    geckOrderedWeight, Matrix.submatrix_apply, Matrix.diagonal_apply]

/-- The conjugated torus has the ordered weight characters on its diagonal. -/
theorem coe_conj_geckTorusMatrix_eq_diagonal (s : Fin t.rank → Aˣ) :
    ((Matrix.GeneralLinearGroup.map (algebraMap ℤ A) (t.geckWeightOrderingMatrix ht) *
        t.geckTorusMatrix ht s *
        (Matrix.GeneralLinearGroup.map (algebraMap ℤ A) (t.geckWeightOrderingMatrix ht))⁻¹ :
          Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) :
      Matrix (Fin (t.geckDim ht)) (Fin (t.geckDim ht)) A) =
        Matrix.diagonal fun r => (torusCharacter s (t.geckOrderedWeight ht r) : A) := by
  rw [conj_geckTorusMatrix_eq_ordered, kostantTorusMatrix_apply, diagGL_coe]

/-- The Geck torus remains diagonal after the weight-ordering permutation. -/
theorem isDiag_conj_geckTorusMatrix (s : Fin t.rank → Aˣ) :
    ((Matrix.GeneralLinearGroup.map (algebraMap ℤ A) (t.geckWeightOrderingMatrix ht) *
        t.geckTorusMatrix ht s *
        (Matrix.GeneralLinearGroup.map (algebraMap ℤ A) (t.geckWeightOrderingMatrix ht))⁻¹ :
          Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) :
      Matrix (Fin (t.geckDim ht)) (Fin (t.geckDim ht)) A).IsDiag := by
  rw [coe_conj_geckTorusMatrix_eq_diagonal]
  exact Matrix.isDiag_diagonal _

/-- Each original torus matrix is upper triangular after conjugation by the integral
weight-ordering matrix. -/
theorem isUpperTriangular_conj_geckTorusMatrix (s : Fin t.rank → Aˣ) :
    ((Matrix.GeneralLinearGroup.map (algebraMap ℤ A) (t.geckWeightOrderingMatrix ht) *
        t.geckTorusMatrix ht s *
        (Matrix.GeneralLinearGroup.map (algebraMap ℤ A) (t.geckWeightOrderingMatrix ht))⁻¹ :
          Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) :
      Matrix (Fin (t.geckDim ht)) (Fin (t.geckDim ht)) A).IsUpperTriangular := by
  intro r c hcr
  exact t.isDiag_conj_geckTorusMatrix ht s (ne_of_gt hcr)

end

end TauCeti.DynkinType
