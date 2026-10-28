/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.Generated.Positive.Basic
public import TauCeti.Algebra.Lie.D4.Tripled.Generated.StandardComodule
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Weight.Order
public import TauCeti.Algebra.AlgebraicGroup.Borel.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.Solvable.UpperTriangular
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.WeightDegree

/-!
# A Borel candidate in the generated tripled D₄ group

The positive subgroup of the tripled D₄ carrier is smooth, geometrically connected and
geometrically solvable over every field. Order the twenty-four weight vectors by decreasing
simple-root height. Every positive simple-root subgroup then becomes upper unitriangular,
while the weight torus stays diagonal. This gives a closed inclusion of the positive subgroup
into a conjugate of the upper-triangular subgroup and proves geometric solvability.

The resulting `isBorelCandidate_definingIdeal` supplies the three geometric properties of
the Borel member of a pinning. Borel maximality and comparison with the specialization of the
integral carrier are separate assertions.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§21 and 26–28.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 17.
* The weight-ordering argument follows
  `TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Generated.Positive.BorelCandidate`, using
  `isUpperUnitriangular_kostantRootSubgroupMatrix_orderedWeightBasis`.
-/

public section

open CategoryTheory WithConv
open TauCeti.UniversalEnvelopingAlgebra
open TauCeti.DynkinType
open TauCeti.GeneralLinear.UpperTriangular
  (geometricallySolvablePointsCommHopfAlgProperty_coordinateHopfAlgebra)
attribute [local instance high] Algebra.toModule

namespace TauCeti.D4Tripled.Generated.Positive

universe u

noncomputable section

/-- Number the tripled weight basis by decreasing simple-root height. Equal heights are
ordered by the finite numbering used by `orderedWeightIndexEquiv`. -/
def weightOrderEquiv : Fin 24 ≃ Fin 24 :=
  orderedWeightIndexEquiv ((D 4).weightDegree (by decide)) d4TripledWeight

/-- The weight ordering is the generic ordering by the type-D₄ simple-root height. -/
theorem weightOrderEquiv_def : weightOrderEquiv =
    orderedWeightIndexEquiv ((D 4).weightDegree (by decide)) d4TripledWeight := (rfl)

/-- Every positive numbered root subgroup is upper unitriangular after ordering the weights
by decreasing height, over every commutative ring. -/
theorem isUpperUnitriangular_reindexGL_rootSubgroupPoints_inl (i : Fin 4) (A : Type*)
    [CommRing A] (u : Multiplicative A) :
    ((weightOrderEquiv.reindexGL A (rootSubgroupPoints (.inl i) A u) :
        Matrix.GeneralLinearGroup (Fin 24) A) :
      Matrix (Fin 24) (Fin 24) A).IsUpperUnitriangular := by
  let degree : (Fin 4 → ℤ) →+ ℚ := (D 4).weightDegree (by decide)
  have hdegree : degree (TypeDStd.rootGeneratorWeight 4 (.inl i)) = 1 := by
    have hrow : TypeDStd.rootGeneratorWeight 4 (.inl i) =
        fun j ↦ (D 4).cartanMatrix i j := by
      funext j
      rw [TypeDStd.rootGeneratorWeight_inl, cartanMatrix_D]
    rw [hrow]
    exact weightDegree_cartanMatrix_row (D 4) (by decide) i
  have h := isUpperUnitriangular_kostantRootSubgroupMatrix_orderedWeightBasis
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice latticeBasis d4TripledWeight
    degree isCartanWeightVector_latticeBasis
    (isNilpotent_rep_serreRootGenerator (.inl i))
    (lie_serreH_serreRootGenerator (.inl i))
    (by rw [hdegree]; norm_num)
    ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm u)
  have hb : latticeBasis.reindex weightOrderEquiv =
      orderedWeightBasis degree d4TripledWeight latticeBasis := by
    ext x : 1
    -- The generic ordered basis is indexed by `Fin (Fintype.card (Fin 24))`.
    erw [Module.Basis.reindex_apply, orderedWeightBasis_apply, weightOrderEquiv_def]
    rfl
  have hmatrix :
      ((weightOrderEquiv.reindexGL A (rootSubgroupPoints (.inl i) A u) :
          Matrix.GeneralLinearGroup (Fin 24) A) : Matrix (Fin 24) (Fin 24) A) =
        kostantRootSubgroupMatrix
          (TauCeti.serreRootGenerator weightTable.cartanMatrix)
          (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
          rep_kostantForm_mem_lattice (.inl i) (isNilpotent_rep_serreRootGenerator (.inl i))
          (latticeBasis.reindex weightOrderEquiv)
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm u) := by
    ext r s
    rw [Equiv.coe_reindexGL, Matrix.submatrix_apply, coe_rootSubgroupPoints,
      kostantRootSubgroupMatrix_reindex_apply]
  rw [hmatrix, hb]
  exact h

variable (A : Type u) [CommRing A]

/-- After conjugation by the weight-ordering permutation matrix, the positive subgroup lies
scheme-theoretically in the upper-triangular subgroup of `GL₂₄`. The right side is its defining
ideal pulled back from the full generated carrier to the ambient general linear group. -/
theorem upperTriangular_comap_le_definingIdeal_comap :
    (GeneralLinear.UpperTriangular.definingHopfIdeal A 24).comapOfSurjective
      (GeneralLinear.conjCoordinateIso (permutationGL (k := A) weightOrderEquiv)).inv.hom
      (ConcreteCategory.bijective_of_isIso
        (GeneralLinear.conjCoordinateIso (permutationGL (k := A) weightOrderEquiv)).inv).2 ≤
      (definingIdeal A).comapOfSurjective (generatedCoordinateMap A).hom
        (generatedCoordinateMap_surjective A) := by
  rw [CommHopfAlgCat.comapOfSurjective_commonKernelHopfIdeal,
    CommHopfAlgCat.le_commonKernelHopfIdeal_iff]
  rintro (i | ⟨⟩)
  · rw [generator_inl, generatedCoordinateMap_comp_generatedCoordinateLift]
    apply GeneralLinear.UpperTriangular.comap_le_ker_of_conjugate
    let B := AdditiveGroup.coordinateHopfAlgebra A
    let q : HopfAlgebra.points (R := A) (H := B) (CommAlgCat.of A B) :=
      toConv (AlgHom.id A B)
    have h := pointToGeneralLinear_mapDomain_generatedCoordinateLift_inl_eq_rootSubgroupPoints
      A (.inl i) (CommAlgCat.of A B) q
    have hpoint : GeneralLinear.pointsMulEquiv 24
        (toConv (generatorCoordinateMap A (.inl (.inl i))).hom.toAlgHom) =
        (rootSubgroupPoints (.inl i) B (AdditiveGroup.gaPointsMulEquiv q) :
          Matrix.GeneralLinearGroup (Fin 24) B) := by
      rw [GeneralLinear.pointsMulEquiv_apply,
        ← generatedCoordinateMap_comp_generatedCoordinateLift]
      simpa only [BialgHom.mapDomain_apply, q, B, ofConv_toConv, AlgHom.id_comp,
        _root_.CommHopfAlgCat.hom_comp, BialgHom.comp_toAlgHom] using h
    rw [hpoint, map_permutationGL, permutationGL_mul_mul_inv]
    exact (isUpperUnitriangular_reindexGL_rootSubgroupPoints_inl i B
      (AdditiveGroup.gaPointsMulEquiv q)).isUpperTriangular
  · rw [generator_inr, generatedCoordinateMap_comp_generatedCoordinateLift]
    apply GeneralLinear.UpperTriangular.comap_le_ker_of_conjugate
    rw [map_permutationGL, permutationGL_mul_mul_inv]
    rintro r s (hsr : s < r)
    simp [GeneralLinear.pointsMulEquiv_apply, GeneralLinear.pointToGeneralLinear_apply,
      generatorCoordinateMap_inr, GeneralLinear.hom_weightTorusBaseChangeCoordinateMap,
      DiagonalizableGroup.diagonalCoordinateMap_X, hsr.ne']

variable (k : Type u) [Field k]

/-- The positive subgroup of the tripled carrier has solvable geometric points over every
field. -/
theorem geometricallySolvablePoints_coordinateHopfAlgebra :
    geometricallySolvablePointsCommHopfAlgProperty k (coordinateHopfAlgebra k) := by
  let e := CommHopfAlgCat.quotientIsoOfIso
    (GeneralLinear.conjCoordinateIso (permutationGL (k := k) weightOrderEquiv)).symm
    (GeneralLinear.UpperTriangular.definingHopfIdeal k 24)
  let f := CommHopfAlgCat.quotientMapOfLe (GeneralLinear.coordinateHopfAlgebra k 24)
    (upperTriangular_comap_le_definingIdeal_comap k)
  let e' := CommHopfAlgCat.Hom.quotientIsoOfSurjective
    (generatedCoordinateMap k) (generatedCoordinateMap_surjective k) (definingIdeal k)
  exact geometricallySolvablePointsCommHopfAlgProperty_of_surjective k
    (e.inv ≫ f ≫ e'.hom)
    ((ConcreteCategory.bijective_of_isIso e'.hom).2.comp
      ((CommHopfAlgCat.quotientMapOfLe_surjective _ _).comp
        (ConcreteCategory.bijective_of_isIso e.inv).2))
    (geometricallySolvablePointsCommHopfAlgProperty_coordinateHopfAlgebra k 24)

/-- The positive subgroup of the generated tripled D₄ carrier is a Borel candidate over every
field: smooth, geometrically connected and geometrically solvable. -/
theorem isBorelCandidate_definingIdeal :
    HopfIdeal.IsBorelCandidate k
      (generatedFiniteTypeCoordinateHopfAlgebra k) (definingIdeal k) :=
  HopfIdeal.IsBorelCandidate.mk (smooth_coordinateHopfAlgebra k)
    (geometricallyConnected_coordinateHopfAlgebra k)
    (geometricallySolvablePoints_coordinateHopfAlgebra k)

end

end TauCeti.D4Tripled.Generated.Positive
