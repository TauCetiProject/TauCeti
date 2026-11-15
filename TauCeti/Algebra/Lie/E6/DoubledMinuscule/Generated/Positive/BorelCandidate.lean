/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.Generated.Positive.Basic
public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.Generated.StandardComodule
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Weight.Order
public import TauCeti.Algebra.AlgebraicGroup.Borel.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.Solvable.UpperTriangular
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.WeightDegree

/-!
# A Borel candidate in the generated doubled E₆ group

The positive subgroup generated over any field by the six positive numbered simple-root
subgroups and the weight torus of the doubled minuscule carrier on `V(ϖ₁) ⊕ V(ϖ₆)` is a Borel
candidate: it is smooth, geometrically connected and geometrically solvable.

The fifty-four matrix coordinates lay out `V(ϖ₁)` and then `V(ϖ₆)`. On the second block the
positive root generators act by the negated lowering matrices of `V(ϖ₁)`, so the two blocks
need different orderings. Renumbering all fifty-four coordinates by decreasing
simple-root height of their weights, `weightOrderEquiv`, makes every positive numbered root
subgroup upper unitriangular, since a raising operator adds a simple root to the weight. The
weight torus stays diagonal. Conjugation by the corresponding permutation matrix,
`TauCeti.permutationGL` of `weightOrderEquiv`, therefore carries the positive subgroup
scheme-theoretically into the upper-triangular subgroup of `GL₅₄`, and its geometric points form
solvable groups.

`isBorelCandidate_carrierDefiningIdeal` expresses this inside the generated doubled carrier.
Maximality among smooth connected solvable subgroups is not asserted, and neither the generated
carrier nor this subgroup is identified with the pinned simply connected group scheme of type
`E₆` or its Borel subgroup.

## Main declarations

* `TauCeti.E6DoubledMinuscule.Generated.Positive.weightOrderEquiv`: the renumbering of the
  matrix coordinates by decreasing weight height.
* `TauCeti.E6DoubledMinuscule.Generated.Positive.upperTriangular_comap_le_definingIdeal`: after
  that conjugation, the positive subgroup lies in the upper-triangular subgroup.
* `TauCeti.E6DoubledMinuscule.Generated.Positive.isBorelCandidate_carrierDefiningIdeal`: the
  positive subgroup is a Borel candidate in the generated doubled carrier over every field.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§21 and 26–28.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 17.
* The argument is that of
  `TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Generated.Positive.BorelCandidate`, with the
  doubled minuscule weights and the type-`E₆` root generators, and uses
  `isUpperUnitriangular_kostantRootSubgroupMatrix_orderedWeightBasis`.
-/

public section

open CategoryTheory WithConv
open TauCeti.UniversalEnvelopingAlgebra
open scoped Matrix
open TauCeti.GeneralLinear.UpperTriangular
  (geometricallySolvablePointsCommHopfAlgProperty_coordinateHopfAlgebra)
attribute [local instance high] Algebra.toModule

namespace TauCeti.E6DoubledMinuscule.Generated.Positive

universe u

noncomputable section

/-- The simple-root height of an integral type-`E₆` weight, `DynkinType.weightDegree` of
`DynkinType.E6` read on weights indexed by `Fin 6`. The rank of `DynkinType.E6` is `6` only up to
unfolding, so this restatement is what lets it order the doubled minuscule weights `matrixWeight`.
-/
def weightDegree : (Fin 6 → ℤ) →+ ℚ :=
  DynkinType.E6.weightDegree DynkinType.valid_E6

/-- The height is the generic type-`E₆` simple-root height `DynkinType.weightDegree`. -/
theorem weightDegree_def : weightDegree = DynkinType.E6.weightDegree DynkinType.valid_E6 := (rfl)

/-- Each positive numbered root generator has a simple root as weight, of height one. -/
@[simp]
theorem weightDegree_rootGeneratorWeight_inl (i : Fin 6) :
    weightDegree (TauCeti.E6.rootGeneratorWeight (.inl i)) = 1 := by
  have hrow : TauCeti.E6.rootGeneratorWeight (.inl i) =
      fun j ↦ DynkinType.E6.cartanMatrix i j := by
    funext j
    rw [TauCeti.E6.rootGeneratorWeight_inl, DynkinType.cartanMatrix_E6]
  rw [hrow]
  exact DynkinType.weightDegree_cartanMatrix_row DynkinType.E6 DynkinType.valid_E6 i

/-- The fifty-four matrix coordinates of the doubled carrier renumbered by decreasing
simple-root height of their weights. Coordinates of equal height are ordered by an arbitrary
finite numbering. -/
def weightOrderEquiv : Fin 54 ≃ Fin 54 :=
  orderedWeightIndexEquiv weightDegree matrixWeight

/-- The weight ordering is the generic ordering of `matrixWeight` by `weightDegree`. -/
theorem weightOrderEquiv_def :
    weightOrderEquiv = orderedWeightIndexEquiv weightDegree matrixWeight := (rfl)

/-- Renumbering the matrix basis by `weightOrderEquiv` gives the ordered weight basis. -/
theorem matrixBasis_reindex_weightOrderEquiv :
    matrixBasis.reindex weightOrderEquiv =
      orderedWeightBasis weightDegree matrixWeight matrixBasis := by
  ext x : 1
  -- The ordered basis is indexed by `Fin (Fintype.card (Fin 54))`, which is `Fin 54` only after
  -- unfolding the cardinality, so its evaluation lemma is applied up to that unfolding.
  rw [Module.Basis.reindex_apply]
  exact (orderedWeightBasis_apply weightDegree matrixWeight matrixBasis x).symm

/-- After renumbering by decreasing weight height, every positive numbered root-subgroup matrix
of the doubled carrier is upper unitriangular, over every commutative ring. -/
theorem isUpperUnitriangular_reindexGL_rootSubgroupPoints_inl (i : Fin 6) (A : Type*)
    [CommRing A] (u : Multiplicative A) :
    ((weightOrderEquiv.reindexGL A (rootSubgroupPoints (.inl i) A u) :
        Matrix.GeneralLinearGroup (Fin 54) A) :
      Matrix (Fin 54) (Fin 54) A).IsUpperUnitriangular := by
  have h := isUpperUnitriangular_kostantRootSubgroupMatrix_orderedWeightBasis
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice matrixBasis matrixWeight
    weightDegree isCartanWeightVector_matrixBasis
    (isNilpotent_rep_serreRootGenerator (.inl i))
    (TauCeti.E6.lie_serreH_rootGenerator (.inl i))
    (by rw [weightDegree_rootGeneratorWeight_inl]; norm_num)
    ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm u)
  have hmatrix :
      ((weightOrderEquiv.reindexGL A (rootSubgroupPoints (.inl i) A u) :
          Matrix.GeneralLinearGroup (Fin 54) A) : Matrix (Fin 54) (Fin 54) A) =
        kostantRootSubgroupMatrix
          (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
          (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
          rep_kostantForm_mem_lattice (.inl i) (isNilpotent_rep_serreRootGenerator (.inl i))
          (matrixBasis.reindex weightOrderEquiv)
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm u) := by
    ext r s
    rw [Equiv.coe_reindexGL, Matrix.submatrix_apply, coe_rootSubgroupPoints,
      kostantRootSubgroupMatrix_reindex_apply]
  rw [hmatrix, matrixBasis_reindex_weightOrderEquiv]
  -- `h` is stated over `Fin (Fintype.card (Fin 54))`, which unfolds to `Fin 54`.
  exact h

variable (A : Type u) [CommRing A]

/-- After conjugation by the permutation matrix of `weightOrderEquiv`, the generated positive
subgroup lies scheme-theoretically in the upper-triangular subgroup of `GL₅₄`. -/
theorem upperTriangular_comap_le_definingIdeal :
    (GeneralLinear.UpperTriangular.definingHopfIdeal A 54).comapOfSurjective
      (GeneralLinear.conjCoordinateIso (permutationGL (k := A) weightOrderEquiv)).inv.hom
      (ConcreteCategory.bijective_of_isIso
        (GeneralLinear.conjCoordinateIso (permutationGL (k := A) weightOrderEquiv)).inv).2 ≤
      definingIdeal A := by
  rw [le_definingIdeal_iff]
  constructor
  · intro i
    apply GeneralLinear.UpperTriangular.comap_le_ker_of_conjugate
    let B := AdditiveGroup.coordinateHopfAlgebra A
    let q : HopfAlgebra.points (R := A) (H := B) (CommAlgCat.of A B) :=
      toConv (AlgHom.id A B)
    have h := pointToGeneralLinear_mapDomain_generatedCoordinateLift_inl_eq_rootSubgroupPoints
      A (.inl i) (CommAlgCat.of A B) q
    have hpoint : GeneralLinear.pointsMulEquiv 54
        (toConv (generatorCoordinateMap A (.inl (.inl i))).hom.toAlgHom) =
        (rootSubgroupPoints (.inl i) B (AdditiveGroup.gaPointsMulEquiv q) :
          Matrix.GeneralLinearGroup (Fin 54) B) := by
      rw [GeneralLinear.pointsMulEquiv_apply,
        ← generatedCoordinateMap_comp_generatedCoordinateLift]
      simpa only [BialgHom.mapDomain_apply, q, B, ofConv_toConv, AlgHom.id_comp,
        _root_.CommHopfAlgCat.hom_comp, BialgHom.comp_toAlgHom] using h
    rw [hpoint, map_permutationGL, permutationGL_mul_mul_inv]
    exact (isUpperUnitriangular_reindexGL_rootSubgroupPoints_inl i B
      (AdditiveGroup.gaPointsMulEquiv q)).isUpperTriangular
  · apply GeneralLinear.UpperTriangular.comap_le_ker_of_conjugate
    rw [map_permutationGL, permutationGL_mul_mul_inv]
    rintro r s (hsr : s < r)
    simp [GeneralLinear.pointsMulEquiv_apply, GeneralLinear.pointToGeneralLinear_apply,
      generatorCoordinateMap_inr, GeneralLinear.hom_weightTorusBaseChangeCoordinateMap,
      DiagonalizableGroup.diagonalCoordinateMap_X, hsr.ne']

/-- The surjective coordinate map from the upper-triangular subgroup of `GL₅₄` onto the positive
subgroup, induced by conjugation by the permutation matrix of `weightOrderEquiv`. -/
def upperTriangularCoordinateMap :
    GeneralLinear.UpperTriangular.coordinateHopfAlgebra A 54 ⟶ coordinateHopfAlgebra A :=
  (CommHopfAlgCat.quotientIsoOfIso
      (GeneralLinear.conjCoordinateIso (permutationGL (k := A) weightOrderEquiv)).symm
      (GeneralLinear.UpperTriangular.definingHopfIdeal A 54)).inv ≫
    CommHopfAlgCat.quotientMapOfLe (GeneralLinear.coordinateHopfAlgebra A 54)
      (upperTriangular_comap_le_definingIdeal A)

/-- The coordinate map from the upper-triangular subgroup onto the positive subgroup is induced
by conjugation by the permutation matrix of `weightOrderEquiv`: precomposed with the
upper-triangular quotient map, it is that conjugation followed by the positive quotient map. -/
@[reassoc (attr := simp)]
theorem coordinateMap_comp_upperTriangularCoordinateMap :
    GeneralLinear.UpperTriangular.coordinateMap A 54 ≫ upperTriangularCoordinateMap A =
      (GeneralLinear.conjCoordinateIso (permutationGL (k := A) weightOrderEquiv)).hom ≫
        CommHopfAlgCat.mkQuotient _ (definingIdeal A) := by
  rw [GeneralLinear.UpperTriangular.coordinateMap_def, upperTriangularCoordinateMap,
    ← Category.assoc, CommHopfAlgCat.mkQuotient_comp_quotientIsoOfIso_inv, Iso.symm_inv,
    Category.assoc, CommHopfAlgCat.mkQuotient_comp_quotientMapOfLe]

/-- The coordinate map from the upper-triangular subgroup onto the positive subgroup is
surjective, so it embeds the positive subgroup into the upper-triangular subgroup. -/
theorem upperTriangularCoordinateMap_surjective :
    Function.Surjective (upperTriangularCoordinateMap A) :=
  (CommHopfAlgCat.quotientMapOfLe_surjective _ _).comp
    (ConcreteCategory.bijective_of_isIso
      (CommHopfAlgCat.quotientIsoOfIso
        (GeneralLinear.conjCoordinateIso (permutationGL (k := A) weightOrderEquiv)).symm
        (GeneralLinear.UpperTriangular.definingHopfIdeal A 54)).inv).2

variable (k : Type u) [Field k]

/-- The positive subgroup has solvable geometric points over any field. -/
theorem geometricallySolvablePoints_coordinateHopfAlgebra :
    geometricallySolvablePointsCommHopfAlgProperty k (coordinateHopfAlgebra k) :=
  geometricallySolvablePointsCommHopfAlgProperty_of_surjective k
    (upperTriangularCoordinateMap k) (upperTriangularCoordinateMap_surjective k)
    (geometricallySolvablePointsCommHopfAlgProperty_coordinateHopfAlgebra k 54)

/-- The positive subgroup of the generated doubled E₆ carrier is a Borel candidate over every
field: smooth, geometrically connected and geometrically solvable. -/
theorem isBorelCandidate_carrierDefiningIdeal :
    HopfIdeal.IsBorelCandidate k
      (FiniteTypeCommHopfAlgCat.of k (generatedCoordinateHopfAlgebra k))
      (carrierDefiningIdeal k) := by
  let e : (FiniteTypeCommHopfAlgCat.quotient
      (FiniteTypeCommHopfAlgCat.of k (generatedCoordinateHopfAlgebra k))
      (carrierDefiningIdeal k)).obj ≅ coordinateHopfAlgebra k :=
    _root_.CommHopfAlgCat.Hom.quotientIsoOfKerOfSurjectiveEq
      (restriction k) (restriction_surjective k) (kerOfSurjective_restriction k)
  exact HopfIdeal.IsBorelCandidate.mk
    ((smoothCommHopfAlgProperty k).prop_of_iso e.symm (smooth_coordinateHopfAlgebra k))
    ((geometricallyConnectedCommHopfAlgProperty k).prop_of_iso e.symm
      (geometricallyConnected_coordinateHopfAlgebra k))
    ((geometricallySolvablePointsCommHopfAlgProperty k).prop_of_iso e.symm
      (geometricallySolvablePoints_coordinateHopfAlgebra k))

end

end TauCeti.E6DoubledMinuscule.Generated.Positive
