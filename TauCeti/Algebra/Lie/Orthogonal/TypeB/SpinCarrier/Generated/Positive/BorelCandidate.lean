/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Generated.Positive.Basic
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Generated.StandardComodule
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Weight.Order
public import TauCeti.Algebra.AlgebraicGroup.Borel.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.Solvable.UpperTriangular
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.WeightDegree

/-!
# A Borel candidate in the generated type-Bₙ₊₁ spin group

The positive subgroup generated over any field by the positive numbered simple-root subgroups and
the weight torus of the full-weight type-`Bₙ₊₁` spin carrier is a Borel candidate: it is smooth,
geometrically connected and geometrically solvable.

The exterior basis of the spin module is numbered independently of its weights. Renumbering it by
decreasing simple-root height of the spin weights, `weightOrderEquiv`, makes every positive
numbered root subgroup upper unitriangular, since a raising operator adds a simple root to the
weight. The weight torus stays diagonal. Conjugation by the corresponding permutation matrix,
`TauCeti.permutationGL` of `weightOrderEquiv`, therefore carries the positive subgroup
scheme-theoretically into the upper-triangular subgroup of `GL_(2^(n+1))`, and its geometric
points form solvable groups.

The height functional is the one of the pinned root system of `DynkinType.B (n + 1)`, so the
statements here assume that this Dynkin type is valid, that is `1 ≤ n`.

`isBorelCandidate_carrierDefiningIdeal` expresses this inside the generated spin group.
Maximality among smooth connected solvable subgroups is not asserted, and neither the generated
spin group nor this subgroup is identified with the pinned simply connected group scheme of type
`Bₙ₊₁` or its Borel subgroup.

## Main declarations

* `TauCeti.TypeBSpinCarrier.Generated.Positive.weightOrderEquiv`: the renumbering of the spin
  basis by decreasing weight height.
* `TauCeti.TypeBSpinCarrier.Generated.Positive.upperTriangular_comap_le_definingIdeal`: after
  that conjugation, the positive subgroup lies in the upper-triangular subgroup.
* `TauCeti.TypeBSpinCarrier.Generated.Positive.isBorelCandidate_carrierDefiningIdeal`: the
  positive subgroup is a Borel candidate in the generated spin group over every field.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§21 and 26–28.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 17.
* The argument is that of
  `TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Generated.Positive.BorelCandidate`, for the
  type-`D` spin carrier, with the type-`B` spin weights and root generators.
-/

public section

open CategoryTheory WithConv
open TauCeti.UniversalEnvelopingAlgebra
open TauCeti.GeneralLinear.UpperTriangular
  (geometricallySolvablePointsCommHopfAlgProperty_coordinateHopfAlgebra)
attribute [local instance high] Algebra.toModule

namespace TauCeti.TypeBSpinCarrier.Generated.Positive

universe u

noncomputable section

variable (n : ℕ) (ht : (DynkinType.B (n + 1)).Valid)

/-- The simple-root height of an integral type-`Bₙ₊₁` weight, `DynkinType.weightDegree` of
`DynkinType.B (n + 1)` read on weights indexed by `Fin (n + 1)`. The rank of
`DynkinType.B (n + 1)` is `n + 1` only up to unfolding, so this restatement is what lets it order
the spin weights `DynkinType.typeBSpinWeight`. -/
def weightDegree : (Fin (n + 1) → ℤ) →+ ℚ :=
  (DynkinType.B (n + 1)).weightDegree ht

/-- Every simple-root row of the type-`Bₙ₊₁` Cartan matrix, the weight of a positive numbered
root generator, has height one. -/
@[simp]
theorem weightDegree_cartanMatrix_row (i : Fin (n + 1)) :
    weightDegree n ht (CartanMatrix.B (n + 1) i) = 1 := by
  rw [weightDegree, ← DynkinType.cartanMatrix_B]
  exact DynkinType.weightDegree_cartanMatrix_row (DynkinType.B (n + 1)) ht i

/-- The exterior basis of the type-`Bₙ₊₁` spin module renumbered by decreasing simple-root height
of its weights. Indices of equal height are ordered by an arbitrary finite numbering. -/
def weightOrderEquiv : Fin (dimension n) ≃ Fin (dimension n) :=
  (Fintype.equivFin (Finset (Fin (n + 1)))).symm.trans
    (orderedWeightIndexEquiv (weightDegree n ht) DynkinType.typeBSpinWeight)

/-- Renumbering the spin lattice basis by `weightOrderEquiv` gives the ordered weight basis. -/
theorem latticeBasis_reindex_weightOrderEquiv :
    (latticeBasis n).reindex (weightOrderEquiv n ht) =
      orderedWeightBasis (weightDegree n ht) DynkinType.typeBSpinWeight
        (TauCeti.ExteriorAlgebra.integralLatticeBasis (polarizationBasis n)) := by
  ext x
  rw [Module.Basis.reindex_apply, orderedWeightBasis_apply, coe_latticeBasis,
    TauCeti.ExteriorAlgebra.coe_integralLatticeBasis]
  simp [weightOrderEquiv, signSet]

/-- After renumbering by decreasing weight height, every positive numbered root-subgroup matrix
of the spin carrier is upper unitriangular, over every commutative ring. -/
theorem isUpperUnitriangular_reindexGL_rootSubgroupPoints_inl (i : Fin (n + 1)) (A : Type*)
    [CommRing A] (u : Multiplicative A) :
    (((weightOrderEquiv n ht).reindexGL A (rootSubgroupPoints n (.inl i) A u) :
        Matrix.GeneralLinearGroup (Fin (dimension n)) A) :
      Matrix (Fin (dimension n)) (Fin (dimension n)) A).IsUpperUnitriangular := by
  have hwt (s : Finset (Fin (n + 1))) := by
    have h := (polarization n).isCartanWeightVector_typeBSpinRep_exteriorBasis
      (polarizationBasis n) (remainderOne n) (TauCeti.splitOddForm_remainderOne ℚ (n + 1)) s
    rwa [← TauCeti.ExteriorAlgebra.coe_integralLatticeBasis] at h
  have h := isUpperUnitriangular_kostantRootSubgroupMatrix_orderedWeightBasis
    (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
    (TauCeti.typeBSimpleCorootGenerator (K := ℚ))
    (rep n) (lattice n).toAddSubgroup (rep_kostantForm_mem_lattice n)
    (TauCeti.ExteriorAlgebra.integralLatticeBasis (polarizationBasis n))
    DynkinType.typeBSpinWeight (weightDegree n ht) hwt
    (isNilpotent_rep_rootGenerator n (.inl i))
    (lie_coroot_rootGenerator n (.inl i))
    (by simp)
    ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm u)
  rw [← latticeBasis_reindex_weightOrderEquiv] at h
  convert h using 1
  ext r s
  rw [Equiv.coe_reindexGL, Matrix.submatrix_apply, coe_rootSubgroupPoints,
    kostantRootSubgroupMatrix_reindex_apply]

variable (A : Type u) [CommRing A]

/-- After conjugation by the permutation matrix of `weightOrderEquiv`, the generated positive
subgroup lies scheme-theoretically in the upper-triangular subgroup of `GL_(2^(n+1))`. -/
theorem upperTriangular_comap_le_definingIdeal :
    (GeneralLinear.UpperTriangular.definingHopfIdeal A (dimension n)).comapOfSurjective
      (GeneralLinear.conjCoordinateIso (permutationGL (k := A) (weightOrderEquiv n ht))).inv.hom
      (ConcreteCategory.bijective_of_isIso
        (GeneralLinear.conjCoordinateIso (permutationGL (k := A) (weightOrderEquiv n ht))).inv).2 ≤
      definingIdeal n A := by
  rw [le_definingIdeal_iff]
  constructor
  · intro i
    apply GeneralLinear.UpperTriangular.comap_le_ker_of_conjugate
    let B := AdditiveGroup.coordinateHopfAlgebra A
    let q : HopfAlgebra.points (R := A) (H := B) (CommAlgCat.of A B) :=
      toConv (AlgHom.id A B)
    have h := pointToGeneralLinear_mapDomain_generatedCoordinateLift_inl_eq_rootSubgroupPoints
      n A (.inl i) q
    have hpoint : GeneralLinear.pointsMulEquiv (dimension n)
        (toConv (generatorCoordinateMap n A (.inl (.inl i))).hom.toAlgHom) =
        (rootSubgroupPoints n (.inl i) B (AdditiveGroup.gaPointsMulEquiv q) :
          Matrix.GeneralLinearGroup (Fin (dimension n)) B) := by
      rw [GeneralLinear.pointsMulEquiv_apply,
        ← generatedCoordinateMap_comp_generatedCoordinateLift]
      simpa only [AlgHom.mapDomain_apply, q, B, ofConv_toConv, AlgHom.id_comp,
        _root_.CommHopfAlgCat.hom_comp, BialgHom.comp_toAlgHom] using h
    rw [hpoint, map_permutationGL, permutationGL_mul_mul_inv]
    exact (isUpperUnitriangular_reindexGL_rootSubgroupPoints_inl n ht i B
      (AdditiveGroup.gaPointsMulEquiv q)).isUpperTriangular
  · apply GeneralLinear.UpperTriangular.comap_le_ker_of_conjugate
    rw [map_permutationGL, permutationGL_mul_mul_inv]
    rintro r s (hsr : s < r)
    simp [GeneralLinear.pointsMulEquiv_apply, GeneralLinear.pointToGeneralLinear_apply,
      generatorCoordinateMap_inr, GeneralLinear.hom_weightTorusBaseChangeCoordinateMap,
      DiagonalizableGroup.diagonalCoordinateMap_X, hsr.ne']

/-- The surjective coordinate map from the upper-triangular subgroup of `GL_(2^(n+1))` onto the
positive subgroup, induced by conjugation by the permutation matrix of `weightOrderEquiv`. -/
def upperTriangularCoordinateMap :
    GeneralLinear.UpperTriangular.coordinateHopfAlgebra A (dimension n) ⟶
      coordinateHopfAlgebra n A :=
  (CommHopfAlgCat.quotientIsoOfIso
      (GeneralLinear.conjCoordinateIso (permutationGL (k := A) (weightOrderEquiv n ht))).symm
      (GeneralLinear.UpperTriangular.definingHopfIdeal A (dimension n))).inv ≫
    CommHopfAlgCat.quotientMapOfLe (GeneralLinear.coordinateHopfAlgebra A (dimension n))
      (upperTriangular_comap_le_definingIdeal n ht A)

/-- The coordinate map from the upper-triangular subgroup onto the positive subgroup is
surjective, so it embeds the positive subgroup into the upper-triangular subgroup. -/
theorem upperTriangularCoordinateMap_surjective :
    Function.Surjective (upperTriangularCoordinateMap n ht A) :=
  (CommHopfAlgCat.quotientMapOfLe_surjective _ _).comp
    (ConcreteCategory.bijective_of_isIso
      (CommHopfAlgCat.quotientIsoOfIso
        (GeneralLinear.conjCoordinateIso (permutationGL (k := A) (weightOrderEquiv n ht))).symm
        (GeneralLinear.UpperTriangular.definingHopfIdeal A (dimension n))).inv).2

variable (k : Type u) [Field k]

include ht in
/-- The positive subgroup has solvable geometric points over any field. -/
theorem geometricallySolvablePoints_coordinateHopfAlgebra :
    geometricallySolvablePointsCommHopfAlgProperty k (coordinateHopfAlgebra n k) :=
  geometricallySolvablePointsCommHopfAlgProperty_of_surjective k
    (upperTriangularCoordinateMap n ht k) (upperTriangularCoordinateMap_surjective n ht k)
    (geometricallySolvablePointsCommHopfAlgProperty_coordinateHopfAlgebra k (dimension n))

include ht in
/-- The positive subgroup of the generated type-`Bₙ₊₁` spin group is a Borel candidate over every
field: smooth, geometrically connected and geometrically solvable. -/
theorem isBorelCandidate_carrierDefiningIdeal :
    HopfIdeal.IsBorelCandidate k
      (FiniteTypeCommHopfAlgCat.of k (generatedCoordinateHopfAlgebra n k))
      (carrierDefiningIdeal n k) := by
  let e : (FiniteTypeCommHopfAlgCat.quotient
      (FiniteTypeCommHopfAlgCat.of k (generatedCoordinateHopfAlgebra n k))
      (carrierDefiningIdeal n k)).obj ≅ coordinateHopfAlgebra n k :=
    CommHopfAlgCat.quotientIsoOfKerOfSurjectiveEq
      (restriction n k) (restriction_surjective n k) (kerOfSurjective_restriction n k)
  exact HopfIdeal.IsBorelCandidate.mk
    ((smoothCommHopfAlgProperty k).prop_of_iso e.symm (smooth_coordinateHopfAlgebra n k))
    ((geometricallyConnectedCommHopfAlgProperty k).prop_of_iso e.symm
      (geometricallyConnected_coordinateHopfAlgebra n k))
    ((geometricallySolvablePointsCommHopfAlgProperty k).prop_of_iso e.symm
      (geometricallySolvablePoints_coordinateHopfAlgebra n ht k))

end

end TauCeti.TypeBSpinCarrier.Generated.Positive
