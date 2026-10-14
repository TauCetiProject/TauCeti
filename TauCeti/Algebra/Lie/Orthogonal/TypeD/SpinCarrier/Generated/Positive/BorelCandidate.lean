/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Generated.Positive.Basic
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Generated.StandardComodule
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Weight.Order
public import TauCeti.Algebra.AlgebraicGroup.Borel.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.Solvable.UpperTriangular
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Equivalence
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.WeightDegree

/-!
# A Borel candidate in the generated type-Dₙ spin group

The positive subgroup generated over any field by the positive numbered simple-root subgroups and
the weight torus of the full-weight type-`Dₙ` spin carrier is a Borel candidate: it is smooth,
geometrically connected and geometrically solvable.

The exterior basis of the spin module is numbered independently of its weights. Renumbering it by
decreasing simple-root height of the spin weights, `weightOrderEquiv`, makes every positive
numbered root subgroup upper unitriangular, since a raising operator adds a simple root to the
weight. The weight torus stays diagonal. Conjugation by the corresponding permutation matrix,
`weightOrderMatrix`, therefore carries the positive subgroup scheme-theoretically into the
upper-triangular subgroup of `GL_(2^n)`, and its geometric points form solvable groups.

`isBorelCandidate_carrierDefiningIdeal` expresses this inside the generated spin group.
Maximality among smooth connected solvable subgroups is not asserted, and neither the generated
spin group nor this subgroup is identified with the pinned simply connected group scheme of type
`Dₙ` or its Borel subgroup.

## Main declarations

* `TauCeti.TypeDSpinCarrier.Generated.Positive.weightOrderEquiv` and
  `TauCeti.TypeDSpinCarrier.Generated.Positive.weightOrderMatrix`: the renumbering of the spin
  basis by decreasing weight height, and its permutation matrix.
* `TauCeti.TypeDSpinCarrier.Generated.Positive.upperTriangular_comap_le_definingIdeal`: after
  that conjugation, the positive subgroup lies in the upper-triangular subgroup.
* `TauCeti.TypeDSpinCarrier.Generated.Positive.isBorelCandidate_carrierDefiningIdeal`: the
  positive subgroup is a Borel candidate in the generated spin group over every field.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§21 and 26–28.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 17.
* The argument follows `TauCeti.Algebra.Lie.E7.Minuscule.Generated.Positive.BorelCandidate`, with
  the weight-ordering conjugation of
  `TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Positive.Triangular.Basic`.
-/

public section

open CategoryTheory WithConv
open TauCeti.UniversalEnvelopingAlgebra
open TauCeti.GeneralLinear.UpperTriangular
  (geometricallySolvablePointsCommHopfAlgProperty_coordinateHopfAlgebra)
attribute [local instance high] Algebra.toModule

namespace TauCeti.TypeDSpinCarrier.Generated.Positive

universe u

noncomputable section

variable (n : ℕ) (hn : 4 ≤ n)

/-- The simple-root height of an integral type-`Dₙ` weight, `DynkinType.weightDegree` of
`DynkinType.D n` read on weights indexed by `Fin n`. The rank of `DynkinType.D n` is `n` only up to
unfolding, so this restatement is what lets it order the spin weights `DynkinType.typeDSpinWeight`.
-/
def weightDegree : (Fin n → ℤ) →+ ℚ :=
  (DynkinType.D n).weightDegree (DynkinType.valid_D.mpr hn)

/-- Each positive numbered root generator has a simple root as weight, of height one. -/
@[simp]
theorem weightDegree_rootGeneratorWeight_inl (i : Fin n) :
    weightDegree n hn (TypeDStd.rootGeneratorWeight n (.inl i)) = 1 := by
  have hrow : TypeDStd.rootGeneratorWeight n (.inl i) =
      fun j ↦ (DynkinType.D n).cartanMatrix i j := by
    funext j
    rw [TypeDStd.rootGeneratorWeight_inl, DynkinType.cartanMatrix_D]
  rw [hrow]
  exact DynkinType.weightDegree_cartanMatrix_row (DynkinType.D n) (DynkinType.valid_D.mpr hn) i

/-- The exterior basis of the type-`Dₙ` spin module renumbered by decreasing simple-root height
of its weights. Indices of equal height are ordered by an arbitrary finite numbering. -/
def weightOrderEquiv : Fin (dimension n) ≃ Fin (dimension n) :=
  (Fintype.equivFin (Finset (Fin n))).symm.trans
    (orderedWeightIndexEquiv (weightDegree n hn) DynkinType.typeDSpinWeight)

/-- Renumbering the spin lattice basis by `weightOrderEquiv` gives the ordered weight basis. -/
theorem latticeBasis_reindex_weightOrderEquiv :
    (latticeBasis n).reindex (weightOrderEquiv n hn) =
      orderedWeightBasis (weightDegree n hn) DynkinType.typeDSpinWeight
        (TauCeti.ExteriorAlgebra.integralLatticeBasis (polarizationBasis n)) := by
  ext x
  rw [Module.Basis.reindex_apply, orderedWeightBasis_apply, coe_latticeBasis,
    TauCeti.ExteriorAlgebra.coe_integralLatticeBasis]
  simp [weightOrderEquiv, signSet]

/-- The permutation matrix renumbering the spin basis by decreasing weight height. -/
def weightOrderMatrix (R : Type*) [CommRing R] :
    Matrix.GeneralLinearGroup (Fin (dimension n)) R :=
  Matrix.permMatrixHom.toHomUnits (weightOrderEquiv n hn)

/-- Over every algebra, the weight-ordering matrix is the permutation matrix of
`weightOrderEquiv`. -/
theorem coe_map_weightOrderMatrix (R : Type*) [CommRing R] {A : Type*} [CommRing A]
    [Algebra R A] :
    (Matrix.GeneralLinearGroup.map (algebraMap R A) (weightOrderMatrix n hn R) :
      Matrix (Fin (dimension n)) (Fin (dimension n)) A) =
      (weightOrderEquiv n hn).symm.toPEquiv.toMatrix := by
  ext r s
  simp [weightOrderMatrix, Matrix.GeneralLinearGroup.map, PEquiv.toMatrix_apply]

/-- Conjugation by the weight-ordering matrix renumbers the rows and columns of a matrix. -/
theorem conj_weightOrderMatrix (R : Type*) [CommRing R] {A : Type*} [CommRing A] [Algebra R A]
    (g : Matrix.GeneralLinearGroup (Fin (dimension n)) A) :
    Matrix.GeneralLinearGroup.map (algebraMap R A) (weightOrderMatrix n hn R) * g *
        (Matrix.GeneralLinearGroup.map (algebraMap R A) (weightOrderMatrix n hn R))⁻¹ =
      (weightOrderEquiv n hn).reindexGL A g := by
  apply (mul_inv_eq_iff_eq_mul).2
  apply Units.ext
  simp only [Units.val_mul, coe_map_weightOrderMatrix, Equiv.coe_reindexGL,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext r s
  simp

/-- After renumbering by decreasing weight height, every positive numbered root-subgroup matrix
of the spin carrier is upper unitriangular, over every commutative ring. -/
theorem isUpperUnitriangular_reindexGL_rootSubgroupPoints_inl (i : Fin n) (A : Type*)
    [CommRing A] (u : Multiplicative A) :
    (((weightOrderEquiv n hn).reindexGL A (rootSubgroupPoints n hn (.inl i) A u) :
        Matrix.GeneralLinearGroup (Fin (dimension n)) A) :
      Matrix (Fin (dimension n)) (Fin (dimension n)) A).IsUpperUnitriangular := by
  have h := isUpperUnitriangular_kostantRootSubgroupMatrix_orderedWeightBasis
    (TauCeti.serreRootGenerator (CartanMatrix.D n)) (TauCeti.serreH ℚ (CartanMatrix.D n))
    (rep n hn) (lattice n).toAddSubgroup (rep_kostantForm_mem_lattice n hn)
    (TauCeti.ExteriorAlgebra.integralLatticeBasis (polarizationBasis n))
    DynkinType.typeDSpinWeight (weightDegree n hn)
    ((polarization n).isCartanWeightVector_typeDSpinRep_integralLatticeBasis
      (polarizationBasis n) hn)
    (isNilpotent_rep_rootGenerator n hn (.inl i))
    (TypeDStd.lie_serreH_serreRootGenerator n (.inl i))
    (by rw [weightDegree_rootGeneratorWeight_inl]; norm_num)
    ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm u)
  rw [← latticeBasis_reindex_weightOrderEquiv] at h
  rw [Matrix.isUpperUnitriangular_def] at h ⊢
  refine ⟨fun r s hsr ↦ ?_, fun r ↦ ?_⟩
  · simpa [Equiv.coe_reindexGL, coe_rootSubgroupPoints, kostantRootSubgroupMatrix_reindex_apply]
      using h.1 hsr
  · simpa [Equiv.coe_reindexGL, coe_rootSubgroupPoints, kostantRootSubgroupMatrix_reindex_apply]
      using h.2 r

variable (A : Type u) [CommRing A]

/-- After conjugation by the weight-ordering matrix, the generated positive subgroup lies
scheme-theoretically in the upper-triangular subgroup of `GL_(2^n)`. -/
theorem upperTriangular_comap_le_definingIdeal :
    (GeneralLinear.UpperTriangular.definingHopfIdeal A (dimension n)).comapOfSurjective
      (GeneralLinear.conjCoordinateIso (weightOrderMatrix n hn A)).inv.hom
      (ConcreteCategory.bijective_of_isIso
        (GeneralLinear.conjCoordinateIso (weightOrderMatrix n hn A)).inv).2 ≤
      definingIdeal n hn A := by
  rw [le_definingIdeal_iff]
  constructor
  · intro i
    apply GeneralLinear.UpperTriangular.comap_le_ker_of_conjugate
    let B := AdditiveGroup.coordinateHopfAlgebra A
    let q : HopfAlgebra.points (R := A) (H := B) (CommAlgCat.of A B) :=
      toConv (AlgHom.id A B)
    have h := pointToGeneralLinear_mapDomain_generatedCoordinateLift_inl_eq_rootSubgroupPoints
      n hn A (.inl i) (CommAlgCat.of A B) q
    have hpoint : GeneralLinear.pointsMulEquiv (dimension n)
        (toConv (generatorCoordinateMap n hn A (.inl (.inl i))).hom.toAlgHom) =
        (rootSubgroupPoints n hn (.inl i) B (AdditiveGroup.gaPointsMulEquiv q) :
          Matrix.GeneralLinearGroup (Fin (dimension n)) B) := by
      rw [GeneralLinear.pointsMulEquiv_apply,
        ← generatedCoordinateMap_comp_generatedCoordinateLift]
      simpa only [AlgHom.mapDomain_apply, q, B, ofConv_toConv, AlgHom.id_comp,
        _root_.CommHopfAlgCat.hom_comp, BialgHom.comp_toAlgHom] using h
    rw [hpoint, conj_weightOrderMatrix]
    exact (isUpperUnitriangular_reindexGL_rootSubgroupPoints_inl n hn i B
      (AdditiveGroup.gaPointsMulEquiv q)).isUpperTriangular
  · apply GeneralLinear.UpperTriangular.comap_le_ker_of_conjugate
    rw [conj_weightOrderMatrix]
    intro r s hsr
    rw [Equiv.coe_reindexGL, Matrix.submatrix_apply, GeneralLinear.pointsMulEquiv_apply,
      GeneralLinear.pointToGeneralLinear_apply, ofConv_toConv, generatorCoordinateMap_inr,
      GeneralLinear.hom_weightTorusBaseChangeCoordinateMap, BialgHom.coe_toAlgHom,
      GeneralLinear.weightTorusCoordinateBialgHom_X]
    exact ite_eq_right_iff.mpr fun h ↦ absurd ((weightOrderEquiv n hn).symm.injective h) hsr.ne'

variable (k : Type u) [Field k]

/-- The surjective coordinate map from the upper-triangular subgroup of `GL_(2^n)` onto the
positive subgroup, induced by conjugation by the weight-ordering matrix. -/
def upperTriangularCoordinateMap :
    GeneralLinear.UpperTriangular.coordinateHopfAlgebra A (dimension n) ⟶
      coordinateHopfAlgebra n hn A :=
  (CommHopfAlgCat.quotientIsoOfIso
      (GeneralLinear.conjCoordinateIso (weightOrderMatrix n hn A)).symm
      (GeneralLinear.UpperTriangular.definingHopfIdeal A (dimension n))).inv ≫
    CommHopfAlgCat.quotientMapOfLe (GeneralLinear.coordinateHopfAlgebra A (dimension n))
      (upperTriangular_comap_le_definingIdeal n hn A)

/-- The coordinate map from the upper-triangular subgroup onto the positive subgroup is
surjective, so it embeds the positive subgroup into the upper-triangular subgroup. -/
theorem upperTriangularCoordinateMap_surjective :
    Function.Surjective (upperTriangularCoordinateMap n hn A) :=
  (CommHopfAlgCat.quotientMapOfLe_surjective _ _).comp
    (ConcreteCategory.bijective_of_isIso
      (CommHopfAlgCat.quotientIsoOfIso
        (GeneralLinear.conjCoordinateIso (weightOrderMatrix n hn A)).symm
        (GeneralLinear.UpperTriangular.definingHopfIdeal A (dimension n))).inv).2

/-- The positive subgroup has solvable geometric points over any field. -/
theorem geometricallySolvablePoints_coordinateHopfAlgebra :
    geometricallySolvablePointsCommHopfAlgProperty k (coordinateHopfAlgebra n hn k) :=
  geometricallySolvablePointsCommHopfAlgProperty_of_surjective k
    (upperTriangularCoordinateMap n hn k) (upperTriangularCoordinateMap_surjective n hn k)
    (geometricallySolvablePointsCommHopfAlgProperty_coordinateHopfAlgebra k (dimension n))

/-- The positive subgroup of the generated type-`Dₙ` spin group is a Borel candidate over every
field: smooth, geometrically connected and geometrically solvable. -/
theorem isBorelCandidate_carrierDefiningIdeal :
    HopfIdeal.IsBorelCandidate k
      (FiniteTypeCommHopfAlgCat.of k (generatedCoordinateHopfAlgebra n hn k))
      (carrierDefiningIdeal n hn k) := by
  let e : (FiniteTypeCommHopfAlgCat.quotient
      (FiniteTypeCommHopfAlgCat.of k (generatedCoordinateHopfAlgebra n hn k))
      (carrierDefiningIdeal n hn k)).obj ≅ coordinateHopfAlgebra n hn k :=
    CommHopfAlgCat.quotientIsoOfKerOfSurjectiveEq
      (restriction n hn k) (restriction_surjective n hn k) (kerOfSurjective_restriction n hn k)
  exact HopfIdeal.IsBorelCandidate.mk
    ((smoothCommHopfAlgProperty k).prop_of_iso e.symm (smooth_coordinateHopfAlgebra n hn k))
    ((geometricallyConnectedCommHopfAlgProperty k).prop_of_iso e.symm
      (geometricallyConnected_coordinateHopfAlgebra n hn k))
    ((geometricallySolvablePointsCommHopfAlgProperty k).prop_of_iso e.symm
      (geometricallySolvablePoints_coordinateHopfAlgebra n hn k))

end

end TauCeti.TypeDSpinCarrier.Generated.Positive
