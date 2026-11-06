/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Datum
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Subgroup

/-!
# All-root morphisms into the group scheme of a Chevalley datum

For every numbered root, the divided-power exponential on an admissible lattice is a polynomial
map, not just a homomorphism on field-valued points. This file factors its integral group-scheme
morphism through the group scheme of a Chevalley datum. The factorization uses the universal
additive-group point: the Weyl conjugation theorem puts its exponential in the elementary group,
so it annihilates the defining Hopf ideal. In particular this works over nonreduced value rings
and does not infer an integral identity from points over fields.

`TauCeti.DynkinType.ChevalleyDatum.rootSubgroupScheme` is the resulting morphism
`𝔾ₐ → G_D`. Its composite into `GLₙ` is the polynomial exponential, and its action on
scheme-valued points is the original lattice action in the datum's weight basis. This file does
not assert that these morphisms are closed immersions.

The construction uses the all-root exponential and Weyl conjugation of
`TauCeti.DynkinType.chevalleyRootSubgroup`, and the polynomial reconstruction
`TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroup`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open AlgebraicGeometry CategoryTheory TensorProduct WithConv
open TauCeti.UniversalEnvelopingAlgebra
open scoped CategoryTheory.MonObj

namespace TauCeti.DynkinType.ChevalleyDatum

noncomputable section

-- Use the scalar-action instance carried by the value algebra in the lattice tensor product.
attribute [local instance high] Algebra.toModule

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- The all-root Kostant form preserves the admissible lattice of a Chevalley datum. -/
theorem representation_allRootKostantForm_mem_lattice :
    ∀ u ∈ UniversalEnvelopingAlgebra.kostantForm (t.chevalleySystem ht) (t.lieBasis ht).h,
      ∀ v ∈ D.lattice, D.representation u v ∈ D.lattice := by
  intro u hu v hv
  apply kostantForm_apply_mem (t.chevalleySystem ht) (t.lieBasis ht).h
    D.representation D.lattice.toIntSubmodule _ _ u hu hv
  · intro γ n w hw
    rw [Associative.map_dividedPower]
    exact dividedPower_chevalleySystem_smul_mem D.representation D.lattice
      D.representation_mem_lattice D.isNilpotent_representation_rootGenerator γ n w hw
  · intro i n w hw
    exact D.representation_mem_lattice _
      (UniversalEnvelopingAlgebra.ringChoose_mem_kostantForm _ _ i n) w hw

/-- Every Chevalley root vector acts nilpotently in the representation of a Chevalley datum. -/
theorem isNilpotent_representation_chevalleySystem (γ : Fin t.numRoots) :
    IsNilpotent (D.representation
      (_root_.UniversalEnvelopingAlgebra.ι ℚ (t.chevalleySystem ht γ))) :=
  isNilpotent_apply_ι_chevalleySystem D.representation
    D.isNilpotent_representation_rootGenerator γ

/-- The polynomial exponential of a root, in the datum's weight basis, is the matrix of the
all-root lattice action. -/
theorem kostantRootSubgroupMatrix_eq_matrix_chevalleyRootSubgroup
    (γ : Fin t.numRoots) (A : Type*) [CommRing A]
    (q : HopfAlgebra.points (R := ℤ) (H := AdditiveGroup.coordinateHopfAlgebra ℤ)
      (CommAlgCat.of ℤ A)) :
    kostantRootSubgroupMatrix (t.chevalleySystem ht) (t.lieBasis ht).h D.representation D.lattice
        D.representation_allRootKostantForm_mem_lattice γ
        (D.isNilpotent_representation_chevalleySystem γ) D.basis q =
      Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMulEquiv
        (chevalleyRootSubgroup D.representation D.lattice D.representation_mem_lattice
          D.isNilpotent_representation_rootGenerator γ (CommAlgCat.of ℤ A)
          (AdditiveGroup.gaPointsMulEquiv q)) := by
  rw [kostantRootSubgroupMatrix_def, MonoidHom.comp_apply]
  congr 1
  apply Units.ext
  rw [kostantRootSubgroupPoints_val, chevalleyRootSubgroup_val]

/-- The ambient coordinate morphism of every root kills the defining ideal of the datum's
integral group scheme. This is tested at the universal additive-group point. -/
theorem definingIdeal_le_ker_rootCoordinateMap (γ : Fin t.numRoots) :
    (kostantToralDefiningIdeal (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
      D.representation D.lattice D.representation_mem_lattice
      D.isNilpotent_representation_rootGenerator D.basis D.coordinateWeight).toIdeal ≤
    RingHom.ker (kostantRootSubgroupCoordinateMap (t.chevalleySystem ht) (t.lieBasis ht).h
      D.representation D.lattice D.representation_allRootKostantForm_mem_lattice γ
      (D.isNilpotent_representation_chevalleySystem γ) D.basis).hom.toAlgHom.toRingHom := by
  let A : Type := AdditiveGroup.coordinateHopfAlgebra ℤ
  have hmem := chevalleyRootSubgroup_mem_kostantElementarySubgroup D.representation D.lattice
    D.representation_mem_lattice D.isNilpotent_representation_rootGenerator γ
    (CommAlgCat.of ℤ A) (AdditiveGroup.gaPointsMulEquiv (toConv (AlgHom.id ℤ A)))
  have hmatrix : kostantRootSubgroupMatrix (t.chevalleySystem ht) (t.lieBasis ht).h
      D.representation D.lattice D.representation_allRootKostantForm_mem_lattice γ
      (D.isNilpotent_representation_chevalleySystem γ) D.basis (toConv (AlgHom.id ℤ A)) ∈
      kostantGeneratedPointsSubgroup (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        D.representation D.lattice D.representation_mem_lattice
        D.isNilpotent_representation_rootGenerator D.basis A := by
    rw [D.kostantRootSubgroupMatrix_eq_matrix_chevalleyRootSubgroup]
    exact map_kostantElementarySubgroup_le_generatedPoints
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h D.representation D.lattice
      D.representation_mem_lattice D.isNilpotent_representation_rootGenerator D.basis A
      (Subgroup.mem_map_of_mem _ hmem)
  have htoral := kostantGeneratedPointsSubgroup_le_toralPoints
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h D.representation D.lattice
    D.representation_mem_lattice D.isNilpotent_representation_rootGenerator D.basis
    D.coordinateWeight A hmatrix
  rw [kostantToralPointsSubgroup_def,
    ← pointsMulEquiv_kostantRootSubgroupCoordinateMap,
    GeneralLinear.pointToGeneralLinear_mem_hopfIdealPointsSubgroup_iff_toIdeal_le_ker] at htoral
  exact htoral

/-- The coordinate morphism of a root subgroup, factored through the datum's coordinate Hopf
algebra. -/
def rootCoordinateMap (γ : Fin t.numRoots) :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ D.dim)
        (kostantToralDefiningIdeal (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
          D.representation D.lattice D.representation_mem_lattice
          D.isNilpotent_representation_rootGenerator D.basis D.coordinateWeight) ⟶
      AdditiveGroup.coordinateHopfAlgebra ℤ :=
  CommHopfAlgCat.liftQuotient _
    (kostantRootSubgroupCoordinateMap (t.chevalleySystem ht) (t.lieBasis ht).h D.representation
      D.lattice D.representation_allRootKostantForm_mem_lattice γ
      (D.isNilpotent_representation_chevalleySystem γ) D.basis)
    (D.definingIdeal_le_ker_rootCoordinateMap γ)

/-- The factored root coordinate morphism recovers the ambient polynomial exponential. -/
@[simp]
theorem mkQuotient_comp_rootCoordinateMap (γ : Fin t.numRoots) :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ D.dim)
        (kostantToralDefiningIdeal (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
          D.representation D.lattice D.representation_mem_lattice
          D.isNilpotent_representation_rootGenerator D.basis D.coordinateWeight) ≫
      D.rootCoordinateMap γ =
    kostantRootSubgroupCoordinateMap (t.chevalleySystem ht) (t.lieBasis ht).h D.representation
      D.lattice D.representation_allRootKostantForm_mem_lattice γ
      (D.isNilpotent_representation_chevalleySystem γ) D.basis :=
  CommHopfAlgCat.mkQuotient_comp_liftQuotient _ _ _

/-- The integral root-subgroup morphism `𝔾ₐ → G_D` for every numbered root. Its composite
into the general linear group is the divided-power exponential of the named root vector. -/
def rootSubgroupScheme (γ : Fin t.numRoots) :
    AdditiveGroup.groupScheme ℤ ⟶ D.groupScheme :=
  eqToHom (AdditiveGroup.groupScheme_def ℤ) ≫
    (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).map (D.rootCoordinateMap γ).op

/-- The root morphism is the relative spectrum of its factored coordinate morphism. -/
theorem rootSubgroupScheme_def (γ : Fin t.numRoots) :
    D.rootSubgroupScheme γ = eqToHom (AdditiveGroup.groupScheme_def ℤ) ≫
      (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).map (D.rootCoordinateMap γ).op :=
  (rfl)

/-- Including the root morphism into `GLₙ` recovers the original polynomial exponential. -/
@[simp]
theorem rootSubgroupScheme_comp_groupSchemeι (γ : Fin t.numRoots) :
    D.rootSubgroupScheme γ ≫ D.groupSchemeι =
      kostantRootSubgroup (t.chevalleySystem ht) (t.lieBasis ht).h D.representation D.lattice
        D.representation_allRootKostantForm_mem_lattice γ
        (D.isNilpotent_representation_chevalleySystem γ) D.basis := by
  rw [rootSubgroupScheme_def, groupSchemeι_def, kostantToralGroupSchemeι_def,
    CommHopfAlgCat.quotientSpecι_def, kostantRootSubgroup_def]
  slice_lhs 2 3 =>
    rw [← (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).map_comp,
      ← op_comp, mkQuotient_comp_rootCoordinateMap]

/-- On scheme-valued points the root morphism acts by the original all-root lattice
exponential, expressed in the weight basis of the datum. -/
theorem schemePointsMulEquiv_rootSubgroupScheme (γ : Fin t.numRoots) (A : Type) [CommRing A]
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (AdditiveGroup.groupScheme ℤ).X) :
    GeneralLinear.schemePointsMulEquiv D.dim A
        (p ≫ (D.rootSubgroupScheme γ).hom.hom ≫ D.groupSchemeι.hom.hom) =
      kostantRootSubgroupMatrix (t.chevalleySystem ht) (t.lieBasis ht).h D.representation
        D.lattice D.representation_allRootKostantForm_mem_lattice γ
        (D.isNilpotent_representation_chevalleySystem γ) D.basis
        ((AdditiveGroup.groupSchemePointMulEquiv A).symm p) := by
  have h : (D.rootSubgroupScheme γ).hom.hom ≫ D.groupSchemeι.hom.hom =
      (kostantRootSubgroup (t.chevalleySystem ht) (t.lieBasis ht).h D.representation D.lattice
        D.representation_allRootKostantForm_mem_lattice γ
        (D.isNilpotent_representation_chevalleySystem γ) D.basis).hom.hom :=
    congrArg (fun f => f.hom.hom) (D.rootSubgroupScheme_comp_groupSchemeι γ)
  rw [h]
  exact schemePointsMulEquiv_kostantRootSubgroup _ _ _ _ _ _ _ _ A p

end

end TauCeti.DynkinType.ChevalleyDatum
