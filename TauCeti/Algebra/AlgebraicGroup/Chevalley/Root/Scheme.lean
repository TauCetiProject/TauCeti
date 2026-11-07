/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.RootSubgroup

/-!
# All-root morphisms into pinned Kostant toral group schemes

For every numbered root, the divided-power exponential on a Kostant-stable lattice is a
polynomial map, not just a homomorphism on field-valued points. This file factors its integral
group-scheme morphism through the pinned Kostant toral group scheme, and specializes it to every
Chevalley datum. The factorization uses the universal additive-group point: the Weyl conjugation
theorem puts its exponential in the elementary group, so it annihilates the defining Hopf ideal.
In particular this works over nonreduced value rings and does not infer an integral identity
from points over fields.

`TauCeti.DynkinType.chevalleyRootSubgroupToToral` needs only Kostant stability, nilpotence of the
simple generators, a lattice basis and torus characters. Its specialization
`TauCeti.DynkinType.ChevalleyDatum.rootSubgroup` is the morphism `𝔾ₐ → G_D`, distinct from
`TauCeti.DynkinType.ChevalleyDatum.rootSubgroupPoints`, the homomorphism on matrix points. Their
composites into `GLₙ` are the polynomial exponentials, agreeing at positive and negative simple
roots with the original Kostant root subgroups. Their action on scheme-valued points is the lattice
action in the chosen basis. This file does not assert that these morphisms are closed immersions.

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

namespace TauCeti.DynkinType

noncomputable section

-- Use the scalar-action instance carried by the value algebra in the lattice tensor product.
attribute [local instance high] Algebra.toModule

variable {t : DynkinType} {ht : t.Valid}

section Toral

variable {V : Type} [AddCommGroup V] [Module ℚ V]
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht) →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ UniversalEnvelopingAlgebra.kostantForm
  (t.lieBasis ht).rootGenerator (t.lieBasis ht).h,
  ∀ v ∈ M, ρ u v ∈ M)
variable (hnil : ∀ i, IsNilpotent
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator i))))
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M) (χ : Fin n → Fin t.rank → ℤ)

/-- The polynomial exponential of a root in a lattice basis is the matrix of the all-root
lattice action. -/
theorem kostantRootSubgroupMatrix_eq_matrix_chevalleyRootSubgroup
    (γ : Fin t.numRoots) (A : Type*) [CommRing A]
    (q : HopfAlgebra.points (R := ℤ) (H := AdditiveGroup.coordinateHopfAlgebra ℤ)
      (CommAlgCat.of ℤ A)) :
    kostantRootSubgroupMatrix (t.chevalleySystem ht) (t.lieBasis ht).h ρ M
        (kostantForm_chevalleySystem_apply_mem_of_isNilpotent ρ M hM hnil) γ
        (isNilpotent_apply_ι_chevalleySystem ρ hnil γ) b q =
      Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMulEquiv
        (chevalleyRootSubgroup ρ M hM hnil γ (CommAlgCat.of ℤ A)
          (AdditiveGroup.gaPointsMulEquiv q)) := by
  rw [kostantRootSubgroupMatrix_def, MonoidHom.comp_apply]
  congr 1
  apply Units.ext
  rw [kostantRootSubgroupPoints_val, chevalleyRootSubgroup_val]

/-- Every all-root exponential matrix is a point of the pinned Kostant toral closure over
any commutative value ring. -/
theorem kostantRootSubgroupMatrix_chevalleySystem_mem_toralPoints (A : Type*) [CommRing A]
    (γ : Fin t.numRoots)
    (q : HopfAlgebra.points (R := ℤ) (H := AdditiveGroup.coordinateHopfAlgebra ℤ)
      (CommAlgCat.of ℤ A)) :
    kostantRootSubgroupMatrix (t.chevalleySystem ht) (t.lieBasis ht).h ρ M
        (kostantForm_chevalleySystem_apply_mem_of_isNilpotent ρ M hM hnil) γ
        (isNilpotent_apply_ι_chevalleySystem ρ hnil γ) b q ∈
      kostantToralPointsSubgroup (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        ρ M hM hnil b χ A := by
  rw [kostantRootSubgroupMatrix_eq_matrix_chevalleyRootSubgroup ρ M hM hnil]
  exact basisMatrix_chevalleyRootSubgroup_mem_toralPoints ρ M hM hnil b χ γ A
    (AdditiveGroup.gaPointsMulEquiv q)

/-- The ambient coordinate morphism of every root kills the defining ideal of the pinned
Kostant toral closure. This is tested at the universal additive-group point. -/
theorem kostantToralDefiningIdeal_toIdeal_le_ker_kostantRootSubgroupCoordinateMap
    (γ : Fin t.numRoots) :
    (kostantToralDefiningIdeal (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
      ρ M hM hnil b χ).toIdeal ≤
    RingHom.ker (kostantRootSubgroupCoordinateMap (t.chevalleySystem ht) (t.lieBasis ht).h
      ρ M (kostantForm_chevalleySystem_apply_mem_of_isNilpotent ρ M hM hnil) γ
      (isNilpotent_apply_ι_chevalleySystem ρ hnil γ) b).hom.toAlgHom.toRingHom := by
  let A : Type := AdditiveGroup.coordinateHopfAlgebra ℤ
  have htoral := kostantRootSubgroupMatrix_chevalleySystem_mem_toralPoints ρ M hM hnil b χ A γ
    (toConv (AlgHom.id ℤ A))
  rw [kostantToralPointsSubgroup_def,
    ← pointsMulEquiv_kostantRootSubgroupCoordinateMap,
    GeneralLinear.pointToGeneralLinear_mem_hopfIdealPointsSubgroup_iff_toIdeal_le_ker] at htoral
  exact htoral

/-- The coordinate morphism of an all-root subgroup, factored through the coordinate Hopf
algebra of the pinned Kostant toral closure. -/
def chevalleyRootSubgroupToralCoordinateMap (γ : Fin t.numRoots) :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
        (kostantToralDefiningIdeal (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
          ρ M hM hnil b χ) ⟶ AdditiveGroup.coordinateHopfAlgebra ℤ :=
  CommHopfAlgCat.liftQuotient _
    (kostantRootSubgroupCoordinateMap (t.chevalleySystem ht) (t.lieBasis ht).h ρ M
      (kostantForm_chevalleySystem_apply_mem_of_isNilpotent ρ M hM hnil) γ
      (isNilpotent_apply_ι_chevalleySystem ρ hnil γ) b)
    (kostantToralDefiningIdeal_toIdeal_le_ker_kostantRootSubgroupCoordinateMap ρ M hM hnil b χ γ)

/-- The factored root coordinate morphism recovers the ambient polynomial exponential. -/
@[simp]
theorem mkQuotient_comp_chevalleyRootSubgroupToralCoordinateMap (γ : Fin t.numRoots) :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
        (kostantToralDefiningIdeal (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
          ρ M hM hnil b χ) ≫ chevalleyRootSubgroupToralCoordinateMap ρ M hM hnil b χ γ =
      kostantRootSubgroupCoordinateMap (t.chevalleySystem ht) (t.lieBasis ht).h ρ M
        (kostantForm_chevalleySystem_apply_mem_of_isNilpotent ρ M hM hnil) γ
        (isNilpotent_apply_ι_chevalleySystem ρ hnil γ) b :=
  CommHopfAlgCat.mkQuotient_comp_liftQuotient _ _ _

/-- The integral root-subgroup morphism into the pinned Kostant toral closure for every
numbered root. -/
def chevalleyRootSubgroupToToral (γ : Fin t.numRoots) :
    AdditiveGroup.groupScheme ℤ ⟶
      kostantToralGroupScheme (t.lieBasis ht).rootGenerator (t.lieBasis ht).h ρ M hM hnil b χ :=
  eqToHom (AdditiveGroup.groupScheme_def ℤ) ≫
    (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).map
      (chevalleyRootSubgroupToralCoordinateMap ρ M hM hnil b χ γ).op

/-- The all-root morphism is the relative spectrum of its factored coordinate morphism. -/
theorem chevalleyRootSubgroupToToral_def (γ : Fin t.numRoots) :
    chevalleyRootSubgroupToToral ρ M hM hnil b χ γ =
      eqToHom (AdditiveGroup.groupScheme_def ℤ) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).map
          (chevalleyRootSubgroupToralCoordinateMap ρ M hM hnil b χ γ).op :=
  (rfl)

/-- Including the all-root morphism into `GLₙ` recovers the polynomial exponential. -/
@[simp]
theorem chevalleyRootSubgroupToToral_comp_ι (γ : Fin t.numRoots) :
    chevalleyRootSubgroupToToral ρ M hM hnil b χ γ ≫
        kostantToralGroupSchemeι (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
          ρ M hM hnil b χ =
      kostantRootSubgroup (t.chevalleySystem ht) (t.lieBasis ht).h ρ M
        (kostantForm_chevalleySystem_apply_mem_of_isNilpotent ρ M hM hnil) γ
        (isNilpotent_apply_ι_chevalleySystem ρ hnil γ) b := by
  rw [chevalleyRootSubgroupToToral_def, kostantToralGroupSchemeι_def,
    CommHopfAlgCat.quotientSpecι_def, kostantRootSubgroup_def]
  slice_lhs 2 3 =>
    rw [← (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).map_comp,
      ← op_comp, mkQuotient_comp_chevalleyRootSubgroupToralCoordinateMap]

/-- On scheme-valued points the all-root morphism acts by the lattice exponential in the
chosen basis. -/
theorem schemePointsMulEquiv_chevalleyRootSubgroupToToral (γ : Fin t.numRoots)
    (A : Type) [CommRing A]
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (AdditiveGroup.groupScheme ℤ).X) :
    GeneralLinear.schemePointsMulEquiv n A
        (p ≫ (chevalleyRootSubgroupToToral ρ M hM hnil b χ γ).hom.hom ≫
          (kostantToralGroupSchemeι (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
            ρ M hM hnil b χ).hom.hom) =
      kostantRootSubgroupMatrix (t.chevalleySystem ht) (t.lieBasis ht).h ρ M
        (kostantForm_chevalleySystem_apply_mem_of_isNilpotent ρ M hM hnil) γ
        (isNilpotent_apply_ι_chevalleySystem ρ hnil γ) b
        ((AdditiveGroup.groupSchemePointMulEquiv A).symm p) := by
  have h : (chevalleyRootSubgroupToToral ρ M hM hnil b χ γ).hom.hom ≫
      (kostantToralGroupSchemeι (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        ρ M hM hnil b χ).hom.hom =
      (kostantRootSubgroup (t.chevalleySystem ht) (t.lieBasis ht).h ρ M
        (kostantForm_chevalleySystem_apply_mem_of_isNilpotent ρ M hM hnil) γ
        (isNilpotent_apply_ι_chevalleySystem ρ hnil γ) b).hom.hom :=
    congrArg (fun f => f.hom.hom) (chevalleyRootSubgroupToToral_comp_ι ρ M hM hnil b χ γ)
  rw [h]
  exact schemePointsMulEquiv_kostantRootSubgroup _ _ _ _ _ _ _ _ A p

/-- At a positive simple root, including the all-root morphism into `GLₙ` gives the
original simple-root Kostant subgroup. -/
theorem chevalleyRootSubgroupToToral_simpleIndex_comp_ι (i : Fin t.rank) :
    chevalleyRootSubgroupToToral ρ M hM hnil b χ (t.simpleIndex ht i) ≫
        kostantToralGroupSchemeι (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
          ρ M hM hnil b χ =
      kostantRootSubgroup (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        ρ M hM (.inl i) (hnil (.inl i)) b := by
  rw [chevalleyRootSubgroupToToral_comp_ι]
  exact kostantRootSubgroup_congr _ _ _ _ _ _ _ _ _ _ _ _ (by simp)

/-- At a negative simple root, including the all-root morphism into `GLₙ` gives the
original negative-simple-root Kostant subgroup. -/
theorem chevalleyRootSubgroupToToral_reflectionPerm_simpleIndex_comp_ι (i : Fin t.rank) :
    chevalleyRootSubgroupToToral ρ M hM hnil b χ
        ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) (t.simpleIndex ht i)) ≫
      kostantToralGroupSchemeι (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        ρ M hM hnil b χ =
      kostantRootSubgroup (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        ρ M hM (.inr i) (hnil (.inr i)) b := by
  rw [chevalleyRootSubgroupToToral_comp_ι]
  exact kostantRootSubgroup_congr _ _ _ _ _ _ _ _ _ _ _ _ (by simp)

end Toral

namespace ChevalleyDatum

variable (D : ChevalleyDatum t ht)

/-- The integral root-subgroup morphism `𝔾ₐ → G_D` for every numbered root. Its composite
into the general linear group is the divided-power exponential of the named root vector. -/
def rootSubgroup (γ : Fin t.numRoots) : AdditiveGroup.groupScheme ℤ ⟶ D.groupScheme :=
  chevalleyRootSubgroupToToral D.representation D.lattice D.representation_mem_lattice
    D.isNilpotent_representation_rootGenerator D.basis D.coordinateWeight γ

/-- The datum's root morphism specializes the all-root morphism into the pinned toral closure. -/
theorem rootSubgroup_def (γ : Fin t.numRoots) :
    D.rootSubgroup γ =
      chevalleyRootSubgroupToToral D.representation D.lattice D.representation_mem_lattice
        D.isNilpotent_representation_rootGenerator D.basis D.coordinateWeight γ :=
  (rfl)

/-- Including the root morphism into `GLₙ` recovers the original polynomial exponential. -/
@[simp]
theorem rootSubgroup_comp_groupSchemeι (γ : Fin t.numRoots) :
    D.rootSubgroup γ ≫ D.groupSchemeι =
      kostantRootSubgroup (t.chevalleySystem ht) (t.lieBasis ht).h D.representation D.lattice
        (kostantForm_chevalleySystem_apply_mem_of_isNilpotent D.representation D.lattice
          D.representation_mem_lattice D.isNilpotent_representation_rootGenerator) γ
        (isNilpotent_apply_ι_chevalleySystem D.representation
          D.isNilpotent_representation_rootGenerator γ) D.basis := by
  rw [rootSubgroup_def, groupSchemeι_def]
  exact chevalleyRootSubgroupToToral_comp_ι D.representation D.lattice
    D.representation_mem_lattice D.isNilpotent_representation_rootGenerator
    D.basis D.coordinateWeight γ

/-- At a positive simple root the composite into `GLₙ` is the original simple-root
Kostant subgroup. -/
theorem rootSubgroup_simpleIndex_comp_groupSchemeι (i : Fin t.rank) :
    D.rootSubgroup (t.simpleIndex ht i) ≫ D.groupSchemeι =
      kostantRootSubgroup (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        D.representation D.lattice D.representation_mem_lattice (.inl i)
        (D.isNilpotent_representation_rootGenerator (.inl i)) D.basis := by
  rw [rootSubgroup_def, groupSchemeι_def]
  exact chevalleyRootSubgroupToToral_simpleIndex_comp_ι D.representation D.lattice
    D.representation_mem_lattice D.isNilpotent_representation_rootGenerator
    D.basis D.coordinateWeight i

/-- At a negative simple root the composite into `GLₙ` is the original negative-simple-root
Kostant subgroup. -/
theorem rootSubgroup_reflectionPerm_simpleIndex_comp_groupSchemeι (i : Fin t.rank) :
    D.rootSubgroup
        ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) (t.simpleIndex ht i)) ≫
      D.groupSchemeι =
      kostantRootSubgroup (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        D.representation D.lattice D.representation_mem_lattice (.inr i)
        (D.isNilpotent_representation_rootGenerator (.inr i)) D.basis := by
  rw [rootSubgroup_def, groupSchemeι_def]
  exact chevalleyRootSubgroupToToral_reflectionPerm_simpleIndex_comp_ι
    D.representation D.lattice D.representation_mem_lattice
    D.isNilpotent_representation_rootGenerator D.basis D.coordinateWeight i

/-- On scheme-valued points the integral root morphism is the datum's matrix-point root
subgroup, with the same additive parameter. -/
@[simp]
theorem schemePointsMulEquiv_rootSubgroup (γ : Fin t.numRoots) (A : Type) [CommRing A]
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (AdditiveGroup.groupScheme ℤ).X) :
    GeneralLinear.schemePointsMulEquiv D.dim A
        (p ≫ (D.rootSubgroup γ).hom.hom ≫ D.groupSchemeι.hom.hom) =
      (D.rootSubgroupPoints γ A
        (AdditiveGroup.gaPointsMulEquiv ((AdditiveGroup.groupSchemePointMulEquiv A).symm p)) :
          Matrix.GeneralLinearGroup (Fin D.dim) A) := by
  rw [rootSubgroup_def, groupSchemeι_def, schemePointsMulEquiv_chevalleyRootSubgroupToToral,
    coe_rootSubgroupPoints, kostantRootSubgroupMatrix_eq_matrix_chevalleyRootSubgroup]

end ChevalleyDatum

end

end TauCeti.DynkinType
