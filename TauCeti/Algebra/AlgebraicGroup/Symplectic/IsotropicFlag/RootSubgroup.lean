/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Symplectic.IsotropicFlag.Scheme
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.DiagonalTorus.Base
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.RootSubgroup.Basic
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Basic

/-!
# Positive root subgroups of the symplectic isotropic flag subgroup

Every positive symplectic root subgroup factors through the standard complete isotropic
flag subgroup. Its coordinate restriction is surjective, so the factored root inclusion
is a closed immersion. On algebra-valued points it gives the usual symplectic root matrix.

The construction reuses the flag subgroup's defining Hopf ideal and quotient coordinate
algebra, together with the ambient symplectic root-coordinate maps. The factorization follows
the formal template in
`TauCeti.Algebra.AlgebraicGroup.SpecialLinear.UpperTriangular.RootSubgroup`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §24.6.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
-/

public section

open CategoryTheory WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti.Symplectic.IsotropicFlag

open GLSymplecticFin.IsotropicFlag

universe u w

variable (R : Type u) [CommRing R] (m : ℕ)

private theorem tangentMatrix_blockTriangular_flagOrder
    {A : Type*} [CommRing A] (root : GLSymplecticFin.RootSubgroupIndex m)
    (hroot : (diagonalRootBase.{u} m).IsPos root) (c : A) :
    (root.tangentMatrix c).BlockTriangular (fun i ↦ flagOrder m (finSumFinEquiv i)) := by
  have hpos (i j : Fin m) :
      flagOrder m (finSumFinEquiv (.inl i)) ≤ flagOrder m (finSumFinEquiv (.inr j)) := by
    simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      Fin.natAdd_eq_addNat, flagOrder_castAdd, flagOrder_addNat,
      Fin.le_def, Fin.val_castAdd, Fin.val_addNat, Fin.val_rev]
    omega
  cases root with
  | positiveLong i =>
    rw [GLSymplecticFin.RootSubgroupIndex.tangentMatrix_positiveLong]
    exact Matrix.blockTriangular_single
      (b := fun i : Fin m ⊕ Fin m ↦ flagOrder m (finSumFinEquiv i)) (hpos i i) c
  | negativeLong i => exact (not_diagonalRootBase_isPos_negativeLong i hroot).elim
  | difference i j hij =>
    have hij' := (diagonalRootBase_isPos_difference_iff hij).mp hroot
    rw [GLSymplecticFin.RootSubgroupIndex.tangentMatrix_difference]
    apply Matrix.BlockTriangular.sub <;> apply Matrix.blockTriangular_single
    · simp only [finSumFinEquiv_apply_left, flagOrder_castAdd, Fin.le_def, Fin.val_castAdd]
      exact (Fin.le_def.mp hij'.le)
    · simp only [finSumFinEquiv_apply_right,
        Fin.natAdd_eq_addNat, flagOrder_addNat, Fin.le_def, Fin.val_addNat, Fin.val_rev]
      have := Fin.lt_def.mp hij'
      omega
  | positiveSum i j hij =>
    rw [GLSymplecticFin.RootSubgroupIndex.tangentMatrix_positiveSum]
    exact (Matrix.blockTriangular_single
      (b := fun i : Fin m ⊕ Fin m ↦ flagOrder m (finSumFinEquiv i)) (hpos i j) c).add
      (Matrix.blockTriangular_single
        (b := fun i : Fin m ⊕ Fin m ↦ flagOrder m (finSumFinEquiv i)) (hpos j i) c)
  | negativeSum i j hij => exact (not_diagonalRootBase_isPos_negativeSum hij hroot).elim

/-- Every positive root subgroup factors through the standard symplectic flag stabilizer:
its coordinate morphism kills the defining ideal over the entire additive group scheme. -/
theorem definingHopfIdeal_toIdeal_le_ker_rootSubgroupCoordinateMap
    (root : GLSymplecticFin.RootSubgroupIndex m)
    (hroot : (diagonalRootBase.{u} m).IsPos root) :
    (definingHopfIdeal R m).toIdeal ≤
      RingHom.ker (rootSubgroupCoordinateMap (R := R) root).hom.toAlgHom.toRingHom := by
  rw [definingHopfIdeal_toIdeal, Ideal.span_le]
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨i, j, hij, rfl⟩ :=
    (GeneralLinear.mem_weightParabolicRelationSet_iff R (weights m) y).mp hy
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rw [SetLike.mem_coe, RingHom.mem_ker]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, BialgHom.coe_toAlgHom]
  rw [rootSubgroupCoordinateMap_apply_X]
  have htri := (Matrix.blockTriangular_one (b := fun i ↦ flagOrder m (finSumFinEquiv i))).add
    (tangentMatrix_blockTriangular_flagOrder m root hroot (SymmetricAlgebra.ι R R 1))
  apply htri
  exact (weights_lt_weights_iff m _ _).mp hij

/-- The coordinate morphism of a positive root subgroup into the flag stabilizer. -/
noncomputable def rootSubgroupCoordinateMap (root : GLSymplecticFin.RootSubgroupIndex m)
    (hroot : (diagonalRootBase.{u} m).IsPos root) :
    coordinateHopfAlgebra R m ⟶ AdditiveGroup.coordinateHopfAlgebra R :=
  CommHopfAlgCat.liftQuotient (definingHopfIdeal R m)
    (Symplectic.rootSubgroupCoordinateMap (R := R) root)
    (definingHopfIdeal_toIdeal_le_ker_rootSubgroupCoordinateMap R m root hroot)

/-- The factored positive-root coordinate map recovers the ambient symplectic root map. -/
@[reassoc (attr := simp)]
theorem coordinateMap_comp_rootSubgroupCoordinateMap (root : GLSymplecticFin.RootSubgroupIndex m)
    (hroot : (diagonalRootBase.{u} m).IsPos root) :
    coordinateMap R m ≫ rootSubgroupCoordinateMap R m root hroot =
      Symplectic.rootSubgroupCoordinateMap (R := R) root :=
  CommHopfAlgCat.mkQuotient_comp_liftQuotient _ _ _

/-- Each positive-root coordinate restriction from the flag stabilizer is surjective. -/
theorem rootSubgroupCoordinateMap_surjective (root : GLSymplecticFin.RootSubgroupIndex m)
    (hroot : (diagonalRootBase.{u} m).IsPos root) :
    Function.Surjective (rootSubgroupCoordinateMap R m root hroot).hom := by
  classical
  let f := (rootSubgroupCoordinateMap R m root hroot).hom.toAlgHom
  apply f.surjective_of_ι_one_mem_range
  have hentry (a b : Fin m ⊕ Fin m)
      (hab : (1 + root.tangentMatrix (SymmetricAlgebra.ι R R 1)) a b =
        SymmetricAlgebra.ι R R 1) : SymmetricAlgebra.ι R R 1 ∈ f.range := by
    refine (AlgHom.mem_range _).mpr ⟨Ideal.Quotient.mkₐ R (definingHopfIdeal R m).toIdeal
      ((Symplectic.coordinateMap R m).hom
        (GeneralLinear.coordinateHopfAlgebraAlgEquiv R (m + m)
          (GeneralLinear.coordinateRingMap R (m + m)
            (MvPolynomial.X (finSumFinEquiv a, finSumFinEquiv b))))), ?_⟩
    exact (CommHopfAlgCat.liftQuotient_mk _ _ _ _).trans
      ((Symplectic.rootSubgroupCoordinateMap_apply_X root a b).trans hab)
  cases root with
  | positiveLong i => apply hentry (.inl i) (.inr i); simp
  | negativeLong i => exact (not_diagonalRootBase_isPos_negativeLong i hroot).elim
  | difference i j hij => apply hentry (.inl i) (.inl j); simp [hij]
  | positiveSum i j hij => apply hentry (.inl i) (.inr j); simp [hij.ne, hij.ne']
  | negativeSum i j hij => exact (not_diagonalRootBase_isPos_negativeSum hij hroot).elim

/-- A positive root subgroup as a morphism into the standard flag stabilizer. -/
noncomputable def rootSubgroup (root : GLSymplecticFin.RootSubgroupIndex m)
    (hroot : (diagonalRootBase.{u} m).IsPos root) :
    AdditiveGroup.groupScheme R ⟶ groupScheme R m :=
  eqToHom (AdditiveGroup.groupScheme_def R) ≫
    (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
      (rootSubgroupCoordinateMap R m root hroot).op

/-- A positive root morphism is relative spectrum applied to its coordinate restriction. -/
theorem rootSubgroup_def (root : GLSymplecticFin.RootSubgroupIndex m)
    (hroot : (diagonalRootBase.{u} m).IsPos root) :
    rootSubgroup R m root hroot =
      eqToHom (AdditiveGroup.groupScheme_def R) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (rootSubgroupCoordinateMap R m root hroot).op := by
  unfold rootSubgroup
  rfl

/-- Composing a factored positive root with inclusion recovers its symplectic morphism. -/
@[reassoc (attr := simp)]
theorem rootSubgroup_comp_inclusion (root : GLSymplecticFin.RootSubgroupIndex m)
    (hroot : (diagonalRootBase.{u} m).IsPos root) :
    rootSubgroup R m root hroot ≫ inclusion R m = Symplectic.rootSubgroup (R := R) root := by
  rw [rootSubgroup, inclusion, CommHopfAlgCat.quotientSpecι_def, Symplectic.rootSubgroup_def]
  simp only [Category.assoc, ← Functor.map_comp, ← op_comp,
    coordinateMap_comp_rootSubgroupCoordinateMap]
  rfl

/-- Every positive root subgroup is a closed subgroup of the flag stabilizer. -/
instance isClosedImmersion_rootSubgroup (root : GLSymplecticFin.RootSubgroupIndex m)
    (hroot : (diagonalRootBase.{u} m).IsPos root) :
    AlgebraicGeometry.IsClosedImmersion (rootSubgroup R m root hroot).hom.hom.left := by
  rw [rootSubgroup]
  exact (CommHopfAlgCat.isClosedImmersion_eqToHom_comp_hopfSpec_map_iff
    (AdditiveGroup.groupScheme_def R) _).mpr
    (rootSubgroupCoordinateMap_surjective R m root hroot)

variable {A : Type w} [CommRing A] [Algebra R A]

/-- The factored positive-root map gives the same symplectic root matrix on
algebra-valued points. -/
@[simp]
theorem pointsMulEquiv_rootSubgroupCoordinateMap (root : GLSymplecticFin.RootSubgroupIndex m)
    (hroot : (diagonalRootBase.{u} m).IsPos root)
    (f : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R)
      (CommAlgCat.of R A)) :
    (pointsMulEquiv R m (A := A)
        (toConv (f.ofConv.comp (rootSubgroupCoordinateMap R m root hroot).hom)) :
        GLSymplecticFin m A) =
      root.hom (AdditiveGroup.gaPointsMulEquiv f) := by
  have hquot := CommHopfAlgCat.mapPointsFunctor_eq_quotientPointsHom_of_mkQuotient_comp
    (definingHopfIdeal R m) (rootSubgroupCoordinateMap R m root hroot)
    (Symplectic.rootSubgroupCoordinateMap (R := R) root)
    (coordinateMap_comp_rootSubgroupCoordinateMap R m root hroot) (CommAlgCat.of R A) f
  rw [CommHopfAlgCat.mapPointsFunctor_app_apply (rootSubgroupCoordinateMap R m root hroot)
    (CommAlgCat.of R A) f] at hquot
  rw [← pointsMulEquiv_coe, ← hquot]
  rw [Symplectic.mapPointsFunctor_rootSubgroupCoordinateMap_app,
    Symplectic.pointsMulEquiv_rootSubgroupPoints]

section SchemePoints

variable (A : Type u) [CommRing A] [Algebra R A]

private theorem groupSchemePointMulEquiv_comp_rootSubgroup
    (root : GLSymplecticFin.RootSubgroupIndex m)
    (hroot : (diagonalRootBase.{u} m).IsPos root)
    (f : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    AdditiveGroup.groupSchemePointMulEquiv A f ≫ (rootSubgroup R m root hroot).hom.hom =
      groupSchemePointMulEquiv R m A
        (toConv (f.ofConv.comp (rootSubgroupCoordinateMap R m root hroot).hom)) := by
  rw [rootSubgroup_def]
  have h := CommHopfAlgCat.pointMulEquivOfPresentation_mapDomain
    (R := R) A (G := groupScheme R m) (H' := AdditiveGroup.groupScheme R)
    rfl (AdditiveGroup.groupScheme_def R)
    (groupSchemePointMulEquiv R m A) (AdditiveGroup.groupSchemePointMulEquiv A)
    (fun f => by simpa only [AlgHom.toRingHom_eq_coe] using
      groupSchemePointMulEquiv_apply_left R m A f)
    (AdditiveGroup.groupSchemePointMulEquiv_apply_left A)
    (rootSubgroupCoordinateMap R m root hroot) f
  erw [CommHopfAlgCat.mapPointsFunctor_app_apply] at h
  simpa only [eqToHom_refl, Category.comp_id] using h

/-- A positive root subgroup on scheme-valued points is its standard symplectic root matrix. -/
theorem schemePointsMulEquiv_rootSubgroup (root : GLSymplecticFin.RootSubgroupIndex m)
    (hroot : (diagonalRootBase.{u} m).IsPos root)
    (p : (AlgebraicGeometry.Spec (CommRingCat.of A)).asOver
      (AlgebraicGeometry.Spec (CommRingCat.of R)) ⟶ (AdditiveGroup.groupScheme R).X) :
    (schemePointsMulEquiv R m A (p ≫ (rootSubgroup R m root hroot).hom.hom) :
      GLSymplecticFin m A) = root.hom (AdditiveGroup.schemePointsMulEquiv A p) := by
  obtain ⟨f, rfl⟩ := (AdditiveGroup.groupSchemePointMulEquiv A).surjective p
  rw [groupSchemePointMulEquiv_comp_rootSubgroup,
    schemePointsMulEquiv_groupSchemePointMulEquiv,
    pointsMulEquiv_rootSubgroupCoordinateMap,
    AdditiveGroup.schemePointsMulEquiv_groupSchemePointMulEquiv]

end SchemePoints

end TauCeti.Symplectic.IsotropicFlag
