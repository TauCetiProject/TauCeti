/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.UpperTriangular.Basic
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.RootSubgroup.Basic
import TauCeti.AlgebraicGeometry.AffineGroupScheme.ClosedImmersion
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.DiagonalTorus.Base
import TauCeti.LinearAlgebra.Matrix.Triangular

/-!
# Positive root subgroups in the special-linear Borel

The elementary root map `xᵢⱼ : 𝔾ₐ → SLₙ` factors through the upper-triangular closed
subgroup when `i < j`. The factored map is a closed immersion and recovers the original
map after inclusion in `SLₙ`. Over a nontrivial base ring, the converse holds: a root
map factors through this subgroup exactly when the root is positive for the consecutive
root base. Thus this is containment of represented root subgroups, over arbitrary rings,
rather than a test of rational points or of tangent vectors alone.

On points over any commutative coefficient algebra, a negative root element lies in the
upper-triangular subgroup exactly when its additive parameter is zero. This also covers
nonreduced coefficient algebras and the zero ring.

The construction uses `CommHopfAlgCat.liftQuotient` and the existing special-linear
root map. The general-linear analogue is
`GeneralLinear.UpperTriangular.rootSubgroupCoordinateMap`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21, Example 21.2.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1 (root subgroups and pinnings).
-/

public section

open AlgebraicGeometry CategoryTheory WithConv

namespace TauCeti.SpecialLinear.UpperTriangular

universe u v

variable (R : Type u) [CommRing R] {n : ℕ} {i j : Fin n}

/-- A root element belongs to the upper-triangular subgroup exactly when its root is
positive or its additive parameter vanishes. -/
@[simp 1100]
theorem rootSubgroupPoints_mem_iff {A : Type v} [CommRing A] [Algebra R A]
    (hij : i ≠ j)
    (f : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R)
      (CommAlgCat.of R A)) :
    SpecialLinear.rootSubgroupPoints hij f ∈
        CommHopfAlgCat.quotientPointsSubgroup (SpecialLinear.coordinateHopfAlgebra R n)
          (definingHopfIdeal R n) (CommAlgCat.of R A) ↔
      i < j ∨ Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv f) = 0 := by
  rw [mem_definingPointsSubgroup_iff, SpecialLinear.pointsMulEquiv_rootSubgroupPoints,
    UpperTriangularGroup.mem_iff, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.transvection_coe]
  by_cases hpos : i < j
  · simp only [hpos, true_or, iff_true]
    exact Matrix.blockTriangular_transvection hpos.le _
  · have hneg : j < i := lt_of_le_of_ne (not_lt.mp hpos) hij.symm
    simpa only [Matrix.transvection, hpos, false_or] using
      TauCeti.isUpperTriangular_transvection_iff hneg
        (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv f))

/-- Positive root-subgroup points lie in the upper-triangular subgroup over every
commutative coefficient algebra. -/
theorem rootSubgroupPoints_mem {A : Type v} [CommRing A] [Algebra R A]
    (hij : i < j)
    (f : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R)
      (CommAlgCat.of R A)) :
    SpecialLinear.rootSubgroupPoints hij.ne f ∈
      CommHopfAlgCat.quotientPointsSubgroup (SpecialLinear.coordinateHopfAlgebra R n)
        (definingHopfIdeal R n) (CommAlgCat.of R A) :=
  (rootSubgroupPoints_mem_iff R hij.ne f).mpr (Or.inl hij)

/-- The coordinate morphism of a positive root subgroup kills the upper-triangular
Hopf ideal, so the root map factors scheme-theoretically through the Borel. -/
theorem definingHopfIdeal_le_ker_rootSubgroupCoordinateMap (hij : i < j) :
    (definingHopfIdeal R n).toIdeal ≤
      RingHom.ker
        ((SpecialLinear.rootSubgroupCoordinateMap (R := R) hij.ne).hom.toAlgHom :
          SpecialLinear.coordinateHopfAlgebra R n →+* AdditiveGroup.coordinateHopfAlgebra R) := by
  let f := toConv (AlgHom.id R (AdditiveGroup.coordinateHopfAlgebra R))
  have hmem := rootSubgroupPoints_mem R hij f
  rw [← SpecialLinear.mapPointsFunctor_rootSubgroupCoordinateMap_app,
    CommHopfAlgCat.mapPointsFunctor_app_apply,
    CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hmem
  intro x hx
  exact hmem x hx

/-- Over a nontrivial base, a root map kills the Borel's defining ideal exactly when
its row precedes its column. Testing the root element with parameter `1` detects the
negative roots. -/
@[simp]
theorem definingHopfIdeal_le_ker_rootSubgroupCoordinateMap_iff [Nontrivial R] (hij : i ≠ j) :
    (definingHopfIdeal R n).toIdeal ≤
        RingHom.ker ((SpecialLinear.rootSubgroupCoordinateMap (R := R) hij).hom.toAlgHom :
          SpecialLinear.coordinateHopfAlgebra R n →+* AdditiveGroup.coordinateHopfAlgebra R) ↔
      i < j := by
  refine ⟨fun h ↦ ?_, fun h ↦ definingHopfIdeal_le_ker_rootSubgroupCoordinateMap R h⟩
  let f := (AdditiveGroup.gaPointsMulEquiv (R := R) (A := R)).symm (Multiplicative.ofAdd 1)
  have hcomp : toConv (f.ofConv.comp
      (SpecialLinear.rootSubgroupCoordinateMap (R := R) hij).hom) =
      SpecialLinear.rootSubgroupPoints hij f :=
    SpecialLinear.mapPointsFunctor_rootSubgroupCoordinateMap_app hij (CommAlgCat.of R R) f
  have hmem : SpecialLinear.rootSubgroupPoints hij f ∈
      CommHopfAlgCat.quotientPointsSubgroup (SpecialLinear.coordinateHopfAlgebra R n)
        (definingHopfIdeal R n) (CommAlgCat.of R R) := by
    apply (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mpr
    intro x hx
    have hz : (SpecialLinear.rootSubgroupCoordinateMap (R := R) hij).hom x = 0 :=
      RingHom.mem_ker.mp (h hx)
    rw [← hcomp, ofConv_toConv, AlgHom.comp_apply]
    exact (congrArg f.ofConv hz).trans (map_zero f.ofConv)
  rw [rootSubgroupPoints_mem_iff] at hmem
  simpa only [f, MulEquiv.apply_symm_apply, toAdd_ofAdd, one_ne_zero,
    or_false] using hmem

/-- The coordinate morphism `O(B) → O(𝔾ₐ)` of a positive root subgroup of the
upper-triangular determinant-one subgroup. -/
noncomputable def rootSubgroupCoordinateMap (hij : i < j) :
    coordinateHopfAlgebra R n ⟶ AdditiveGroup.coordinateHopfAlgebra R :=
  CommHopfAlgCat.liftQuotient (definingHopfIdeal R n)
    (SpecialLinear.rootSubgroupCoordinateMap (R := R) hij.ne)
    (definingHopfIdeal_le_ker_rootSubgroupCoordinateMap R hij)

/-- The factorization through the Borel recovers the ambient root-coordinate map. -/
@[reassoc (attr := simp)]
theorem coordinateMap_comp_rootSubgroupCoordinateMap (hij : i < j) :
    coordinateMap R n ≫ rootSubgroupCoordinateMap R hij =
      SpecialLinear.rootSubgroupCoordinateMap (R := R) hij.ne :=
  CommHopfAlgCat.mkQuotient_comp_liftQuotient _ _ _

/-- On algebra-valued points, the factored root map gives the same determinant-one
transvection as the ambient root map. -/
@[simp]
theorem pointsMulEquiv_rootSubgroupCoordinateMap (hij : i < j)
    {A : Type v} [CommRing A] [Algebra R A]
    (f : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R)
      (CommAlgCat.of R A)) :
    (pointsMulEquiv R n (A := A) (toConv (f.ofConv.comp (rootSubgroupCoordinateMap R hij).hom)) :
        Matrix.SpecialLinearGroup (Fin n) A) =
      Matrix.SpecialLinearGroup.transvection hij.ne
        (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv f)) := by
  rw [← pointsMulEquiv_coe]
  have hquot : CommHopfAlgCat.quotientPointsHom
      (SpecialLinear.coordinateHopfAlgebra R n) (definingHopfIdeal R n) (CommAlgCat.of R A)
      (toConv (f.ofConv.comp (rootSubgroupCoordinateMap R hij).hom)) =
      toConv (f.ofConv.comp (SpecialLinear.rootSubgroupCoordinateMap (R := R) hij.ne).hom) := by
    rw [← CommHopfAlgCat.mapPointsFunctor_app_apply (rootSubgroupCoordinateMap R hij),
      ← CommHopfAlgCat.mapPointsFunctor_app_apply
        (SpecialLinear.rootSubgroupCoordinateMap (R := R) hij.ne)]
    exact (CommHopfAlgCat.mapPointsFunctor_eq_quotientPointsHom_of_mkQuotient_comp
        (definingHopfIdeal R n) (rootSubgroupCoordinateMap R hij)
        (SpecialLinear.rootSubgroupCoordinateMap (R := R) hij.ne)
        (coordinateMap_comp_rootSubgroupCoordinateMap R hij) (CommAlgCat.of R A) f).symm
  rw [hquot]
  -- Calculate at the universal additive point, then map its coefficients to `A`.
  have hgeneric : toConv ((AlgHom.id R (AdditiveGroup.coordinateHopfAlgebra R)).comp
      (SpecialLinear.rootSubgroupCoordinateMap (R := R) hij.ne).hom.toAlgHom) =
      SpecialLinear.rootSubgroupPoints hij.ne
        (toConv (AlgHom.id R (AdditiveGroup.coordinateHopfAlgebra R))) :=
    SpecialLinear.mapPointsFunctor_rootSubgroupCoordinateMap_app hij.ne
      (CommAlgCat.of R (AdditiveGroup.coordinateHopfAlgebra R))
      (toConv (AlgHom.id R (AdditiveGroup.coordinateHopfAlgebra R)))
  rw [AlgHom.id_comp] at hgeneric
  have hmatrix :
      (SpecialLinear.pointsMulEquiv (R := R) (A := AdditiveGroup.coordinateHopfAlgebra R) n)
          (toConv (SpecialLinear.rootSubgroupCoordinateMap (R := R) hij.ne).hom.toAlgHom) =
        Matrix.SpecialLinearGroup.transvection hij.ne (SymmetricAlgebra.ι R R 1) := by
    rw [hgeneric, SpecialLinear.pointsMulEquiv_rootSubgroupPoints,
      AdditiveGroup.toAdd_gaPointsMulEquiv, ofConv_toConv, AlgHom.id_apply]
  have hvalue := SpecialLinear.pointsMulEquiv_mapValue (R := R) n f.ofConv
    (toConv (SpecialLinear.rootSubgroupCoordinateMap (R := R) hij.ne).hom.toAlgHom)
  rw [AlgHom.mapValue_apply, ofConv_toConv] at hvalue
  rw [hvalue, hmatrix, Matrix.SpecialLinearGroup.map_transvection,
    AdditiveGroup.toAdd_gaPointsMulEquiv]
  exact congrArg (Matrix.SpecialLinearGroup.transvection hij.ne)
    (congrFun (AlgHom.coe_toRingHom f.ofConv) (SymmetricAlgebra.ι R R 1))

/-- The positive root subgroup is closed even as a subgroup of the Borel. -/
theorem rootSubgroupCoordinateMap_surjective (hij : i < j) :
    Function.Surjective (rootSubgroupCoordinateMap R hij).hom := by
  exact CommHopfAlgCat.liftQuotient_surjective_of_surjective _ _ _
    (SpecialLinear.rootSubgroupCoordinateMap_surjective hij.ne)

/-- The positive root map into the represented upper-triangular subgroup of `SLₙ`. -/
noncomputable def rootSubgroup (hij : i < j) :
    AdditiveGroup.groupScheme R ⟶
      CommHopfAlgCat.quotientSpec (SpecialLinear.coordinateHopfAlgebra R n)
        (definingHopfIdeal R n) :=
  eqToHom (AdditiveGroup.groupScheme_def R) ≫
    (hopfSpec (CommRingCat.of R)).map (rootSubgroupCoordinateMap R hij).op

/-- Inclusion of a factored positive root subgroup in `SLₙ` recovers the elementary
root map. -/
@[reassoc (attr := simp)]
theorem rootSubgroup_comp_quotientSpecι (hij : i < j) :
    rootSubgroup R hij ≫
        CommHopfAlgCat.quotientSpecι (SpecialLinear.coordinateHopfAlgebra R n)
          (definingHopfIdeal R n) ≫ eqToHom (SpecialLinear.groupScheme_def R n).symm =
      SpecialLinear.rootSubgroup hij.ne := by
  have hcomp := CommHopfAlgCat.hopfSpec_map_comp_quotientSpecι
    (definingHopfIdeal R n) (rootSubgroupCoordinateMap R hij)
  rw [coordinateMap_comp_rootSubgroupCoordinateMap] at hcomp
  simpa only [rootSubgroup, SpecialLinear.rootSubgroup_def, Category.assoc] using
    congrArg (fun g ↦ eqToHom (AdditiveGroup.groupScheme_def R) ≫ g ≫
      eqToHom (SpecialLinear.groupScheme_def R n).symm) hcomp

/-- Each positive root map identifies `𝔾ₐ` with a closed subgroup scheme of the Borel. -/
instance isClosedImmersion_rootSubgroup (hij : i < j) :
    IsClosedImmersion (rootSubgroup R hij).hom.hom.left := by
  rw [rootSubgroup]
  exact (CommHopfAlgCat.isClosedImmersion_eqToHom_comp_hopfSpec_map_iff
    (AdditiveGroup.groupScheme_def R) _).mpr
    (rootSubgroupCoordinateMap_surjective R hij)

/-- A root of the diagonal root datum has its represented additive root subgroup
inside the standard Borel exactly when it is positive. -/
theorem definingHopfIdeal_le_ker_rootSubgroupCoordinateMap_iff_isPos [Nontrivial R]
    (r : ℕ) (p : SplitTorus.CoordinateRootIndex (Fin (r + 1))) :
    (definingHopfIdeal R (r + 1)).toIdeal ≤
        RingHom.ker ((SpecialLinear.rootSubgroupCoordinateMap (R := R) p.2).hom.toAlgHom :
          SpecialLinear.coordinateHopfAlgebra R (r + 1) →+*
            AdditiveGroup.coordinateHopfAlgebra R) ↔
      (SpecialLinear.diagonalRootBase r).IsPos p := by
  rw [definingHopfIdeal_le_ker_rootSubgroupCoordinateMap_iff,
    SpecialLinear.diagonalRootBase_isPos_iff]

end TauCeti.SpecialLinear.UpperTriangular
