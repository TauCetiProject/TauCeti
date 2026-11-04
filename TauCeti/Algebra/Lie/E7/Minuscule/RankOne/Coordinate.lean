/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.RankOne.Basic
public import TauCeti.Algebra.Lie.E7.Minuscule.BaseChange
public import TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.RankOne.Coordinate
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.RootSubgroup.Basic

/-!
# The algebraic rank-one action in the E₇ minuscule representation

The algebraic `SL₂ → GL₅₆` block representation of the E₇ weight table agrees with the
existing rank-one map on field-valued points. Its upper and lower additive subgroups
have exactly the numbered positive and negative root parameters of the minuscule carrier.
These comparisons hold over arbitrary commutative rings, before any recognition of that
carrier as the pinned simply connected group.

The block representation is a closed immersion by
`MinusculeWeightTable.isClosedImmersion_sl2BlockGroupScheme` and
`DynkinType.exists_e7MinusculeWeight_apply_eq_neg_one`. Its factorization through the
carrier over a general base ring is not asserted here.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, Chapter 6.
-/

public section

open CategoryTheory
open scoped Matrix

namespace TauCeti.E7Minuscule

universe u

variable (R : Type u) [CommRing R] (i : Fin 7)

/-- The algebraic rank-one map sends the upper additive subgroup to the numbered positive
root subgroup, without changing its parameter. -/
@[simp]
theorem pointsMulEquiv_sl2BlockCoordinateMap_upper (A : CommAlgCat.{u} R)
    (q : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) A) :
    GeneralLinear.pointsMulEquiv 56
        ((CommHopfAlgCat.Hom.mapPointsFunctor (weightTable.sl2BlockCoordinateMap R i)).app A
          (SpecialLinear.rootSubgroupPoints (by decide : (0 : Fin 2) ≠ 1) q)) =
      (rootSubgroupPoints (.inl i) A (AdditiveGroup.gaPointsMulEquiv q) : GL (Fin 56) A) := by
  rw [weightTable.pointsMulEquiv_sl2BlockCoordinateMap,
    SpecialLinear.pointsMulEquiv_rootSubgroupPoints]
  apply Units.ext
  rw [weightTable.coe_sl2BlockSL, weightTable.sl2BlockMatrix_upper_transvection,
    weightTable_raisingMatrix, coe_rootSubgroupPoints_inl]

/-- The algebraic rank-one map sends the lower additive subgroup to the numbered negative
root subgroup, without changing its parameter. -/
@[simp]
theorem pointsMulEquiv_sl2BlockCoordinateMap_lower (A : CommAlgCat.{u} R)
    (q : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) A) :
    GeneralLinear.pointsMulEquiv 56
        ((CommHopfAlgCat.Hom.mapPointsFunctor (weightTable.sl2BlockCoordinateMap R i)).app A
          (SpecialLinear.rootSubgroupPoints (by decide : (1 : Fin 2) ≠ 0) q)) =
      (rootSubgroupPoints (.inr i) A (AdditiveGroup.gaPointsMulEquiv q) : GL (Fin 56) A) := by
  rw [weightTable.pointsMulEquiv_sl2BlockCoordinateMap,
    SpecialLinear.pointsMulEquiv_rootSubgroupPoints]
  apply Units.ext
  rw [weightTable.coe_sl2BlockSL, weightTable.sl2BlockMatrix_lower_transvection,
    weightTable_loweringMatrix, coe_rootSubgroupPoints_inr]

/-- Restricting the algebraic rank-one representation along the upper root of `SL₂`
is the positive numbered root morphism of the specialized carrier, inside `GL₅₆`. -/
@[simp]
theorem sl2BlockCoordinateMap_comp_upper_rootSubgroupCoordinateMap :
    weightTable.sl2BlockCoordinateMap R i ≫
        SpecialLinear.rootSubgroupCoordinateMap (by decide : (0 : Fin 2) ≠ 1) =
      coordinateMap R ≫ rootSubgroupToBaseChangeCoordinateMap R (.inl i) := by
  apply Quiver.Hom.op_inj
  apply (CommHopfAlgCat.pointsFunctor.{u, u, u} (R := R)).map_injective
  simp only [CommHopfAlgCat.pointsFunctor_map, Quiver.Hom.unop_op,
    CommHopfAlgCat.Hom.mapPointsFunctor_comp]
  ext A q
  apply (GeneralLinear.pointsMulEquiv 56).injective
  simp only [NatTrans.comp_app, GrpCat.comp_apply]
  erw [SpecialLinear.mapPointsFunctor_rootSubgroupCoordinateMap_app,
    pointsMulEquiv_sl2BlockCoordinateMap_upper]
  symm
  -- The existing root comparison uses concrete convolution points rather than functor objects.
  erw [CommHopfAlgCat.Hom.mapPointsFunctor_app_apply,
    CommHopfAlgCat.Hom.mapPointsFunctor_app_apply, GeneralLinear.pointsMulEquiv_apply]
  simpa only [BialgHom.mapDomain_apply] using
    pointToGeneralLinear_mapDomain_rootSubgroupToBaseChangeCoordinateMap_eq_rootSubgroupPoints
      R (.inl i) A q

/-- Restricting the algebraic rank-one representation along the lower root of `SL₂`
is the negative numbered root morphism of the specialized carrier, inside `GL₅₆`. -/
@[simp]
theorem sl2BlockCoordinateMap_comp_lower_rootSubgroupCoordinateMap :
    weightTable.sl2BlockCoordinateMap R i ≫
        SpecialLinear.rootSubgroupCoordinateMap (by decide : (1 : Fin 2) ≠ 0) =
      coordinateMap R ≫ rootSubgroupToBaseChangeCoordinateMap R (.inr i) := by
  apply Quiver.Hom.op_inj
  apply (CommHopfAlgCat.pointsFunctor.{u, u, u} (R := R)).map_injective
  simp only [CommHopfAlgCat.pointsFunctor_map, Quiver.Hom.unop_op,
    CommHopfAlgCat.Hom.mapPointsFunctor_comp]
  ext A q
  apply (GeneralLinear.pointsMulEquiv 56).injective
  simp only [NatTrans.comp_app, GrpCat.comp_apply]
  erw [SpecialLinear.mapPointsFunctor_rootSubgroupCoordinateMap_app,
    pointsMulEquiv_sl2BlockCoordinateMap_lower]
  symm
  -- The existing root comparison uses concrete convolution points rather than functor objects.
  erw [CommHopfAlgCat.Hom.mapPointsFunctor_app_apply,
    CommHopfAlgCat.Hom.mapPointsFunctor_app_apply, GeneralLinear.pointsMulEquiv_apply]
  simpa only [BialgHom.mapDomain_apply] using
    pointToGeneralLinear_mapDomain_rootSubgroupToBaseChangeCoordinateMap_eq_rootSubgroupPoints
      R (.inr i) A q

/-- On field-valued points, the algebraic block map is the existing carrier-valued rank-one
map followed by the carrier's matrix inclusion. -/
@[simp]
theorem pointsMulEquiv_sl2BlockCoordinateMap_eq_rankOnePoints
    (k : Type u) [Field k] [Algebra R k]
    (q : HopfAlgebra.points (R := R) (H := SpecialLinear.coordinateHopfAlgebra R 2)
      (CommAlgCat.of R k)) :
    GeneralLinear.pointsMulEquiv 56
        ((CommHopfAlgCat.Hom.mapPointsFunctor (weightTable.sl2BlockCoordinateMap R i)).app
          (CommAlgCat.of R k) q) =
      (rankOnePoints k i (SpecialLinear.pointsMulEquiv (R := R) (A := k) 2 q) : GL (Fin 56) k) := by
  rw [weightTable.pointsMulEquiv_sl2BlockCoordinateMap, coe_rankOnePoints]

end TauCeti.E7Minuscule
