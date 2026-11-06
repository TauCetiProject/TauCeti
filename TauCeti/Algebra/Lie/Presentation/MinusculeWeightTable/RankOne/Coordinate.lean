/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.RankOne.Basic
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Scheme
import TauCeti.AlgebraicGeometry.AffineGroupScheme.ClosedImmersion

/-!
# Algebraic rank-one block representations

The two-by-two block action of a minuscule weight table is a morphism of affine group
schemes `SL₂ → GL_N` over any commutative ring. If the node has a weight of coordinate
`-1`, this morphism is a closed immersion: the corresponding two-dimensional block
recovers all four coordinate functions of `SL₂`.

`sl2BlockCoordinateMap` gives the coordinate Hopf morphism, with its matrix-entry and
algebra-valued point formulas. `sl2BlockGroupScheme` is the represented group morphism.
These maps give algebraic rank-one representations for minuscule carriers, rather than
only homomorphisms on field-valued points. Factorization through a particular closed
carrier is a separate question.

The construction uses `CommHopfAlgCat.homOfPointsMap`, as in the special-linear root
subgroup construction, and the existing `MinusculeWeightTable.sl2BlockSL` action.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, Chapter 6.
-/

public section

open AlgebraicGeometry CategoryTheory WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti.MinusculeWeightTable

universe u v w

variable {B : Type v} {N : ℕ} (T : MinusculeWeightTable B (Fin N))
variable (R : Type u) [CommRing R]

private noncomputable def sl2BlockPointsMap (i : B) :
    HopfAlgebra.pointsFunctor (R := R) (H := SpecialLinear.coordinateHopfAlgebra R 2) ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := GeneralLinear.coordinateHopfAlgebra R N) where
  app A := GrpCat.ofHom <|
    (GeneralLinear.pointsMulEquiv N).symm.toMonoidHom.comp
      ((T.sl2BlockSL i).comp (SpecialLinear.pointsMulEquiv (R := R) 2).toMonoidHom)
  naturality A C f := by
    ext q
    -- Expose the components of the point functors behind the categorical hom wrappers.
    change (GeneralLinear.pointsMulEquiv (R := R) (A := C) N).symm
        (T.sl2BlockSL i (SpecialLinear.pointsMulEquiv (R := R) (A := C) 2
          (AlgHom.mapValue f.hom q))) =
      AlgHom.mapValue f.hom ((GeneralLinear.pointsMulEquiv (R := R) (A := A) N).symm
        (T.sl2BlockSL i (SpecialLinear.pointsMulEquiv (R := R) (A := A) 2 q)))
    apply (GeneralLinear.pointsMulEquiv N).injective
    rw [MulEquiv.apply_symm_apply, GeneralLinear.pointsMulEquiv_mapValue,
      MulEquiv.apply_symm_apply]
    -- `q` is displayed through `pointsFunctor.obj`; reconcile its convolution-point wrapper.
    erw [SpecialLinear.pointsMulEquiv_mapValue, map_sl2BlockSL]
    rfl

/-- The coordinate Hopf morphism of the rank-one block representation at a node. -/
noncomputable def sl2BlockCoordinateMap (i : B) :
    GeneralLinear.coordinateHopfAlgebra R N ⟶ SpecialLinear.coordinateHopfAlgebra R 2 :=
  CommHopfAlgCat.homOfPointsMap (T.sl2BlockPointsMap R i)

/-- On algebra-valued points, the coordinate morphism induces the two-by-two block action. -/
@[simp]
theorem pointsMulEquiv_sl2BlockCoordinateMap (i : B) (A : CommAlgCat.{u} R)
    (q : HopfAlgebra.points (R := R) (H := SpecialLinear.coordinateHopfAlgebra R 2) A) :
    GeneralLinear.pointsMulEquiv N
        ((CommHopfAlgCat.Hom.mapPointsFunctor (T.sl2BlockCoordinateMap R i)).app A q) =
      T.sl2BlockSL i (SpecialLinear.pointsMulEquiv (R := R) (A := A) 2 q) := by
  rw [sl2BlockCoordinateMap, CommHopfAlgCat.mapPointsFunctor_homOfPointsMap]
  exact MulEquiv.apply_symm_apply _ _

/-- Restricting the ambient generic matrix gives the block action on the generic `SL₂`
matrix. This determines every matrix-entry coordinate of the representation. -/
@[simp]
theorem map_genericMatrix_sl2BlockCoordinateMap (i : B) :
    (GeneralLinear.genericMatrix R N).map (T.sl2BlockCoordinateMap R i).hom =
      T.sl2BlockMatrix i
        ((GeneralLinear.genericMatrix R 2).map (SpecialLinear.coordinateMap R 2).hom) := by
  let H := SpecialLinear.coordinateHopfAlgebra R 2
  let q : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R H) :=
    toConv (AlgHom.id R H)
  have h := T.pointsMulEquiv_sl2BlockCoordinateMap R i (CommAlgCat.of R H) q
  have hs : (SpecialLinear.pointsMulEquiv (R := R) (A := H) 2 q :
      Matrix (Fin 2) (Fin 2) H) =
      (GeneralLinear.genericMatrix R 2).map (SpecialLinear.coordinateMap R 2).hom := by
    ext c d
    -- The value algebra is the coordinate object itself; expose its algebra carrier.
    erw [SpecialLinear.coe_pointsMulEquiv_apply]
    rfl
  have hm := congrArg (fun g : Matrix.GeneralLinearGroup (Fin N) H ↦
    (g : Matrix (Fin N) (Fin N) H)) h
  rw [coe_sl2BlockSL, hs] at hm
  ext a b
  have hab := congrFun (congrFun hm a) b
  rw [CommHopfAlgCat.Hom.mapPointsFunctor_app_apply,
    GeneralLinear.pointsMulEquiv_apply, GeneralLinear.pointToGeneralLinear_apply] at hab
  simpa only [q, H, ofConv_toConv, AlgHom.comp_apply, AlgHom.id_apply,
    Matrix.map_apply, GeneralLinear.genericMatrix_apply, BialgHom.coe_toAlgHom] using hab

/-- A weight of coordinate `-1` makes the coordinate map surjective, over arbitrary
commutative base rings. Thus faithfulness here is scheme-theoretic. -/
theorem sl2BlockCoordinateMap_surjective (i : B) (hi : ∃ a, T.weight a i = -1) :
    Function.Surjective (T.sl2BlockCoordinateMap R i).hom := by
  obtain ⟨a, ha⟩ := hi
  have hs : T.weight (T.reflection i a) i = 1 := by simp [ha]
  have hne : T.reflection i a ≠ a := by
    intro h
    rw [h, ha] at hs
    omega
  let f := (T.sl2BlockCoordinateMap R i).hom.toAlgHom
  suffices hf : f.range = ⊤ from (AlgHom.range_eq_top f).mp hf
  apply top_unique
  rw [← SpecialLinear.adjoin_range_map_genericMatrix R 2, Algebra.adjoin_le_iff]
  rintro _ ⟨⟨j, k⟩, rfl⟩
  let row := if j = 0 then T.reflection i a else a
  let col := if k = 0 then T.reflection i a else a
  refine ⟨GeneralLinear.genericMatrix R N row col, ?_⟩
  have h := congrFun (congrFun (T.map_genericMatrix_sl2BlockCoordinateMap R i) row) col
  fin_cases j <;> fin_cases k <;>
    simpa [row, col, sl2BlockMatrix_apply, ha, hs, Matrix.one_apply, hne, hne.symm,
      f] using h

/-- The morphism `SL₂ → GL_N` acting on each pair of weights of coordinates `1,-1`
and fixing the weight-zero vectors. -/
noncomputable def sl2BlockGroupScheme (i : B) :
    SpecialLinear.groupScheme R 2 ⟶ GeneralLinear.groupScheme R N :=
  eqToHom (SpecialLinear.groupScheme_def R 2) ≫
    (hopfSpec (CommRingCat.of R)).map (T.sl2BlockCoordinateMap R i).op ≫
    eqToHom (GeneralLinear.groupScheme_def R N).symm

/-- The block representation is the relative spectrum of its coordinate Hopf morphism. -/
theorem sl2BlockGroupScheme_def (i : B) :
    T.sl2BlockGroupScheme R i =
      eqToHom (SpecialLinear.groupScheme_def R 2) ≫
        (hopfSpec (CommRingCat.of R)).map (T.sl2BlockCoordinateMap R i).op ≫
        eqToHom (GeneralLinear.groupScheme_def R N).symm :=
  (rfl)

/-- On scheme-valued points, the rank-one morphism is the prescribed block action. -/
@[simp]
theorem schemePointsMulEquiv_sl2BlockGroupScheme (i : B) (A : Type u)
    [CommRing A] [Algebra R A]
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (SpecialLinear.groupScheme R 2).X) :
    GeneralLinear.schemePointsMulEquiv N A (p ≫ (T.sl2BlockGroupScheme R i).hom.hom) =
      T.sl2BlockSL i (SpecialLinear.schemePointsMulEquiv 2 A p) := by
  obtain ⟨q, rfl⟩ := (SpecialLinear.groupSchemePointMulEquiv 2 A).surjective p
  have h := CommHopfAlgCat.pointMulEquivOfPresentation_mapDomain
    (R := R) A (GeneralLinear.groupScheme_def R N) (SpecialLinear.groupScheme_def R 2)
    (GeneralLinear.groupSchemePointMulEquiv N A) (SpecialLinear.groupSchemePointMulEquiv 2 A)
    (GeneralLinear.groupSchemePointMulEquiv_apply_left N A)
    (SpecialLinear.groupSchemePointMulEquiv_apply_left 2 A) (T.sl2BlockCoordinateMap R i) q
  rw [← sl2BlockGroupScheme_def] at h
  rw [h]
  -- The presentation comparison uses categorical points; the matrix comparisons use
  -- convolution points of the same algebra, so rewriting needs their concrete wrappers.
  erw [GeneralLinear.schemePointsMulEquiv_groupSchemePointMulEquiv,
    T.pointsMulEquiv_sl2BlockCoordinateMap R i (CommAlgCat.of R A) q,
    SpecialLinear.schemePointsMulEquiv_groupSchemePointMulEquiv]

/-- A nontrivial weight pair makes the algebraic rank-one block representation a closed
immersion, including in bad characteristic and over nonreduced rings. -/
theorem isClosedImmersion_sl2BlockGroupScheme (i : B) (hi : ∃ a, T.weight a i = -1) :
    IsClosedImmersion (T.sl2BlockGroupScheme R i).hom.hom.left := by
  rw [sl2BlockGroupScheme_def]
  exact (CommHopfAlgCat.isClosedImmersion_eqToHom_comp_hopfSpec_map_comp_eqToHom_iff
    (SpecialLinear.groupScheme_def R 2) (GeneralLinear.groupScheme_def R N) _).mpr
    (T.sl2BlockCoordinateMap_surjective R i hi)

end TauCeti.MinusculeWeightTable
