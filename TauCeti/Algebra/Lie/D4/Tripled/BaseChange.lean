/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.PointsFunctor
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.GeneralLinearBaseChange

/-!
# Base change of the tripled type-D4 carrier

`TauCeti.D4Tripled.groupScheme` is the explicit integral affine group scheme obtained by closing
the eight numbered type-`D₄` root subgroups and the rank-four weight torus of
`V(ϖ₁) ⊕ V(ϖ₃) ⊕ V(ϖ₄)` inside `GL₂₄`. This file specializes the base-change construction for a
general Kostant toral closure to that carrier.

For every commutative ring `A`, `TauCeti.D4Tripled.baseChangeDefiningIdeal` is an ideal in
`O(GL₂₄/A)` whose quotient is canonically the scalar extension of the integral coordinate Hopf
algebra, and whose points in a commutative `A`-algebra `B` are the integral carrier's matrix
points over `B`. The transported numbered root-subgroup maps and weight-torus map factor through
that quotient, and on points they are the carrier's named root-subgroup and weight-torus points.
Thus the integral carrier and its numbered generators base-change together; none of the data is
chosen anew over `A`.

The defining ideal transported from `ℤ` is contained in the common kernel of the transported
generators. Equality is not asserted over an arbitrary, possibly non-flat, base: additional
equations can appear after specialization. Nor does this file assert that the carrier is
reductive, that its torus is maximal, or that it is isomorphic to an independently defined pinned
group scheme of type `D₄`.

## Main declarations

* `TauCeti.D4Tripled.baseChangeDefiningIdeal`: the transported defining ideal in `O(GL₂₄/A)`.
* `TauCeti.D4Tripled.baseChangeCoordinateIso`: its quotient is the scalar extension of the
  integral carrier coordinate Hopf algebra.
* `TauCeti.D4Tripled.baseChangePointsMulEquiv`: the points of that quotient in a commutative
  `A`-algebra are the matrix points of the integral carrier over that algebra.
* `TauCeti.D4Tripled.rootSubgroupToBaseChangeCoordinateMap`: the transported numbered root
  subgroup factored through the specialized carrier.
* `TauCeti.D4Tripled.weightTorusToBaseChangeCoordinateMap`: the transported weight torus factored
  through the specialized carrier.

## Main results

* `TauCeti.D4Tripled.mkQuotient_comp_baseChangeCoordinateIso_hom`: the coordinate isomorphism is
  compatible with the quotient presentations.
* `TauCeti.D4Tripled.baseChangeCoordinateIso_hom_comp_rootSubgroupBaseChangeMap` and
  `TauCeti.D4Tripled.baseChangeCoordinateIso_hom_comp_weightTorusBaseChangeMap`: the numbered
  generators are the scalar extensions of their integral coordinate maps.
* `TauCeti.D4Tripled.hopfSpec_map_rootSubgroupIntegralCoordinateMap_op` and
  `TauCeti.D4Tripled.hopfSpec_map_weightTorusIntegralCoordinateMap_op`: the integral coordinate
  maps represent the existing root-subgroup and weight-torus morphisms.
* `pointsMulEquiv_mapPointsFunctor_rootSubgroupIntegralCoordinateMap` and
  `pointsMulEquiv_mapPointsFunctor_weightTorusIntegralCoordinateMap`: over `ℤ`, the integral
  coordinate maps induce the named root-subgroup and weight-torus points.
* `baseChangePointsMulEquiv_mapPointsFunctor_rootSubgroupToBaseChangeCoordinateMap` and
  `baseChangePointsMulEquiv_mapPointsFunctor_weightTorusToBaseChangeCoordinateMap`:
  the transported coordinate maps induce the named root-subgroup and weight-torus points.
* `TauCeti.D4Tripled.baseChangeDefiningIdeal_le_commonKernel`: the transported carrier contains
  the subgroup generated after base change by the transported maps.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 12.2.
* J. E. Humphreys, *Linear Algebraic Groups*, §§26--27.
* B. Conrad, *Reductive Group Schemes*, §1.
* Analogous base-change APIs for other explicit carriers are provided by
  `TauCeti.Algebra.Lie.E6.DoubledMinuscule.BaseChange` and
  `TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.BaseChange`.
-/

public section

open CategoryTheory
open TauCeti.DynkinType
open TauCeti.UniversalEnvelopingAlgebra
open scoped TensorProduct

namespace TauCeti.D4Tripled

universe v w

noncomputable section

attribute [local instance] TauCeti.moduleNNRat
attribute [local instance 100] LieRing.ofAssociativeRing

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

variable (A : Type v) [CommRing A]

/-- The Hopf ideal in `O(GL₂₄/A)` obtained by transporting the defining ideal of the integral
tripled type-`D₄` carrier along `ℤ → A`. -/
noncomputable def baseChangeDefiningIdeal :
    HopfIdeal A (GeneralLinear.coordinateHopfAlgebra A 24) :=
  kostantToralBaseChangePresentationIdeal
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    d4TripledWeight A

/-- Membership in the transported defining ideal is membership of the corresponding element in the
base change of the named integral defining ideal. -/
@[simp]
theorem mem_baseChangeDefiningIdeal_iff
    {x : GeneralLinear.coordinateHopfAlgebra A 24} :
    x ∈ baseChangeDefiningIdeal A ↔
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A 24).inv.hom x ∈
        CommHopfAlgCat.baseChangeHopfIdeal (K := A) definingIdeal := by
  rw [baseChangeDefiningIdeal, mem_kostantToralBaseChangePresentationIdeal_iff,
    kostantToralBaseChangeIdeal_def, ← definingIdeal_def]

/-- Transporting a pure tensor of a scalar and an integral defining equation produces an equation
in the transported defining ideal. -/
theorem map_tmul_mem_baseChangeDefiningIdeal_of_mem (s : A)
    {y : GeneralLinear.coordinateHopfAlgebra ℤ 24} (hy : y ∈ definingIdeal) :
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A 24).hom.hom
        (s ⊗ₜ[ℤ] y) ∈ baseChangeDefiningIdeal A := by
  rw [baseChangeDefiningIdeal]
  exact map_tmul_mem_kostantToralBaseChangePresentationIdeal_of_mem
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    d4TripledWeight A s (definingIdeal_def ▸ hy)

/-- The coordinate Hopf algebra cut out over `A` by the transported tripled type-`D₄` defining
ideal is canonically the scalar extension of the integral coordinate Hopf algebra. -/
noncomputable def baseChangeCoordinateIso :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A 24)
        (baseChangeDefiningIdeal A) ≅
      CommHopfAlgCat.baseChange (K := A)
        (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ 24) definingIdeal) :=
  kostantToralBaseChangePresentationIsoOfEq
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    d4TripledWeight A definingIdeal_def

/-- The base-change coordinate isomorphism is compatible with the quotient presentation inside
`GL₂₄`. -/
@[simp]
theorem mkQuotient_comp_baseChangeCoordinateIso_hom :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A 24)
          (baseChangeDefiningIdeal A) ≫
        (baseChangeCoordinateIso A).hom =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A 24).inv ≫
        CommHopfAlgCat.baseChangeMap
          (CommHopfAlgCat.mkQuotient
            (GeneralLinear.coordinateHopfAlgebra ℤ 24) definingIdeal) := by
  rw [baseChangeCoordinateIso]
  exact mkQuotient_comp_kostantToralBaseChangePresentationIsoOfEq_hom
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    d4TripledWeight A definingIdeal_def

/-! ## Points of the base-changed carrier -/

/-- The points of the base-changed tripled type-`D₄` carrier over a commutative `A`-algebra are
its matrix-valued carrier points over that algebra. -/
noncomputable def baseChangePointsMulEquiv (B : CommAlgCat.{w} A) :
    HopfAlgebra.points (R := A)
        (H := CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A 24)
          (baseChangeDefiningIdeal A)) B ≃*
      points B :=
  (CommHopfAlgCat.baseChangeIsoPointsMulEquiv (baseChangeCoordinateIso A) B).trans
    (pointsMulEquiv (TauCeti.CommAlgCat.restrictScalarsObj (algebraMap ℤ A) B))

/-- The base-change points equivalence preserves the ambient invertible matrix. -/
@[simp]
theorem coe_baseChangePointsMulEquiv_apply (B : CommAlgCat.{w} A)
    (q : HopfAlgebra.points (R := A)
      (H := CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A 24)
        (baseChangeDefiningIdeal A)) B) :
    (baseChangePointsMulEquiv A B q : Matrix.GeneralLinearGroup (Fin 24) B) =
      GeneralLinear.pointsMulEquiv 24
        (CommHopfAlgCat.quotientPointsHom (GeneralLinear.coordinateHopfAlgebra A 24)
          (baseChangeDefiningIdeal A) B q) := by
  rw [baseChangePointsMulEquiv, MulEquiv.trans_apply, coe_pointsMulEquiv_apply]
  exact GeneralLinear.pointsMulEquiv_quotientPointsHom_baseChangeIsoPointsMulEquiv
    24 definingIdeal (baseChangeDefiningIdeal A) (baseChangeCoordinateIso A)
    (mkQuotient_comp_baseChangeCoordinateIso_hom A) B q

/-- The quotient point underlying the inverse base-change equivalence is the point determined by
the ambient invertible matrix. -/
@[simp]
theorem quotientPointsHom_baseChangePointsMulEquiv_symm (B : CommAlgCat.{w} A) (g : points B) :
    CommHopfAlgCat.quotientPointsHom (GeneralLinear.coordinateHopfAlgebra A 24)
        (baseChangeDefiningIdeal A) B ((baseChangePointsMulEquiv A B).symm g) =
      (GeneralLinear.pointsMulEquiv (R := A) 24).symm
        (g : Matrix.GeneralLinearGroup (Fin 24) B) := by
  have h := coe_baseChangePointsMulEquiv_apply A B ((baseChangePointsMulEquiv A B).symm g)
  rw [MulEquiv.apply_symm_apply] at h
  rw [h, MulEquiv.symm_apply_apply]

/-- The identification of the base-changed carrier's points is natural in the value algebra. -/
@[simp]
theorem baseChangePointsMulEquiv_mapPoints {B C : CommAlgCat.{w} A} (f : B ⟶ C)
    (q : HopfAlgebra.points (R := A)
      (H := CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A 24)
        (baseChangeDefiningIdeal A)) B) :
    baseChangePointsMulEquiv A C
        (HopfAlgebra.mapPoints
          (H := CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A 24)
            (baseChangeDefiningIdeal A)) f q) =
      pointsMap f.hom (baseChangePointsMulEquiv A B q) := by
  simp only [baseChangePointsMulEquiv, MulEquiv.trans_apply]
  rw [CommHopfAlgCat.baseChangeIsoPointsMulEquiv_mapPoints, pointsMulEquiv_mapPoints]
  have hring :
      ((((TauCeti.CommAlgCat.restrictScalars (algebraMap ℤ A)).map f).hom : ↑B →+* ↑C)) =
        (f.hom : ↑B →+* ↑C) := by
    rw [TauCeti.CommAlgCat.restrictScalars_map, TauCeti.CommAlgCat.restrictScalarsMap_hom]
    exact RingHom.ext fun x ↦ AlgHom.restrictScalars_apply ℤ f.hom x
  rw [hring]

/-! ## The transported root subgroups -/

/-- The integral `k`th root-subgroup coordinate map, with source expressed using the named tripled
type-`D₄` defining ideal. -/
noncomputable def rootSubgroupIntegralCoordinateMap (k : Fin 4 ⊕ Fin 4) :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ 24) definingIdeal ⟶
      AdditiveGroup.coordinateHopfAlgebra ℤ :=
  kostantRootSubgroupToralCoordinateMapOfEq
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    d4TripledWeight definingIdeal_def k

/-- The integral factored root-subgroup map recovers the represented `k`th root-subgroup coordinate
map inside `GL₂₄`. -/
@[simp]
theorem mkQuotient_comp_rootSubgroupIntegralCoordinateMap (k : Fin 4 ⊕ Fin 4) :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ 24) definingIdeal ≫
        rootSubgroupIntegralCoordinateMap k =
      kostantRootSubgroupCoordinateMap
        (TauCeti.serreRootGenerator weightTable.cartanMatrix)
        (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
        rep_kostantForm_mem_lattice k (isNilpotent_rep_serreRootGenerator k) latticeBasis := by
  rw [rootSubgroupIntegralCoordinateMap]
  exact mkQuotient_comp_kostantRootSubgroupToralCoordinateMapOfEq
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    d4TripledWeight definingIdeal_def k

/-- On points, the integral factored coordinate map is the named numbered root subgroup. -/
@[simp]
theorem pointsMulEquiv_mapPointsFunctor_rootSubgroupIntegralCoordinateMap
    (B : CommAlgCat.{w} ℤ) (k : Fin 4 ⊕ Fin 4)
    (q : HopfAlgebra.points (R := ℤ) (H := AdditiveGroup.coordinateHopfAlgebra ℤ) B) :
    pointsMulEquiv B
        ((CommHopfAlgCat.mapPointsFunctor (rootSubgroupIntegralCoordinateMap k)).app B q) =
      rootSubgroupPoints k B (AdditiveGroup.gaPointsMulEquiv q) := by
  rw [CommHopfAlgCat.mapPointsFunctor_app_apply]
  apply Subtype.ext
  rw [coe_pointsMulEquiv_apply, coe_rootSubgroupPoints]
  have h := pointsMulEquiv_kostantRootSubgroupToralCoordinateMapOfEq
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    d4TripledWeight definingIdeal_def k B q
  rw [CommHopfAlgCat.mapPointsFunctor_app_apply] at h
  simpa only [rootSubgroupIntegralCoordinateMap] using h

/-- The integral factored root-subgroup coordinate map represents the carrier's `k`th numbered root
subgroup. -/
-- Not a `simp` lemma: `simp` rewrites `hopfSpec` to `algSpec.mapGrp` composed with the
-- Hopf-algebra/cogroup equivalence, so the left-hand side is not in `simp` normal form.
theorem hopfSpec_map_rootSubgroupIntegralCoordinateMap_op (k : Fin 4 ⊕ Fin 4) :
    (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).map
        (rootSubgroupIntegralCoordinateMap k).op =
      eqToHom (AdditiveGroup.groupScheme_def ℤ).symm ≫
        rootSubgroup k ≫ eqToHom groupScheme_def := by
  rw [rootSubgroupIntegralCoordinateMap, rootSubgroup_def]
  exact hopfSpec_map_kostantRootSubgroupToralCoordinateMapOfEq_op
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    d4TripledWeight definingIdeal_def k

/-- The base-changed `k`th root-subgroup coordinate map factored through the transported tripled
type-`D₄` carrier. -/
noncomputable def rootSubgroupToBaseChangeCoordinateMap (k : Fin 4 ⊕ Fin 4) :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A 24)
        (baseChangeDefiningIdeal A) ⟶ AdditiveGroup.coordinateHopfAlgebra A :=
  kostantRootSubgroupToralBaseChangePresentationCoordinateMap
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    d4TripledWeight A k

/-- The factored root-subgroup map recovers its ambient transported coordinate map. -/
@[simp]
theorem mkQuotient_comp_rootSubgroupToBaseChangeCoordinateMap (k : Fin 4 ⊕ Fin 4) :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A 24)
          (baseChangeDefiningIdeal A) ≫
        rootSubgroupToBaseChangeCoordinateMap A k =
      kostantRootSubgroupBaseChangePresentationCoordinateMap
        (TauCeti.serreRootGenerator weightTable.cartanMatrix)
        (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
        rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis A k := by
  unfold baseChangeDefiningIdeal rootSubgroupToBaseChangeCoordinateMap
  exact mkQuotient_comp_kostantRootSubgroupToralBaseChangePresentationCoordinateMap
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    d4TripledWeight A k

/-- Under the base-change coordinate isomorphism, the factored `k`th root-subgroup map is the
scalar extension of its integral coordinate map. -/
@[simp]
theorem baseChangeCoordinateIso_hom_comp_rootSubgroupBaseChangeMap (k : Fin 4 ⊕ Fin 4) :
    (baseChangeCoordinateIso A).hom ≫
          CommHopfAlgCat.baseChangeMap (rootSubgroupIntegralCoordinateMap k) ≫
        (_root_.CommHopfAlgCat.ofHom
          (AdditiveGroup.gaScalarTensorBialgEquiv (k := ℤ) (K := A))) =
      rootSubgroupToBaseChangeCoordinateMap A k := by
  rw [baseChangeCoordinateIso, rootSubgroupIntegralCoordinateMap,
    rootSubgroupToBaseChangeCoordinateMap]
  exact kostantToralBaseChangePresentationIsoOfEq_hom_comp_rootSubgroupBaseChangeMap
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    d4TripledWeight A definingIdeal_def k

/-- On points, the transported factored coordinate map is the named numbered root subgroup. -/
@[simp]
theorem baseChangePointsMulEquiv_mapPointsFunctor_rootSubgroupToBaseChangeCoordinateMap
    (B : CommAlgCat.{w} A) (k : Fin 4 ⊕ Fin 4)
    (q : HopfAlgebra.points (R := A) (H := AdditiveGroup.coordinateHopfAlgebra A) B) :
    baseChangePointsMulEquiv A B
        ((CommHopfAlgCat.mapPointsFunctor
          (rootSubgroupToBaseChangeCoordinateMap A k)).app B q) =
      rootSubgroupPoints k B (AdditiveGroup.gaPointsMulEquiv q) := by
  rw [CommHopfAlgCat.mapPointsFunctor_app_apply]
  apply Subtype.ext
  rw [coe_baseChangePointsMulEquiv_apply, coe_rootSubgroupPoints]
  -- The generic matrix theorem uses the canonical integer-algebra instance; this spelling makes
  -- that definitionally equal instance explicit before applying it.
  change _ = kostantRootSubgroupMatrix
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice k (isNilpotent_rep_serreRootGenerator k) latticeBasis
      ((@AdditiveGroup.gaPointsMulEquiv ℤ Int.instCommSemiring B _
        (Ring.toIntAlgebra B)).symm (AdditiveGroup.gaPointsMulEquiv q))
  have h := pointsMulEquiv_kostantRootSubgroupToralBaseChangeCoordinateMap
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    d4TripledWeight A definingIdeal_def k B q
  rw [CommHopfAlgCat.mapPointsFunctor_app_apply] at h
  unfold baseChangeDefiningIdeal rootSubgroupToBaseChangeCoordinateMap
  exact h

/-! ## The transported weight torus -/

/-- The integral weight-torus coordinate map, with source expressed using the named tripled
type-`D₄` defining ideal. -/
noncomputable def weightTorusIntegralCoordinateMap :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ 24) definingIdeal ⟶
      (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup (Fin 4))).obj :=
  kostantWeightTorusToralCoordinateMapOfEq
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    d4TripledWeight definingIdeal_def

/-- The integral factored weight-torus map recovers the represented weight-torus coordinate map
inside `GL₂₄`. -/
@[simp]
theorem mkQuotient_comp_weightTorusIntegralCoordinateMap :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ 24) definingIdeal ≫
        weightTorusIntegralCoordinateMap =
      GeneralLinear.weightTorusCoordinateMap d4TripledWeight := by
  rw [weightTorusIntegralCoordinateMap]
  exact mkQuotient_comp_kostantWeightTorusToralCoordinateMapOfEq
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    d4TripledWeight definingIdeal_def

/-- On points, the integral factored coordinate map is the named weight torus. -/
@[simp]
theorem pointsMulEquiv_mapPointsFunctor_weightTorusIntegralCoordinateMap
    (B : CommAlgCat.{w} ℤ)
    (q : HopfAlgebra.points (R := ℤ)
      (H := (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup (Fin 4))).obj) B) :
    pointsMulEquiv B
        ((CommHopfAlgCat.mapPointsFunctor weightTorusIntegralCoordinateMap).app B q) =
      weightTorusPoints B (SplitTorus.pointsMulEquiv q) := by
  rw [CommHopfAlgCat.mapPointsFunctor_app_apply]
  apply Subtype.ext
  rw [coe_pointsMulEquiv_apply, coe_weightTorusPoints]
  have h := pointsMulEquiv_kostantWeightTorusToralCoordinateMapOfEq
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    d4TripledWeight definingIdeal_def B q
  rw [CommHopfAlgCat.mapPointsFunctor_app_apply] at h
  simpa only [weightTorusIntegralCoordinateMap] using h

/-- The integral factored weight-torus coordinate map represents the carrier's weight torus. -/
-- Not a `simp` lemma, for the same reason as `hopfSpec_map_rootSubgroupIntegralCoordinateMap_op`.
theorem hopfSpec_map_weightTorusIntegralCoordinateMap_op :
    (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).map
        weightTorusIntegralCoordinateMap.op =
      eqToHom (DiagonalizableGroup.groupScheme_def ℤ
          (SplitTorus.characterGroup (Fin 4))).symm ≫
        weightTorus ≫ eqToHom groupScheme_def := by
  rw [weightTorusIntegralCoordinateMap, weightTorus_def]
  exact hopfSpec_map_kostantWeightTorusToralCoordinateMapOfEq_op
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    d4TripledWeight definingIdeal_def

/-- The base-changed weight-torus coordinate map factored through the transported tripled
type-`D₄` carrier. -/
noncomputable def weightTorusToBaseChangeCoordinateMap :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A 24)
        (baseChangeDefiningIdeal A) ⟶
      (DiagonalizableGroup.coordinateRing A (SplitTorus.characterGroup (Fin 4))).obj :=
  kostantWeightTorusToralBaseChangePresentationCoordinateMap
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    d4TripledWeight A

/-- The factored weight-torus map recovers its ambient transported coordinate map. -/
@[simp]
theorem mkQuotient_comp_weightTorusToBaseChangeCoordinateMap :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A 24)
          (baseChangeDefiningIdeal A) ≫
        weightTorusToBaseChangeCoordinateMap A =
      GeneralLinear.weightTorusBaseChangeCoordinateMap ℤ A d4TripledWeight := by
  unfold baseChangeDefiningIdeal weightTorusToBaseChangeCoordinateMap
  exact mkQuotient_comp_kostantWeightTorusToralBaseChangePresentationCoordinateMap
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    d4TripledWeight A

/-- Under the base-change coordinate isomorphism, the factored weight-torus map is the scalar
extension of its integral coordinate map. -/
@[simp]
theorem baseChangeCoordinateIso_hom_comp_weightTorusBaseChangeMap :
    (baseChangeCoordinateIso A).hom ≫
          CommHopfAlgCat.baseChangeMap weightTorusIntegralCoordinateMap ≫
        (_root_.CommHopfAlgCat.ofHom
          (BialgHomClass.toBialgHom
            (TauCeti.MonoidAlgebra.scalarTensorBialgEquiv ℤ A
              (G := SplitTorus.characterGroup (Fin 4))))) =
      weightTorusToBaseChangeCoordinateMap A := by
  rw [baseChangeCoordinateIso, weightTorusIntegralCoordinateMap,
    weightTorusToBaseChangeCoordinateMap]
  exact kostantToralBaseChangePresentationIsoOfEq_hom_comp_weightTorusBaseChangeMap
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    d4TripledWeight A definingIdeal_def

/-- On points, the transported factored weight-torus map is the named weight torus. -/
@[simp]
theorem baseChangePointsMulEquiv_mapPointsFunctor_weightTorusToBaseChangeCoordinateMap
    (B : CommAlgCat.{w} A)
    (q : HopfAlgebra.points (R := A)
      (H := (DiagonalizableGroup.coordinateRing A (SplitTorus.characterGroup (Fin 4))).obj) B) :
    baseChangePointsMulEquiv A B
        ((CommHopfAlgCat.mapPointsFunctor (weightTorusToBaseChangeCoordinateMap A)).app B q) =
      weightTorusPoints B (SplitTorus.pointsMulEquiv q) := by
  rw [CommHopfAlgCat.mapPointsFunctor_app_apply]
  apply Subtype.ext
  rw [coe_baseChangePointsMulEquiv_apply, coe_weightTorusPoints]
  have h := pointsMulEquiv_kostantWeightTorusToralBaseChangeCoordinateMap
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    d4TripledWeight A definingIdeal_def B q
  rw [CommHopfAlgCat.mapPointsFunctor_app_apply] at h
  unfold baseChangeDefiningIdeal weightTorusToBaseChangeCoordinateMap
  exact h

/-- The closed subgroup of `GL₂₄/A` generated by the transported numbered root subgroups and weight
torus lies in the base change of the integral tripled type-`D₄` carrier.

The reverse inclusion is not asserted over an arbitrary base ring. -/
theorem baseChangeDefiningIdeal_le_commonKernel :
    let K : Sum (Fin 4 ⊕ Fin 4) Unit → CommHopfAlgCat A
      | .inl _ => AdditiveGroup.coordinateHopfAlgebra A
      | .inr _ =>
          (DiagonalizableGroup.coordinateRing A (SplitTorus.characterGroup (Fin 4))).obj
    baseChangeDefiningIdeal A ≤
      CommHopfAlgCat.commonKernelHopfIdeal (K := K)
        (fun j => match j with
          | .inl k => kostantRootSubgroupBaseChangePresentationCoordinateMap
              (TauCeti.serreRootGenerator weightTable.cartanMatrix)
              (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
              rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis A k
          | .inr _ =>
              GeneralLinear.weightTorusBaseChangeCoordinateMap ℤ A d4TripledWeight) := by
  have h := kostantToralBaseChangePresentationIdeal_le_commonKernelHopfIdeal
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    d4TripledWeight A
  -- The generic containment indexes its generators by a `match` of its own, and neither that
  -- matcher nor `commonKernelHopfIdeal` is exposed, so compare the two families branchwise.
  dsimp only at h ⊢
  rw [CommHopfAlgCat.le_commonKernelHopfIdeal_iff] at h ⊢
  rintro (k | _)
  · exact h (.inl k)
  · exact h (.inr ())

end

end TauCeti.D4Tripled
