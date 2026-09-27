/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Subsystem.BaseChange
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.PositiveGroupScheme

/-!
# Base change of the positive Geck carrier

For a valid Dynkin type, the positive Geck carrier is the closed subgroup scheme generated over
`ℤ` by the numbered positive simple-root subgroups and the represented weight torus. It is the
scheme-theoretic candidate for the Borel member of the Geck carrier's pinning.

This file transports that positive carrier along `ℤ → A`. Its coordinate Hopf algebra is the
quotient by the scalar extension of the positive defining ideal, canonically identified with the
base change of the integral positive coordinate algebra. The positive simple-root maps and the
weight-torus map are transported through the same comparison, so the candidate Borel and the
distinguished generators base-change as one package.

The scalar extension of the full Geck defining ideal remains contained in the scalar extension of
the positive defining ideal. The resulting quotient morphism is the coordinate map of the
base-changed inclusion of the positive carrier in the full carrier.

No reductivity, Borel maximality, or maximal-torus assertion is made here. Those are the remaining
geometric inputs needed to turn this base-change-compatible candidate into a pinning.

## Main declarations

* `TauCeti.DynkinType.geckTorusPositiveBaseChangeIdeal`: the scalar extension of the positive
  Geck defining ideal.
* `TauCeti.DynkinType.geckTorusPositiveBaseChangeCoordinateIso`: the quotient comparison with the
  base change of the integral positive coordinate algebra.
* `TauCeti.DynkinType.geckTorusPositiveBaseChangePointsMulEquiv`: the resulting identification of
  points, natural in the value algebra.
* `TauCeti.DynkinType.geckPositiveRootSubgroupBaseChangeCoordinateMap`: the transported positive
  simple-root maps.
* `TauCeti.DynkinType.geckPositiveWeightTorusBaseChangeCoordinateMap`: the transported weight
  torus.
* `TauCeti.DynkinType.geckTorusPositiveBaseChangeInclusionCoordinateMap`: the coordinate map of
  the base-changed inclusion into the full Geck carrier.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* R. W. Carter, *Simple Groups of Lie Type*, §4.4.
* B. Conrad, *Reductive Group Schemes*, §1.
-/

public section

open CategoryTheory
open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType

universe v w

noncomputable section

attribute [local instance high] Algebra.toModule

variable (t : DynkinType) (ht : t.Valid)
variable (A : Type v) [CommRing A]

private abbrev positiveRootSet : Set (Fin t.rank ⊕ Fin t.rank) := Set.range Sum.inl

private abbrev positiveNilpotence (i : positiveRootSet t) :
    IsNilpotent
      (t.geckRepresentation ht
        (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator i.1))) :=
  t.isNilpotent_geckRepresentation_rootGenerator ht i.1

/-- Quotient maps commute with transport of the defining ideal along an equality. -/
private theorem mkQuotient_comp_eqToIso
    {I J : HopfIdeal ℤ (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht))}
    (hIJ : I = J) :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)) I ≫
        (eqToIso (congrArg
          (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)))
          hIJ)).hom =
      CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)) J := by
  subst J
  simp

/-! ## The transported positive carrier -/

/-- The defining ideal of the base-changed positive Geck carrier, in the scalar extension of the
integral ambient general-linear coordinate algebra. -/
def geckTorusPositiveBaseChangeIdeal :
    HopfIdeal A
      (CommHopfAlgCat.baseChange (K := A)
        (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht))) :=
  CommHopfAlgCat.baseChangeHopfIdeal (K := A) (t.geckTorusPositiveDefiningIdeal ht)

/-- The transported positive ideal is the scalar extension of the named integral positive ideal. -/
theorem geckTorusPositiveBaseChangeIdeal_eq_baseChange :
    t.geckTorusPositiveBaseChangeIdeal ht A =
      CommHopfAlgCat.baseChangeHopfIdeal (K := A) (t.geckTorusPositiveDefiningIdeal ht) := by
  rfl

/-- The coordinate algebra of the transported positive carrier is canonically the base change of
the integral positive coordinate algebra. -/
def geckTorusPositiveBaseChangeCoordinateIso :
    CommHopfAlgCat.quotient
        (CommHopfAlgCat.baseChange (K := A)
          (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)))
        (t.geckTorusPositiveBaseChangeIdeal ht A) ≅
      CommHopfAlgCat.baseChange (K := A)
        (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht))
          (t.geckTorusPositiveDefiningIdeal ht)) :=
  CommHopfAlgCat.quotientBaseChangeIso (t.geckTorusPositiveDefiningIdeal ht)

/-- The positive-carrier base-change comparison is compatible with the integral quotient map. -/
@[simp]
theorem mkQuotient_comp_geckTorusPositiveBaseChangeCoordinateIso_hom :
    CommHopfAlgCat.mkQuotient
          (CommHopfAlgCat.baseChange (K := A)
            (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)))
          (t.geckTorusPositiveBaseChangeIdeal ht A) ≫
        (t.geckTorusPositiveBaseChangeCoordinateIso ht A).hom =
      CommHopfAlgCat.baseChangeMap
        (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht))
          (t.geckTorusPositiveDefiningIdeal ht)) := by
  exact CommHopfAlgCat.mkQuotient_comp_quotientBaseChangeIso_hom (K := A)
    (t.geckTorusPositiveDefiningIdeal ht)

/-! ## Points of the transported positive carrier -/

/-- Points of the transported positive carrier are canonically the points of the integral
positive carrier over the same value algebra with its scalars restricted to `ℤ`. -/
def geckTorusPositiveBaseChangePointsMulEquiv (B : CommAlgCat.{w} A) :
    HopfAlgebra.points (R := A)
        (H := CommHopfAlgCat.quotient
          (CommHopfAlgCat.baseChange (K := A)
            (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)))
          (t.geckTorusPositiveBaseChangeIdeal ht A)) B ≃*
      HopfAlgebra.points (R := ℤ)
        (H := CommHopfAlgCat.quotient
          (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht))
          (t.geckTorusPositiveDefiningIdeal ht))
        (TauCeti.CommAlgCat.restrictScalarsObj (algebraMap ℤ A) B) :=
  CommHopfAlgCat.baseChangeIsoPointsMulEquiv
    (t.geckTorusPositiveBaseChangeCoordinateIso ht A) B

/-- The identification of transported positive-carrier points is natural in the value algebra. -/
@[simp]
theorem geckTorusPositiveBaseChangePointsMulEquiv_mapPoints
    {B C : CommAlgCat.{w} A} (χ : B ⟶ C)
    (q : HopfAlgebra.points (R := A)
      (H := CommHopfAlgCat.quotient
        (CommHopfAlgCat.baseChange (K := A)
          (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)))
        (t.geckTorusPositiveBaseChangeIdeal ht A)) B) :
    t.geckTorusPositiveBaseChangePointsMulEquiv ht A C
        (HopfAlgebra.mapPoints
          (H := CommHopfAlgCat.quotient
            (CommHopfAlgCat.baseChange (K := A)
              (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)))
            (t.geckTorusPositiveBaseChangeIdeal ht A)) χ q) =
      HopfAlgebra.mapPoints
        ((TauCeti.CommAlgCat.restrictScalars (algebraMap ℤ A)).map χ)
        (t.geckTorusPositiveBaseChangePointsMulEquiv ht A B q) := by
  exact CommHopfAlgCat.baseChangeIsoPointsMulEquiv_mapPoints
    (t.geckTorusPositiveBaseChangeCoordinateIso ht A) χ q

/-! ## The transported positive simple-root maps -/

/-- The integral coordinate map of the `i`th positive simple-root subgroup, factored through the
positive Geck carrier. -/
def geckPositiveRootSubgroupIntegralCoordinateMap (i : Fin t.rank) :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht))
        (t.geckTorusPositiveDefiningIdeal ht) ⟶ AdditiveGroup.coordinateHopfAlgebra ℤ :=
  (eqToIso (congrArg
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)))
      (t.geckTorusPositiveDefiningIdeal_def ht))).hom ≫
    kostantRootSubgroupTorusSubsystemCoordinateMap
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
      (t.geckCoordinateLattice ht).toAddSubgroup
      (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
      (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) (positiveRootSet t)
      (positiveNilpotence t ht) (Set.mem_range_self i)

/-- The integral factored positive-root map recovers the represented root-subgroup coordinate
map in the ambient general linear group. -/
@[simp]
theorem mkQuotient_comp_geckPositiveRootSubgroupIntegralCoordinateMap (i : Fin t.rank) :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht))
          (t.geckTorusPositiveDefiningIdeal ht) ≫
        t.geckPositiveRootSubgroupIntegralCoordinateMap ht i =
      kostantRootSubgroupCoordinateMap
        (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
        (t.geckCoordinateLattice ht).toAddSubgroup
        (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht) (.inl i)
        (t.isNilpotent_geckRepresentation_rootGenerator ht (.inl i))
        (t.geckCoordinateBasisFin ht) := by
  rw [geckPositiveRootSubgroupIntegralCoordinateMap, ← Category.assoc,
    t.mkQuotient_comp_eqToIso ht (t.geckTorusPositiveDefiningIdeal_def ht),
    mkQuotient_comp_kostantRootSubgroupTorusSubsystemCoordinateMap]

/-- The coordinate map of the `i`th positive simple-root subgroup after base change. -/
def geckPositiveRootSubgroupBaseChangeCoordinateMap (i : Fin t.rank) :
    CommHopfAlgCat.quotient
        (CommHopfAlgCat.baseChange (K := A)
          (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)))
        (t.geckTorusPositiveBaseChangeIdeal ht A) ⟶
      CommHopfAlgCat.baseChange (K := A) (AdditiveGroup.coordinateHopfAlgebra ℤ) :=
  (t.geckTorusPositiveBaseChangeCoordinateIso ht A).hom ≫
    CommHopfAlgCat.baseChangeMap (t.geckPositiveRootSubgroupIntegralCoordinateMap ht i)

/-- The transported positive-root map is the scalar extension of its integral factorization. -/
theorem geckPositiveRootSubgroupBaseChangeCoordinateMap_eq (i : Fin t.rank) :
    t.geckPositiveRootSubgroupBaseChangeCoordinateMap ht A i =
      (t.geckTorusPositiveBaseChangeCoordinateIso ht A).hom ≫
        CommHopfAlgCat.baseChangeMap
          (t.geckPositiveRootSubgroupIntegralCoordinateMap ht i) := by
  rfl

/-- The specialized quotient map followed by a positive-root map is the scalar extension of the
corresponding ambient integral root-subgroup coordinate map. -/
@[simp]
theorem mkQuotient_comp_geckPositiveRootSubgroupBaseChangeCoordinateMap (i : Fin t.rank) :
    CommHopfAlgCat.mkQuotient
          (CommHopfAlgCat.baseChange (K := A)
            (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)))
          (t.geckTorusPositiveBaseChangeIdeal ht A) ≫
        t.geckPositiveRootSubgroupBaseChangeCoordinateMap ht A i =
      CommHopfAlgCat.baseChangeMap
        (kostantRootSubgroupCoordinateMap
          (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
          (t.geckCoordinateLattice ht).toAddSubgroup
          (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht) (.inl i)
          (t.isNilpotent_geckRepresentation_rootGenerator ht (.inl i))
          (t.geckCoordinateBasisFin ht)) := by
  rw [geckPositiveRootSubgroupBaseChangeCoordinateMap, ← Category.assoc,
    mkQuotient_comp_geckTorusPositiveBaseChangeCoordinateIso_hom,
    ← (CommHopfAlgCat.baseChangeFunctor (K := A)).map_comp,
    mkQuotient_comp_geckPositiveRootSubgroupIntegralCoordinateMap]

/-! ## The transported weight torus -/

/-- The integral weight-torus coordinate map factored through the positive Geck carrier. -/
def geckPositiveWeightTorusIntegralCoordinateMap :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht))
        (t.geckTorusPositiveDefiningIdeal ht) ⟶
      (DiagonalizableGroup.coordinateRing ℤ
        (SplitTorus.characterGroup (Fin t.rank))).obj :=
  (eqToIso (congrArg
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)))
      (t.geckTorusPositiveDefiningIdeal_def ht))).hom ≫
    kostantWeightTorusTorusSubsystemCoordinateMap
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
      (t.geckCoordinateLattice ht).toAddSubgroup
      (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
      (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) (positiveRootSet t)
      (positiveNilpotence t ht)

/-- The integral factored torus map recovers the represented weight-torus coordinate map. -/
@[simp]
theorem mkQuotient_comp_geckPositiveWeightTorusIntegralCoordinateMap :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht))
          (t.geckTorusPositiveDefiningIdeal ht) ≫
        t.geckPositiveWeightTorusIntegralCoordinateMap ht =
      GeneralLinear.weightTorusCoordinateMap (t.geckWeightFin ht) := by
  rw [geckPositiveWeightTorusIntegralCoordinateMap, ← Category.assoc,
    t.mkQuotient_comp_eqToIso ht (t.geckTorusPositiveDefiningIdeal_def ht),
    mkQuotient_comp_kostantWeightTorusTorusSubsystemCoordinateMap]

/-- The represented weight-torus coordinate map after base change, factored through the
transported positive carrier. -/
def geckPositiveWeightTorusBaseChangeCoordinateMap :
    CommHopfAlgCat.quotient
        (CommHopfAlgCat.baseChange (K := A)
          (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)))
        (t.geckTorusPositiveBaseChangeIdeal ht A) ⟶
      CommHopfAlgCat.baseChange (K := A)
        (DiagonalizableGroup.coordinateRing ℤ
          (SplitTorus.characterGroup (Fin t.rank))).obj :=
  (t.geckTorusPositiveBaseChangeCoordinateIso ht A).hom ≫
    CommHopfAlgCat.baseChangeMap (t.geckPositiveWeightTorusIntegralCoordinateMap ht)

/-- The transported weight-torus map is the scalar extension of its integral factorization. -/
theorem geckPositiveWeightTorusBaseChangeCoordinateMap_eq :
    t.geckPositiveWeightTorusBaseChangeCoordinateMap ht A =
      (t.geckTorusPositiveBaseChangeCoordinateIso ht A).hom ≫
        CommHopfAlgCat.baseChangeMap
          (t.geckPositiveWeightTorusIntegralCoordinateMap ht) := by
  rfl

/-- The specialized quotient map followed by the weight-torus map is the scalar extension of the
ambient integral weight-torus coordinate map. -/
@[simp]
theorem mkQuotient_comp_geckPositiveWeightTorusBaseChangeCoordinateMap :
    CommHopfAlgCat.mkQuotient
          (CommHopfAlgCat.baseChange (K := A)
            (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)))
          (t.geckTorusPositiveBaseChangeIdeal ht A) ≫
        t.geckPositiveWeightTorusBaseChangeCoordinateMap ht A =
      CommHopfAlgCat.baseChangeMap
        (GeneralLinear.weightTorusCoordinateMap (t.geckWeightFin ht)) := by
  rw [geckPositiveWeightTorusBaseChangeCoordinateMap, ← Category.assoc,
    mkQuotient_comp_geckTorusPositiveBaseChangeCoordinateIso_hom,
    ← (CommHopfAlgCat.baseChangeFunctor (K := A)).map_comp,
    mkQuotient_comp_geckPositiveWeightTorusIntegralCoordinateMap]

/-! ## The base-changed inclusion into the full carrier -/

/-- Scalar extension preserves the inclusion of the full Geck defining ideal in the positive
defining ideal. Contravariantly, this is the base-changed inclusion of the positive carrier into
the full carrier. -/
theorem geckDefiningIdeal_baseChange_le_geckTorusPositiveBaseChangeIdeal :
    CommHopfAlgCat.baseChangeHopfIdeal (K := A) (t.geckDefiningIdeal ht) ≤
      t.geckTorusPositiveBaseChangeIdeal ht A := by
  rw [geckTorusPositiveBaseChangeIdeal_eq_baseChange]
  exact CommHopfAlgCat.baseChangeHopfIdeal_mono
    (t.geckDefiningIdeal_le_geckTorusPositiveDefiningIdeal ht)

/-- The coordinate morphism representing the base-changed inclusion of the positive Geck carrier
into the full Geck carrier. -/
def geckTorusPositiveBaseChangeInclusionCoordinateMap :
    CommHopfAlgCat.quotient
        (CommHopfAlgCat.baseChange (K := A)
          (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)))
        (CommHopfAlgCat.baseChangeHopfIdeal (K := A) (t.geckDefiningIdeal ht)) ⟶
      CommHopfAlgCat.quotient
        (CommHopfAlgCat.baseChange (K := A)
          (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)))
        (t.geckTorusPositiveBaseChangeIdeal ht A) :=
  CommHopfAlgCat.quotientMapOfLe _
    (t.geckDefiningIdeal_baseChange_le_geckTorusPositiveBaseChangeIdeal ht A)

/-- The base-changed inclusion coordinate map is compatible with the two ambient quotient maps. -/
@[simp]
theorem mkQuotient_comp_geckTorusPositiveBaseChangeInclusionCoordinateMap :
    CommHopfAlgCat.mkQuotient
          (CommHopfAlgCat.baseChange (K := A)
            (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)))
          (CommHopfAlgCat.baseChangeHopfIdeal (K := A) (t.geckDefiningIdeal ht)) ≫
        t.geckTorusPositiveBaseChangeInclusionCoordinateMap ht A =
      CommHopfAlgCat.mkQuotient
        (CommHopfAlgCat.baseChange (K := A)
          (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)))
        (t.geckTorusPositiveBaseChangeIdeal ht A) := by
  exact CommHopfAlgCat.mkQuotient_comp_quotientMapOfLe _
    (t.geckDefiningIdeal_baseChange_le_geckTorusPositiveBaseChangeIdeal ht A)

end

end TauCeti.DynkinType
