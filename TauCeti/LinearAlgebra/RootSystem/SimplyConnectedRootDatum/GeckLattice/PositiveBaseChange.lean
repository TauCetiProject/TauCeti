/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Subsystem.BaseChange
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.BaseChange
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.PositiveGroupScheme

/-!
# Base change of the positive Geck carrier

For a valid Dynkin type, the positive Geck carrier is the closed subgroup scheme generated over
`ℤ` by the numbered positive simple-root subgroups and the represented weight torus. It is the
scheme-theoretic candidate for the Borel member of the Geck carrier's pinning.

This file specializes the generic Kostant torus-subsystem base-change API to that carrier. Its
coordinate Hopf algebra is the quotient by the scalar extension of the positive defining ideal,
canonically identified with the base change of the integral positive coordinate algebra. The
positive simple-root maps and the weight-torus map are transported through the same comparison.

The positive carrier and its transported generators remain in tensor-product coordinates. The
full carrier uses the coordinate algebra constructed directly over the new base. The inclusion
defined here bridges those presentations: its source is the canonical full Geck carrier from
`GeckLattice.BaseChange`, and its target is the tensor presentation of the positive carrier. Its
compatibility equations identify the transported positive generators with the canonical
full-carrier generators after the standard scalar-tensor comparisons.

No reductivity, Borel maximality, or maximal-torus assertion is made here. Those are the remaining
geometric inputs needed to turn this base-change-compatible candidate into a pinning.

## Main declarations

* `TauCeti.DynkinType.geckTorusPositiveBaseChangeIdeal`: the generic subsystem base-change ideal
  specialized to the positive Geck data.
* `TauCeti.DynkinType.geckTorusPositiveBaseChangeCoordinateIso`: the corresponding quotient
  comparison.
* `TauCeti.DynkinType.geckRootSubgroupToTorusPositiveBaseChangeCoordinateMap`: the transported
  positive simple-root maps.
* `TauCeti.DynkinType.geckWeightTorusToTorusPositiveBaseChangeCoordinateMap`: the transported
  weight torus.
* `TauCeti.DynkinType.geckTorusPositiveBaseChangeInclusionCoordinateMap`: the coordinate map from
  the canonical base-changed full Geck carrier to the tensor presentation of the positive carrier.

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

universe v

noncomputable section

attribute [local instance high] Algebra.toModule

variable (t : DynkinType) (ht : t.Valid)
variable (A : Type v) [CommRing A]

/-! ## The transported positive carrier -/

/-- The generic Kostant torus-subsystem base-change ideal specialized to the positive simple roots
of the Geck data. -/
abbrev geckTorusPositiveBaseChangeIdeal :
    HopfIdeal A
      (CommHopfAlgCat.baseChange (K := A)
        (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht))) :=
  kostantTorusSubsystemBaseChangeIdeal
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) (Set.range Sum.inl)
    (fun i => t.isNilpotent_geckRepresentation_rootGenerator ht i.1) A

/-- The positive Geck base-change ideal is the specialization of the generic subsystem ideal. -/
theorem geckTorusPositiveBaseChangeIdeal_def :
    t.geckTorusPositiveBaseChangeIdeal ht A =
      kostantTorusSubsystemBaseChangeIdeal
        (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
        (t.geckCoordinateLattice ht).toAddSubgroup
        (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
        (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) (Set.range Sum.inl)
        (fun i => t.isNilpotent_geckRepresentation_rootGenerator ht i.1) A := rfl

/-- The coordinate algebra of the transported positive carrier is canonically the base change of
the integral positive coordinate algebra. -/
def geckTorusPositiveBaseChangeCoordinateIso :
    CommHopfAlgCat.quotient
        (CommHopfAlgCat.baseChange (K := A)
          (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)))
        (t.geckTorusPositiveBaseChangeIdeal ht A) ≅
      CommHopfAlgCat.baseChange (K := A)
        (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht))
          (kostantTorusSubsystemDefiningIdeal
            (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
            (t.geckCoordinateLattice ht).toAddSubgroup
            (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
            (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) (Set.range Sum.inl)
            (fun i => t.isNilpotent_geckRepresentation_rootGenerator ht i.1))) :=
  kostantTorusSubsystemBaseChangeIso
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) (Set.range Sum.inl)
    (fun i => t.isNilpotent_geckRepresentation_rootGenerator ht i.1) A

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
          (kostantTorusSubsystemDefiningIdeal
            (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
            (t.geckCoordinateLattice ht).toAddSubgroup
            (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
            (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) (Set.range Sum.inl)
            (fun i => t.isNilpotent_geckRepresentation_rootGenerator ht i.1))) :=
  mkQuotient_comp_kostantTorusSubsystemBaseChangeIso_hom
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) (Set.range Sum.inl)
    (fun i => t.isNilpotent_geckRepresentation_rootGenerator ht i.1) A

/-! ## The transported generators -/

/-- The coordinate map of the `i`th positive simple-root subgroup after base change, specialized
from the generic Kostant subsystem map. -/
def geckRootSubgroupToTorusPositiveBaseChangeCoordinateMap (i : Fin t.rank) :
    CommHopfAlgCat.quotient
        (CommHopfAlgCat.baseChange (K := A)
          (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)))
        (t.geckTorusPositiveBaseChangeIdeal ht A) ⟶
      CommHopfAlgCat.baseChange (K := A) (AdditiveGroup.coordinateHopfAlgebra ℤ) :=
  kostantRootSubgroupTorusSubsystemBaseChangeCoordinateMap
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) (Set.range Sum.inl)
    (fun j => t.isNilpotent_geckRepresentation_rootGenerator ht j.1) A
    (Set.mem_range_self i)

/-- The specialized quotient map followed by a positive-root map is the scalar extension of the
corresponding ambient integral root-subgroup coordinate map. -/
@[simp]
theorem mkQuotient_comp_geckRootSubgroupToTorusPositiveBaseChangeCoordinateMap
    (i : Fin t.rank) :
    CommHopfAlgCat.mkQuotient
          (CommHopfAlgCat.baseChange (K := A)
            (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)))
          (t.geckTorusPositiveBaseChangeIdeal ht A) ≫
        t.geckRootSubgroupToTorusPositiveBaseChangeCoordinateMap ht A i =
      CommHopfAlgCat.baseChangeMap
        (kostantRootSubgroupCoordinateMap
          (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
          (t.geckCoordinateLattice ht).toAddSubgroup
          (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht) (.inl i)
          (t.isNilpotent_geckRepresentation_rootGenerator ht (.inl i))
          (t.geckCoordinateBasisFin ht)) :=
  mkQuotient_comp_kostantRootSubgroupTorusSubsystemBaseChangeCoordinateMap
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) (Set.range Sum.inl)
    (fun j => t.isNilpotent_geckRepresentation_rootGenerator ht j.1) A
    (Set.mem_range_self i)

/-- The represented weight-torus coordinate map after base change, specialized from the generic
Kostant subsystem map. -/
def geckWeightTorusToTorusPositiveBaseChangeCoordinateMap :
    CommHopfAlgCat.quotient
        (CommHopfAlgCat.baseChange (K := A)
          (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)))
        (t.geckTorusPositiveBaseChangeIdeal ht A) ⟶
      CommHopfAlgCat.baseChange (K := A)
        (DiagonalizableGroup.coordinateRing ℤ
          (SplitTorus.characterGroup (Fin t.rank))).obj :=
  kostantWeightTorusTorusSubsystemBaseChangeCoordinateMap
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) (Set.range Sum.inl)
    (fun i => t.isNilpotent_geckRepresentation_rootGenerator ht i.1) A

/-- The specialized quotient map followed by the weight-torus map is the scalar extension of the
ambient integral weight-torus coordinate map. -/
@[simp]
theorem mkQuotient_comp_geckWeightTorusToTorusPositiveBaseChangeCoordinateMap :
    CommHopfAlgCat.mkQuotient
          (CommHopfAlgCat.baseChange (K := A)
            (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)))
          (t.geckTorusPositiveBaseChangeIdeal ht A) ≫
        t.geckWeightTorusToTorusPositiveBaseChangeCoordinateMap ht A =
      CommHopfAlgCat.baseChangeMap
        (GeneralLinear.weightTorusCoordinateMap (t.geckWeightFin ht)) :=
  mkQuotient_comp_kostantWeightTorusTorusSubsystemBaseChangeCoordinateMap
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) (Set.range Sum.inl)
    (fun i => t.isNilpotent_geckRepresentation_rootGenerator ht i.1) A

/-! ## Inclusion from the canonical full carrier -/

/-- The coordinate morphism representing the base-changed inclusion of the positive Geck carrier
into the full Geck carrier. Its source is the canonical carrier over `A`; its target is the tensor
presentation of the transported positive carrier. -/
def geckTorusPositiveBaseChangeInclusionCoordinateMap :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A (t.geckDim ht))
        (t.geckBaseChangeDefiningIdeal ht A) ⟶
      CommHopfAlgCat.quotient
        (CommHopfAlgCat.baseChange (K := A)
          (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)))
        (t.geckTorusPositiveBaseChangeIdeal ht A) :=
  (t.geckBaseChangeCoordinateIso ht A).hom ≫
    (kostantToralBaseChangeIso
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
      (t.geckCoordinateLattice ht).toAddSubgroup
      (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
      (t.isNilpotent_geckRepresentation_rootGenerator ht)
      (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) A).inv ≫
    kostantTorusSubsystemBaseChangeInclusionCoordinateMap
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
      (t.geckCoordinateLattice ht).toAddSubgroup
      (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
      (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) A
      (t.isNilpotent_geckRepresentation_rootGenerator ht) (Set.range Sum.inl)

/-- The base-changed inclusion intertwines each transported positive simple-root map with the
canonical full-carrier map after identifying the scalar-tensor additive coordinate algebra with
the coordinate algebra constructed over `A`. -/
@[simp]
theorem geckTorusPositiveBaseChangeInclusionCoordinateMap_comp_root
    (i : Fin t.rank) :
    t.geckTorusPositiveBaseChangeInclusionCoordinateMap ht A ≫
          t.geckRootSubgroupToTorusPositiveBaseChangeCoordinateMap ht A i ≫
        (_root_.CommHopfAlgCat.ofHom
          (AdditiveGroup.gaScalarTensorBialgEquiv (k := ℤ) (K := A))) =
      t.geckRootSubgroupToBaseChangeCoordinateMap ht A (.inl i) := by
  rw [geckTorusPositiveBaseChangeInclusionCoordinateMap,
    geckRootSubgroupToTorusPositiveBaseChangeCoordinateMap]
  slice_lhs 3 4 =>
    rw [kostantTorusSubsystemBaseChangeInclusionCoordinateMap_comp_root]
  slice_lhs 2 3 =>
    rw [kostantToralBaseChangeIso_inv_comp_rootSubgroupToralBaseChangeCoordinateMap]
  rw [← t.geckRootSubgroupIntegralCoordinateMap_def ht (.inl i)]
  exact t.geckBaseChangeCoordinateIso_hom_comp_rootSubgroupBaseChangeMap ht A (.inl i)

/-- The base-changed inclusion intertwines the transported weight torus with the canonical
full-carrier weight torus after the standard scalar-tensor comparison. -/
@[simp]
theorem geckTorusPositiveBaseChangeInclusionCoordinateMap_comp_weightTorus :
    t.geckTorusPositiveBaseChangeInclusionCoordinateMap ht A ≫
          t.geckWeightTorusToTorusPositiveBaseChangeCoordinateMap ht A ≫
        (_root_.CommHopfAlgCat.ofHom
          (TauCeti.MonoidAlgebra.scalarTensorBialgEquiv ℤ A
            (G := SplitTorus.characterGroup (Fin t.rank)))) =
      t.geckWeightTorusToBaseChangeCoordinateMap ht A := by
  rw [geckTorusPositiveBaseChangeInclusionCoordinateMap,
    geckWeightTorusToTorusPositiveBaseChangeCoordinateMap]
  slice_lhs 3 4 =>
    rw [kostantTorusSubsystemBaseChangeInclusionCoordinateMap_comp_weightTorus]
  slice_lhs 2 3 =>
    rw [kostantToralBaseChangeIso_inv_comp_weightTorusToralBaseChangeCoordinateMap]
  rw [← t.geckWeightTorusIntegralCoordinateMap_def ht]
  exact t.geckBaseChangeCoordinateIso_hom_comp_weightTorusBaseChangeMap ht A

end

end TauCeti.DynkinType
