/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.ClosedRootSubgroup
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Subsystem.Basic

/-!
# The positive subgroup of the type-B spin carrier

The positive numbered simple-root subgroups and the split weight torus generate a closed subgroup
scheme of the integral full-spin carrier.  This file constructs that subgroup by specializing the
Kostant torus-subsystem construction to the positive simple roots of type `Bₙ₊₁`.

The positive root subgroups and the weight torus factor canonically through this subgroup, and
their factorizations recover the named maps into the full carrier.  The resulting universal
property makes this the smallest closed subgroup of the carrier containing those generators.

This is the scheme-theoretic candidate for the Borel subgroup in a pinning of the spin carrier.
No smoothness, solvability, maximality, or comparison with an independently constructed pinned
simply connected group scheme is asserted here.

## Main definitions

* `TauCeti.TypeBSpinCarrier.Positive.definingIdeal`: the common-kernel Hopf ideal of the positive
  simple-root maps and the weight torus.
* `TauCeti.TypeBSpinCarrier.Positive.groupScheme`: the corresponding affine group scheme over
  `ℤ`.
* `TauCeti.TypeBSpinCarrier.Positive.inclusion`: its closed inclusion into the full spin carrier.
* `TauCeti.TypeBSpinCarrier.Positive.rootSubgroup` and
  `TauCeti.TypeBSpinCarrier.Positive.weightTorus`: the generators factored through the positive
  subgroup.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4, 7.1 and 8.2.
* J. E. Humphreys, *Linear Algebraic Groups*, §§26--28.

The construction specializes
`TauCeti.UniversalEnvelopingAlgebra.kostantTorusSubsystemGroupScheme`.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.TypeBSpinCarrier.Positive

noncomputable section

open TauCeti.UniversalEnvelopingAlgebra

variable (n : ℕ)

/-- The defining Hopf ideal of the positive type-`Bₙ₊₁` spin subgroup.  It is the largest
Hopf ideal killed by every positive numbered simple-root map and by the represented weight-torus
map. -/
def definingIdeal : HopfIdeal ℤ
    (TauCeti.GeneralLinear.coordinateHopfAlgebra ℤ (dimension n)) :=
  kostantTorusSubsystemDefiningIdeal
    (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
    (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n) (latticeBasis n) (basisWeight n) (Set.range Sum.inl)
    (fun i ↦ isNilpotent_rep_rootGenerator n i.1)

/-- The positive subgroup ideal is the generic Kostant torus-subsystem ideal for the positive
simple-root labels. -/
theorem definingIdeal_def :
    definingIdeal n =
      kostantTorusSubsystemDefiningIdeal
        (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
        (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
        (rep_kostantForm_mem_lattice n) (latticeBasis n) (basisWeight n) (Set.range Sum.inl)
        (fun i ↦ isNilpotent_rep_rootGenerator n i.1) :=
  (rfl)

/-- A Hopf ideal is contained in the positive subgroup ideal exactly when the positive simple-root
coordinate maps and the weight-torus coordinate map kill it. -/
theorem le_definingIdeal_iff
    (J : HopfIdeal ℤ (TauCeti.GeneralLinear.coordinateHopfAlgebra ℤ (dimension n))) :
    J ≤ definingIdeal n ↔
      (∀ i : Fin (n + 1), J.toIdeal ≤ RingHom.ker
        (kostantRootSubgroupCoordinateMap
          (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
          (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n)
          (lattice n).toAddSubgroup (rep_kostantForm_mem_lattice n) (.inl i)
          (isNilpotent_rep_rootGenerator n (.inl i)) (latticeBasis n)).hom.toAlgHom.toRingHom) ∧
      J.toIdeal ≤ RingHom.ker
        (TauCeti.GeneralLinear.weightTorusCoordinateMap
          (basisWeight n)).hom.toAlgHom.toRingHom := by
  rw [definingIdeal_def, le_kostantTorusSubsystemDefiningIdeal_iff]
  constructor
  · intro h
    exact ⟨fun i ↦ h.1 (.inl i) ⟨i, rfl⟩, h.2⟩
  · rintro ⟨hroot, htorus⟩
    refine ⟨?_, htorus⟩
    intro k hk
    obtain ⟨i, rfl⟩ := hk
    exact hroot i

/-- The full spin-carrier ideal is contained in the positive subgroup ideal.  Contravariantly,
this is the closed inclusion of the positive subgroup into the full carrier. -/
theorem carrierDefiningIdeal_le : TypeBSpinCarrier.definingIdeal n ≤ definingIdeal n := by
  rw [TypeBSpinCarrier.definingIdeal_def, definingIdeal_def]
  exact kostantToralDefiningIdeal_le_kostantTorusSubsystemDefiningIdeal
    (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
    (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n) (latticeBasis n) (basisWeight n)
    (isNilpotent_rep_rootGenerator n) (Set.range Sum.inl)

/-- The affine group scheme generated by the positive simple-root subgroups and the weight torus. -/
abbrev groupScheme : Grp (Over (Spec (CommRingCat.of ℤ))) :=
  kostantTorusSubsystemGroupScheme
    (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
    (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n) (latticeBasis n) (basisWeight n) (Set.range Sum.inl)
    (fun i ↦ isNilpotent_rep_rootGenerator n i.1)

/-- The positive subgroup is the quotient spectrum cut out by `definingIdeal`. -/
theorem groupScheme_eq_quotientSpec :
    groupScheme n = CommHopfAlgCat.quotientSpec
      (TauCeti.GeneralLinear.coordinateHopfAlgebra ℤ (dimension n)) (definingIdeal n) := by
  rw [definingIdeal]

/-- The closed inclusion of the positive subgroup into the full type-`Bₙ₊₁` spin carrier. -/
def inclusion : groupScheme n ⟶ TypeBSpinCarrier.groupScheme n :=
  kostantTorusSubsystemToToral
      (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
      (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
      (rep_kostantForm_mem_lattice n) (latticeBasis n) (basisWeight n)
      (isNilpotent_rep_rootGenerator n) (Set.range Sum.inl) ≫
    eqToHom (TypeBSpinCarrier.groupScheme_eq_kostantToralGroupScheme n).symm

/-- Including the positive subgroup into the full carrier and then into the ambient general linear
group is the direct Kostant torus-subsystem inclusion. -/
@[reassoc (attr := simp)]
theorem inclusion_comp_carrierι :
    inclusion n ≫ TypeBSpinCarrier.carrierι n =
      kostantTorusSubsystemGroupSchemeι
        (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
        (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
        (rep_kostantForm_mem_lattice n) (latticeBasis n) (basisWeight n) (Set.range Sum.inl)
        (fun i ↦ isNilpotent_rep_rootGenerator n i.1) := by
  rw [inclusion, TypeBSpinCarrier.carrierι_def]
  slice_lhs 2 4 =>
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact kostantTorusSubsystemToToral_comp_ι _ _ _ _ _ _ _ _ _

/-- The positive subgroup is a closed subgroup scheme of the full spin carrier. -/
instance isClosedImmersion_inclusion : IsClosedImmersion (inclusion n).hom.hom.left := by
  rw [← closedSubgroupMorphismProperty_iff]
  rw [inclusion, (closedSubgroupMorphismProperty _).cancel_right_of_respectsIso]
  rw [closedSubgroupMorphismProperty_iff]
  infer_instance

/-- The positive subgroup bundled as a closed subgroup of the full spin carrier. -/
def closedSubgroup : ClosedSubgroupScheme (TypeBSpinCarrier.groupScheme n) :=
  ClosedSubgroupScheme.mk (inclusion n)

/-- The positive closed subgroup is represented by its named inclusion. -/
@[simp]
theorem coe_closedSubgroup : (closedSubgroup n).1 = Subobject.mk (inclusion n) :=
  ClosedSubgroupScheme.coe_mk _

/-- The `i`-th positive simple-root subgroup factored through the positive subgroup. -/
def rootSubgroup (i : Fin (n + 1)) : AdditiveGroup.groupScheme ℤ ⟶ groupScheme n :=
  kostantRootSubgroupToTorusSubsystem
    (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
    (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n) (latticeBasis n) (basisWeight n) (Set.range Sum.inl)
    (fun j ↦ isNilpotent_rep_rootGenerator n j.1) ⟨i, rfl⟩

/-- Including a positive simple-root subgroup into the full carrier recovers its named root map. -/
@[simp]
theorem rootSubgroup_comp_inclusion (i : Fin (n + 1)) :
    rootSubgroup n i ≫ inclusion n = TypeBSpinCarrier.rootSubgroup n (.inl i) := by
  have h := kostantRootSubgroupToTorusSubsystem_comp_kostantTorusSubsystemToToral
    (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
    (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n) (latticeBasis n) (basisWeight n)
    (isNilpotent_rep_rootGenerator n) (Set.range Sum.inl) (i := (.inl i)) ⟨i, rfl⟩
  simpa only [rootSubgroup, inclusion, TypeBSpinCarrier.rootSubgroup_def, Category.assoc] using
    congrArg (fun f =>
      f ≫ eqToHom (TypeBSpinCarrier.groupScheme_eq_kostantToralGroupScheme n).symm) h

/-- The represented weight torus factored through the positive subgroup. -/
def weightTorus : SplitTorus.groupScheme ℤ (Fin (n + 1)) ⟶ groupScheme n :=
  kostantWeightTorusToTorusSubsystem
    (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
    (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n) (latticeBasis n) (basisWeight n) (Set.range Sum.inl)
    (fun j ↦ isNilpotent_rep_rootGenerator n j.1)

/-- Including the positive subgroup's weight torus recovers the full carrier's weight torus. -/
@[simp]
theorem weightTorus_comp_inclusion :
    weightTorus n ≫ inclusion n = TypeBSpinCarrier.weightTorus n := by
  have h := kostantWeightTorusToTorusSubsystem_comp_kostantTorusSubsystemToToral
    (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
    (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n) (latticeBasis n) (basisWeight n)
    (isNilpotent_rep_rootGenerator n) (Set.range Sum.inl)
  simpa only [weightTorus, inclusion, TypeBSpinCarrier.weightTorus_def, Category.assoc] using
    congrArg (fun f =>
      f ≫ eqToHom (TypeBSpinCarrier.groupScheme_eq_kostantToralGroupScheme n).symm) h

/-- Positive simple-root maps remain closed immersions after factoring through the positive
subgroup. -/
instance isClosedImmersion_rootSubgroup (i : Fin (n + 1)) :
    IsClosedImmersion (rootSubgroup n i).hom.hom.left := by
  have h : IsClosedImmersion ((rootSubgroup n i ≫ inclusion n).hom.hom.left) := by
    rw [rootSubgroup_comp_inclusion]
    infer_instance
  simp only [Grp.comp', Mon.comp_hom', Over.comp_left] at h
  exact IsClosedImmersion.of_comp (f := (rootSubgroup n i).hom.hom.left)
    (g := (inclusion n).hom.hom.left)

/-- The weight torus remains a closed immersion after factoring through the positive subgroup. -/
instance isClosedImmersion_weightTorus :
    IsClosedImmersion (weightTorus n).hom.hom.left := by
  exact isClosedImmersion_kostantWeightTorusToTorusSubsystem
    (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
    (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n) (latticeBasis n) (basisWeight n) (Set.range Sum.inl)
    (fun j ↦ isNilpotent_rep_rootGenerator n j.1) (span_range_basisWeight_eq_top n)

/-- Each positive simple-root closed subgroup of the full carrier lies in the positive subgroup. -/
theorem rootSubgroup_le_closedSubgroup (i : Fin (n + 1)) :
    ClosedSubgroupScheme.mk (TypeBSpinCarrier.rootSubgroup n (.inl i)) ≤ closedSubgroup n := by
  rw [← Subtype.coe_le_coe, ClosedSubgroupScheme.coe_mk, coe_closedSubgroup]
  exact Subobject.mk_le_mk_of_comm (rootSubgroup n i) (rootSubgroup_comp_inclusion n i)

/-- The full carrier's weight torus lies in the positive subgroup. -/
theorem weightTorus_le_closedSubgroup :
    ClosedSubgroupScheme.mk (TypeBSpinCarrier.weightTorus n) ≤ closedSubgroup n := by
  rw [← Subtype.coe_le_coe, ClosedSubgroupScheme.coe_mk, coe_closedSubgroup]
  exact Subobject.mk_le_mk_of_comm (weightTorus n) (weightTorus_comp_inclusion n)

/-- A morphism from the positive subgroup is determined by its restrictions to the positive
simple-root subgroups and the weight torus. -/
@[ext]
theorem groupScheme_hom_ext {Y : _root_.CommHopfAlgCat.{0} ℤ}
    (f g : groupScheme n ⟶
      (hopfSpec (CommRingCat.of ℤ)).obj (Opposite.op Y))
    (hroot : ∀ i, rootSubgroup n i ≫ f = rootSubgroup n i ≫ g)
    (htorus : weightTorus n ≫ f = weightTorus n ≫ g) : f = g := by
  apply kostantTorusSubsystemGroupScheme_hom_ext
  · intro k hk
    obtain ⟨i, rfl⟩ := hk
    exact hroot i
  · exact htorus

end

end TauCeti.TypeBSpinCarrier.Positive
