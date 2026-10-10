/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.ClosedGenerators
public import TauCeti.Algebra.AlgebraicGroup.Connected.Generated
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.CommonKernel.PerfectField
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Equalizer
import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.CoordinateBaseChange
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.SmoothConnected
import TauCeti.AlgebraicGeometry.AffineGroupScheme.Smooth

/-!
# The positive subgroup of the short-root F₄ carrier over 𝔽₂

The four positive numbered simple-root subgroups and the rank-four weight torus generate a
smooth, geometrically connected closed subgroup scheme of the short-root type-`F₄` carrier over
`𝔽₂`. This file constructs that subgroup by the common-kernel Hopf ideal of their coordinate maps
inside `GL₂₆`. Its universal property characterizes it as the smallest closed subgroup of `GL₂₆`
containing those generators.

The factorizations of the positive root subgroups and the weight torus through it recover the
named maps into the full carrier, and morphisms out of it are determined by their restrictions to
these generators. This is the subgroup from which a Borel subgroup containing the weight torus is
to be built. Maximality among solvable subgroups, and identification of the carrier with an
independently pinned simply connected group scheme, are not asserted here.

## Main definitions

* `TauCeti.F4ShortRoot.PrimeField.Positive.definingIdeal`: the largest Hopf ideal of
  `O(GL₂₆/𝔽₂)` killed by the positive simple-root and weight-torus coordinate maps.
* `TauCeti.F4ShortRoot.PrimeField.Positive.groupScheme`: the positive subgroup, with
  `inclusion` its closed immersion into the carrier and `closedSubgroup` the corresponding
  closed subgroup.
* `TauCeti.F4ShortRoot.PrimeField.Positive.rootSubgroup` and
  `TauCeti.F4ShortRoot.PrimeField.Positive.weightTorus`: the generators, factored through it.

## Main results

* `TauCeti.F4ShortRoot.PrimeField.Positive.le_definingIdeal_iff`: the universal property.
* `TauCeti.F4ShortRoot.PrimeField.Positive.groupScheme_hom_ext`: rigidity of morphisms out of
  the positive subgroup.
* `TauCeti.F4ShortRoot.PrimeField.Positive.algebraSmooth_coordinateHopfAlgebra` and
  `TauCeti.F4ShortRoot.PrimeField.Positive.geometricallyConnected_coordinateHopfAlgebra`: the
  positive subgroup is smooth and geometrically connected.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.h and Chapters 17 and 21.
* J. E. Humphreys, *Linear Algebraic Groups*, §§26–28.

The construction follows the positive short-root type-`G₂` subgroup in
`TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Positive.Basic`.
-/

public section

open AlgebraicGeometry CategoryTheory
open TauCeti.CommHopfAlgCat (
  geometricallyConnectedCommHopfAlgProperty_commonKernelQuotient_of_geometricallyConnected)

namespace TauCeti.F4ShortRoot.PrimeField.Positive

noncomputable section

/-- The coordinate algebras of the four positive simple-root subgroups and the weight torus. -/
abbrev generatorCodomain : Fin 4 ⊕ Unit → CommHopfAlgCat (ZMod 2)
  | .inl i => PrimeField.generatorCodomain (.inl (.inl i))
  | .inr u => PrimeField.generatorCodomain (.inr u)

/-- The positive generating coordinate maps, retaining the numbered positive roots of the
short-root carrier and its weight torus. -/
def generator : ∀ j, GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26 ⟶ generatorCodomain j
  | .inl i => PrimeField.generator (.inl (.inl i))
  | .inr u => PrimeField.generator (.inr u)

/-- A positive root coordinate map is the corresponding map of the full carrier. -/
@[simp]
theorem generator_inl (i : Fin 4) :
    generator (.inl i) = PrimeField.generator (.inl (.inl i)) := (rfl)

/-- The positive subgroup uses the full carrier's weight-torus coordinate map. -/
@[simp]
theorem generator_inr : generator (.inr ()) = PrimeField.generator (.inr ()) := (rfl)

/-- The largest Hopf ideal killed by the four positive simple-root maps and the weight torus. -/
abbrev definingIdeal : HopfIdeal (ZMod 2) (GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26) :=
  CommHopfAlgCat.commonKernelHopfIdeal generator

/-- The positive subgroup is the smallest closed subgroup containing the positive simple-root
subgroups and the weight torus, expressed contravariantly on Hopf ideals. -/
theorem le_definingIdeal_iff
    (I : HopfIdeal (ZMod 2) (GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26)) :
    I ≤ definingIdeal ↔
      (∀ i : Fin 4, I.toIdeal ≤ RingHom.ker
        (PrimeField.generator (.inl (.inl i))).hom.toAlgHom.toRingHom) ∧
      I.toIdeal ≤ RingHom.ker
        (PrimeField.generator (.inr ())).hom.toAlgHom.toRingHom := by
  rw [CommHopfAlgCat.le_commonKernelHopfIdeal_iff]
  constructor
  · intro h
    exact ⟨fun i ↦ h (.inl i), h (.inr ())⟩
  · rintro ⟨hroot, htorus⟩ (i | ⟨⟩)
    · exact hroot i
    · exact htorus

/-- The full carrier's ideal is contained in the positive subgroup's ideal. -/
theorem carrierDefiningIdeal_le : PrimeField.definingIdeal ≤ definingIdeal := by
  rw [le_definingIdeal_iff, PrimeField.definingIdeal_def]
  exact ⟨fun i ↦ CommHopfAlgCat.commonKernelHopfIdeal_toIdeal_le_ker
    PrimeField.generator (.inl (.inl i)),
    CommHopfAlgCat.commonKernelHopfIdeal_toIdeal_le_ker PrimeField.generator (.inr ())⟩

/-- The coordinate Hopf algebra of the positive subgroup. -/
abbrev coordinateHopfAlgebra : CommHopfAlgCat (ZMod 2) :=
  CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26) definingIdeal

/-- The positive subgroup as an affine group scheme over 𝔽₂. -/
abbrev groupScheme : Grp (Over (Spec (CommRingCat.of (ZMod 2)))) :=
  CommHopfAlgCat.quotientSpec (GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26) definingIdeal

/-- The closed inclusion of the positive subgroup in the full short-root carrier. -/
def inclusion : groupScheme ⟶ PrimeField.groupScheme :=
  CommHopfAlgCat.quotientSpecMapOfLe _ carrierDefiningIdeal_le ≫
    eqToHom PrimeField.groupScheme_def.symm

/-- The positive subgroup is a closed subgroup of the full carrier. -/
instance isClosedImmersion_inclusion : IsClosedImmersion inclusion.hom.hom.left := by
  rw [← closedSubgroupMorphismProperty_iff]
  rw [inclusion, (closedSubgroupMorphismProperty _).cancel_right_of_respectsIso]
  rw [closedSubgroupMorphismProperty_iff]
  infer_instance

/-- The positive subgroup bundled as a closed subgroup of the full short-root carrier. -/
def closedSubgroup : ClosedSubgroupScheme PrimeField.groupScheme :=
  ClosedSubgroupScheme.mk inclusion

/-- The positive closed subgroup is represented by its named inclusion. -/
@[simp]
theorem coe_closedSubgroup : closedSubgroup.1 = Subobject.mk inclusion :=
  ClosedSubgroupScheme.coe_mk _

/-- A positive simple-root subgroup factored through the positive subgroup. -/
def rootSubgroup (i : Fin 4) : AdditiveGroup.groupScheme (ZMod 2) ⟶ groupScheme :=
  eqToHom (AdditiveGroup.groupScheme_def (ZMod 2)) ≫
    (hopfSpec (CommRingCat.of (ZMod 2))).map
      (CommHopfAlgCat.commonKernelLift generator (.inl i)).op

/-- The weight torus factored through the positive subgroup. -/
def weightTorus : SplitTorus.groupScheme (ZMod 2) (Fin 4) ⟶ groupScheme :=
  eqToHom (DiagonalizableGroup.groupScheme_def (ZMod 2) (SplitTorus.characterGroup (Fin 4))) ≫
    (hopfSpec (CommRingCat.of (ZMod 2))).map
      (CommHopfAlgCat.commonKernelLift generator (.inr ())).op

/-- The positive inclusion followed by the carrier embedding is the quotient-spectrum
inclusion into the ambient general linear group. -/
@[reassoc (attr := simp)]
theorem inclusion_comp_carrierι :
    inclusion ≫ PrimeField.carrierι =
      CommHopfAlgCat.quotientSpecι _ definingIdeal ≫
        eqToHom (GeneralLinear.groupScheme_def (ZMod 2) 26).symm := by
  rw [inclusion, PrimeField.carrierι_def, GeneralLinear.generatedGroupSchemeι_def]
  simp only [Category.assoc, eqToHom_trans_assoc]
  -- `carrierι` is stated through the common-kernel ideal, which equals the carrier's named
  -- `definingIdeal` only propositionally; generalizing it lets the two be identified by `subst`.
  generalize_proofs hspec
  have hJ := PrimeField.definingIdeal_def
  generalize CommHopfAlgCat.commonKernelHopfIdeal PrimeField.generator = J at hspec hJ ⊢
  subst hJ
  rw [eqToHom_refl, Category.id_comp, ← Category.assoc,
    CommHopfAlgCat.quotientSpecMapOfLe_comp_quotientSpecι]

/-- Including a positive root subgroup into the full carrier recovers its numbered root map. -/
@[simp]
theorem rootSubgroup_comp_inclusion (i : Fin 4) :
    rootSubgroup i ≫ inclusion = PrimeField.rootSubgroup (.inl i) := by
  apply (cancel_mono PrimeField.carrierι).1
  rw [Category.assoc, inclusion_comp_carrierι, PrimeField.rootSubgroup_comp_carrierι]
  simp only [rootSubgroup, Category.assoc]
  slice_lhs 2 3 =>
    rw [CommHopfAlgCat.hopfSpec_map_comp_quotientSpecι,
      CommHopfAlgCat.mkQuotient_comp_commonKernelLift, generator_inl]

/-- Including the positive subgroup's weight torus recovers the carrier's weight torus. -/
@[simp]
theorem weightTorus_comp_inclusion : weightTorus ≫ inclusion = PrimeField.weightTorus := by
  apply (cancel_mono PrimeField.carrierι).1
  rw [Category.assoc, inclusion_comp_carrierι, PrimeField.weightTorus_comp_carrierι]
  simp only [weightTorus, Category.assoc]
  slice_lhs 2 3 =>
    rw [CommHopfAlgCat.hopfSpec_map_comp_quotientSpecι,
      CommHopfAlgCat.mkQuotient_comp_commonKernelLift, generator_inr]

/-- Positive simple-root maps remain closed immersions after factoring through the subgroup. -/
instance isClosedImmersion_rootSubgroup (i : Fin 4) :
    IsClosedImmersion (rootSubgroup i).hom.hom.left := by
  have h : IsClosedImmersion ((rootSubgroup i ≫ inclusion).hom.hom.left) := by
    rw [rootSubgroup_comp_inclusion]
    infer_instance
  simp only [Grp.comp', Mon.comp_hom', Over.comp_left] at h
  exact IsClosedImmersion.of_comp (f := (rootSubgroup i).hom.hom.left)
    (g := inclusion.hom.hom.left)

/-- The weight torus is a closed subgroup of the positive subgroup. -/
instance isClosedImmersion_weightTorus : IsClosedImmersion weightTorus.hom.hom.left := by
  have h : IsClosedImmersion ((weightTorus ≫ inclusion).hom.hom.left) := by
    rw [weightTorus_comp_inclusion]
    infer_instance
  simp only [Grp.comp', Mon.comp_hom', Over.comp_left] at h
  exact IsClosedImmersion.of_comp (f := weightTorus.hom.hom.left) (g := inclusion.hom.hom.left)

/-- Each positive simple-root closed subgroup of the carrier lies in the positive subgroup. -/
theorem rootSubgroup_le_closedSubgroup (i : Fin 4) :
    ClosedSubgroupScheme.mk (PrimeField.rootSubgroup (.inl i)) ≤ closedSubgroup := by
  rw [← Subtype.coe_le_coe, ClosedSubgroupScheme.coe_mk, coe_closedSubgroup]
  exact Subobject.mk_le_mk_of_comm (rootSubgroup i) (rootSubgroup_comp_inclusion i)

/-- The carrier's weight torus lies in the positive subgroup. -/
theorem weightTorus_le_closedSubgroup :
    ClosedSubgroupScheme.mk PrimeField.weightTorus ≤ closedSubgroup := by
  rw [← Subtype.coe_le_coe, ClosedSubgroupScheme.coe_mk, coe_closedSubgroup]
  exact Subobject.mk_le_mk_of_comm weightTorus weightTorus_comp_inclusion

/-- A morphism from the positive subgroup to an affine group scheme is determined by its
restrictions to the positive simple-root subgroups and the weight torus. -/
@[ext]
theorem groupScheme_hom_ext {Y : _root_.CommHopfAlgCat.{0} (ZMod 2)}
    (f g : groupScheme ⟶ (hopfSpec (CommRingCat.of (ZMod 2))).obj (Opposite.op Y))
    (hroot : ∀ i, rootSubgroup i ≫ f = rootSubgroup i ≫ g)
    (htorus : weightTorus ≫ f = weightTorus ≫ g) : f = g := by
  apply CommHopfAlgCat.hom_ext_of_preimage_unop_eq f g
  apply CommHopfAlgCat.commonKernelLift_hom_ext generator
  rintro (i | ⟨⟩)
  · apply CommHopfAlgCat.preimage_unop_comp_eq_of_hopfSpec_map_comp_eq _ f g
    have hi := hroot i
    rw [rootSubgroup, Category.assoc] at hi
    exact (cancel_epi (eqToHom (AdditiveGroup.groupScheme_def (ZMod 2)))).1 hi
  · apply CommHopfAlgCat.preimage_unop_comp_eq_of_hopfSpec_map_comp_eq _ f g
    rw [weightTorus, Category.assoc] at htorus
    exact (cancel_epi (eqToHom
      (DiagonalizableGroup.groupScheme_def (ZMod 2) (SplitTorus.characterGroup (Fin 4))))).1 htorus

/-- The positive subgroup is smooth over its prime field. -/
instance algebraSmooth_coordinateHopfAlgebra : Algebra.Smooth (ZMod 2) coordinateHopfAlgebra := by
  let : ∀ j, IsReduced (generatorCodomain j) := by
    rintro (i | ⟨⟩)
    · exact AdditiveGroup.isReduced_coordinateHopfAlgebra (ZMod 2)
    · exact inferInstance
  exact (smoothCommHopfAlgProperty_iff _).mp
    (CommHopfAlgCat.smoothCommHopfAlgProperty_quotient_commonKernelHopfIdeal_of_perfectField
      generator)

/-- The positive subgroup has smooth structural morphism. -/
instance smooth_groupScheme : Smooth groupScheme.X.hom :=
  (smoothAffineGroupSchemeProperty_iff _ _).mp
    ((algebraSmooth_iff_smooth_hopfSpec (ZMod 2) _).mp
      ((smoothCommHopfAlgProperty_iff _).mpr algebraSmooth_coordinateHopfAlgebra))

/-- The positive subgroup is geometrically connected over 𝔽₂. -/
theorem geometricallyConnected_coordinateHopfAlgebra :
    geometricallyConnectedCommHopfAlgProperty (ZMod 2) coordinateHopfAlgebra := by
  apply geometricallyConnectedCommHopfAlgProperty_commonKernelQuotient_of_geometricallyConnected
    generator
  rintro (i | ⟨⟩)
  · rw [geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace_of_isAlgClosed]
    intro K _ _ _
    have := AdditiveGroup.connectedSpace_primeSpectrum_baseChange_coordinateHopfAlgebra
      (ZMod 2) K
    let e := Algebra.TensorProduct.comm (ZMod 2)
      (AdditiveGroup.coordinateHopfAlgebra (ZMod 2)) K
    exact connectedSpace_primeSpectrum_of_injective e.toRingHom e.injective
  · exact DiagonalizableGroup.geometricallyConnected_coordinateRing (ZMod 2)
      (SplitTorus.characterGroup (Fin 4))

end

end TauCeti.F4ShortRoot.PrimeField.Positive
