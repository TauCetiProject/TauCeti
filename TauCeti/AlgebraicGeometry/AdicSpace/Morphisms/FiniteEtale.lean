/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Affinoid
public import TauCeti.RingTheory.Huber.Pair.Finite

import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.Topology.LocalAtTarget
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Emptiness
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.FiniteAlgebra
import TauCeti.RingTheory.Huber.ModuleTopology.FiniteEtale
import TauCeti.RingTheory.Huber.ModuleTopology.NaturallyComplete

/-!
# Finite étale morphisms of analytic adic spaces

A morphism `f : Y ⟶ X` of adic spaces is *finite étale* (`TauCeti.AdicSpace.IsFiniteEtale`) when
every point of `X` has an open neighbourhood `V`, isomorphic to `Spa(A, A⁺)` for a complete
Hausdorff Tate Huber pair `(A, A⁺)`, whose preimage `f⁻¹(V)` is isomorphic to `Spa(B, B⁺)` for a
sheafy Huber pair `(B, B⁺)` such that over `V` the morphism `f` is induced by a finite étale
morphism of Huber pairs `(A, A⁺) → (B, B⁺)` (`TauCeti.Huber.Pair.Hom.IsFiniteEtale`). Neither
noetherianness nor strong sheafiness of the base is assumed. Because `B` is finite projective over
`A` with its module topology, `B` is automatically complete, Hausdorff, and Tate
(`IsFiniteEtale.exists_complete_tate_chart`, `IsFiniteEtale.exists_ofPair_chart`), so both `X` and
`Y` are analytic (`IsFiniteEtale.isAnalytic_target`, `IsFiniteEtale.isAnalytic_source`).

## Main definitions and results

* `TauCeti.AdicSpace.IsFiniteEtale`, `IsFiniteEtale.Chart`, `IsFiniteEtale.CompleteTateChart`,
  `IsFiniteEtale.OfPairChart`, `IsFiniteEtale.exists_complete_tate_chart`,
  `IsFiniteEtale.exists_ofPair_chart`, `IsFiniteEtale.isAnalytic_target`,
  `IsFiniteEtale.isAnalytic_source`.
* `IsFiniteEtale.respectsIso`, `IsFiniteEtale.comapOfPresentation`, `IsFiniteEtale.comapOfPair`,
  `IsFiniteEtale.of_iSup_eq_top`, and characterizations of `𝟙 X`, isomorphisms, and empty sources.
* `IsFiniteEtale.locallyOfFiniteType`, `IsFiniteEtale.quasiCompact`,
  `IsFiniteEtale.isWeaklyFiniteType`, `IsFiniteEtale.isLocallyNoetherianAnalytic_source`,
  `IsFiniteEtale.isClopen_range`, `IsFiniteEtale.surjective_of_nonempty_of_preconnectedSpace`.

## Implementation notes

`IsFiniteEtale`, `IsFiniteEtale.respectsIso`, and `IsFiniteEtale.of_iSup_eq_top` are adapted from
`TauCeti.PreAdicSpace.IsClosedImmersion` and `TauCeti.PreAdicSpace.IsClosedImmersion.of_iSup_eq_top`
via `Hom.prop_restrictPreimage_iff_of_isOpenImmersion` and
`Hom.prop_restrictPreimage_restrictPreimage_iff`.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §8.2, Definition 8.2.16.
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §7, Definition 7.1.
* P. Scholze, *Étale cohomology of diamonds*, arXiv:1709.07343, §6, Definition 6.2(i).
* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of Mathematics
  E30 (1996), §1.6.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

namespace TauCeti.AdicSpace

open Huber PreAdicSpace ValuationSpectrum

universe u

variable {X Y Z : AdicSpace.{u}}

/-! ### Definition and chart upgrades -/

private structure FiniteEtaleModel {U' V' : PreAdicSpace.{u}} (g : U' ⟶ V') : Type (u + 1) where
  Target : Type u
  [commRingTarget : CommRing Target]
  [uniformSpaceTarget : UniformSpace Target]
  [isUniformAddGroupTarget : IsUniformAddGroup Target]
  [isTopologicalRingTarget : IsTopologicalRing Target]
  [completeSpaceTarget : CompleteSpace Target]
  [t2SpaceTarget : T2Space Target]
  [isTateRingTarget : IsTateRing Target]
  targetPair : Pair Target
  targetPresentation : PairOfDefinition Target
  targetLe : targetPresentation.ringOfDefinition ≤ targetPair.plus
  Source : Type u
  [commRingSource : CommRing Source]
  [topologicalSpaceSource : TopologicalSpace Source]
  [isTopologicalRingSource : IsTopologicalRing Source]
  [isHuberRingSource : IsHuberRing Source]
  sourcePair : Pair Source
  sourcePresentation : PairOfDefinition Source
  sourceLe : sourcePresentation.ringOfDefinition ≤ sourcePair.plus
  isSheafSource : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa sourcePair.plus))
    (presentationLimitPresheaf sourcePresentation sourcePair.plus)
  pairHom : Pair.Hom targetPair sourcePair
  isFiniteEtale : pairHom.IsFiniteEtale
  targetIso : V' ≅ presentationLimitPreAdicSpace targetPresentation targetPair.plus
    targetPair.isRingOfIntegralElements.isPowerBounded_of_mem targetLe
  sourceIso : U' ≅ presentationLimitPreAdicSpace sourcePresentation sourcePair.plus
    sourcePair.isRingOfIntegralElements.isPowerBounded_of_mem sourceLe
  fac : g = sourceIso.hom ≫
    presentationLimitPreAdicSpacePairComap targetPresentation sourcePresentation
      targetLe sourceLe isSheafSource pairHom ≫ targetIso.inv

attribute [instance] FiniteEtaleModel.commRingTarget FiniteEtaleModel.uniformSpaceTarget
  FiniteEtaleModel.isUniformAddGroupTarget FiniteEtaleModel.isTopologicalRingTarget
  FiniteEtaleModel.completeSpaceTarget FiniteEtaleModel.t2SpaceTarget
  FiniteEtaleModel.isTateRingTarget FiniteEtaleModel.commRingSource
  FiniteEtaleModel.topologicalSpaceSource FiniteEtaleModel.isTopologicalRingSource
  FiniteEtaleModel.isHuberRingSource

private def hasFiniteEtaleModel : MorphismProperty PreAdicSpace.{u} := fun _ _ g ↦
  Nonempty (FiniteEtaleModel g)

private instance : MorphismProperty.RespectsIso (@hasFiniteEtaleModel.{u}) :=
  MorphismProperty.RespectsIso.mk _
    (fun e _ ⟨m⟩ ↦ ⟨{ m with sourceIso := e ≪≫ m.sourceIso, fac := by simp [m.fac] }⟩)
    (fun e _ ⟨m⟩ ↦ ⟨{ m with targetIso := e.symm ≪≫ m.targetIso, fac := by simp [m.fac] }⟩)

/-- **Finite étale morphisms of analytic adic spaces** (Kedlaya–Liu I, Definition 8.2.16; Scholze,
Definition 7.1; modelled formally on `TauCeti.PreAdicSpace.IsClosedImmersion`): a morphism
`f : Y ⟶ X` in `AdicSpace` is *finite étale* when every point `x` of `X` has an open neighbourhood
`V`, isomorphic to `Spa(A, A⁺)` for a complete Hausdorff Tate Huber pair `(A, A⁺)`, whose full
preimage `f⁻¹(V)` is isomorphic to `Spa(B, B⁺)` for a sheafy Huber pair `(B, B⁺)` such that over `V`
the morphism `f` is induced by a finite étale morphism of Huber pairs `φ : (A, A⁺) → (B, B⁺)`. -/
def IsFiniteEtale : MorphismProperty AdicSpace.{u} := fun _ X f ↦
  ∀ x : X.obj, ∃ V : Opens X.obj, x ∈ V ∧ hasFiniteEtaleModel (f.hom.restrictPreimage V)

namespace IsFiniteEtale

/-- A local presentation-based chart witnessing `IsFiniteEtale f` around `x : X.obj`. -/
structure Chart {Y X : AdicSpace.{u}} (f : Y ⟶ X) (x : X.obj) : Type (u + 1) where
  /-- Open neighbourhood of `x` in the target. -/
  V : Opens X.obj
  /-- Membership of `x` in `V`. -/
  mem : x ∈ V
  /-- Target coefficient ring. -/
  Target : Type u
  [commRingTarget : CommRing Target]
  [uniformSpaceTarget : UniformSpace Target]
  [isUniformAddGroupTarget : IsUniformAddGroup Target]
  [isTopologicalRingTarget : IsTopologicalRing Target]
  [completeSpaceTarget : CompleteSpace Target]
  [t2SpaceTarget : T2Space Target]
  [isTateRingTarget : IsTateRing Target]
  /-- Target Huber pair. -/
  targetPair : Pair Target
  /-- Compatible pair of definition for `Target`. -/
  targetPresentation : PairOfDefinition Target
  /-- Compatibility of `targetPresentation` with `targetPair.plus`. -/
  targetLe : targetPresentation.ringOfDefinition ≤ targetPair.plus
  /-- Source coefficient ring. -/
  Source : Type u
  [commRingSource : CommRing Source]
  [topologicalSpaceSource : TopologicalSpace Source]
  [isTopologicalRingSource : IsTopologicalRing Source]
  [isHuberRingSource : IsHuberRing Source]
  /-- Source Huber pair. -/
  sourcePair : Pair Source
  /-- Compatible pair of definition for `Source`. -/
  sourcePresentation : PairOfDefinition Source
  /-- Compatibility of `sourcePresentation` with `sourcePair.plus`. -/
  sourceLe : sourcePresentation.ringOfDefinition ≤ sourcePair.plus
  /-- Sheafiness of the source presentation. -/
  isSheafSource : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa sourcePair.plus))
    (presentationLimitPresheaf sourcePresentation sourcePair.plus)
  /-- Underlying finite étale morphism of Huber pairs. -/
  pairHom : Pair.Hom targetPair sourcePair
  /-- Proof that `pairHom` is finite étale. -/
  isFiniteEtale : pairHom.IsFiniteEtale
  /-- Identification of `X|_V` with `Spa(Target, targetPair⁺)`. -/
  targetIso : X.obj.restrict V.isOpenEmbedding ≅
    presentationLimitPreAdicSpace targetPresentation targetPair.plus
      targetPair.isRingOfIntegralElements.isPowerBounded_of_mem targetLe
  /-- Identification of `Y|_{f⁻¹(V)}` with `Spa(Source, sourcePair⁺)`. -/
  sourceIso : Y.obj.restrict ((Opens.map f.hom.base).obj V).isOpenEmbedding ≅
    presentationLimitPreAdicSpace sourcePresentation sourcePair.plus
      sourcePair.isRingOfIntegralElements.isPowerBounded_of_mem sourceLe
  /-- Compatibility of `f` over `V` with `pairHom`. -/
  fac : Y.obj.ofRestrict _ ≫ f.hom =
    sourceIso.hom ≫
      presentationLimitPreAdicSpacePairComap targetPresentation sourcePresentation
        targetLe sourceLe isSheafSource pairHom ≫
      targetIso.inv ≫ X.obj.ofRestrict _

attribute [instance] Chart.commRingTarget Chart.uniformSpaceTarget Chart.isUniformAddGroupTarget
  Chart.isTopologicalRingTarget Chart.completeSpaceTarget Chart.t2SpaceTarget
  Chart.isTateRingTarget Chart.commRingSource Chart.topologicalSpaceSource
  Chart.isTopologicalRingSource Chart.isHuberRingSource

private def Chart.toModel {f : Y ⟶ X} {x : X.obj} (c : Chart f x) :
    FiniteEtaleModel (f.hom.restrictPreimage c.V) where
  Target := c.Target
  targetPair := c.targetPair
  targetPresentation := c.targetPresentation
  targetLe := c.targetLe
  Source := c.Source
  sourcePair := c.sourcePair
  sourcePresentation := c.sourcePresentation
  sourceLe := c.sourceLe
  isSheafSource := c.isSheafSource
  pairHom := c.pairHom
  isFiniteEtale := c.isFiniteEtale
  targetIso := c.targetIso
  sourceIso := c.sourceIso
  fac := by
    rw [← cancel_mono (X.obj.ofRestrict c.V.isOpenEmbedding), Hom.restrictPreimage_ofRestrict,
      c.fac, Category.assoc, Category.assoc]

private def _root_.TauCeti.AdicSpace.FiniteEtaleModel.toChart {f : Y ⟶ X} {V : Opens X.obj}
    {x : X.obj} (hx : x ∈ V) (m : FiniteEtaleModel (f.hom.restrictPreimage V)) : Chart f x where
  V := V
  mem := hx
  Target := m.Target
  targetPair := m.targetPair
  targetPresentation := m.targetPresentation
  targetLe := m.targetLe
  Source := m.Source
  sourcePair := m.sourcePair
  sourcePresentation := m.sourcePresentation
  sourceLe := m.sourceLe
  isSheafSource := m.isSheafSource
  pairHom := m.pairHom
  isFiniteEtale := m.isFiniteEtale
  targetIso := m.targetIso
  sourceIso := m.sourceIso
  fac := by
    rw [← Hom.restrictPreimage_ofRestrict]
    exact (congrArg (· ≫ X.obj.ofRestrict V.isOpenEmbedding) m.fac).trans
      (by simp only [Category.assoc])

/-- A local presentation-based chart for `IsFiniteEtale f` around `x : X.obj` in which the source
coefficient ring is also complete, Hausdorff, and Tate. -/
structure CompleteTateChart {Y X : AdicSpace.{u}} (f : Y ⟶ X) (x : X.obj) : Type (u + 1) where
  /-- Open neighbourhood of `x` in the target. -/
  V : Opens X.obj
  /-- Membership of `x` in `V`. -/
  mem : x ∈ V
  /-- Target coefficient ring. -/
  Target : Type u
  [commRingTarget : CommRing Target]
  [uniformSpaceTarget : UniformSpace Target]
  [isUniformAddGroupTarget : IsUniformAddGroup Target]
  [isTopologicalRingTarget : IsTopologicalRing Target]
  [completeSpaceTarget : CompleteSpace Target]
  [t2SpaceTarget : T2Space Target]
  [isTateRingTarget : IsTateRing Target]
  /-- Target Huber pair. -/
  targetPair : Pair Target
  /-- Compatible pair of definition for `Target`. -/
  targetPresentation : PairOfDefinition Target
  /-- Compatibility of `targetPresentation` with `targetPair.plus`. -/
  targetLe : targetPresentation.ringOfDefinition ≤ targetPair.plus
  /-- Source coefficient ring. -/
  Source : Type u
  [commRingSource : CommRing Source]
  [uniformSpaceSource : UniformSpace Source]
  [isUniformAddGroupSource : IsUniformAddGroup Source]
  [isTopologicalRingSource : IsTopologicalRing Source]
  [completeSpaceSource : CompleteSpace Source]
  [t2SpaceSource : T2Space Source]
  [isTateRingSource : IsTateRing Source]
  /-- Source Huber pair. -/
  sourcePair : Pair Source
  /-- Compatible pair of definition for `Source`. -/
  sourcePresentation : PairOfDefinition Source
  /-- Compatibility of `sourcePresentation` with `sourcePair.plus`. -/
  sourceLe : sourcePresentation.ringOfDefinition ≤ sourcePair.plus
  /-- Sheafiness of the source presentation. -/
  isSheafSource : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa sourcePair.plus))
    (presentationLimitPresheaf sourcePresentation sourcePair.plus)
  /-- Underlying finite étale morphism of Huber pairs. -/
  pairHom : Pair.Hom targetPair sourcePair
  /-- Proof that `pairHom` is finite étale. -/
  isFiniteEtale : pairHom.IsFiniteEtale
  /-- Identification of `X|_V` with `Spa(Target, targetPair⁺)`. -/
  targetIso : X.obj.restrict V.isOpenEmbedding ≅
    presentationLimitPreAdicSpace targetPresentation targetPair.plus
      targetPair.isRingOfIntegralElements.isPowerBounded_of_mem targetLe
  /-- Identification of `Y|_{f⁻¹(V)}` with `Spa(Source, sourcePair⁺)`. -/
  sourceIso : Y.obj.restrict ((Opens.map f.hom.base).obj V).isOpenEmbedding ≅
    presentationLimitPreAdicSpace sourcePresentation sourcePair.plus
      sourcePair.isRingOfIntegralElements.isPowerBounded_of_mem sourceLe
  /-- Compatibility of `f` over `V` with `pairHom`. -/
  fac : Y.obj.ofRestrict _ ≫ f.hom =
    sourceIso.hom ≫
      presentationLimitPreAdicSpacePairComap targetPresentation sourcePresentation
        targetLe sourceLe isSheafSource pairHom ≫
      targetIso.inv ≫ X.obj.ofRestrict _

attribute [instance] CompleteTateChart.commRingTarget CompleteTateChart.uniformSpaceTarget
  CompleteTateChart.isUniformAddGroupTarget CompleteTateChart.isTopologicalRingTarget
  CompleteTateChart.completeSpaceTarget CompleteTateChart.t2SpaceTarget
  CompleteTateChart.isTateRingTarget CompleteTateChart.commRingSource
  CompleteTateChart.uniformSpaceSource CompleteTateChart.isUniformAddGroupSource
  CompleteTateChart.isTopologicalRingSource CompleteTateChart.completeSpaceSource
  CompleteTateChart.t2SpaceSource CompleteTateChart.isTateRingSource

/-- A local `AdicSpace.ofPair`-based chart for `IsFiniteEtale f` around `x : X.obj`. -/
structure OfPairChart {Y X : AdicSpace.{u}} (f : Y ⟶ X) (x : X.obj) : Type (u + 1) where
  /-- Open neighbourhood of `x` in the target. -/
  V : Opens X.obj
  /-- Membership of `x` in `V`. -/
  mem : x ∈ V
  /-- Target coefficient ring. -/
  Target : Type u
  [commRingTarget : CommRing Target]
  [uniformSpaceTarget : UniformSpace Target]
  [isUniformAddGroupTarget : IsUniformAddGroup Target]
  [isTopologicalRingTarget : IsTopologicalRing Target]
  [completeSpaceTarget : CompleteSpace Target]
  [t2SpaceTarget : T2Space Target]
  [isTateRingTarget : IsTateRing Target]
  /-- Target Huber pair. -/
  targetPair : Pair Target
  /-- Sheafiness of `targetPair`. -/
  isSheafyTarget : IsSheafyForEveryPresentation targetPair.plus
  /-- Source coefficient ring. -/
  Source : Type u
  [commRingSource : CommRing Source]
  [uniformSpaceSource : UniformSpace Source]
  [isUniformAddGroupSource : IsUniformAddGroup Source]
  [isTopologicalRingSource : IsTopologicalRing Source]
  [completeSpaceSource : CompleteSpace Source]
  [t2SpaceSource : T2Space Source]
  [isTateRingSource : IsTateRing Source]
  /-- Source Huber pair. -/
  sourcePair : Pair Source
  /-- Sheafiness of `sourcePair`. -/
  isSheafySource : IsSheafyForEveryPresentation sourcePair.plus
  /-- Underlying finite étale morphism of Huber pairs. -/
  pairHom : Pair.Hom targetPair sourcePair
  /-- Proof that `pairHom` is finite étale. -/
  isFiniteEtale : pairHom.IsFiniteEtale
  /-- Identification of `X|_V` with `(ofPair targetPair isSheafyTarget).obj`. -/
  targetIso : X.obj.restrict V.isOpenEmbedding ≅ (ofPair targetPair isSheafyTarget).obj
  /-- Identification of `Y|_{f⁻¹(V)}` with `(ofPair sourcePair isSheafySource).obj`. -/
  sourceIso : Y.obj.restrict ((Opens.map f.hom.base).obj V).isOpenEmbedding ≅
    (ofPair sourcePair isSheafySource).obj
  /-- Compatibility of `f` over `V` with `comapOfPair isSheafyTarget isSheafySource pairHom`. -/
  fac : Y.obj.ofRestrict _ ≫ f.hom =
    sourceIso.hom ≫ (comapOfPair isSheafyTarget isSheafySource pairHom).hom ≫
      targetIso.inv ≫ X.obj.ofRestrict _

attribute [instance] OfPairChart.commRingTarget OfPairChart.uniformSpaceTarget
  OfPairChart.isUniformAddGroupTarget OfPairChart.isTopologicalRingTarget
  OfPairChart.completeSpaceTarget OfPairChart.t2SpaceTarget OfPairChart.isTateRingTarget
  OfPairChart.commRingSource OfPairChart.uniformSpaceSource OfPairChart.isUniformAddGroupSource
  OfPairChart.isTopologicalRingSource OfPairChart.completeSpaceSource OfPairChart.t2SpaceSource
  OfPairChart.isTateRingSource

end IsFiniteEtale

/-- Unfolding lemma for `TauCeti.AdicSpace.IsFiniteEtale`. -/
theorem isFiniteEtale_iff (f : Y ⟶ X) :
    IsFiniteEtale f ↔ ∀ x : X.obj, Nonempty (IsFiniteEtale.Chart f x) :=
  ⟨fun hf x ↦ let ⟨_, hx, ⟨m⟩⟩ := hf x; ⟨m.toChart hx⟩,
    fun hf x ↦ let ⟨c⟩ := hf x; ⟨c.V, c.mem, ⟨c.toModel⟩⟩⟩

private theorem isNaturallyComplete_of_isFiniteEtale {A B : Type u} [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T2Space A] [IsHuberRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
    {S : Pair A} {T : Pair B} {φ : Pair.Hom S T} (hφ : φ.IsFiniteEtale) :
    letI : Algebra A B := φ.toRingHom.toAlgebra
    IsNaturallyComplete A B := by
  let _ : Algebra A B := φ.toRingHom.toAlgebra
  have _ : Module.Finite A B := hφ.finite
  have _ : Algebra.Etale A B := hφ.etale
  have _ : Module.FinitePresentation A B := .of_finite_of_finitePresentation A B
  have _ : Module.Projective A B := Module.Flat.projective_of_finitePresentation
  exact IsNaturallyComplete.of_projective (A := A) (M := B)

/-- Around every point `x : X.obj`, a finite étale morphism `f : Y ⟶ X` admits an open
neighbourhood `V` of `x` over which `f` is modelled by a finite étale morphism `φ : (A, S) → (B, T)`
where both `A` and `B` are complete Hausdorff Tate rings. -/
theorem IsFiniteEtale.exists_complete_tate_chart {f : Y ⟶ X} (hf : IsFiniteEtale f) (x : X.obj) :
    Nonempty (IsFiniteEtale.CompleteTateChart f x) := by
  obtain ⟨c⟩ := (isFiniteEtale_iff f).mp hf x
  let _ : Algebra c.Target c.Source := c.pairHom.toRingHom.toAlgebra
  have _ : Module.Finite c.Target c.Source := c.isFiniteEtale.finite
  have _ : IsModuleTopology c.Target c.Source := c.isFiniteEtale.isModuleTopology
  let _ : UniformSpace c.Source := IsTopologicalAddGroup.rightUniformSpace c.Source
  have _ : IsUniformAddGroup c.Source := isUniformAddGroup_of_addCommGroup
  obtain ⟨_, _⟩ := isNaturallyComplete_iff.mp (isNaturallyComplete_of_isFiniteEtale c.isFiniteEtale)
  have _ : IsTateRing c.Source := IsTateRing.of_isModuleTopology (A := c.Target) (B := c.Source)
  exact ⟨{
    V := c.V
    mem := c.mem
    Target := c.Target
    targetPair := c.targetPair
    targetPresentation := c.targetPresentation
    targetLe := c.targetLe
    Source := c.Source
    sourcePair := c.sourcePair
    sourcePresentation := c.sourcePresentation
    sourceLe := c.sourceLe
    isSheafSource := c.isSheafSource
    pairHom := c.pairHom
    isFiniteEtale := c.isFiniteEtale
    targetIso := c.targetIso
    sourceIso := c.sourceIso
    fac := c.fac }⟩

private theorem isSheaf_of_restrict_iso {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsHuberRing A] {S : Pair A} {P : PairOfDefinition A}
    (hP : P.ringOfDefinition ≤ S.plus) {V : Opens X.obj} (eV : X.obj.restrict V.isOpenEmbedding ≅
      presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP) :
    Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus) :=
  (isSheafy_presentationLimitPreAdicSpace_iff P S.plus _ hP).mp
    ((ObjectProperty.prop_iff_of_iso PreAdicSpace.isSheafy eV).mp
      (isSheafy_restrict _ X.property.isSheafy))

/-- Around every point `x : X.obj`, a finite étale morphism `f : Y ⟶ X` admits an open
neighbourhood `V` of `x` over which `f` is modelled by `AdicSpace.comapOfPair` for a finite étale
morphism `φ : (A, S) → (B, T)` between complete Hausdorff Tate sheafy Huber pairs. -/
theorem IsFiniteEtale.exists_ofPair_chart {f : Y ⟶ X} (hf : IsFiniteEtale f) (x : X.obj) :
    Nonempty (IsFiniteEtale.OfPairChart f x) := by
  obtain ⟨c⟩ := hf.exists_complete_tate_chart x
  have hS := (isSheafyForEveryPresentation_iff_isRingOfIntegralElements_and_isSheaf
    c.targetPresentation).mpr ⟨c.targetPair.isRingOfIntegralElements,
      isSheaf_of_restrict_iso c.targetLe c.targetIso⟩
  have hT := (isSheafyForEveryPresentation_iff_isRingOfIntegralElements_and_isSheaf
    c.sourcePresentation).mpr ⟨c.sourcePair.isRingOfIntegralElements, c.isSheafSource⟩
  let iS : (ofPair c.targetPair hS).obj ≅
      presentationLimitPreAdicSpace c.targetPresentation c.targetPair.plus
        c.targetPair.isRingOfIntegralElements.isPowerBounded_of_mem c.targetLe :=
    (ObjectProperty.ι isAdic).mapIso
      (ofPairIsoOfPresentation c.targetPair hS c.targetPresentation c.targetLe)
  let iT : (ofPair c.sourcePair hT).obj ≅
      presentationLimitPreAdicSpace c.sourcePresentation c.sourcePair.plus
        c.sourcePair.isRingOfIntegralElements.isPowerBounded_of_mem c.sourceLe :=
    (ObjectProperty.ι isAdic).mapIso
      (ofPairIsoOfPresentation c.sourcePair hT c.sourcePresentation c.sourceLe)
  have hcomp_pre : iT.inv ≫ (comapOfPair hS hT c.pairHom).hom ≫ iS.hom =
      presentationLimitPreAdicSpacePairComap c.targetPresentation c.sourcePresentation
        c.targetLe c.sourceLe c.isSheafSource c.pairHom := by
    have hconj := congrArg InducedCategory.Hom.hom
      (comapOfPresentation_eq_ofPairIsoOfPresentation hS hT c.targetPresentation c.targetLe
        c.sourcePresentation c.sourceLe c.pairHom).symm
    simpa only [iS, iT, Functor.mapIso_hom, Functor.mapIso_inv, ObjectProperty.ι_map,
      ObjectProperty.FullSubcategory.comp_hom, comapOfPresentation_hom] using hconj
  refine ⟨{
    V := c.V
    mem := c.mem
    Target := c.Target
    targetPair := c.targetPair
    isSheafyTarget := hS
    Source := c.Source
    sourcePair := c.sourcePair
    isSheafySource := hT
    pairHom := c.pairHom
    isFiniteEtale := c.isFiniteEtale
    targetIso := c.targetIso ≪≫ iS.symm
    sourceIso := c.sourceIso ≪≫ iT.symm
    fac := ?_ }⟩
  rw [c.fac, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv]
  simp only [Category.assoc, ← reassoc_of% hcomp_pre]

/-- **The target of a finite étale morphism is analytic.** -/
theorem IsFiniteEtale.isAnalytic_target {f : Y ⟶ X} (hf : IsFiniteEtale f) : X.IsAnalytic := by
  refine isAnalytic_iff.mpr fun x ↦ ?_
  obtain ⟨V, hx, ⟨m⟩⟩ := hf x
  exact ⟨V, (mem_propOpens_iff _).mpr ((isTateAffinoid_iff _).mpr ⟨m.Target, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    m.targetPair, m.targetPresentation, m.targetLe, ⟨m.targetIso⟩⟩), hx⟩

/-- **The source of a finite étale morphism is analytic.** -/
theorem IsFiniteEtale.isAnalytic_source {f : Y ⟶ X} (hf : IsFiniteEtale f) : Y.IsAnalytic := by
  refine isAnalytic_iff.mpr fun y ↦ ?_
  obtain ⟨c⟩ := hf.exists_complete_tate_chart (f.hom.base y)
  exact ⟨(Opens.map f.hom.base).obj c.V, (mem_propOpens_iff _).mpr ((isTateAffinoid_iff _).mpr
    ⟨c.Source, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, c.sourcePair, c.sourcePresentation, c.sourceLe,
      ⟨c.sourceIso⟩⟩), c.mem⟩

/-! ### Invariance under isomorphism and affinoid constructors -/

private theorem IsFiniteEtale.iso_hom_comp (e : Z ≅ Y) {f : Y ⟶ X}
    (hf : IsFiniteEtale f) : IsFiniteEtale (e.hom ≫ f) := by
  intro x
  obtain ⟨V, hx, hV⟩ := hf x
  let e' : Z.obj ≅ Y.obj := (ObjectProperty.ι isAdic).mapIso e
  have : IsIso e'.inv := e'.isIso_inv
  refine ⟨V, hx, (Hom.prop_restrictPreimage_iff_of_isOpenImmersion ((e.hom ≫ f).hom) V
    (@hasFiniteEtaleModel.{u}) (f.hom.restrictPreimage V)
    (Y.obj.ofRestrict ((Opens.map f.hom.base).obj V).isOpenEmbedding ≫ e'.inv)
    (X.obj.ofRestrict V.isOpenEmbedding) (Opens.set_range_inclusion' V) ?_ ?_).mpr hV⟩
  · rw [comp_base, TopCat.coe_comp, Set.range_comp]
    exact (congrArg (e'.inv.base '' ·)
      (Opens.set_range_inclusion' ((Opens.map f.hom.base).obj V))).trans
        ((TopCat.homeoOfIso (forgetToTop.mapIso e')).toEquiv.image_symm_eq_preimage _)
  · simp [e', Hom.restrictPreimage_ofRestrict]

private theorem IsFiniteEtale.comp_iso_hom (e : X ≅ Z) {f : Y ⟶ X}
    (hf : IsFiniteEtale f) : IsFiniteEtale (f ≫ e.hom) := by
  intro z
  let e' : X.obj ≅ Z.obj := (ObjectProperty.ι isAdic).mapIso e
  have : IsIso e'.hom := e'.isIso_hom
  obtain ⟨V, hx, hV⟩ := hf (e'.inv.base z)
  let W : Opens Z.obj := (Opens.map e'.inv.base).obj V
  refine ⟨W, hx, (Hom.prop_restrictPreimage_iff_of_isOpenImmersion ((f ≫ e.hom).hom) W
    (@hasFiniteEtaleModel.{u}) (f.hom.restrictPreimage V)
    (Y.obj.ofRestrict ((Opens.map f.hom.base).obj V).isOpenEmbedding)
    (X.obj.ofRestrict V.isOpenEmbedding ≫ e'.hom) ?_ ?_ ?_).mpr hV⟩
  · rw [comp_base, TopCat.coe_comp, Set.range_comp]
    exact (congrArg (e'.hom.base '' ·) (Opens.set_range_inclusion' V)).trans
      ((TopCat.homeoOfIso (forgetToTop.mapIso e')).toEquiv.image_eq_preimage_symm _)
  · have key := Opens.map_hom_obj_map_inv_obj (forgetToTop.mapIso e') V
    simp only [Functor.mapIso_hom, Functor.mapIso_inv, forgetToTop_map] at key
    exact (Opens.set_range_inclusion' ((Opens.map f.hom.base).obj V)).trans
      (congrArg (f.hom.base ⁻¹' ·) (congrArg SetLike.coe key.symm))
  · simp [e', Hom.restrictPreimage_ofRestrict_assoc]

/-- Being finite étale is invariant under isomorphisms of the source and of the target. -/
instance IsFiniteEtale.respectsIso : MorphismProperty.RespectsIso (@IsFiniteEtale.{u}) :=
  MorphismProperty.RespectsIso.mk _ (fun e _ hf ↦ hf.iso_hom_comp e)
    (fun e _ hf ↦ hf.comp_iso_hom e)

/-- **Affinoid finite étale morphisms for explicit presentations.** If `(A, A⁺)` is a complete
Hausdorff Tate Huber pair and `φ : (A, A⁺) → (B, B⁺)` is finite étale between compatible sheafy
presentations, the induced morphism `Spa(B, B⁺) ⟶ Spa(A, A⁺)` in `AdicSpace` is finite étale. -/
theorem IsFiniteEtale.comapOfPresentation {A : Type u} [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T0Space A] [IsTateRing A]
    {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
    (S : Pair A) (P : PairOfDefinition A) (hS : P.ringOfDefinition ≤ S.plus)
    (hsheafS : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus)) (T : Pair B) (P' : PairOfDefinition B)
    (hT : P'.ringOfDefinition ≤ T.plus)
    (hsheafT : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus)) (φ : Pair.Hom S T) (hφ : φ.IsFiniteEtale) :
    IsFiniteEtale (AdicSpace.comapOfPresentation S P hS hsheafS T P' hT hsheafT φ) := by
  refine (isFiniteEtale_iff _).mpr fun _ ↦ ⟨{
    V := ⊤
    mem := trivial
    Target := A
    targetPair := S
    targetPresentation := P
    targetLe := hS
    Source := B
    sourcePair := T
    sourcePresentation := P'
    sourceLe := hT
    isSheafSource := hsheafT
    pairHom := φ
    isFiniteEtale := hφ
    targetIso := restrictTopIso _
    sourceIso :=
      restrictIsoOfRangeEq _ _ (Opens.isOpenEmbedding ⊤) (by rw [Opens.map_top]) ≪≫ restrictTopIso _
    fac := by
      rw [← restrictTopIso_hom, Iso.inv_hom_id, Category.comp_id, Iso.trans_hom, restrictTopIso_hom,
        Category.assoc, ← comapOfPresentation_hom S P hS hsheafS T P' hT hsheafT φ,
        restrictIsoOfRangeEq_hom_ofRestrict_assoc] }⟩

/-- **`Spa(φ)` is finite étale for a finite étale morphism of sheafy Huber pairs** over a complete
Hausdorff Tate ring (`AdicSpace.comapOfPair`). -/
theorem IsFiniteEtale.comapOfPair {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
    [IsTopologicalRing A] [CompleteSpace A] [T0Space A] [IsTateRing A] {B : Type u} [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B] {S : Pair A} {T : Pair B}
    (hS : IsSheafyForEveryPresentation S.plus) (hT : IsSheafyForEveryPresentation T.plus)
    (φ : Pair.Hom S T) (hφ : φ.IsFiniteEtale) : IsFiniteEtale (AdicSpace.comapOfPair hS hT φ) := by
  obtain ⟨P, hP, _⟩ := hS.exists_compatible_isSheaf
  obtain ⟨P', hP', _⟩ := hT.exists_compatible_isSheaf
  rw [comapOfPair_eq_ofPairIsoOfPresentation hS hT P hP P' hP' φ]
  exact ((IsFiniteEtale.comapOfPresentation S P hP (hS.isSheaf P hP) T P' hP'
    (hT.isSheaf P' hP') φ hφ).comp_iso_hom (ofPairIsoOfPresentation S hS P hP).symm).iso_hom_comp
    (ofPairIsoOfPresentation T hT P' hP')

/-! ### Target-cover descent, identities, isomorphisms, and empty covers -/

/-- **Finite étale morphisms descend along any open cover of the target**
(cf. `TauCeti.PreAdicSpace.IsClosedImmersion.of_iSup_eq_top`). -/
theorem IsFiniteEtale.of_iSup_eq_top {f : Y ⟶ X} {ι : Type*} (V : ι → Opens X.obj)
    (hV : iSup V = ⊤) (hf : ∀ i, IsFiniteEtale (AdicSpace.restrictPreimage f (V i))) :
    IsFiniteEtale f := by
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hV.symm ▸ Set.mem_univ x : x ∈ iSup V)
  obtain ⟨W, hx, hW⟩ := hf i ⟨x, hi⟩
  have hW' : hasFiniteEtaleModel ((f.hom.restrictPreimage (V i)).restrictPreimage W) :=
    (congrArg (fun g : (Y.restrict ((Opens.map f.hom.base).obj (V i))).obj ⟶
        (X.restrict (V i)).obj ↦ hasFiniteEtaleModel (g.restrictPreimage W))
      (AdicSpace.restrictPreimage_hom f (V i))).mp hW
  exact ⟨(V i).isOpenEmbedding.isOpenMap.functor.obj W, ⟨⟨x, hi⟩, hx, rfl⟩,
    (Hom.prop_restrictPreimage_restrictPreimage_iff f.hom (@hasFiniteEtaleModel.{u}) (V i) W).mp
      hW'⟩

/-- **The identity of an analytic adic space is finite étale.** -/
theorem IsFiniteEtale.id {X : AdicSpace.{u}} (hX : X.IsAnalytic) : IsFiniteEtale (𝟙 X) := by
  refine (isFiniteEtale_iff _).mpr fun x ↦ ?_
  obtain ⟨V, hV, hx⟩ := isAnalytic_iff.mp hX x
  obtain ⟨A, _, _, _, _, _, _, _, S, P, hP, ⟨eV⟩⟩ :=
    (isTateAffinoid_iff _).mp ((mem_propOpens_iff _).mp hV)
  refine ⟨{
    V := V
    mem := hx
    Target := A
    targetPair := S
    targetPresentation := P
    targetLe := hP
    Source := A
    sourcePair := S
    sourcePresentation := P
    sourceLe := hP
    isSheafSource := isSheaf_of_restrict_iso hP eV
    pairHom := Pair.Hom.id S
    isFiniteEtale := Pair.Hom.isFiniteEtale_id S
    targetIso := eV
    sourceIso := restrictIsoOfRangeEq X.obj _ V.isOpenEmbedding
      (by rw [Opens.set_range_inclusion', Opens.set_range_inclusion']; rfl) ≪≫ eV
    fac := ?_ }⟩
  rw [presentationLimitPreAdicSpacePairComap_id, Category.id_comp, Iso.trans_hom, Category.assoc,
    Iso.hom_inv_id_assoc, restrictIsoOfRangeEq_hom_ofRestrict]; exact Category.comp_id _

/-- **The identity of an adic space `X` is finite étale if and only if `X` is analytic.** -/
@[simp] theorem isFiniteEtale_id_iff {X : AdicSpace.{u}} : IsFiniteEtale (𝟙 X) ↔ X.IsAnalytic :=
  ⟨IsFiniteEtale.isAnalytic_target, IsFiniteEtale.id⟩

/-- **An isomorphism onto an analytic adic space is finite étale.** -/
theorem IsFiniteEtale.of_isIso (f : Y ⟶ X) [IsIso f] (hX : X.IsAnalytic) : IsFiniteEtale f := by
  simpa using (IsFiniteEtale.id hX).iso_hom_comp (asIso f)

/-- **An isomorphism in `AdicSpace` is finite étale if and only if its target is analytic.** -/
theorem isFiniteEtale_iff_of_isIso (f : Y ⟶ X) [IsIso f] : IsFiniteEtale f ↔ X.IsAnalytic :=
  ⟨IsFiniteEtale.isAnalytic_target, IsFiniteEtale.of_isIso f⟩

/-- **Every morphism from an empty adic space into an analytic adic space is finite étale.** -/
theorem IsFiniteEtale.of_isEmpty (f : Y ⟶ X) [IsEmpty Y.obj] (hX : X.IsAnalytic) :
    IsFiniteEtale f := by
  refine (isFiniteEtale_iff _).mpr fun x ↦ ?_
  obtain ⟨V, hV, hx⟩ := isAnalytic_iff.mp hX x
  obtain ⟨A, _, _, _, _, _, _, _, S, P, hP, ⟨eV⟩⟩ :=
    (isTateAffinoid_iff _).mp ((mem_propOpens_iff _).mp hV)
  let _ : IsTateRing PUnit.{u + 1} := IsTateRing.of_isModuleTopology (A := A) (B := PUnit.{u + 1})
  have _ : IsStronglyNoetherian PUnit.{u + 1} := IsNoetherianType.isStronglyNoetherian
  let T : Pair PUnit.{u + 1} := S.finiteAlgebra PUnit.{u + 1}
  obtain ⟨P', hP', hsheaf⟩ := (isSheafyForEveryPresentation_of_isStronglyNoetherian
    T.isRingOfIntegralElements).exists_compatible_isSheaf
  let Z : AdicSpace.{u} := ofPresentation T P' hP' hsheaf
  have _ : IsEmpty Z.obj := Set.isEmpty_coe_sort.mpr
    ((spa_eq_empty_iff_subsingleton _ T.isRingOfIntegralElements).mpr inferInstance)
  let U := (Opens.map f.hom.base).obj V
  have _ : IsEmpty (Y.restrict U).obj := ⟨fun z ↦ IsEmpty.false ((Y.ofRestrict U).hom.base z)⟩
  let g₁ : Y.restrict U ⟶ X := Y.ofRestrict U ≫ f
  let g₂ : Z ⟶ X := ObjectProperty.homMk (presentationLimitPreAdicSpacePairComap P P' hP hP' hsheaf
    (Pair.finiteAlgebra.algebraHom S PUnit.{u + 1}) ≫ eV.inv ≫ X.obj.ofRestrict V.isOpenEmbedding)
  have hr : Set.range g₁.hom.base = Set.range g₂.hom.base := by simp [Set.range_eq_empty]
  refine ⟨{
    V := V
    mem := hx
    Target := A
    targetPair := S
    targetPresentation := P
    targetLe := hP
    Source := PUnit.{u + 1}
    sourcePair := T
    sourcePresentation := P'
    sourceLe := hP'
    isSheafSource := hsheaf
    pairHom := Pair.finiteAlgebra.algebraHom S PUnit.{u + 1}
    isFiniteEtale := .of_subsingleton
    targetIso := eV
    sourceIso := IsOpenImmersion.isoOfRangeEq g₁.hom g₂.hom hr
    fac := ?_ }⟩
  rw [← AdicSpace.ofRestrict_hom, ← ObjectProperty.FullSubcategory.comp_hom]
  exact (IsOpenImmersion.isoOfRangeEq_hom_comp g₁.hom g₂.hom hr).symm

/-- **A morphism from an empty adic space into `X` is finite étale if and only if `X` is
analytic.** -/
theorem isFiniteEtale_iff_of_isEmpty (f : Y ⟶ X) [IsEmpty Y.obj] :
    IsFiniteEtale f ↔ X.IsAnalytic :=
  ⟨IsFiniteEtale.isAnalytic_target, IsFiniteEtale.of_isEmpty f⟩

/-! ### Finiteness hierarchy and topological properties -/

private theorem hasFiniteEtaleModel.locallyOfFiniteType {U' V' : PreAdicSpace.{u}} {g : U' ⟶ V'}
    (hg : hasFiniteEtaleModel g) : PreAdicSpace.LocallyOfFiniteType g := by
  obtain ⟨m⟩ := hg
  let _ : Algebra m.Target m.Source := m.pairHom.toRingHom.toAlgebra
  have _ : IsModuleTopology m.Target m.Source := m.isFiniteEtale.isModuleTopology
  let _ : UniformSpace m.Source := IsTopologicalAddGroup.rightUniformSpace m.Source
  have _ : IsUniformAddGroup m.Source := isUniformAddGroup_of_addCommGroup
  obtain ⟨_, _⟩ := isNaturallyComplete_iff.mp (isNaturallyComplete_of_isFiniteEtale m.isFiniteEtale)
  rw [m.fac, MorphismProperty.cancel_left_of_respectsIso @PreAdicSpace.LocallyOfFiniteType.{u},
    MorphismProperty.cancel_right_of_respectsIso @PreAdicSpace.LocallyOfFiniteType.{u},
    presentationLimitPreAdicSpacePairComap_def]
  exact locallyOfFiniteType_presentationLimitPreAdicSpaceComap m.targetPresentation
    m.sourcePresentation m.targetLe m.sourceLe m.isSheafSource m.pairHom
    m.isFiniteEtale.isFinite.isTopologicallyFiniteType

/-- **A finite étale morphism is locally of finite type.** -/
theorem IsFiniteEtale.locallyOfFiniteType {f : Y ⟶ X} (hf : IsFiniteEtale f) :
    PreAdicSpace.LocallyOfFiniteType f.hom := by
  choose V hx hV using hf
  exact PreAdicSpace.LocallyOfFiniteType.of_iSup_eq_top_restrictPreimage V
    (eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hx x⟩) fun x ↦ (hV x).locallyOfFiniteType

private theorem restrictPreimage_base_eq_of_iso {f : Y ⟶ X} {V : Opens X.obj}
    {U' V' : PreAdicSpace.{u}} {g : U' ⟶ V'} {eV : X.obj.restrict V.isOpenEmbedding ≅ V'}
    {eU : Y.obj.restrict ((Opens.map f.hom.base).obj V).isOpenEmbedding ≅ U'}
    (hfac : Y.obj.ofRestrict _ ≫ f.hom = eU.hom ≫ g ≫ eV.inv ≫ X.obj.ofRestrict _) :
    (V : Set X.obj).restrictPreimage f.hom.base =
      (TopCat.homeoOfIso (forgetToTop.mapIso eV)).symm ∘ g.base ∘
        TopCat.homeoOfIso (forgetToTop.mapIso eU) := by
  have hfac' := congrArg (fun k ↦ ConcreteCategory.hom (forgetToTop.map k)) hfac
  simp only [Functor.map_comp, TopCat.hom_comp] at hfac'
  exact funext fun y ↦ Subtype.ext (congrArg (fun k ↦ k y) hfac')

/-- **A finite étale morphism is quasi-compact.** -/
theorem IsFiniteEtale.quasiCompact {f : Y ⟶ X} (hf : IsFiniteEtale f) : QuasiCompact f := by
  let c (x : X.obj) : IsFiniteEtale.Chart f x := Classical.choice ((isFiniteEtale_iff f).mp hf x)
  have hspec (x : X.obj) :
      IsSpectralMap (((c x).V : Set X.obj).restrictPreimage f.hom.base) := by
    have hg : IsSpectralMap (presentationLimitPreAdicSpacePairComap (c x).targetPresentation
        (c x).sourcePresentation (c x).targetLe (c x).sourceLe (c x).isSheafSource
        (c x).pairHom).base := by
      rw [presentationLimitPreAdicSpacePairComap_def]
      exact (quasiCompact_iff_isSpectralMap _).mp
        (quasiCompact_presentationLimitPreAdicSpaceComap (c x).targetPresentation
          (c x).sourcePresentation (c x).targetLe (c x).sourceLe (c x).isSheafSource
          ((ObjectProperty.prop_iff_of_iso isAdic (c x).targetIso).mp
            (isAdic_restrict _ X.property))
          (c x).pairHom fun J hJ ↦ IsTateRing.isOpen_map_of_isOpen (c x).pairHom.toRingHom hJ)
    rw [restrictPreimage_base_eq_of_iso (c x).fac]
    exact (TopCat.homeoOfIso
        (forgetToTop.mapIso (c x).targetIso)).symm.isProperMap.isSpectralMap.comp
      (hg.comp (TopCat.homeoOfIso (forgetToTop.mapIso (c x).sourceIso)).isProperMap.isSpectralMap)
  have hB : Opens.IsBasis {W : Opens X.obj | W ∈ X.obj.affinoidOpens ∧ ∃ x : X.obj, W ≤ (c x).V} :=
    Opens.isBasis_iff_nbhd.mpr fun {U z} hzU ↦ by
      obtain ⟨W, hW, hzW, hWle⟩ := (Opens.isBasis_iff_nbhd.mp
        (isBasis_affinoidOpens X.property.isLocallyAffinoid)) (Opens.mem_inf.mpr ⟨hzU, (c z).mem⟩)
      exact ⟨W, ⟨hW, z, hWle.trans inf_le_right⟩, hzW, hWle.trans inf_le_left⟩
  refine (quasiCompact_iff_isSpectralMap f).mpr
    (isSpectralMap_of_isTopologicalBasis hB f.hom.base.hom.continuous ?_)
  rintro _ ⟨W, ⟨hW, x, hWV⟩, rfl⟩
  have hcomp := ((Set.mapsTo_preimage f.hom.base ((c x).V : Set X.obj)).isSpectralMap_restrict_iff
    f.hom.base.hom.continuous.continuousOn (c x).V.isOpen).mp (hspec x)
    (W : Set X.obj) hWV W.isOpen (isCompact_of_mem_affinoidOpens hW)
  rwa [Set.inter_eq_right.mpr (Set.preimage_mono hWV)] at hcomp

/-- **A finite étale morphism is of weakly finite type.** -/
theorem IsFiniteEtale.isWeaklyFiniteType {f : Y ⟶ X} (hf : IsFiniteEtale f) :
    IsWeaklyFiniteType f :=
  (isWeaklyFiniteType_iff f).mpr ⟨hf.locallyOfFiniteType.locallyOfWeaklyFiniteType, hf.quasiCompact⟩

/-- **Locally noetherian analytic structure ascends along finite étale morphisms.** -/
theorem IsFiniteEtale.isLocallyNoetherianAnalytic_source {f : Y ⟶ X} (hf : IsFiniteEtale f)
    (hX : X.IsLocallyNoetherianAnalytic) : Y.IsLocallyNoetherianAnalytic :=
  isLocallyNoetherianAnalytic_iff.mpr
    ⟨hX.isLocallyNoetherian.of_locallyOfFiniteType hf.locallyOfFiniteType, hf.isAnalytic_source⟩

/-- **The image of a finite étale morphism of adic spaces is clopen.** -/
theorem IsFiniteEtale.isClopen_range {f : Y ⟶ X} (hf : IsFiniteEtale f) :
    IsClopen (Set.range f.hom.base) := by
  let c (x : X.obj) : IsFiniteEtale.Chart f x := Classical.choice ((isFiniteEtale_iff f).mp hf x)
  have hcov : IsOpenCover (fun x ↦ (c x).V) :=
    eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, (c x).mem⟩
  have hlocal (x) : IsClopen (Set.range (((c x).V : Set X.obj).restrictPreimage f.hom.base)) := by
    let hU := TopCat.homeoOfIso (forgetToTop.mapIso (c x).sourceIso)
    let hV := TopCat.homeoOfIso (forgetToTop.mapIso (c x).targetIso)
    have hrange : Set.range (presentationLimitPreAdicSpacePairComap (c x).targetPresentation
        (c x).sourcePresentation (c x).targetLe (c x).sourceLe (c x).isSheafSource
        (c x).pairHom).base = Set.range (c x).pairHom.spaComap :=
      congrArg Set.range (funext (presentationLimitPreAdicSpacePairComap_base_apply
        (c x).targetPresentation (c x).sourcePresentation (c x).targetLe (c x).sourceLe
        (c x).isSheafSource (c x).pairHom))
    have hr : Set.range (((c x).V : Set X.obj).restrictPreimage f.hom.base) =
        hV ⁻¹' Set.range (c x).pairHom.spaComap := by
      rw [restrictPreimage_base_eq_of_iso (c x).fac]
      exact (Set.range_comp _ _).trans
        ((congrArg (hV.symm '' ·) (hU.surjective.range_comp _)).trans
          ((hV.toEquiv.image_symm_eq_preimage _).trans (congrArg (hV ⁻¹' ·) hrange)))
    exact hr ▸ (c x).isFiniteEtale.isClopen_range_spaComap.preimage hV.continuous
  simp_rw [Set.range_restrictPreimage] at hlocal
  exact ⟨hcov.isClosed_iff_coe_preimage.mpr fun x ↦ (hlocal x).1,
    hcov.isOpen_iff_coe_preimage.mpr fun x ↦ (hlocal x).2⟩

/-- **A finite étale morphism from a nonempty source into a preconnected target is surjective.** -/
theorem IsFiniteEtale.surjective_of_nonempty_of_preconnectedSpace {f : Y ⟶ X} (hf : IsFiniteEtale f)
    [Nonempty Y.obj] [PreconnectedSpace X.obj] : Function.Surjective f.hom.base :=
  Set.range_eq_univ.mp (hf.isClopen_range.eq_univ (Set.range_nonempty f.hom.base))

end TauCeti.AdicSpace
