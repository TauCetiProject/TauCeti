/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Affinoid
public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.Finite.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.LocallyTate
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.FiniteAlgebra
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Emptiness
import TauCeti.RingTheory.Huber.ModuleTopology.FiniteEtale
import TauCeti.RingTheory.Huber.ModuleTopology.NaturallyComplete

/-!
# Finite étale morphisms of adic spaces

A morphism `f : X ⟶ Y` of adic spaces is *finite étale* (Kedlaya–Liu, Definition 8.2.16) if every
point of `Y` has an open neighbourhood `V` such that `V ≅ Spa(A, A⁺)` for a complete Hausdorff Tate
Huber pair and `f⁻¹(V) ≅ Spa(B, B⁺)` for a complete Hausdorff Huber pair, under which `f`
restricted to `f⁻¹(V) → V` is the morphism induced by a finite étale morphism of Huber pairs
`φ : (A, A⁺) → (B, B⁺)` (`TauCeti.Huber.Pair.Hom.IsFiniteEtale`): `B` is a finite étale
`A`-algebra with its natural topology and `B⁺` is the integral closure of the image of `A⁺`.

This is the notion of finite étale morphism for analytic adic spaces that need not be locally
noetherian, where Huber's infinitesimal definition is not available. The condition is local on the
target, and no particular cover is fixed. The plus ring is part of the condition: for a finite étale
`A`-algebra `B` the pair `(B, B°)` is in general not the one attached to `B`. The Tate charts force
both spaces to be analytic. Sheafiness is not automatic: the definition asks that `Spa(B, B⁺)` be an
adic space, and that `Spa(A, A⁺)` be one follows from its being an open subspace of `Y`.

A finite étale morphism of Huber pairs over a complete Hausdorff Tate ring is finite
(`TauCeti.Huber.Pair.Hom.IsFiniteEtale.isFinite`), so finite étale morphisms of adic spaces are
finite in Huber's sense (`TauCeti.AdicSpace.IsFinite`), hence quasi-compact
(`TauCeti.AdicSpace.IsFinite.quasiCompact`) and of weakly finite type
(`TauCeti.AdicSpace.IsFinite.isWeaklyFiniteType`). The fibres of `Spa(B, B⁺) → Spa(A, A⁺)` have
at most as many points as the local rank of `B`
(`TauCeti.Huber.Pair.Hom.IsFiniteEtale.finite_fibre`), so finite étale morphisms have finite
fibres.

## Main definitions

* `TauCeti.AdicSpace.IsFiniteEtale`: finite étale morphisms of adic spaces.
* `TauCeti.AdicSpace.IsFiniteEtale.OfPairChart`: local `AdicSpace.ofPair`-based charts.

## Main results

* `TauCeti.AdicSpace.isFiniteEtale_presentationLimitPreAdicSpaceComap` and
  `TauCeti.AdicSpace.IsFiniteEtale.comapOfPair`: the morphism `Spa(B, B⁺) ⟶ Spa(A, A⁺)` induced
  by a finite étale morphism of complete Hausdorff Huber pairs over a Tate ring, both of whose
  spectra are adic spaces, is finite étale.
* `TauCeti.AdicSpace.IsFiniteEtale.exists_ofPair_chart`: local refinement to `ofPair` charts.
* `TauCeti.AdicSpace.IsFiniteEtale.isFinite`: finite étale morphisms are finite.
* `TauCeti.AdicSpace.IsFiniteEtale.finite_preimage_singleton`: finite étale morphisms have finite
  fibres.
* `TauCeti.AdicSpace.IsFiniteEtale.isAnalytic_source`,
  `TauCeti.AdicSpace.IsFiniteEtale.isAnalytic_target`,
  `TauCeti.AdicSpace.IsFiniteEtale.isLocallyNoetherianAnalytic_source`: analyticity and locally
  noetherian analyticity properties.
* `TauCeti.AdicSpace.IsFiniteEtale.of_iSup_eq_top`: being finite étale descends along open covers
  of the target.
* `TauCeti.AdicSpace.IsFiniteEtale.respectsIso`: being finite étale is invariant under isomorphisms
  of the source and of the target.
* `TauCeti.AdicSpace.isFiniteEtale_id`, `TauCeti.AdicSpace.isFiniteEtale_id_iff`,
  `TauCeti.AdicSpace.isFiniteEtale_of_isIso`, `TauCeti.AdicSpace.isFiniteEtale_iff_of_isIso`,
  `TauCeti.AdicSpace.IsFiniteEtale.of_isEmpty`, and
  `TauCeti.AdicSpace.isFiniteEtale_iff_of_isEmpty`: characterizations for identities,
  isomorphisms, and empty sources.
* `TauCeti.AdicSpace.IsFiniteEtale.isClopen_range` and
  `TauCeti.AdicSpace.IsFiniteEtale.surjective_of_nonempty_of_preconnectedSpace`: clopen image and
  surjectivity onto preconnected targets.

## Implementation notes

`IsFiniteEtale` is the target-local property `TauCeti.AdicSpace.targetLocally` attached to the
finite étale morphisms of Huber pairs `(A, A⁺) → (B, B⁺)` with `A` a Tate ring, the same shape as
`TauCeti.AdicSpace.IsFinite` (`Morphisms/Finite/Basic.lean`). Descent along open covers, the
affinoid case, isomorphism invariance and the identity are specializations of the general results
for `targetLocally`, and `IsFiniteEtale.isFinite` is its monotonicity in the property of Huber
pairs.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §8.2, Definition 8.2.16.
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §7, Definition 7.1(ii).
* P. Scholze and J. Weinstein, *Berkeley lectures on p-adic geometry*, Annals of Mathematics
  Studies 207 (2020), Lecture 7, Definition 7.5.1(1).
-/

public section

open CategoryTheory TopologicalSpace Topology

namespace TauCeti

open Huber

universe u

namespace AdicSpace

open PreAdicSpace ValuationSpectrum

/-- **Finite étale morphisms** (Kedlaya–Liu, Definition 8.2.16): a morphism `f : X ⟶ Y` of adic
spaces is *finite étale* when every point `y` of `Y` has an open neighbourhood `V` together with a
complete Hausdorff Tate Huber pair `(A, A⁺)`, a complete Hausdorff Huber pair `(B, B⁺)` such that
`Spa(B, B⁺)` has a sheaf as structure presheaf, a finite étale morphism `φ : (A, A⁺) → (B, B⁺)` of
Huber pairs, and isomorphisms identifying `Y` restricted to `V` with `Spa(A, A⁺)` and `X` restricted
to `f⁻¹(V)` with `Spa(B, B⁺)`, under which `f` becomes the morphism induced by `φ`. -/
def IsFiniteEtale {X Y : AdicSpace.{u}} (f : X ⟶ Y) : Prop :=
  targetLocally (@fun A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ φ ↦ IsTateRing A ∧ φ.IsFiniteEtale) f

variable {X Y : AdicSpace.{u}}

/-- Unfolding lemma for `TauCeti.AdicSpace.IsFiniteEtale`: being finite étale is the target-local
property attached to finite étale morphisms of Huber pairs over Tate rings. -/
theorem isFiniteEtale_iff (f : X ⟶ Y) : IsFiniteEtale f ↔
    targetLocally (@fun A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ φ ↦ IsTateRing A ∧ φ.IsFiniteEtale) f :=
  Iff.rfl

/-! ### Finite étale morphisms are finite -/

/-- **Finite étale morphisms are finite**: over a complete Hausdorff Tate ring, a finite étale
morphism of Huber pairs is finite (`TauCeti.Huber.Pair.Hom.IsFiniteEtale.isFinite`). -/
theorem IsFiniteEtale.isFinite {f : X ⟶ Y} (hf : IsFiniteEtale f) : IsFinite f :=
  (isFinite_iff f).mpr <|
    targetLocally_mono (fun _ ⟨_, hφ⟩ ↦ hφ.isFinite) ((isFiniteEtale_iff f).mp hf)

/-! ### Finite étale morphisms have analytic source and target -/

/-- **The target of a finite étale morphism is analytic**: the neighbourhoods supplied by the
definition are open Tate affinoid subspaces. -/
theorem IsFiniteEtale.isAnalytic_target {f : X ⟶ Y} (hf : IsFiniteEtale f) : Y.IsAnalytic :=
  isAnalytic_iff.mpr fun y ↦ by
    obtain ⟨V, hy, A, _, _, _, _, _, _, _, S, P, hP, _, _, _, _, _, _, _, _, _, _, _, _, ⟨hA, -⟩,
      _, eV, _⟩ := (targetLocally_iff f).mp ((isFiniteEtale_iff f).mp hf) y
    exact ⟨V, (mem_propOpens_iff _).mpr <| (isTateAffinoid_iff _).mpr ⟨A, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hA, S, P, hP,
      ⟨eV⟩⟩, hy⟩

/-- **The source of a finite étale morphism is analytic**: the preimages of the neighbourhoods
supplied by the definition are open Tate affinoid subspaces, a finite algebra over a Tate ring being
Tate. -/
theorem IsFiniteEtale.isAnalytic_source {f : X ⟶ Y} (hf : IsFiniteEtale f) : X.IsAnalytic :=
  isAnalytic_iff.mpr fun x ↦ by
    obtain ⟨V, hy, _, _, _, _, _, _, _, _, _, _, _, B, _, _, _, _, _, _, _, T, P', hP', φ, ⟨_, -⟩,
      _, _, eU, _⟩ := (targetLocally_iff f).mp ((isFiniteEtale_iff f).mp hf) (f.hom.base x)
    have : IsTateRing B := IsTateRing.of_continuous (φ := φ.toRingHom) φ.continuous_toRingHom
    exact ⟨(Opens.map f.hom.base).obj V, (mem_propOpens_iff _).mpr <| (isTateAffinoid_iff _).mpr
      ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
        inferInstance, T, P', hP', ⟨eU⟩⟩, hy⟩

/-! ### Descent along open covers of the target -/

/-- **Being finite étale descends along open covers of the target**: if `Y` is covered by opens
`V i` over which the restrictions `f⁻¹(V i) → V i` of `f` are finite étale, then `f` is finite
étale. A neighbourhood supplied by a restriction is an open of `V i`, hence an open of `Y`, with the
same preimage in `X`. -/
theorem IsFiniteEtale.of_iSup_eq_top {f : X ⟶ Y} {ι : Type*} (V : ι → Opens Y.obj)
    (hV : iSup V = ⊤)
    (hf : ∀ i, IsFiniteEtale
      (X := ⟨_, isAdic_restrict ((Opens.map f.hom.base).obj (V i)).isOpenEmbedding X.property⟩)
      (Y := ⟨_, isAdic_restrict (V i).isOpenEmbedding Y.property⟩)
      (ObjectProperty.homMk (f.hom.restrictPreimage (V i)))) :
    IsFiniteEtale f :=
  targetLocally_of_iSup_eq_top V hV hf

/-! ### Affinoid morphisms, identities and isomorphisms -/

/-- **Affinoid morphisms**: for a finite étale morphism of Huber pairs `φ : (A, A⁺) → (B, B⁺)`
between complete Hausdorff pairs, with `A` a Tate ring and both adic spectra adic spaces, the
morphism `Spa(B, B⁺) ⟶ Spa(A, A⁺)` induced by `φ` is finite étale, witnessed over the whole of
`Spa(A, A⁺)`. -/
theorem isFiniteEtale_presentationLimitPreAdicSpaceComap {A : Type u} [CommRing A]
    [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T2Space A]
    [IsTateRing A] {B : Type u} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
    [IsTopologicalRing B] [CompleteSpace B] [T2Space B] [IsHuberRing B] {S : Pair A} {T : Pair B}
    (P : PairOfDefinition A) (P' : PairOfDefinition B) (hP : P.ringOfDefinition ≤ S.plus)
    (hP' : P'.ringOfDefinition ≤ T.plus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (hA : PreAdicSpace.isAdic (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP)) (φ : Pair.Hom S T)
    (hφ : φ.IsFiniteEtale) :
    IsFiniteEtale (X := ⟨_, isAdic_presentationLimitPreAdicSpace P' T.plus
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP' hsheaf⟩) (Y := ⟨_, hA⟩)
      (ObjectProperty.homMk (presentationLimitPreAdicSpaceComap φ.toRingHom
        φ.continuous_toRingHom φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf)) :=
  targetLocally_presentationLimitPreAdicSpaceComap P P' hP hP' hsheaf hA φ ⟨inferInstance, hφ⟩

/-- **Being finite étale is invariant under isomorphisms** of the source and of the target. -/
instance IsFiniteEtale.respectsIso : MorphismProperty.RespectsIso @IsFiniteEtale.{u} :=
  targetLocally_respectsIso

/-- **The identity of an analytic adic space is finite étale**: every point has an open Tate
affinoid neighbourhood `Spa(A, A⁺)`, over which the identity is the morphism induced by the
identity of `(A, A⁺)`, a finite étale morphism of Huber pairs. Analyticity is necessary, since the
target of a finite étale morphism is analytic
(`TauCeti.AdicSpace.IsFiniteEtale.isAnalytic_target`). -/
theorem isFiniteEtale_id (hX : X.IsAnalytic) : IsFiniteEtale (𝟙 X) :=
  targetLocally_id fun y ↦ by
    obtain ⟨V, hV, hyV⟩ := isAnalytic_iff.mp hX y
    obtain ⟨A, _, _, _, _, _, _, _, S, P, hP, eV⟩ :=
      (isTateAffinoid_iff _).mp ((mem_propOpens_iff _).mp hV)
    exact ⟨V, hyV, A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, S, P, hP, ⟨inferInstance, Pair.Hom.isFiniteEtale_id S⟩, eV⟩

/-- **Isomorphisms onto analytic adic spaces are finite étale.** -/
theorem isFiniteEtale_of_isIso (f : X ⟶ Y) [IsIso f] (hY : Y.IsAnalytic) : IsFiniteEtale f := by
  simpa using MorphismProperty.RespectsIso.precomp @IsFiniteEtale.{u} f (𝟙 Y)
    (isFiniteEtale_id hY)

/-- **The identity of an adic space `X` is finite étale if and only if `X` is analytic.** -/
@[simp]
theorem isFiniteEtale_id_iff {X : AdicSpace.{u}} : IsFiniteEtale (𝟙 X) ↔ X.IsAnalytic :=
  ⟨IsFiniteEtale.isAnalytic_target, isFiniteEtale_id⟩

/-- **An isomorphism in `AdicSpace` is finite étale if and only if its target is analytic.** -/
theorem isFiniteEtale_iff_of_isIso (f : X ⟶ Y) [IsIso f] : IsFiniteEtale f ↔ Y.IsAnalytic :=
  ⟨IsFiniteEtale.isAnalytic_target, isFiniteEtale_of_isIso f⟩

/-! ### `ofPair` charts and affinoid `comapOfPair` -/

/-- A local `AdicSpace.ofPair`-based chart for `IsFiniteEtale f` around `y : Y.obj`. -/
structure IsFiniteEtale.OfPairChart {X Y : AdicSpace.{u}} (f : X ⟶ Y) (y : Y.obj) :
    Type (u + 1) where
  /-- Open neighbourhood of `y` in the target. -/
  V : Opens Y.obj
  /-- Membership of `y` in `V`. -/
  mem : y ∈ V
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
  /-- Identification of `Y|_V` with `(ofPair targetPair isSheafyTarget).obj`. -/
  targetIso : Y.obj.restrict V.isOpenEmbedding ≅ (ofPair targetPair isSheafyTarget).obj
  /-- Identification of `X|_{f⁻¹(V)}` with `(ofPair sourcePair isSheafySource).obj`. -/
  sourceIso : X.obj.restrict ((Opens.map f.hom.base).obj V).isOpenEmbedding ≅
    (ofPair sourcePair isSheafySource).obj
  /-- Compatibility of `f` over `V` with `comapOfPair isSheafyTarget isSheafySource pairHom`. -/
  fac : X.obj.ofRestrict _ ≫ f.hom =
    sourceIso.hom ≫ (comapOfPair isSheafyTarget isSheafySource pairHom).hom ≫
      targetIso.inv ≫ Y.obj.ofRestrict _

attribute [instance] IsFiniteEtale.OfPairChart.commRingTarget
  IsFiniteEtale.OfPairChart.uniformSpaceTarget IsFiniteEtale.OfPairChart.isUniformAddGroupTarget
  IsFiniteEtale.OfPairChart.isTopologicalRingTarget IsFiniteEtale.OfPairChart.completeSpaceTarget
  IsFiniteEtale.OfPairChart.t2SpaceTarget IsFiniteEtale.OfPairChart.isTateRingTarget
  IsFiniteEtale.OfPairChart.commRingSource IsFiniteEtale.OfPairChart.uniformSpaceSource
  IsFiniteEtale.OfPairChart.isUniformAddGroupSource
  IsFiniteEtale.OfPairChart.isTopologicalRingSource IsFiniteEtale.OfPairChart.completeSpaceSource
  IsFiniteEtale.OfPairChart.t2SpaceSource IsFiniteEtale.OfPairChart.isTateRingSource

private theorem isSheaf_of_restrict_iso {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsHuberRing A] {S : Pair A} {P : PairOfDefinition A}
    (hP : P.ringOfDefinition ≤ S.plus) {V : Opens Y.obj} (eV : Y.obj.restrict V.isOpenEmbedding ≅
      presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP) :
    Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus) :=
  (isSheafy_presentationLimitPreAdicSpace_iff P S.plus _ hP).mp
    ((ObjectProperty.prop_iff_of_iso PreAdicSpace.isSheafy eV).mp
      (isSheafy_restrict _ Y.property.isSheafy))

/-- Around every point `y : Y.obj`, a finite étale morphism `f : X ⟶ Y` admits an open
neighbourhood `V` of `y` over which `f` is modelled by `AdicSpace.comapOfPair` for a finite étale
morphism `φ : (A, A⁺) → (B, B⁺)` between complete Hausdorff Tate sheafy Huber pairs. -/
theorem IsFiniteEtale.exists_ofPair_chart {f : X ⟶ Y} (hf : IsFiniteEtale f) (y : Y.obj) :
    Nonempty (IsFiniteEtale.OfPairChart f y) := by
  obtain ⟨V, hy, A, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ,
    ⟨hA, hφ⟩, hsheaf, eV, eU, hfac⟩ :=
    (targetLocally_iff f).mp ((isFiniteEtale_iff f).mp hf) y
  have _ : IsTateRing A := hA
  have _ : IsTateRing B := IsTateRing.of_continuous (φ := φ.toRingHom) φ.continuous_toRingHom
  have hS := (isSheafyForEveryPresentation_iff_isRingOfIntegralElements_and_isSheaf P).mpr
    ⟨S.isRingOfIntegralElements, isSheaf_of_restrict_iso hP eV⟩
  have hT := (isSheafyForEveryPresentation_iff_isRingOfIntegralElements_and_isSheaf P').mpr
    ⟨T.isRingOfIntegralElements, hsheaf⟩
  let iS : (ofPair S hS).obj ≅ presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP :=
    (ObjectProperty.ι isAdic).mapIso (ofPairIsoOfPresentation S hS P hP)
  let iT : (ofPair T hT).obj ≅ presentationLimitPreAdicSpace P' T.plus
      T.isRingOfIntegralElements.isPowerBounded_of_mem hP' :=
    (ObjectProperty.ι isAdic).mapIso (ofPairIsoOfPresentation T hT P' hP')
  have hcomp_pre : iT.inv ≫ (comapOfPair hS hT φ).hom ≫ iS.hom =
      presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom φ.map_mem_plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf := by
    have hconj := congrArg InducedCategory.Hom.hom
      (comapOfPresentation_eq_ofPairIsoOfPresentation hS hT P hP P' hP' φ).symm
    rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
      comapOfPresentation_hom, presentationLimitPreAdicSpacePairComap_def] at hconj
    simpa only [iS, iT, Functor.mapIso_hom, Functor.mapIso_inv, ObjectProperty.ι_map] using hconj
  refine ⟨{
    V := V
    mem := hy
    Target := A
    targetPair := S
    isSheafyTarget := hS
    Source := B
    sourcePair := T
    isSheafySource := hT
    pairHom := φ
    isFiniteEtale := hφ
    targetIso := eV ≪≫ iS.symm
    sourceIso := eU ≪≫ iT.symm
    fac := ?_ }⟩
  rw [hfac, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv]
  simp only [Category.assoc, ← reassoc_of% hcomp_pre]

private noncomputable def IsFiniteEtale.OfPairChart.sourceHomeomorph
    {f : X ⟶ Y} {y : Y.obj} (c : IsFiniteEtale.OfPairChart f y) :
    ↥((Opens.map f.hom.base).obj c.V) ≃ₜ spa c.sourcePair.plus :=
  (TopCat.homeoOfIso (forgetToTop.mapIso c.sourceIso)).trans
    (ofPairHomeomorph c.sourcePair c.isSheafySource)

private noncomputable def IsFiniteEtale.OfPairChart.targetHomeomorph
    {f : X ⟶ Y} {y : Y.obj} (c : IsFiniteEtale.OfPairChart f y) :
    ↥c.V ≃ₜ spa c.targetPair.plus :=
  (TopCat.homeoOfIso (forgetToTop.mapIso c.targetIso)).trans
    (ofPairHomeomorph c.targetPair c.isSheafyTarget)

private theorem IsFiniteEtale.OfPairChart.targetHomeomorph_restrictPreimage
    {f : X ⟶ Y} {y : Y.obj} (c : IsFiniteEtale.OfPairChart f y)
    (x : (Opens.map f.hom.base).obj c.V) :
    c.targetHomeomorph ((c.V : Set Y.obj).restrictPreimage f.hom.base x) =
      c.pairHom.spaComap (c.sourceHomeomorph x) := by
  have hfac := congrArg (fun k ↦ ConcreteCategory.hom (forgetToTop.map k)) c.fac
  simp only [Functor.map_comp, TopCat.hom_comp] at hfac
  have hres : (c.V : Set Y.obj).restrictPreimage f.hom.base x =
      (TopCat.homeoOfIso (forgetToTop.mapIso c.targetIso)).symm
        ((comapOfPair c.isSheafyTarget c.isSheafySource c.pairHom).hom.base
          (TopCat.homeoOfIso (forgetToTop.mapIso c.sourceIso) x)) :=
    Subtype.ext (congrArg (fun k ↦ k x) hfac)
  have h1 := (congrArg (TopCat.homeoOfIso (forgetToTop.mapIso c.targetIso)) hres).trans
    ((TopCat.homeoOfIso (forgetToTop.mapIso c.targetIso)).apply_symm_apply _)
  exact (congrArg (ofPairHomeomorph c.targetPair c.isSheafyTarget) h1).trans
    (ofPairHomeomorph_comapOfPair_apply _ _ _ _)

/-- **`Spa(φ)` is finite étale for a finite étale morphism of sheafy Huber pairs** over a complete
Hausdorff Tate ring (`AdicSpace.comapOfPair`). -/
theorem IsFiniteEtale.comapOfPair {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
    [IsTopologicalRing A] [CompleteSpace A] [T0Space A] [IsTateRing A] {B : Type u} [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B] {S : Pair A} {T : Pair B}
    (hS : IsSheafyForEveryPresentation S.plus) (hT : IsSheafyForEveryPresentation T.plus)
    (φ : Pair.Hom S T) (hφ : φ.IsFiniteEtale) :
    IsFiniteEtale (AdicSpace.comapOfPair hS hT φ) := by
  let _ : Algebra A B := φ.toRingHom.toAlgebra
  have _ : Module.Finite A B := hφ.finite
  have _ : Algebra.Etale A B := hφ.etale
  have _ : IsModuleTopology A B := hφ.isModuleTopology
  have _ : Module.FinitePresentation A B := .of_finite_of_finitePresentation A B
  have _ : Module.Projective A B := Module.Flat.projective_of_finitePresentation
  let _ : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
  have _ : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
  obtain ⟨_, _⟩ := isNaturallyComplete_iff.mp (IsNaturallyComplete.of_projective (A := A) (M := B))
  have _ : T2Space A := inferInstance
  obtain ⟨P, hP, _⟩ := hS.exists_compatible_isSheaf
  obtain ⟨P', hP', _⟩ := hT.exists_compatible_isSheaf
  rw [comapOfPair_eq_ofPairIsoOfPresentation hS hT P hP P' hP' φ,
    comapOfPresentation_eq_homMk_presentationLimitPreAdicSpaceComap]
  have hbase := isFiniteEtale_presentationLimitPreAdicSpaceComap P P' hP hP' (hT.isSheaf P' hP')
    (isAdic_presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP (hS.isSheaf P hP)) φ hφ
  exact MorphismProperty.RespectsIso.precomp @IsFiniteEtale.{u} _ _
    (MorphismProperty.RespectsIso.postcomp @IsFiniteEtale.{u} _ _ hbase)

/-! ### Finite fibres, empty sources, locally noetherian ascent, and clopen image -/

/-- **The fibres of a finite étale morphism are finite.** Over a chart neighbourhood supplied by
`IsFiniteEtale.exists_ofPair_chart`, the restricted map agrees under chart homeomorphisms with
`Pair.Hom.spaComap`, whose fibres are finite
(`TauCeti.Huber.Pair.Hom.IsFiniteEtale.finite_fibre`). -/
theorem IsFiniteEtale.finite_preimage_singleton {f : X ⟶ Y} (hf : IsFiniteEtale f) (y : Y.obj) :
    (f.hom.base ⁻¹' {y}).Finite := by
  obtain ⟨c⟩ := hf.exists_ofPair_chart y
  have hfin : (c.pairHom.spaComap ⁻¹' {c.targetHomeomorph ⟨y, c.mem⟩}).Finite :=
    (c.isFiniteEtale.finite_fibre _).1
  refine (hfin.image fun w ↦ (c.sourceHomeomorph.symm w).val).subset fun x hx ↦ ?_
  have hxV : f.hom.base x ∈ c.V := (Set.mem_singleton_iff.mp hx).symm ▸ c.mem
  refine ⟨c.sourceHomeomorph ⟨x, hxV⟩, ?_,
    congrArg Subtype.val (c.sourceHomeomorph.symm_apply_apply _)⟩
  exact (c.targetHomeomorph_restrictPreimage ⟨x, hxV⟩).symm.trans
    (congrArg c.targetHomeomorph (Subtype.ext hx))

/-- **Every morphism from an empty adic space into an analytic adic space is finite étale.** -/
theorem IsFiniteEtale.of_isEmpty (f : X ⟶ Y) [IsEmpty X.obj] (hY : Y.IsAnalytic) :
    IsFiniteEtale f := by
  refine (isFiniteEtale_iff f).mpr ((targetLocally_iff f).mpr fun y ↦ ?_)
  obtain ⟨V, hV, hy⟩ := isAnalytic_iff.mp hY y
  obtain ⟨A, _, _, _, _, _, _, _, S, P, hP, ⟨eV⟩⟩ :=
    (isTateAffinoid_iff _).mp ((mem_propOpens_iff _).mp hV)
  let _ : IsTateRing PUnit.{u + 1} := IsTateRing.of_isModuleTopology (A := A) (B := PUnit.{u + 1})
  have _ : IsStronglyNoetherian PUnit.{u + 1} := IsNoetherianType.isStronglyNoetherian
  let T : Pair PUnit.{u + 1} := S.finiteAlgebra PUnit.{u + 1}
  obtain ⟨P', hP', hsheaf⟩ := (isSheafyForEveryPresentation_of_isStronglyNoetherian
    T.isRingOfIntegralElements).exists_compatible_isSheaf
  let Z : PreAdicSpace.{u} := presentationLimitPreAdicSpace P' T.plus
    T.isRingOfIntegralElements.isPowerBounded_of_mem hP'
  have _ : IsEmpty Z := Set.isEmpty_coe_sort.mpr
    ((spa_eq_empty_iff_subsingleton _ T.isRingOfIntegralElements).mpr inferInstance)
  let U := (Opens.map f.hom.base).obj V
  have _ : IsEmpty (X.obj.restrict U.isOpenEmbedding) :=
    ⟨fun z ↦ IsEmpty.false ((X.obj.ofRestrict U.isOpenEmbedding).base z)⟩
  let g₁ : X.obj.restrict U.isOpenEmbedding ⟶ Y.obj :=
    X.obj.ofRestrict U.isOpenEmbedding ≫ f.hom
  let g₂ : Z ⟶ Y.obj := presentationLimitPreAdicSpaceComap
    (Pair.finiteAlgebra.algebraHom S PUnit.{u + 1}).toRingHom
    (Pair.finiteAlgebra.algebraHom S PUnit.{u + 1}).continuous_toRingHom
    (Pair.finiteAlgebra.algebraHom S PUnit.{u + 1}).map_mem_plus
    S.isRingOfIntegralElements.isPowerBounded_of_mem
    T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf ≫
    eV.inv ≫ Y.obj.ofRestrict V.isOpenEmbedding
  have _ : IsOpenImmersion g₂ := by
    refine PreAdicSpace.isOpenImmersion_of_isEmpty _ hsheaf Y.property.isSheafy
  have hr : Set.range g₁.base = Set.range g₂.base := by simp [Set.range_eq_empty]
  refine ⟨V, hy, A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, S, P, hP, PUnit.{u + 1}, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, T, P', hP',
    Pair.finiteAlgebra.algebraHom S PUnit.{u + 1}, ⟨inferInstance, .of_subsingleton⟩, hsheaf, eV,
    IsOpenImmersion.isoOfRangeEq g₁ g₂ hr, ?_⟩
  exact (IsOpenImmersion.isoOfRangeEq_hom_comp g₁ g₂ hr).symm

/-- **A morphism from an empty adic space into `Y` is finite étale if and only if `Y` is
analytic.** -/
theorem isFiniteEtale_iff_of_isEmpty (f : X ⟶ Y) [IsEmpty X.obj] :
    IsFiniteEtale f ↔ Y.IsAnalytic :=
  ⟨IsFiniteEtale.isAnalytic_target, IsFiniteEtale.of_isEmpty f⟩

/-- **Locally noetherian analytic structure ascends along finite étale morphisms.** -/
theorem IsFiniteEtale.isLocallyNoetherianAnalytic_source {f : X ⟶ Y} (hf : IsFiniteEtale f)
    (hY : Y.IsLocallyNoetherianAnalytic) : X.IsLocallyNoetherianAnalytic :=
  isLocallyNoetherianAnalytic_iff.mpr
    ⟨hY.isLocallyNoetherian.of_locallyOfFiniteType hf.isFinite.locallyOfFiniteType,
      hf.isAnalytic_source⟩

/-- **The image of a finite étale morphism of adic spaces is clopen.** -/
theorem IsFiniteEtale.isClopen_range {f : X ⟶ Y} (hf : IsFiniteEtale f) :
    IsClopen (Set.range f.hom.base) := by
  have hlocal (y : Y.obj) : ∃ V : Opens Y.obj,
      y ∈ V ∧ IsClopen (Set.range ((V : Set Y.obj).restrictPreimage f.hom.base)) := by
    obtain ⟨c⟩ := hf.exists_ofPair_chart y
    have hr : Set.range ((c.V : Set Y.obj).restrictPreimage f.hom.base) =
        c.targetHomeomorph ⁻¹' Set.range c.pairHom.spaComap := by
      refine Set.ext fun z ↦ ⟨fun ⟨x, hx⟩ ↦ ?_, fun ⟨w, hw⟩ ↦ ?_⟩
      · exact ⟨c.sourceHomeomorph x,
          (c.targetHomeomorph_restrictPreimage x).symm.trans (congrArg c.targetHomeomorph hx)⟩
      · exact ⟨c.sourceHomeomorph.symm w, c.targetHomeomorph.injective
          ((c.targetHomeomorph_restrictPreimage _).trans
            ((congrArg c.pairHom.spaComap (c.sourceHomeomorph.apply_symm_apply w)).trans hw))⟩
    exact ⟨c.V, c.mem, hr ▸ c.isFiniteEtale.isClopen_range_spaComap.preimage
      c.targetHomeomorph.continuous⟩
  choose V hV hcl using hlocal
  have hcov : IsOpenCover V := eq_top_iff.mpr fun y _ ↦ Opens.mem_iSup.mpr ⟨y, hV y⟩
  simp_rw [Set.range_restrictPreimage] at hcl
  exact ⟨hcov.isClosed_iff_coe_preimage.mpr fun y ↦ (hcl y).1,
    hcov.isOpen_iff_coe_preimage.mpr fun y ↦ (hcl y).2⟩

/-- **A finite étale morphism from a nonempty source into a preconnected target is surjective.** -/
theorem IsFiniteEtale.surjective_of_nonempty_of_preconnectedSpace {f : X ⟶ Y}
    (hf : IsFiniteEtale f) [Nonempty X.obj] [PreconnectedSpace Y.obj] :
    Function.Surjective f.hom.base :=
  Set.range_eq_univ.mp (hf.isClopen_range.eq_univ (Set.range_nonempty f.hom.base))

end AdicSpace

end TauCeti
