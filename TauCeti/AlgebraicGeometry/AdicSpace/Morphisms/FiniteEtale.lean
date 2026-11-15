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

* `TauCeti.AdicSpace.IsFiniteEtale`, `IsFiniteEtale.exists_complete_tate_chart`,
  `IsFiniteEtale.exists_ofPair_chart`, `IsFiniteEtale.isAnalytic_target`,
  `IsFiniteEtale.isAnalytic_source`.
* `IsFiniteEtale.respectsIso`, `IsFiniteEtale.comapOfPresentation`, `IsFiniteEtale.spa`,
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

/-- **Finite étale morphisms of analytic adic spaces** (Kedlaya–Liu I, Definition 8.2.16; Scholze,
Definition 7.1; modelled formally on `TauCeti.PreAdicSpace.IsClosedImmersion`): a morphism
`f : Y ⟶ X` in `AdicSpace` is *finite étale* when every point `x` of `X` has an open neighbourhood
`V`, isomorphic to `Spa(A, A⁺)` for a complete Hausdorff Tate Huber pair `(A, A⁺)`, whose full
preimage `f⁻¹(V)` is isomorphic to `Spa(B, B⁺)` for a sheafy Huber pair `(B, B⁺)` such that over `V`
the morphism `f` is induced by a finite étale morphism of Huber pairs `φ : (A, A⁺) → (B, B⁺)`. -/
def IsFiniteEtale : MorphismProperty AdicSpace.{u} := fun Y X f ↦
  ∀ x : X.obj, ∃ (V : Opens X.obj) (_ : x ∈ V)
    (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
    (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsTateRing A)
    (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
    (B : Type u) (_ : CommRing B) (_ : TopologicalSpace B) (_ : IsTopologicalRing B)
    (_ : IsHuberRing B) (T : Pair B) (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus)) (φ : Pair.Hom S T) (_ : φ.IsFiniteEtale)
    (eV : X.obj.restrict V.isOpenEmbedding ≅
      presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP)
    (eU : Y.obj.restrict ((Opens.map f.hom.base).obj V).isOpenEmbedding ≅
      presentationLimitPreAdicSpace P' T.plus T.isRingOfIntegralElements.isPowerBounded_of_mem hP'),
    Y.obj.ofRestrict _ ≫ f.hom =
      eU.hom ≫ presentationLimitPreAdicSpacePairComap P P' hP hP' hsheaf φ ≫
        eV.inv ≫ X.obj.ofRestrict _

/-- Unfolding lemma for `TauCeti.AdicSpace.IsFiniteEtale`. -/
theorem isFiniteEtale_iff (f : Y ⟶ X) :
    IsFiniteEtale f ↔
      ∀ x : X.obj, ∃ (V : Opens X.obj) (_ : x ∈ V)
        (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
        (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsTateRing A)
        (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
        (B : Type u) (_ : CommRing B) (_ : TopologicalSpace B) (_ : IsTopologicalRing B)
        (_ : IsHuberRing B) (T : Pair B) (P' : PairOfDefinition B)
        (hP' : P'.ringOfDefinition ≤ T.plus)
        (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
          (presentationLimitPresheaf P' T.plus)) (φ : Pair.Hom S T) (_ : φ.IsFiniteEtale)
        (eV : X.obj.restrict V.isOpenEmbedding ≅ presentationLimitPreAdicSpace P S.plus
          S.isRingOfIntegralElements.isPowerBounded_of_mem hP)
        (eU : Y.obj.restrict ((Opens.map f.hom.base).obj V).isOpenEmbedding ≅
          presentationLimitPreAdicSpace P' T.plus
            T.isRingOfIntegralElements.isPowerBounded_of_mem hP'),
        Y.obj.ofRestrict _ ≫ f.hom =
          eU.hom ≫ presentationLimitPreAdicSpacePairComap P P' hP hP' hsheaf φ ≫
            eV.inv ≫ X.obj.ofRestrict _ :=
  Iff.rfl

/-- Around every point `x : X.obj`, a finite étale morphism `f : Y ⟶ X` admits an open
neighbourhood `V` of `x` over which `f` is modelled by a finite étale morphism `φ : (A, S) → (B, T)`
where both `A` and `B` are complete Hausdorff Tate rings. -/
theorem IsFiniteEtale.exists_complete_tate_chart {f : Y ⟶ X} (hf : IsFiniteEtale f) (x : X.obj) :
    ∃ (V : Opens X.obj) (_ : x ∈ V)
      (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
      (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsTateRing A)
      (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
      (B : Type u) (_ : CommRing B) (_ : UniformSpace B) (_ : IsUniformAddGroup B)
      (_ : IsTopologicalRing B) (_ : CompleteSpace B) (_ : T2Space B) (_ : IsTateRing B)
      (T : Pair B) (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
      (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
        (presentationLimitPresheaf P' T.plus)) (φ : Pair.Hom S T) (_ : φ.IsFiniteEtale)
      (eV : X.obj.restrict V.isOpenEmbedding ≅
        presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP)
      (eU : Y.obj.restrict ((Opens.map f.hom.base).obj V).isOpenEmbedding ≅
        presentationLimitPreAdicSpace P' T.plus
          T.isRingOfIntegralElements.isPowerBounded_of_mem hP'),
      Y.obj.ofRestrict _ ≫ f.hom =
        eU.hom ≫ presentationLimitPreAdicSpacePairComap P P' hP hP' hsheaf φ ≫
          eV.inv ≫ X.obj.ofRestrict _ := by
  obtain ⟨V, hx, A, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, T, P', hP', hsheaf, φ, hφ,
    eV, eU, hfac⟩ := hf x
  let _ : Algebra A B := φ.toRingHom.toAlgebra
  have _ : Module.Finite A B := hφ.finite
  have _ : Algebra.Etale A B := hφ.etale
  have _ : IsModuleTopology A B := hφ.isModuleTopology
  have _ : Module.FinitePresentation A B := .of_finite_of_finitePresentation A B
  have _ : Module.Projective A B := Module.Flat.projective_of_finitePresentation
  let _ : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
  have _ : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
  obtain ⟨_, _⟩ := isNaturallyComplete_iff.mp (IsNaturallyComplete.of_projective (A := A) (M := B))
  have _ : IsTateRing B := IsTateRing.of_isModuleTopology (A := A) (B := B)
  exact ⟨V, hx, A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, S, P, hP, B, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, T, P', hP', hsheaf, φ, hφ,
    eV, eU, hfac⟩

/-- Around every point `x : X.obj`, a finite étale morphism `f : Y ⟶ X` admits an open
neighbourhood `V` of `x` over which `f` is modelled by `AdicSpace.comapOfPair` for a finite étale
morphism `φ : (A, S) → (B, T)` between complete Hausdorff Tate sheafy Huber pairs. -/
theorem IsFiniteEtale.exists_ofPair_chart {f : Y ⟶ X} (hf : IsFiniteEtale f) (x : X.obj) :
    ∃ (V : Opens X.obj) (_ : x ∈ V)
      (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
      (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsTateRing A)
      (S : Pair A) (hS : IsSheafyForEveryPresentation S.plus)
      (B : Type u) (_ : CommRing B) (_ : UniformSpace B) (_ : IsUniformAddGroup B)
      (_ : IsTopologicalRing B) (_ : CompleteSpace B) (_ : T2Space B) (_ : IsTateRing B)
      (T : Pair B) (hT : IsSheafyForEveryPresentation T.plus)
      (φ : Pair.Hom S T) (_ : φ.IsFiniteEtale)
      (eV : X.obj.restrict V.isOpenEmbedding ≅ (ofPair S hS).obj)
      (eU : Y.obj.restrict ((Opens.map f.hom.base).obj V).isOpenEmbedding ≅ (ofPair T hT).obj),
      Y.obj.ofRestrict _ ≫ f.hom =
        eU.hom ≫ (comapOfPair hS hT φ).hom ≫ eV.inv ≫ X.obj.ofRestrict _ := by
  obtain ⟨V, hx, A, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP',
    hsheafT, φ, hφ, eV, eU, hfac⟩ := hf.exists_complete_tate_chart x
  have hS : IsSheafyForEveryPresentation S.plus :=
    (isSheafyForEveryPresentation_iff_isRingOfIntegralElements_and_isSheaf P).mpr
      ⟨S.isRingOfIntegralElements, (isSheafy_presentationLimitPreAdicSpace_iff P S.plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem hP).mp
          ((ObjectProperty.prop_iff_of_iso PreAdicSpace.isSheafy eV).mp
            (isSheafy_restrict _ (isAdic_iff.mp X.property).1))⟩
  have hT : IsSheafyForEveryPresentation T.plus :=
    (isSheafyForEveryPresentation_iff_isRingOfIntegralElements_and_isSheaf P').mpr
      ⟨T.isRingOfIntegralElements, hsheafT⟩
  let iS := (ObjectProperty.ι isAdic).mapIso (ofPairIsoOfPresentation S hS P hP)
  let iT := (ObjectProperty.ι isAdic).mapIso (ofPairIsoOfPresentation T hT P' hP')
  have hcomp_pre : iT.inv ≫ (comapOfPair hS hT φ).hom ≫ iS.hom =
      presentationLimitPreAdicSpacePairComap P P' hP hP' hsheafT φ := by
    simpa [iS, iT, comapOfPresentation_hom] using congrArg InducedCategory.Hom.hom
      (by rw [← comapOfPresentation_ofPairIsoOfPresentation_inv_assoc, Iso.inv_hom_id,
            Category.comp_id] :
        (ofPairIsoOfPresentation T hT P' hP').inv ≫ comapOfPair hS hT φ ≫
          (ofPairIsoOfPresentation S hS P hP).hom =
          AdicSpace.comapOfPresentation S P hP (hS.isSheaf P hP) T P' hP' (hT.isSheaf P' hP') φ)
  refine ⟨V, hx, A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, S, hS, B, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, T, hT, φ, hφ,
    eV ≪≫ iS.symm, eU ≪≫ iT.symm, ?_⟩
  rw [hfac, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv]
  simp only [Category.assoc, ← reassoc_of% hcomp_pre]

/-- **The target of a finite étale morphism is analytic.** -/
theorem IsFiniteEtale.isAnalytic_target {f : Y ⟶ X} (hf : IsFiniteEtale f) : X.IsAnalytic := by
  refine isAnalytic_iff.mpr fun x ↦ ?_
  obtain ⟨V, hx, A, _, _, _, _, _, _, _, S, P, hP, _, _, _, _, _, _, _, _, _, _, _, eV, _, _⟩ :=
    hf x
  exact ⟨V, (mem_propOpens_iff _).mpr ((isTateAffinoid_iff _).mpr
    ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, S, P, hP, ⟨eV⟩⟩), hx⟩

/-- **The source of a finite étale morphism is analytic.** -/
theorem IsFiniteEtale.isAnalytic_source {f : Y ⟶ X} (hf : IsFiniteEtale f) : Y.IsAnalytic := by
  refine isAnalytic_iff.mpr fun y ↦ ?_
  obtain ⟨V, hx, _, _, _, _, _, _, _, _, _, _, _, B, _, _, _, _, _, _, _, T, P', hP', _, _, _,
    _, eU, _⟩ := hf.exists_complete_tate_chart (f.hom.base y)
  exact ⟨(Opens.map f.hom.base).obj V, (mem_propOpens_iff _).mpr ((isTateAffinoid_iff _).mpr
    ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, T, P', hP', ⟨eU⟩⟩), hx⟩

/-! ### Invariance under isomorphism and affinoid constructors -/

private def hasFiniteEtaleModel : MorphismProperty PreAdicSpace.{u} := fun U' V' g ↦
  ∃ (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
    (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsTateRing A)
    (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
    (B : Type u) (_ : CommRing B) (_ : TopologicalSpace B) (_ : IsTopologicalRing B)
    (_ : IsHuberRing B) (T : Pair B) (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus)) (φ : Pair.Hom S T) (_ : φ.IsFiniteEtale)
    (eV : V' ≅ presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP)
    (eU : U' ≅ presentationLimitPreAdicSpace P' T.plus
      T.isRingOfIntegralElements.isPowerBounded_of_mem hP'),
    g = eU.hom ≫ presentationLimitPreAdicSpacePairComap P P' hP hP' hsheaf φ ≫ eV.inv

private instance : MorphismProperty.RespectsIso (@hasFiniteEtaleModel.{u}) :=
  MorphismProperty.RespectsIso.mk _
    (fun e _ ⟨A, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, T, P', hP', hs, φ, hφ, eV, eU, hg⟩ ↦
      ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
        inferInstance, S, P, hP, B, inferInstance, inferInstance, inferInstance, inferInstance, T,
        P', hP', hs, φ, hφ, eV, e ≪≫ eU, by simp [hg]⟩)
    (fun e _ ⟨A, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, T, P', hP', hs, φ, hφ, eV, eU, hg⟩ ↦
      ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
        inferInstance, S, P, hP, B, inferInstance, inferInstance, inferInstance, inferInstance, T,
        P', hP', hs, φ, hφ, e.symm ≪≫ eV, eU, by simp [hg]⟩)

private theorem isFiniteEtale_iff_hasFiniteEtaleModel (f : Y ⟶ X) :
    IsFiniteEtale f ↔
      ∀ x : X.obj, ∃ V : Opens X.obj, x ∈ V ∧ hasFiniteEtaleModel (f.hom.restrictPreimage V) := by
  simp only [isFiniteEtale_iff, hasFiniteEtaleModel, ← Hom.restrictPreimage_ofRestrict,
    ← Category.assoc, cancel_mono, exists_prop]

private theorem range_ofRestrict {W : PreAdicSpace.{u}} (U : Opens W) :
    Set.range (W.ofRestrict U.isOpenEmbedding).base = U :=
  Set.ext fun _ ↦ ⟨by rintro ⟨z, rfl⟩; exact z.2, fun h ↦ ⟨⟨_, h⟩, rfl⟩⟩

private theorem IsFiniteEtale.iso_hom_comp (e : Z ≅ Y) {f : Y ⟶ X}
    (hf : IsFiniteEtale f) : IsFiniteEtale (e.hom ≫ f) := by
  rw [isFiniteEtale_iff_hasFiniteEtaleModel] at hf ⊢
  intro x
  obtain ⟨V, hx, hV⟩ := hf x
  let e' : Z.obj ≅ Y.obj := (ObjectProperty.ι isAdic).mapIso e
  have : IsIso e'.inv := e'.isIso_inv
  refine ⟨V, hx, (Hom.prop_restrictPreimage_iff_of_isOpenImmersion ((e.hom ≫ f).hom) V
    (@hasFiniteEtaleModel.{u}) (f.hom.restrictPreimage V)
    (Y.obj.ofRestrict ((Opens.map f.hom.base).obj V).isOpenEmbedding ≫ e'.inv)
    (X.obj.ofRestrict V.isOpenEmbedding) (range_ofRestrict V) ?_ ?_).mpr hV⟩
  · rw [comp_base, TopCat.coe_comp, Set.range_comp, range_ofRestrict]
    exact (TopCat.homeoOfIso (forgetToTop.mapIso e')).toEquiv.image_symm_eq_preimage _
  · simp [e', Hom.restrictPreimage_ofRestrict]

private theorem IsFiniteEtale.comp_iso_hom (e : X ≅ Z) {f : Y ⟶ X}
    (hf : IsFiniteEtale f) : IsFiniteEtale (f ≫ e.hom) := by
  rw [isFiniteEtale_iff_hasFiniteEtaleModel] at hf ⊢
  intro z
  let e' : X.obj ≅ Z.obj := (ObjectProperty.ι isAdic).mapIso e
  have : IsIso e'.hom := e'.isIso_hom
  obtain ⟨V, hx, hV⟩ := hf (e'.inv.base z)
  let W : Opens Z.obj := (Opens.map e'.inv.base).obj V
  refine ⟨W, hx, (Hom.prop_restrictPreimage_iff_of_isOpenImmersion ((f ≫ e.hom).hom) W
    (@hasFiniteEtaleModel.{u}) (f.hom.restrictPreimage V)
    (Y.obj.ofRestrict ((Opens.map f.hom.base).obj V).isOpenEmbedding)
    (X.obj.ofRestrict V.isOpenEmbedding ≫ e'.hom) ?_ ?_ ?_).mpr hV⟩
  · rw [comp_base, TopCat.coe_comp, Set.range_comp, range_ofRestrict]
    exact (TopCat.homeoOfIso (forgetToTop.mapIso e')).toEquiv.image_eq_preimage_symm _
  · have key := Opens.map_hom_obj_map_inv_obj (forgetToTop.mapIso e') V
    simp only [Functor.mapIso_hom, Functor.mapIso_inv, forgetToTop_map] at key
    have hhom : (f ≫ e.hom).hom = f.hom ≫ e'.hom := rfl
    rw [range_ofRestrict, hhom, comp_base, TopCat.coe_comp, Set.preimage_comp]
    exact congrArg (f.hom.base ⁻¹' ·) (congrArg SetLike.coe key.symm)
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
      (presentationLimitPresheaf P S.plus))
    (T : Pair B) (P' : PairOfDefinition B) (hT : P'.ringOfDefinition ≤ T.plus)
    (hsheafT : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (φ : Pair.Hom S T) (hφ : φ.IsFiniteEtale) :
    IsFiniteEtale (AdicSpace.comapOfPresentation S P hS hsheafS T P' hT hsheafT φ) := by
  refine fun _ ↦ ⟨⊤, trivial, A, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, S, P, hS, B, inferInstance, inferInstance,
    inferInstance, inferInstance, T, P', hT, hsheafT, φ, hφ, restrictTopIso _,
    restrictIsoOfRangeEq _ _ (Opens.isOpenEmbedding ⊤) (by rw [Opens.map_top]) ≪≫ restrictTopIso _,
    ?_⟩
  rw [← restrictTopIso_hom, Iso.inv_hom_id, Category.comp_id, Iso.trans_hom, restrictTopIso_hom,
    Category.assoc, ← comapOfPresentation_hom S P hS hsheafS T P' hT hsheafT φ,
    restrictIsoOfRangeEq_hom_ofRestrict_assoc]

/-- **`Spa(φ)` is finite étale for a finite étale morphism of sheafy Huber pairs** over a complete
Hausdorff Tate ring (`AdicSpace.comapOfPair`). -/
theorem IsFiniteEtale.spa {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
    [IsTopologicalRing A] [CompleteSpace A] [T0Space A] [IsTateRing A]
    {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
    {S : Pair A} {T : Pair B}
    (hS : IsSheafyForEveryPresentation S.plus) (hT : IsSheafyForEveryPresentation T.plus)
    (φ : Pair.Hom S T) (hφ : φ.IsFiniteEtale) : IsFiniteEtale (comapOfPair hS hT φ) := by
  obtain ⟨P, hP, _⟩ := hS.exists_compatible_isSheaf
  obtain ⟨P', hP', _⟩ := hT.exists_compatible_isSheaf
  have hfac : comapOfPair hS hT φ = (ofPairIsoOfPresentation T hT P' hP').hom ≫
      AdicSpace.comapOfPresentation S P hP (hS.isSheaf P hP) T P' hP' (hT.isSheaf P' hP') φ ≫
      (ofPairIsoOfPresentation S hS P hP).inv := by
    rw [comapOfPresentation_ofPairIsoOfPresentation_inv, Iso.hom_inv_id_assoc]
  rw [hfac]
  exact ((IsFiniteEtale.comapOfPresentation S P hP (hS.isSheaf P hP) T P' hP' (hT.isSheaf P' hP')
    φ hφ).comp_iso_hom (ofPairIsoOfPresentation S hS P hP).symm).iso_hom_comp
    (ofPairIsoOfPresentation T hT P' hP')

/-! ### Target-cover descent, identities, isomorphisms, and empty covers -/

/-- **Finite étale morphisms descend along any open cover of the target**
(cf. `TauCeti.PreAdicSpace.IsClosedImmersion.of_iSup_eq_top`). -/
theorem IsFiniteEtale.of_iSup_eq_top {f : Y ⟶ X} {ι : Type*} (V : ι → Opens X.obj)
    (hV : iSup V = ⊤)
    (hf : ∀ i, IsFiniteEtale
      (ObjectProperty.homMk (f.hom.restrictPreimage (V i)) :
        (⟨Y.obj.restrict ((Opens.map f.hom.base).obj (V i)).isOpenEmbedding,
          isAdic_restrict _ Y.property⟩ : AdicSpace.{u}) ⟶
        ⟨X.obj.restrict (V i).isOpenEmbedding, isAdic_restrict _ X.property⟩)) :
    IsFiniteEtale f := by
  rw [isFiniteEtale_iff_hasFiniteEtaleModel]
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hV.symm ▸ Set.mem_univ x : x ∈ iSup V)
  obtain ⟨W, hx, hW⟩ := (isFiniteEtale_iff_hasFiniteEtaleModel _).mp (hf i) ⟨x, hi⟩
  exact ⟨(V i).isOpenEmbedding.isOpenMap.functor.obj W, ⟨⟨x, hi⟩, hx, rfl⟩,
    (Hom.prop_restrictPreimage_restrictPreimage_iff f.hom (@hasFiniteEtaleModel.{u}) (V i) W).mp
      hW⟩

/-- **The identity of an analytic adic space is finite étale.** -/
theorem IsFiniteEtale.id {X : AdicSpace.{u}} (hX : X.IsAnalytic) : IsFiniteEtale (𝟙 X) := by
  intro x
  obtain ⟨V, hV, hx⟩ := isAnalytic_iff.mp hX x
  obtain ⟨A, _, _, _, _, _, _, _, S, P, hP, ⟨eV⟩⟩ :=
    (isTateAffinoid_iff _).mp ((mem_propOpens_iff _).mp hV)
  refine ⟨V, hx, A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, S, P, hP, A, inferInstance, inferInstance, inferInstance,
    inferInstance, S, P, hP,
    (isSheafy_presentationLimitPreAdicSpace_iff P S.plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem hP).mp
      ((ObjectProperty.prop_iff_of_iso PreAdicSpace.isSheafy eV).mp
        (isSheafy_restrict _ (isAdic_iff.mp X.property).1)),
    Pair.Hom.id S, Pair.Hom.isFiniteEtale_id S, eV,
    restrictIsoOfRangeEq X.obj _ V.isOpenEmbedding
      (by rw [Opens.set_range_inclusion', Opens.set_range_inclusion']; rfl) ≪≫ eV, ?_⟩
  rw [presentationLimitPreAdicSpacePairComap_id, Category.id_comp, Iso.trans_hom, Category.assoc,
    Iso.hom_inv_id_assoc, restrictIsoOfRangeEq_hom_ofRestrict]; exact Category.comp_id _

/-- **The identity of an adic space `X` is finite étale if and only if `X` is analytic.** -/
@[simp]
theorem isFiniteEtale_id_iff {X : AdicSpace.{u}} : IsFiniteEtale (𝟙 X) ↔ X.IsAnalytic :=
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
  intro x
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
  let YV : AdicSpace.{u} := ⟨Y.obj.restrict U.isOpenEmbedding, isAdic_restrict _ Y.property⟩
  have _ : IsEmpty YV.obj := ⟨fun z ↦ IsEmpty.false ((Y.obj.ofRestrict U.isOpenEmbedding).base z)⟩
  let g₁ : YV ⟶ X := ObjectProperty.homMk (Y.obj.ofRestrict U.isOpenEmbedding ≫ f.hom)
  let g₂ : Z ⟶ X := ObjectProperty.homMk (presentationLimitPreAdicSpacePairComap P P' hP hP' hsheaf
    (Pair.finiteAlgebra.algebraHom S PUnit.{u + 1}) ≫ eV.inv ≫ X.obj.ofRestrict V.isOpenEmbedding)
  have hr : Set.range g₁.hom.base = Set.range g₂.hom.base := by
    rw [Set.range_eq_empty, Set.range_eq_empty]
  exact ⟨V, hx, A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, S, P, hP, PUnit.{u + 1}, inferInstance, inferInstance,
    inferInstance, inferInstance, T, P', hP', hsheaf, _, .of_subsingleton, eV,
    IsOpenImmersion.isoOfRangeEq g₁.hom g₂.hom hr,
    (IsOpenImmersion.isoOfRangeEq_hom_comp g₁.hom g₂.hom hr).symm⟩

/-- **A morphism from an empty adic space into `X` is finite étale if and only if `X` is
analytic.** -/
theorem isFiniteEtale_iff_of_isEmpty (f : Y ⟶ X) [IsEmpty Y.obj] :
    IsFiniteEtale f ↔ X.IsAnalytic :=
  ⟨IsFiniteEtale.isAnalytic_target, IsFiniteEtale.of_isEmpty f⟩

/-! ### Finiteness hierarchy and topological properties -/

/-- **A finite étale morphism is locally of finite type.** -/
theorem IsFiniteEtale.locallyOfFiniteType {f : Y ⟶ X} (hf : IsFiniteEtale f) :
    PreAdicSpace.LocallyOfFiniteType f.hom := by
  choose V hx A iCA uA gA tA cA h2A tateA S P hP B iCB uB gB tB cB h2B tateB T P' hP'
    hsheaf φ hφ eV eU hfac using hf.exists_complete_tate_chart
  refine PreAdicSpace.LocallyOfFiniteType.of_iSup_eq_top_restrictPreimage V
    (eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hx x⟩) fun x ↦ ?_
  have hres : f.hom.restrictPreimage (V x) =
      (eU x).hom ≫ presentationLimitPreAdicSpacePairComap (P x) (P' x) (hP x) (hP' x)
        (hsheaf x) (φ x) ≫ (eV x).inv := by
    rw [← cancel_mono (X.obj.ofRestrict (V x).isOpenEmbedding), Hom.restrictPreimage_ofRestrict,
      hfac x, Category.assoc, Category.assoc]
  rw [hres, MorphismProperty.cancel_left_of_respectsIso @PreAdicSpace.LocallyOfFiniteType.{u}]
  refine (MorphismProperty.cancel_right_of_respectsIso @PreAdicSpace.LocallyOfFiniteType.{u}
    _ _).mpr ?_
  rw [presentationLimitPreAdicSpacePairComap_def]
  exact locallyOfFiniteType_presentationLimitPreAdicSpaceComap (P x) (P' x) (hP x) (hP' x)
    (hsheaf x) (φ x) (hφ x).isFinite.isTopologicallyFiniteType

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
  choose V hx A iCA uA _ tA _ _ tateA S P hP B iCB tB rB hB T P' hP'
    hsheaf φ _ eV eU hfac using hf
  have hspec (x : X.obj) :
      IsSpectralMap ((V x : Set X.obj).restrictPreimage f.hom.base) := by
    have hg : IsSpectralMap (presentationLimitPreAdicSpacePairComap (P x) (P' x) (hP x) (hP' x)
        (hsheaf x) (φ x)).base := by
      rw [presentationLimitPreAdicSpacePairComap_def]
      exact (quasiCompact_iff_isSpectralMap _).mp
        (quasiCompact_presentationLimitPreAdicSpaceComap (P x) (P' x) (hP x) (hP' x) (hsheaf x)
          ((ObjectProperty.prop_iff_of_iso isAdic (eV x)).mp (isAdic_restrict _ X.property))
          (φ x) fun J hJ ↦ IsTateRing.isOpen_map_of_isOpen (φ x).toRingHom hJ)
    rw [restrictPreimage_base_eq_of_iso (hfac x)]
    exact (TopCat.homeoOfIso (forgetToTop.mapIso (eV x))).symm.isProperMap.isSpectralMap.comp
      (hg.comp (TopCat.homeoOfIso (forgetToTop.mapIso (eU x))).isProperMap.isSpectralMap)
  have hB : Opens.IsBasis {W : Opens X.obj | W ∈ X.obj.affinoidOpens ∧ ∃ x : X.obj, W ≤ V x} :=
    Opens.isBasis_iff_nbhd.mpr fun {U z} hzU ↦ by
      have hzUV : z ∈ U ⊓ V z := ⟨hzU, hx z⟩
      obtain ⟨W, hW, hzW, hWle⟩ := (Opens.isBasis_iff_nbhd.mp
        (isBasis_affinoidOpens X.property.isLocallyAffinoid)) hzUV
      exact ⟨W, ⟨hW, z, hWle.trans inf_le_right⟩, hzW, hWle.trans inf_le_left⟩
  refine (quasiCompact_iff_isSpectralMap f).mpr
    (isSpectralMap_of_isTopologicalBasis hB f.hom.base.hom.continuous ?_)
  rintro _ ⟨W, ⟨hW, x, hWV⟩, rfl⟩
  have hcomp := ((Set.mapsTo_preimage f.hom.base (V x : Set X.obj)).isSpectralMap_restrict_iff
    f.hom.base.hom.continuous.continuousOn (V x).isOpen).mp (hspec x)
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
  choose V hx A iCA uA _ tA _ _ tateA S P hP B iCB tB rB hB T P' hP'
    hsheaf φ hφ eV eU hfac using hf
  have hcov : IsOpenCover V := eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hx x⟩
  have hlocal (x : X.obj) :
      IsClopen (Set.range ((V x : Set X.obj).restrictPreimage f.hom.base)) := by
    let hU := TopCat.homeoOfIso (forgetToTop.mapIso (eU x))
    let hV := TopCat.homeoOfIso (forgetToTop.mapIso (eV x))
    have hrange : Set.range (presentationLimitPreAdicSpacePairComap (P x) (P' x) (hP x) (hP' x)
        (hsheaf x) (φ x)).base = Set.range (φ x).spaComap :=
      congrArg Set.range (funext (presentationLimitPreAdicSpacePairComap_base_apply
        (P x) (P' x) (hP x) (hP' x) (hsheaf x) (φ x)))
    have hr : Set.range ((V x : Set X.obj).restrictPreimage f.hom.base) =
        hV ⁻¹' Set.range (φ x).spaComap := by
      rw [restrictPreimage_base_eq_of_iso (hfac x)]
      exact (Set.range_comp _ _).trans
        ((congrArg (hV.symm '' ·) (hU.surjective.range_comp _)).trans
          ((hV.toEquiv.image_symm_eq_preimage _).trans (congrArg (hV ⁻¹' ·) hrange)))
    rw [hr]
    exact (hφ x).isClopen_range_spaComap.preimage hV.continuous
  simp_rw [Set.range_restrictPreimage] at hlocal
  exact ⟨hcov.isClosed_iff_coe_preimage.mpr fun x ↦ (hlocal x).1,
    hcov.isOpen_iff_coe_preimage.mpr fun x ↦ (hlocal x).2⟩

/-- **A finite étale morphism from a nonempty source into a preconnected target is surjective.** -/
theorem IsFiniteEtale.surjective_of_nonempty_of_preconnectedSpace {f : Y ⟶ X} (hf : IsFiniteEtale f)
    [Nonempty Y.obj] [PreconnectedSpace X.obj] : Function.Surjective f.hom.base :=
  Set.range_eq_univ.mp (hf.isClopen_range.eq_univ (Set.range_nonempty f.hom.base))

end TauCeti.AdicSpace
