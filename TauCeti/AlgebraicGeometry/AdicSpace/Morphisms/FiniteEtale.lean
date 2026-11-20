/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Affinoid
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.LocallyTate
public import TauCeti.RingTheory.Huber.ModuleTopology.FiniteEtale

import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.FiniteAlgebra
import TauCeti.RingTheory.Huber.ModuleTopology.NaturallyComplete

/-!
# Finite étale morphisms of analytic adic spaces

A finite étale morphism is modelled over a cover of its target by Tate affinoids. Over each
chart the **whole preimage** is an affinoid, with its map induced by a finite étale morphism
of Huber pairs. In particular the topology and the plus ring on the source chart are the
natural module topology and the integral-closure plus ring, not arbitrary choices.

We use open immersions to express the chart condition without choosing a cover or a
presentation of a restriction. The condition is at a point of the target, including points
with empty fibre. This is the finite part of the local description of étale morphisms by
open immersions and finite étale morphisms.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  Definition 8.2.16 and Lemma 8.2.17.
-/

public section

open CategoryTheory TopologicalSpace

namespace TauCeti.AdicSpace

open Huber PreAdicSpace ValuationSpectrum

universe u

variable {X Y : AdicSpace.{u}}

/-- `f` is finite étale over a neighbourhood of the **target** point `y` if some open Tate
affinoid chart containing `y` has whole preimage given by a finite étale Huber pair. Both
chart spectra are sheafy and their rings are complete Hausdorff. -/
def IsFiniteEtaleAt (f : X ⟶ Y) (y : Y.obj) : Prop :=
  ∃ (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
    (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsTateRing A)
    (S : Pair A) (hS : IsSheafyForEveryPresentation S.plus)
    (B : Type u) (_ : CommRing B) (_ : UniformSpace B) (_ : IsUniformAddGroup B)
    (_ : IsTopologicalRing B) (_ : CompleteSpace B) (_ : T2Space B) (_ : IsHuberRing B)
    (T : Pair B) (hT : IsSheafyForEveryPresentation T.plus)
    (φ : Pair.Hom S T) (_ : φ.IsFiniteEtale)
    (i : ofPair T hT ⟶ X) (j : ofPair S hS ⟶ Y),
    IsOpenImmersion i.hom ∧ IsOpenImmersion j.hom ∧ y ∈ Set.range j.hom.base ∧
    Set.range i.hom.base = f.hom.base ⁻¹' Set.range j.hom.base ∧
    comapOfPair hS hT φ ≫ j = i ≫ f

/-- A finite étale neighbourhood is exhibited by open immersions of the two affinoid spectra,
with the source chart having image exactly the preimage of the target chart. -/
theorem isFiniteEtaleAt_iff {f : X ⟶ Y} {y : Y.obj} : IsFiniteEtaleAt f y ↔
    ∃ (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
      (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsTateRing A)
      (S : Pair A) (hS : IsSheafyForEveryPresentation S.plus)
      (B : Type u) (_ : CommRing B) (_ : UniformSpace B) (_ : IsUniformAddGroup B)
      (_ : IsTopologicalRing B) (_ : CompleteSpace B) (_ : T2Space B) (_ : IsHuberRing B)
      (T : Pair B) (hT : IsSheafyForEveryPresentation T.plus)
      (φ : Pair.Hom S T) (_ : φ.IsFiniteEtale)
      (i : ofPair T hT ⟶ X) (j : ofPair S hS ⟶ Y),
      IsOpenImmersion i.hom ∧ IsOpenImmersion j.hom ∧ y ∈ Set.range j.hom.base ∧
      Set.range i.hom.base = f.hom.base ⁻¹' Set.range j.hom.base ∧
      comapOfPair hS hT φ ≫ j = i ≫ f :=
  (Iff.rfl)

/-- A morphism of adic spaces is finite étale if it is finite étale over a neighbourhood of
every point of the target. In particular its target is analytic. -/
def IsFiniteEtale : MorphismProperty AdicSpace.{u} := fun _ _ f ↦
  ∀ y, IsFiniteEtaleAt f y

/-- Finite étaleness can be checked at all points of the target. -/
theorem isFiniteEtale_iff {f : X ⟶ Y} : IsFiniteEtale f ↔ ∀ y, IsFiniteEtaleAt f y :=
  (Iff.rfl)

/-- A finite étale morphism of Huber pairs over a complete Hausdorff Tate base induces a
finite étale map of adic spaces when both spectra are sheafy. -/
theorem IsFiniteEtale.spa {A B : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
    [IsTopologicalRing A] [CompleteSpace A] [T2Space A] [IsTateRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
    {S : Pair A} {T : Pair B} (hS : IsSheafyForEveryPresentation S.plus)
    (hT : IsSheafyForEveryPresentation T.plus) {φ : Pair.Hom S T} (hφ : φ.IsFiniteEtale) :
    IsFiniteEtale (comapOfPair hS hT φ) := by
  let _ : Algebra A B := φ.toRingHom.toAlgebra
  have : Module.Finite A B := hφ.finite
  have : Algebra.Etale A B := hφ.etale
  have : IsModuleTopology A B := hφ.isModuleTopology
  have : Module.FinitePresentation A B := .of_finite_of_finitePresentation A B
  have : Module.Projective A B := Module.Flat.projective_of_finitePresentation
  let _ : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
  have : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
  obtain ⟨_, _⟩ := isNaturallyComplete_iff.mp (IsNaturallyComplete.of_projective (A := A) (M := B))
  refine isFiniteEtale_iff.mpr fun y ↦ isFiniteEtaleAt_iff.mpr ?_
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, S, hS, B, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, T, hT, φ, hφ,
    𝟙 (ofPair T hT), 𝟙 (ofPair S hS), inferInstance, inferInstance, ⟨y, rfl⟩, ?_, by simp⟩
  simp [← PreAdicSpace.forgetToTop_map]

/-- An isomorphism onto an analytic adic space is finite étale. -/
theorem IsFiniteEtale.of_isIso (f : X ⟶ Y) [IsIso f] (hY : Y.IsAnalytic) : IsFiniteEtale f := by
  refine isFiniteEtale_iff.mpr fun y ↦ isFiniteEtaleAt_iff.mpr ?_
  obtain ⟨V, hV, hy⟩ := (isAnalytic_iff.mp hY) y
  obtain ⟨A, _, _, _, _, _, _, _, S, P, hP, ⟨e⟩⟩ :=
    (isTateAffinoid_iff _).mp ((mem_propOpens_iff _).mp hV)
  have hV' := isSheafy_restrict V.isOpenEmbedding Y.property.isSheafy
  have h := ObjectProperty.prop_of_iso PreAdicSpace.isSheafy e hV'
  have hs := (isSheafy_presentationLimitPreAdicSpace_iff P S.plus _ hP).mp h
  have hS := (isSheafyForEveryPresentation_iff_isRingOfIntegralElements_and_isSheaf P).mpr
    ⟨S.isRingOfIntegralElements, hs⟩
  let e' := ofPairIsoOfPresentation S hS P hP
  let j : ofPair S hS ⟶ Y := ObjectProperty.homMk
    (e'.hom.hom ≫ e.inv ≫ Y.obj.ofRestrict V.isOpenEmbedding)
  have hj : IsOpenImmersion j.hom := by
    dsimp [j]
    infer_instance
  have hyj : y ∈ Set.range j.hom.base := by
    have he : Function.Surjective (e'.hom.hom ≫ e.inv).base :=
      (TopCat.homeoOfIso (PreAdicSpace.forgetToTop.mapIso
        (((ObjectProperty.ι _).mapIso e') ≪≫ e.symm))).surjective
    obtain ⟨z, hz⟩ := he ⟨y, hy⟩
    exact ⟨z, congrArg Subtype.val hz⟩
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, S, hS, A, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, S, hS, Pair.Hom.id S,
    Pair.Hom.isFiniteEtale_id S, j ≫ inv f, j,
    IsOpenImmersion.comp j.hom (inv f).hom, hj, hyj, ?_, by simp⟩
  let F := ObjectProperty.ι PreAdicSpace.isAdic ⋙ PreAdicSpace.forgetToTop
  -- The point map of the inverse is the inverse of the underlying homeomorphism.
  let eF := TopCat.homeoOfIso (F.mapIso (asIso f))
  exact (Set.range_comp eF.symm j.hom.base).trans (eF.symm.image_eq_preimage_symm _)

/-- The identity of an analytic adic space is finite étale. -/
theorem IsFiniteEtale.id (hX : X.IsAnalytic) : IsFiniteEtale (𝟙 X) :=
  IsFiniteEtale.of_isIso (𝟙 X) hX

/-- The target of a finite étale morphism is analytic. -/
theorem IsFiniteEtale.isAnalytic_target {f : X ⟶ Y} (hf : IsFiniteEtale f) : Y.IsAnalytic := by
  refine isAnalytic_iff_analyticPoints_eq_univ.mpr (Set.eq_univ_iff_forall.mpr fun y ↦ ?_)
  obtain ⟨A, _, _, _, _, _, _, _, S, hS, _, _, _, _, _, _, _, _, _, _, _, _,
    _, j, _, hj, ⟨z, rfl⟩, _, _⟩ := isFiniteEtaleAt_iff.mp (isFiniteEtale_iff.mp hf y)
  obtain ⟨P, hP, hs⟩ := hS.exists_compatible_isSheaf
  have ha := IsAnalytic.spa P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP hs
  exact mapsTo_analyticPoints_of_isOpenImmersion j.hom
    (by simp [(ha.of_iso (ofPairIsoOfPresentation S hS P hP)).analyticPoints_eq_univ])

/-- The source of a finite étale morphism is analytic: the source rings on the charts
are Tate because they receive continuous ring maps from Tate rings. -/
theorem IsFiniteEtale.isAnalytic_source {f : X ⟶ Y} (hf : IsFiniteEtale f) : X.IsAnalytic := by
  refine isAnalytic_iff_analyticPoints_eq_univ.mpr (Set.eq_univ_iff_forall.mpr fun x ↦ ?_)
  obtain ⟨A, _, _, _, _, _, _, _, S, hS, B, _, _, _, _, _, _, _, T, hT, φ, _,
    i, j, hi, _, hx, hrange, _⟩ := isFiniteEtaleAt_iff.mp (isFiniteEtale_iff.mp hf (f.hom.base x))
  have hxi : x ∈ Set.range i.hom.base := hrange.symm ▸ hx
  obtain ⟨w, rfl⟩ := hxi
  have : IsTateRing B := IsTateRing.of_continuous φ.continuous_toRingHom
  obtain ⟨P, hP, hs⟩ := hT.exists_compatible_isSheaf
  have ha := IsAnalytic.spa P T.plus T.isRingOfIntegralElements.isPowerBounded_of_mem hP hs
  exact mapsTo_analyticPoints_of_isOpenImmersion i.hom
    (by simp [(ha.of_iso (ofPairIsoOfPresentation T hT P hP)).analyticPoints_eq_univ])

/-- Every fibre of a finite étale morphism is finite, including over higher-rank points. -/
theorem IsFiniteEtale.finite_fibre {f : X ⟶ Y} (hf : IsFiniteEtale f) (y : Y.obj) :
    (f.hom.base ⁻¹' {y}).Finite := by
  obtain ⟨A, _, _, _, _, _, _, _, S, hS, B, _, _, _, _, _, _, _, T, hT, φ, hφ,
    i, j, _, hj, ⟨z, rfl⟩, hrange, hcomm⟩ :=
    isFiniteEtaleAt_iff.mp (isFiniteEtale_iff.mp hf y)
  have hj' := j.hom.isOpenEmbedding.injective
  have hpoint (w : (ofPair T hT).obj) :
      j.hom.base ((comapOfPair hS hT φ).hom.base w) = f.hom.base (i.hom.base w) :=
    congrArg (fun g : ofPair T hT ⟶ Y ↦ g.hom.base w) hcomm
  have hz : ((comapOfPair hS hT φ).hom.base ⁻¹' {z}).Finite := by
    have hfinite := hφ.finite_fibre (ofPairHomeomorph S hS z)
    refine (hfinite.1.preimage (ofPairHomeomorph T hT).injective.injOn).subset ?_
    intro w hw
    have hw' : (comapOfPair hS hT φ).hom.base w = z := hw
    simpa only [Set.mem_preimage, Set.mem_singleton_iff, Function.comp_apply,
      ofPairHomeomorph_comapOfPair_apply] using congrArg (ofPairHomeomorph S hS) hw'
  refine (hz.image i.hom.base).subset ?_
  intro x hx
  have hx' : f.hom.base x = j.hom.base z := hx
  have hxi : x ∈ Set.range i.hom.base := by
    rw [hrange]
    exact ⟨z, hx'.symm⟩
  obtain ⟨w, rfl⟩ := hxi
  exact ⟨w, hj' ((hpoint w).trans hx'), rfl⟩

end TauCeti.AdicSpace
