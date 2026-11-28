/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.KrullSchmidt.Basic
public import TauCeti.CategoryTheory.Skeletal
import TauCeti.CategoryTheory.Functor.LocalEnd
import TauCeti.CategoryTheory.Preadditive.KrullSchmidt.Uniqueness
import TauCeti.RingTheory.LocalRing.Basic

/-!
# Isomorphism classes of indecomposables under additive quotients

Under a full, essentially surjective additive functor from a Krull–Schmidt category, each object
with a local endomorphism ring is the image up to isomorphism of a unique isomorphism class of
indecomposable objects. This identifies the surviving indecomposable classes with the classes of
objects with local endomorphism rings in the target. In particular, it applies to the quotients
by projectively and injectively trivial morphisms used in Auslander–Reiten duality.

The stable and costable cases are described in Iyama, Nakaoka and Palu, *Auslander–Reiten theory
in extriangulated categories*, arXiv:1805.03776v3, §2.1 and Remark 3.5.
-/

public section

namespace CategoryTheory.Functor

open Limits TauCeti

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasFiniteBiproducts C] [IsKrullSchmidt C] (F : C ⥤ D) [F.Additive] [F.Full]
  (P : ObjectProperty C) (hP : ∀ X, IsZero (F.obj X) ↔ P X)

private def liftToLocalEndFullSubcategory :
    (ObjectProperty.FullSubcategory fun X ↦ Indecomposable X ∧ ¬ P X) ⥤
      (ObjectProperty.FullSubcategory fun Y : D ↦ IsLocalRing (End Y)) :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ F) fun X ↦ by
    have := (IsKrullSchmidt.indecomposable_iff_isLocalRing_end X.obj).mp X.property.1
    exact F.isLocalRing_end_obj (X := X.obj) ((hP X.obj).not.mpr X.property.2)

private theorem injective_mapSkeleton_liftToLocalEndFullSubcategory :
    Function.Injective (F.liftToLocalEndFullSubcategory P hP).mapSkeleton.obj := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro X Y h
  have h' : (F.liftToLocalEndFullSubcategory P hP).mapSkeleton.obj (toSkeleton X) =
      (F.liftToLocalEndFullSubcategory P hP).mapSkeleton.obj (toSkeleton Y) := h
  rw [Functor.mapSkeleton_obj_toSkeleton, Functor.mapSkeleton_obj_toSkeleton] at h'
  apply (ObjectProperty.toSkeleton_eq_toSkeleton_iff_nonempty_iso _ _ _).mpr
  have := (IsKrullSchmidt.indecomposable_iff_isLocalRing_end X.obj).mp X.property.1
  have := (IsKrullSchmidt.indecomposable_iff_isLocalRing_end Y.obj).mp Y.property.1
  apply (F.nonempty_iso_obj_iff_of_isLocalRing_end ((hP X.obj).not.mpr X.property.2)
    F.map_surjective F.map_surjective).mp
  exact (ObjectProperty.toSkeleton_eq_toSkeleton_iff_nonempty_iso _ _ _).mp h'

private instance [F.EssSurj] : (F.liftToLocalEndFullSubcategory P hP).EssSurj where
  mem_essImage Y := by
    let W := F.objPreimage Y.obj
    let e := F.objObjPreimageIso Y.obj
    have : IsLocalRing (End Y.obj) := Y.property
    have : IsLocalRing (End (F.obj W)) := e.symm.endRingEquiv.isLocalRing
    obtain ⟨X, hX, ⟨i⟩⟩ := IsKrullSchmidt.exists_isLocalRing_end_iso_obj F W
    let j : F.obj X ≅ Y.obj := i.symm ≪≫ e
    have hPX : ¬ P X := fun h ↦ not_isZero_of_nontrivial_end (((hP X).mpr h).of_iso j.symm)
    exact ⟨⟨X, (IsKrullSchmidt.indecomposable_iff_isLocalRing_end X).mpr hX, hPX⟩,
      ⟨(ObjectProperty.ι _).preimageIso j⟩⟩

variable [F.EssSurj]

/-- A full, essentially surjective additive functor from a Krull–Schmidt category induces a
bijection from the isomorphism classes of indecomposables it sends to nonzero objects to the
classes of objects with local endomorphism rings in the target. The property `P` specifies the
objects sent to zero. -/
noncomputable def skeletonEquivOfIsLocalRingEnd :
    Skeleton (ObjectProperty.FullSubcategory fun X ↦ Indecomposable X ∧ ¬ P X) ≃
      Skeleton (ObjectProperty.FullSubcategory fun Y : D ↦ IsLocalRing (End Y)) :=
  Equiv.ofBijective _
    ⟨F.injective_mapSkeleton_liftToLocalEndFullSubcategory P hP, Functor.mapSkeleton_surjective _⟩

/-- The image of an indecomposable class under `skeletonEquivOfIsLocalRingEnd` is represented by
its image under the functor. -/
theorem skeletonEquivOfIsLocalRingEnd_apply_eq_iff {X : C} (hX : Indecomposable X) (hXP : ¬ P X)
    {Y : D} (hY : IsLocalRing (End Y)) :
    F.skeletonEquivOfIsLocalRingEnd P hP (toSkeleton ⟨X, hX, hXP⟩) = toSkeleton ⟨Y, hY⟩ ↔
      Nonempty (F.obj X ≅ Y) := by
  let x : ObjectProperty.FullSubcategory (fun W ↦ Indecomposable W ∧ ¬ P W) := ⟨X, hX, hXP⟩
  have hmap : F.skeletonEquivOfIsLocalRingEnd P hP (toSkeleton x) =
      (F.liftToLocalEndFullSubcategory P hP).mapSkeleton.obj (toSkeleton x) := rfl
  rw [hmap, Functor.mapSkeleton_obj_toSkeleton]
  exact ObjectProperty.toSkeleton_eq_toSkeleton_iff_nonempty_iso _ _ _

end CategoryTheory.Functor
