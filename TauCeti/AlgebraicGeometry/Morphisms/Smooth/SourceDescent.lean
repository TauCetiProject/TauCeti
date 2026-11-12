/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Basic
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.RingTheory.RegularLocalRing.Descent

/-!
# Smoothness along flat surjections on the source

For schemes locally of finite type over a field, smoothness descends along a flat surjection
on the source. Passing to an algebraic closure reduces this to descent of regular local rings.

Over an arbitrary base, the same conclusion holds when the resulting morphism is already
known to be locally of finite presentation. Flatness descends on stalks and the field case
applies to each fibre. No finite presentation or quasi-compactness of the covering morphism
is needed. Descent of finite presentation is a separate obligation.

## Main results

* `Scheme.Hom.smooth_of_flat_surjective_comp_of_field`: smoothness over a field.
* `Scheme.Hom.smooth_of_flat_surjective_comp`: smoothness over an arbitrary base, with local
  finite presentation of the target morphism supplied.

## References

* The Stacks Project, Tags 05AX and 05B5.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Smoothness over a field descends through any flat surjection on the source, provided
that the target morphism is locally of finite type. -/
theorem smooth_of_flat_surjective_comp_of_field {K : Type u} [Field K] {X' X : Scheme.{u}}
    (u : X' ⟶ X) (f : X ⟶ Spec (.of K)) [Flat u] [Surjective u]
    [LocallyOfFiniteType f] [Smooth (u ≫ f)] : Smooth f := by
  wlog hK : IsAlgClosed K generalizing K X X' with H
  · let g : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of K) :=
      Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
    have hP : MorphismProperty.IsStableUnderBaseChange
        (@Smooth : MorphismProperty Scheme.{u}) := smooth_isStableUnderBaseChange
    have h₁ : Smooth (pullback.snd (u ≫ f) g) :=
      hP.of_isPullback (IsPullback.of_hasPullback (u ≫ f) g) ‹Smooth (u ≫ f)›
    have : Smooth (pullback.snd u (pullback.fst f g) ≫ pullback.snd f g) := by
      rw [← pullbackRightPullbackFstIso_hom_snd]
      have h₂ : Smooth (pullbackRightPullbackFstIso f g u).hom := inferInstance
      exact MorphismProperty.comp_mem _ _ _ h₂ h₁
    have hsnd := H (pullback.snd u (pullback.fst f g)) (pullback.snd f g)
      (AlgebraicClosure.isAlgClosed K)
    have : Surjective g := ⟨fun _ ↦ ⟨⟨⊥, Ideal.isPrime_bot⟩, Subsingleton.elim _ _⟩⟩
    have : Flat g := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact RingHom.flat_algebraMap_iff.2 inferInstance
    exact MorphismProperty.of_pullback_snd_of_descendsAlong
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨⟨‹_›, ‹_›⟩, inferInstance⟩ hsnd
  -- Over an algebraically closed field, regular stalks characterize smoothness.
  let : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) := fun x ↦ by
    obtain ⟨x', rfl⟩ := u.surjective x
    have : IsRegularLocalRing (X'.presheaf.stalk x') :=
      TauCeti.AlgebraicGeometry.isRegularLocalRing_stalk_of_smooth (u ≫ f) x'
    let := (u.stalkMap x').hom.toAlgebra
    have : IsLocalHom (algebraMap (X.presheaf.stalk (u x')) (X'.presheaf.stalk x')) :=
      inferInstanceAs (IsLocalHom (u.stalkMap x').hom)
    have : Module.Flat (X.presheaf.stalk (u x')) (X'.presheaf.stalk x') := Flat.stalkMap u x'
    exact TauCeti.IsRegularLocalRing.of_flat_of_isLocalHom (S := X'.presheaf.stalk x')
  exact f.smooth_of_isRegularLocalRing_stalk

/-- Smoothness of a locally finitely presented morphism descends through any flat surjection
on its source. The covering morphism need not be quasi-compact or locally finitely presented. -/
theorem smooth_of_flat_surjective_comp {X' X S : Scheme.{u}} (u : X' ⟶ X) (f : X ⟶ S)
    [Flat u] [Surjective u] [LocallyOfFinitePresentation f] [Smooth (u ≫ f)] : Smooth f := by
  have : Flat f := Flat.of_comp_surjective u f
  refine Smooth.of_smooth_fiberToSpecResidueField f fun s ↦ ?_
  let g := S.fromSpecResidueField s
  have hP : MorphismProperty.IsStableUnderBaseChange
      (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) :=
    locallyOfFiniteType_isStableUnderBaseChange
  have hft : LocallyOfFiniteType (pullback.snd f g) :=
    hP.of_isPullback (IsPullback.of_hasPullback f g) inferInstance
  have hsm : Smooth (pullback.snd u (pullback.fst f g) ≫ f.fiberToSpecResidueField s) := by
    change Smooth (pullback.snd u (pullback.fst f g) ≫ pullback.snd f g)
    rw [← pullbackRightPullbackFstIso_hom_snd]
    infer_instance
  exact @smooth_of_flat_surjective_comp_of_field _ _ _ _
    (pullback.snd u (pullback.fst f g)) (f.fiberToSpecResidueField s)
    inferInstance inferInstance hft hsm

end AlgebraicGeometry.Scheme.Hom
