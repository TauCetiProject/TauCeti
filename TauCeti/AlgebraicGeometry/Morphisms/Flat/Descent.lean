/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import TauCeti.RingTheory.Flat.Descent
import Mathlib.CategoryTheory.Sites.JointlySurjective
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Basic

/-!
# Descent and locality of flat morphisms

A morphism whose base change along a surjective, flat and quasi-compact morphism is flat is
itself flat. The affine statement is the descent of flatness of a module along a faithfully
flat extension of scalars (`RingHom.Flat.codescendsAlong_faithfullyFlat`), and Mathlib's
`AlgebraicGeometry.HasRingHomProperty.descendsAlong_flat` globalizes it.

We also provide
`CategoryTheory.MorphismProperty.of_isPullback_of_surjective_of_flat_of_quasiCompact`, which
applies fpqc descent (`DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)`) along a cartesian
square directly from the typeclass instances `[Surjective f] [Flat f] [QuasiCompact f]`.

Mathlib also passes from fpqc to fppf descent for properties local on the target, by an anonymous
instance which instance search does not apply to concrete properties such as `@Flat`.
`MorphismProperty.descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation` names it,
so that it can be invoked for a given property.

Using stalkwise flat descent (`AlgebraicGeometry.Scheme.Hom.flat_stalkMap_of_comp`), flatness is
also local at the source and at the target for `Scheme.precoverage @Flat` (without any
quasi-compactness or finite-presentation assumption on the cover), and hence for the fpqc, fppf,
and étale precoverages.
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

/-- If a morphism property of schemes satisfies fpqc descent (`DescendsAlong` surjective, flat,
quasi-compact morphisms), then it descends along any cartesian square whose base-change morphism
is surjective, flat and quasi-compact. -/
theorem _root_.CategoryTheory.MorphismProperty.of_isPullback_of_surjective_of_flat_of_quasiCompact
    {P : MorphismProperty Scheme.{u}}
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    {A X Y Z : Scheme.{u}} {fst : A ⟶ X} {snd : A ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    [Surjective f] [Flat f] [QuasiCompact f]
    (h : IsPullback fst snd f g) (hfst : P fst) : P g :=
  MorphismProperty.of_isPullback_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) h
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hfst

/-- **Flat morphisms satisfy fpqc descent.** Flatness descends along surjective, flat,
quasi-compact morphisms. -/
instance Flat.descendsAlong_surjective_inf_flat_inf_quasicompact :
    MorphismProperty.DescendsAlong @Flat.{u} (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat RingHom.Flat.codescendsAlong_faithfullyFlat

namespace Flat

/-- Flatness of scheme morphisms is local at the source for the flat precoverage. -/
instance isLocalAtSource_precoverage :
    MorphismProperty.IsLocalAtSource @Flat.{u} (Scheme.precoverage @Flat) :=
  have : MorphismProperty.RespectsIso @Flat.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  { comp hR _ g hg hf :=
      have : Flat g := hR.2 hg
      have : Flat _ := hf
      inferInstance
    of_forall_comp {_ _ f _} hR h := Flat.of_stalkMap f fun x ↦ by
      obtain ⟨_, g, hg, u, rfl⟩ :=
        (Presieve.mem_comap_jointlySurjectivePrecoverage_iff Scheme.forget).mp hR.1 x
      have : Flat g := hR.2 hg
      have : Flat (g ≫ f) := h hg
      exact g.flat_stalkMap_of_comp f u (Flat.stalkMap g u) (Flat.stalkMap (g ≫ f) u) }

/-- Flatness of scheme morphisms is local at the target for the flat precoverage. -/
instance isLocalAtTarget_precoverage :
    MorphismProperty.IsLocalAtTarget @Flat.{u} (Scheme.precoverage @Flat) :=
  have : MorphismProperty.RespectsIso @Flat.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  { pullbackSnd {_ _ f _ _ _} _ _ hf :=
      have : Flat f := hf
      inferInstance
    of_forall_pullbackSnd {_ _ f _} hR h := Flat.of_stalkMap f fun y ↦ by
      obtain ⟨_, g, hg, u, hu⟩ :=
        (Presieve.mem_comap_jointlySurjectivePrecoverage_iff Scheme.forget).mp hR.1 (f y)
      let F : MorphismProperty Scheme.{u} := fun ⦃_ _⦄ k ↦ Flat k
      obtain ⟨w, rfl⟩ :=
        Scheme.IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop
          (P := F) (hR.2 hg) y u hu.symm
      have : Flat g := hR.2 hg
      have : Flat (pullback.snd f g) := h hg
      have : Flat (pullback.fst f g ≫ f) := by
        rw [pullback.condition]
        exact inferInstanceAs (Flat (pullback.snd f g ≫ g))
      exact (pullback.fst f g).flat_stalkMap_of_comp f w
        (Flat.stalkMap (pullback.fst f g) w) (Flat.stalkMap (pullback.fst f g ≫ f) w) }

/-- Flatness of scheme morphisms is local at the source for the fpqc precoverage. -/
instance isLocalAtSource_fpqcPrecoverage :
    MorphismProperty.IsLocalAtSource @Flat.{u} Scheme.fpqcPrecoverage :=
  MorphismProperty.IsLocalAtSource.of_le (Scheme.propQCPrecoverage_le_precoverage (P := @Flat))

/-- Flatness of scheme morphisms is local at the target for the fpqc precoverage. -/
instance isLocalAtTarget_fpqcPrecoverage :
    MorphismProperty.IsLocalAtTarget @Flat.{u} Scheme.fpqcPrecoverage :=
  MorphismProperty.IsLocalAtTarget.of_le (Scheme.propQCPrecoverage_le_precoverage (P := @Flat))

/-- Flatness of scheme morphisms is local at the source for the fppf precoverage. -/
instance isLocalAtSource_fppfPrecoverage :
    MorphismProperty.IsLocalAtSource @Flat.{u} Scheme.fppfPrecoverage :=
  MorphismProperty.IsLocalAtSource.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage

/-- Flatness of scheme morphisms is local at the target for the fppf precoverage. -/
instance isLocalAtTarget_fppfPrecoverage :
    MorphismProperty.IsLocalAtTarget @Flat.{u} Scheme.fppfPrecoverage :=
  MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage

/-- Flatness of scheme morphisms is local at the source for the étale precoverage. -/
instance isLocalAtSource_etalePrecoverage :
    MorphismProperty.IsLocalAtSource @Flat.{u} Scheme.etalePrecoverage :=
  MorphismProperty.IsLocalAtSource.of_le
    (Scheme.precoverage_mono (P := @Etale) (Q := @Flat) fun _ _ _ _ ↦ inferInstance)

/-- Flatness of scheme morphisms is local at the target for the étale precoverage. -/
instance isLocalAtTarget_etalePrecoverage :
    MorphismProperty.IsLocalAtTarget @Flat.{u} Scheme.etalePrecoverage :=
  MorphismProperty.IsLocalAtTarget.of_le
    (Scheme.precoverage_mono (P := @Etale) (Q := @Flat) fun _ _ _ _ ↦ inferInstance)

end Flat

end AlgebraicGeometry

namespace CategoryTheory.MorphismProperty

open AlgebraicGeometry

/-- **fpqc descent implies fppf descent.** A property of morphisms of schemes which is local on
the target and descends along surjective, flat, quasi-compact morphisms descends along surjective,
flat morphisms locally of finite presentation. This is Mathlib's instance, stated for a generic
predicate: instance search does not unify it with concrete predicates such as `@Flat`. -/
theorem descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation
    (P : MorphismProperty Scheme.{u}) [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    [IsZariskiLocalAtTarget P] :
    P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
  inferInstance

end CategoryTheory.MorphismProperty
