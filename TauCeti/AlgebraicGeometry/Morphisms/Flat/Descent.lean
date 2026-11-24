/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.JointlySurjective
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Basic
import TauCeti.AlgebraicGeometry.Sites.Descent

/-!
# Descent and locality of flat morphisms

A morphism whose base change along a surjective flat morphism is flat is itself flat
(`AlgebraicGeometry.Flat.descendsAlong_surjective_inf_flat`). No quasi-compactness or finite
presentation is needed: the base-changed cover is again flat and surjective, so this is
`AlgebraicGeometry.Flat.of_comp_surjective`, which is checked on stalks. In particular flatness
satisfies fpqc descent (`AlgebraicGeometry.Flat.descendsAlong_surjective_inf_flat_inf_quasicompact`)
and fppf descent
(`AlgebraicGeometry.Flat.descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation`).

We also provide
`CategoryTheory.MorphismProperty.of_isPullback_of_surjective_of_flat_of_quasiCompact`, which
applies fpqc descent (`DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)`) along a cartesian
square directly from the typeclass instances `[Surjective f] [Flat f] [QuasiCompact f]`.

Mathlib also passes from fpqc to fppf descent for properties local on the target, by an anonymous
instance which instance search does not apply to concrete properties such as `@Flat`.
`MorphismProperty.descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation` names it,
so that it can be invoked for a given property.

Using stalkwise flat descent (`AlgebraicGeometry.Scheme.Hom.flat_stalkMap_of_comp`) and
`AlgebraicGeometry.Flat.descendsAlong_surjective_inf_flat`, flatness is also local at the source
and at the target for `Scheme.precoverage @Flat` (without any quasi-compactness or
finite-presentation assumption on the cover), and hence for the fpqc, fppf, and étale precoverages.
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

/-- **Flatness descends along flat surjective morphisms.** A morphism whose base change along a
surjective flat morphism is flat is itself flat. -/
instance Flat.descendsAlong_surjective_inf_flat :
    MorphismProperty.DescendsAlong @Flat.{u} (@Surjective ⊓ @Flat) where
  of_isPullback {_ _ _ _ fst snd f g} h hf hfst := by
    have : Surjective snd := MorphismProperty.of_isPullback h hf.1
    have : Flat snd := MorphismProperty.of_isPullback h hf.2
    have : Flat (snd ≫ g) := h.w ▸ MorphismProperty.comp_mem _ fst f hfst hf.2
    exact Flat.of_comp_surjective snd g

/-- **Flat morphisms satisfy fpqc descent.** Flatness descends along surjective, flat,
quasi-compact morphisms. -/
instance Flat.descendsAlong_surjective_inf_flat_inf_quasicompact :
    MorphismProperty.DescendsAlong @Flat.{u} (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  .of_le inf_le_left

/-- **Flat morphisms satisfy fppf descent.** Flatness descends along surjective, flat morphisms
locally of finite presentation. -/
instance Flat.descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation :
    MorphismProperty.DescendsAlong @Flat.{u} (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
  .of_le inf_le_left

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
  let F : MorphismProperty Scheme.{u} := @Flat
  have : HasRingHomProperty F RingHom.Flat := inferInstanceAs (HasRingHomProperty @Flat _)
  have : F.IsStableUnderBaseChange :=
    inferInstanceAs (MorphismProperty.IsStableUnderBaseChange @Flat)
  have : F.DescendsAlong (@Surjective ⊓ F) := Flat.descendsAlong_surjective_inf_flat
  MorphismProperty.isLocalAtTarget_precoverage_of_descendsAlong F F

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
