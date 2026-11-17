/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import TauCeti.AlgebraicGeometry.Sites.Descent

/-!
# Morphism properties local at the target in the fppf topology

This file specializes `CategoryTheory.MorphismProperty.isLocalAtTarget_precoverage_of_descendsAlong`
to `Scheme.fppfPrecoverage`, obtaining fppf target locality from fppf or fpqc descent (via Mathlib's
`FlatDescent` reduction from fpqc descent to fppf descent).

## Main results

* `CategoryTheory.MorphismProperty.isLocalAtTarget_fppfPrecoverage_of_descendsAlong`: any
  Zariski-local-at-target, base-change-stable morphism property satisfying fppf descent is local at
  the target for `Scheme.fppfPrecoverage`.
* `AlgebraicGeometry.HasRingHomProperty.isLocalAtTarget_fppfPrecoverage` and
  `AlgebraicGeometry.HasRingHomProperty.isLocalAtTarget_fppfPrecoverage_of_fpqc`: specializations to
  raw scheme morphism predicates equipped with `HasRingHomProperty` at `instances` transparency.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry

namespace CategoryTheory.MorphismProperty

/-- Any Zariski-local-at-target, base-change-stable scheme morphism property that descends along
surjective flat morphisms locally of finite presentation is local at the target for
`Scheme.fppfPrecoverage`. -/
instance isLocalAtTarget_fppfPrecoverage_of_descendsAlong
    (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] [P.IsStableUnderBaseChange]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)] :
    P.IsLocalAtTarget Scheme.fppfPrecoverage :=
  let F : MorphismProperty Scheme.{u} := @Flat
  let L : MorphismProperty Scheme.{u} := @LocallyOfFinitePresentation
  have : HasRingHomProperty F RingHom.Flat := inferInstanceAs (HasRingHomProperty @Flat _)
  have : HasRingHomProperty L RingHom.FinitePresentation :=
    inferInstanceAs (HasRingHomProperty @LocallyOfFinitePresentation _)
  have hle : (@Surjective ⊓ (F ⊓ L) : MorphismProperty Scheme.{u}) ≤
      ((@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) : MorphismProperty Scheme.{u}) :=
    fun _ _ _ ⟨h₁, h₂, h₃⟩ ↦ ⟨⟨h₁, h₂⟩, h₃⟩
  have : P.DescendsAlong (@Surjective ⊓ (F ⊓ L)) := DescendsAlong.of_le hle
  isLocalAtTarget_precoverage_of_descendsAlong P (F ⊓ L)

end CategoryTheory.MorphismProperty

namespace AlgebraicGeometry

open CategoryTheory.MorphismProperty

/-- Specializes `isLocalAtTarget_fppfPrecoverage_of_descendsAlong` to scheme morphism predicates
equipped with `HasRingHomProperty` and fppf descent. -/
instance HasRingHomProperty.isLocalAtTarget_fppfPrecoverage
    (P : ∀ ⦃X Y : Scheme.{u}⦄, (X ⟶ Y) → Prop)
    {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    [HasRingHomProperty P Q] [IsStableUnderBaseChange P]
    [DescendsAlong P (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)] :
    IsLocalAtTarget P Scheme.fppfPrecoverage :=
  let P' : MorphismProperty Scheme.{u} := P
  have : HasRingHomProperty P' Q := ‹_›
  have : P'.IsStableUnderBaseChange := ‹_›
  have : P'.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) := ‹_›
  isLocalAtTarget_fppfPrecoverage_of_descendsAlong P'

/-- Specializes `isLocalAtTarget_fppfPrecoverage_of_descendsAlong` to scheme morphism predicates
equipped with `HasRingHomProperty` and fpqc descent. -/
instance HasRingHomProperty.isLocalAtTarget_fppfPrecoverage_of_fpqc
    (P : ∀ ⦃X Y : Scheme.{u}⦄, (X ⟶ Y) → Prop)
    {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    [HasRingHomProperty P Q] [IsStableUnderBaseChange P]
    [DescendsAlong P (@Surjective ⊓ @Flat ⊓ @QuasiCompact)] :
    IsLocalAtTarget P Scheme.fppfPrecoverage :=
  let P' : MorphismProperty Scheme.{u} := P
  have : HasRingHomProperty P' Q := ‹_›
  have : P'.IsStableUnderBaseChange := ‹_›
  have : P'.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := ‹_›
  isLocalAtTarget_fppfPrecoverage_of_descendsAlong P'

end AlgebraicGeometry
