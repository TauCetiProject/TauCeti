/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale

/-!
# Base change of weakly étale morphisms

Instances making Mathlib's `CategoryTheory.MorphismProperty.Over.pullback` available for the
morphism property `@AlgebraicGeometry.WeaklyEtale` along any morphism of schemes, as
`TauCeti.AlgebraicGeometry.etale_hasPullbacksAlong` and
`TauCeti.AlgebraicGeometry.etale_isStableUnderBaseChangeAlong` do for
`@AlgebraicGeometry.Etale`.
-/

public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

-- Instance search does not derive these from the general instances for categories with pullbacks
-- and for properties stable under base change, as for `@Etale` in
-- `TauCeti/AlgebraicGeometry/Morphisms/Etale/Basic.lean`.
/-- Weakly étale schemes over `Y` can be pulled back along any `f : X ⟶ Y`. -/
instance weaklyEtale_hasPullbacksAlong {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.HasPullbacksAlong @WeaklyEtale f :=
  ⟨fun _ _ ↦ inferInstance⟩

/-- Weakly étale morphisms are stable under base change along any `f : X ⟶ Y`. -/
instance weaklyEtale_isStableUnderBaseChangeAlong {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong @WeaklyEtale f :=
  ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback⟩

end AlgebraicGeometry
