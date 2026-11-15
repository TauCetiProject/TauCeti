/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Ranges of open immersions under base change

In a cartesian square of schemes, the preimage of an open immersion's range is the
range of the base-changed immersion.
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- In a cartesian square, the preimage of an open immersion's range is the range of its
base change. -/
lemma preimage_opensRange_of_isPullback {P X Y S : Scheme.{u}}
    {c : P ⟶ X} {g' : P ⟶ Y} {g : X ⟶ S} {b : Y ⟶ S}
    [IsOpenImmersion g] [IsOpenImmersion g'] (h : IsPullback c g' g b) :
    b ⁻¹ᵁ g.opensRange = g'.opensRange := by
  simpa using (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback h ⊤).symm

end AlgebraicGeometry.Scheme
