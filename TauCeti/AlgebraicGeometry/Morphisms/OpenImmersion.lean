/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Open immersions under base change

In a cartesian square of schemes, the preimage of an open immersion's range is the
range of the base-changed immersion. The pullback of an integral scheme along an open immersion
whose image it meets is integral (`AlgebraicGeometry.isIntegral_pullback_of_isOpenImmersion`).
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

namespace AlgebraicGeometry

/-- The pullback of an integral scheme along an open immersion whose image it meets is integral. -/
lemma isIntegral_pullback_of_isOpenImmersion {W X U : Scheme.{u}} [IsIntegral W] (i : W ⟶ X)
    (j : U ⟶ X) [IsOpenImmersion j] (h : (Set.range i ∩ Set.range j).Nonempty) :
    IsIntegral (pullback i j) :=
  have : Nonempty ↥(pullback i j) := not_isEmpty_iff.mp
    (Scheme.isEmpty_pullback_iff.not.mpr (Set.not_disjoint_iff_nonempty_inter.mpr h))
  isIntegral_of_isOpenImmersion (pullback.fst i j)

end AlgebraicGeometry
