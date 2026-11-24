/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Open immersions: ranges under base change and stalks

In a cartesian square of schemes, the preimage of an open immersion's range is the
range of the base-changed immersion.

An open immersion `j : U ⟶ X` identifies the stalk of `U` at `u` with the stalk of `X` at `j u`,
so the former is factorial whenever the latter is
(`AlgebraicGeometry.Scheme.Hom.uniqueFactorizationMonoid_stalk_of_isOpenImmersion`).
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

/-- For an open immersion `j : U ⟶ X`, the stalk of `U` at `u` is a unique factorization monoid
whenever the stalk of `X` at `j u` is. -/
theorem Hom.uniqueFactorizationMonoid_stalk_of_isOpenImmersion {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (u : U) [UniqueFactorizationMonoid (X.presheaf.stalk (j u))] :
    UniqueFactorizationMonoid (U.presheaf.stalk u) :=
  (asIso (j.stalkMap u)).commRingCatIsoToRingEquiv.toMulEquiv.uniqueFactorizationMonoid
    inferInstance

end AlgebraicGeometry.Scheme
