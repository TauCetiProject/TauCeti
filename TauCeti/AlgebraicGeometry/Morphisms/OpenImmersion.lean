/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu, The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Open immersions: ranges under base change and stalk-domain transport

In a cartesian square of schemes, the preimage of an open immersion's range is the
range of the base-changed immersion. We also record that any morphism whose stalk map
at a point is an isomorphism (in particular, any open immersion) preserves and reflects
having an integral-domain stalk.
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

/-- A morphism of schemes whose stalk map at `x` is an isomorphism (in particular, any open
immersion) preserves and reflects having an integral-domain stalk. -/
theorem Hom.isDomain_stalk_iff_of_isIso_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    [IsIso (f.stalkMap x)] :
    IsDomain (Y.presheaf.stalk (f x)) ↔ IsDomain (X.presheaf.stalk x) :=
  let e := (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
  ⟨fun _ ↦ e.symm.toMulEquiv.isDomain _, fun _ ↦ e.toMulEquiv.isDomain _⟩

end AlgebraicGeometry.Scheme
