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

For an open immersion `j : U ⟶ X`, a function on an open `W` of `X` pulls back to zero along `j`
exactly when it restricts to zero on the image `j ''ᵁ (j ⁻¹ᵁ W)`
(`AlgebraicGeometry.Scheme.Hom.app_eq_zero_iff`).

An open immersion out of an empty scheme has empty range
(`AlgebraicGeometry.Scheme.Hom.opensRange_eq_bot_of_isEmpty`).
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

/-- For an open immersion `j : U ⟶ X`, a function on an open `W` of `X` pulls back to zero on
`j ⁻¹ᵁ W` exactly when it restricts to zero on the image `j ''ᵁ (j ⁻¹ᵁ W)`. -/
theorem Hom.app_eq_zero_iff {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (W : X.Opens)
    (s : Γ(X, W)) :
    j.app W s = 0 ↔ X.presheaf.map (homOfLE (j.image_preimage_le W)).op s = 0 := by
  rw [← (ConcreteCategory.bijective_of_isIso (j.appIso (j ⁻¹ᵁ W)).inv).injective.eq_iff,
    map_zero, ← ConcreteCategory.comp_apply, Scheme.Hom.app_appIso_inv]
  -- both sides restrict along the inclusion `j ''ᵁ (j ⁻¹ᵁ W) ≤ W`, with different proofs
  rfl

/-- An open immersion out of an empty scheme has empty range. -/
@[simp]
lemma Hom.opensRange_eq_bot_of_isEmpty {U X : Scheme.{u}} [IsEmpty U] (j : U ⟶ X)
    [IsOpenImmersion j] : j.opensRange = ⊥ := by
  ext
  simp [Scheme.Hom.coe_opensRange]

end AlgebraicGeometry.Scheme
