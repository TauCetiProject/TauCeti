/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Restricting local properties of scheme morphisms

For a morphism of schemes `f : X ⟶ Y` and an open `U` of `Y`, Mathlib's `f ∣_ U` is the
restriction `f ⁻¹ᵁ U ⟶ U`. A property local on the target passes from this restriction to
every smaller open. An open immersion restricts to an isomorphism over opens in its range.
Restricting the source to an open equal to the full preimage gives a pullback square, which
transfers properties stable under base change to `Scheme.Hom.resLE`.

## Main results

* `AlgebraicGeometry.IsZariskiLocalAtTarget.restrict_of_le`: a property local on the target
  passes from `f ∣_ U` to `f ∣_ V` when `V ≤ U`.
* `AlgebraicGeometry.Scheme.Hom.isIso_morphismRestrict_of_le_opensRange`: an open immersion
  restricts to an isomorphism over every open contained in its range.
* `AlgebraicGeometry.Scheme.Hom.isPullback_resLE_of_eq`: the restriction of `f` to an open `U`
  of the target and an open `V` of the source equal to `f ⁻¹ᵁ U` is a pullback of `f`.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A property local on the target passes from the restriction over `U` to the restriction
over every open `V ≤ U`. -/
theorem IsZariskiLocalAtTarget.restrict_of_le (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] {f : X ⟶ Y} {U V : Y.Opens} (h : P (f ∣_ U)) (hVU : V ≤ U) :
    P (f ∣_ V) := by
  have himage : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hVU
  exact (P.arrow_mk_iso_iff
    (morphismRestrictRestrict f _ _ ≪≫ morphismRestrictEq f himage)).mp
    (IsZariskiLocalAtTarget.restrict h _)

/-- An open immersion `f` restricts to an isomorphism over every open `V` contained in its
range. -/
theorem Scheme.Hom.isIso_morphismRestrict_of_le_opensRange [IsOpenImmersion f] {V : Y.Opens}
    (hV : V ≤ f.opensRange) : IsIso (f ∣_ V) := by
  refine (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, ⟨fun y ↦ ?_⟩⟩
  obtain ⟨z, hz⟩ := hV y.2
  exact ⟨⟨z, (Scheme.Hom.mem_preimage _).mpr (hz ▸ y.2)⟩,
    Subtype.ext ((morphismRestrict_base_coe _ _ _).trans hz)⟩

/-- Restricting `f` over an open `U` of the target, with source the open `V = f ⁻¹ᵁ U` (up to a
propositional equality), gives a pullback of `f` along the inclusion of `U`. -/
theorem Scheme.Hom.isPullback_resLE_of_eq (U : Y.Opens) {V : X.Opens} (h : V = f ⁻¹ᵁ U) :
    IsPullback (f.resLE U V h.le) V.ι U.ι f := by
  subst h
  simpa [Scheme.Hom.resLE_eq_morphismRestrict] using isPullback_morphismRestrict f U

end AlgebraicGeometry
