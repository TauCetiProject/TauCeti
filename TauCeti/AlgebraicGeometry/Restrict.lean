/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Restrictions of morphisms that are isomorphisms

For a morphism of schemes `f : X ⟶ Y` and an open `U` of `Y`, Mathlib's `f ∣_ U` is the
restriction `f ⁻¹ᵁ U ⟶ U`. This file records two ways of seeing that such a restriction is an
isomorphism.

## Main results

* `AlgebraicGeometry.isIso_morphismRestrict_of_le`: if `f ∣_ U` is an isomorphism and `V ≤ U`,
  then `f ∣_ V` is an isomorphism.
* `AlgebraicGeometry.Scheme.Hom.isIso_morphismRestrict_of_le_opensRange`: an open immersion
  restricts to an isomorphism over every open contained in its range.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- If `f` restricts to an isomorphism over `U`, then it restricts to an isomorphism over every
open `V ≤ U`. -/
theorem isIso_morphismRestrict_of_le {U V : Y.Opens} [IsIso (f ∣_ U)] (hVU : V ≤ U) :
    IsIso (f ∣_ V) := by
  have himage : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hVU
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict f _ _ ≪≫ morphismRestrictEq f himage)).mp
    (inferInstanceAs (IsIso ((f ∣_ U) ∣_ _)))

/-- An open immersion `f` restricts to an isomorphism over every open `V` contained in its
range. -/
theorem Scheme.Hom.isIso_morphismRestrict_of_le_opensRange [IsOpenImmersion f] {V : Y.Opens}
    (hV : V ≤ f.opensRange) : IsIso (f ∣_ V) := by
  refine (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, ⟨fun y ↦ ?_⟩⟩
  obtain ⟨z, hz⟩ := hV y.2
  exact ⟨⟨z, (Scheme.Hom.mem_preimage _).mpr (hz ▸ y.2)⟩,
    Subtype.ext ((morphismRestrict_base_coe _ _ _).trans hz)⟩

end AlgebraicGeometry
