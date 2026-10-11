/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Open subsets of schemes

This file records general-purpose facts about open subsets of schemes.

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.instNonemptyTop` states that the whole space is a nonempty open
  subset of any nonempty scheme.
* `AlgebraicGeometry.IsAffineOpen.presheaf_map_fromSpec_appIso_hom` identifies restriction of
  structure-sheaf sections along the affine chart `Spec Γ(X, U)`.
* `AlgebraicGeometry.Scheme.Hom.appLE_eq_id_of_eq_id` identifies the restriction maps of a scheme
  endomorphism equal to the identity.
-/

open TopologicalSpace AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

public section

open CategoryTheory Opposite

noncomputable section

variable {X : Scheme.{u}} {U : X.Opens}

/-- If an endomorphism `f` of `X` equals the identity, then so does each of its restriction maps
`Γ(X, U) ⟶ Γ(X, U)`. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.appLE_eq_id_of_eq_id {f : X ⟶ X}
    (hf : f = 𝟙 X) (U : X.Opens) (e : U ≤ f ⁻¹ᵁ U) : f.appLE U U e = 𝟙 _ := by
  subst hf
  rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
  exact (Category.id_comp _).trans (X.presheaf.map_id _)

/-- Along the open immersion `hU.fromSpec : Spec Γ(X, U) ⟶ X` onto an affine open `U`,
restricting a section of `𝒪_X` from `U` to the image of an open `V` and transporting it to `V`
gives the restriction to `V` of the corresponding global section of `Spec Γ(X, U)`. -/
@[reassoc]
theorem _root_.AlgebraicGeometry.IsAffineOpen.presheaf_map_fromSpec_appIso_hom
    (hU : IsAffineOpen U) (V : (Spec Γ(X, U)).Opens) :
    X.presheaf.map (homOfLE (by
        simpa [hU.opensRange_fromSpec] using hU.fromSpec.image_le_opensRange V)).op ≫
      (hU.fromSpec.appIso V).hom =
      (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec Γ(X, U)).presheaf.map V.leTop.op := by
  rw [← hU.fromSpec.appLE_appIso_inv (by simp [hU.fromSpec_preimage_self]), Category.assoc,
    Iso.inv_hom_id, Category.comp_id, Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc,
    ← Functor.map_comp]
  rfl

end

end

namespace Scheme

/-- The whole space is a nonempty open subset of a nonempty scheme. -/
public instance instNonemptyTop {X : Scheme.{u}} [Nonempty X] :
    Nonempty ((⊤ : X.Opens) : Type u) :=
  let ⟨x⟩ := ‹Nonempty X›
  ⟨⟨x, trivial⟩⟩

end Scheme

end AlgebraicGeometry

end TauCeti
