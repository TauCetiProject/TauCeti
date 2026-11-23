/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Basic
public import TauCeti.Geometry.RingedSpace.LocallyRingedSpace.Restrict

/-!
# Inclusions between restrictions of a formal scheme to nested opens

For opens `V ≤ W` of a formal scheme `X`, `TauCeti.FormalScheme.restrictHomOfLE` lifts
`LocallyRingedSpace.restrictHomOfLE` to the inclusion `X.restrict V ⟶ X.restrict W`, compatibly
with `ofRestrict` and `forgetToLocallyRingedSpace`. We also record the global-section restriction
formula `ofRestrict_c_app_top_apply`.
-/

public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace TauCeti.FormalScheme

variable (X : FormalScheme.{u})

/-- For opens `V ≤ W` of a formal scheme `X`, the inclusion `X.restrict V ⟶ X.restrict W`. -/
noncomputable def restrictHomOfLE {V W : Opens X} (h : V ≤ W) : X.restrict V ⟶ X.restrict W :=
  InducedCategory.homMk (X.toLocallyRingedSpace.restrictHomOfLE h)

@[simp]
theorem forgetToLocallyRingedSpace_map_restrictHomOfLE {V W : Opens X} (h : V ≤ W) :
    forgetToLocallyRingedSpace.map (X.restrictHomOfLE h) =
      X.toLocallyRingedSpace.restrictHomOfLE h := (rfl)

/-- Composing `X.restrictHomOfLE h` with `X.ofRestrict W` recovers `X.ofRestrict V`. -/
@[reassoc (attr := simp)]
theorem restrictHomOfLE_ofRestrict {V W : Opens X} (h : V ≤ W) :
    X.restrictHomOfLE h ≫ X.ofRestrict W = X.ofRestrict V :=
  fullyFaithfulForgetToLocallyRingedSpace.map_injective <| by
    simp only [Functor.map_comp, forgetToLocallyRingedSpace_map_restrictHomOfLE,
      forgetToLocallyRingedSpace_map_ofRestrict]
    exact X.toLocallyRingedSpace.restrictHomOfLE_ofRestrict h

/-- The inclusion of an open formal subscheme into itself is the identity. -/
@[simp]
theorem restrictHomOfLE_refl (V : Opens X) :
    X.restrictHomOfLE (le_refl V) = 𝟙 (X.restrict V) :=
  InducedCategory.hom_ext (X.toLocallyRingedSpace.restrictHomOfLE_refl V)

/-- Inclusions between open formal subschemes compose functorially. -/
@[reassoc (attr := simp)]
theorem restrictHomOfLE_comp {U V W : Opens X} (h : U ≤ V) (k : V ≤ W) :
    X.restrictHomOfLE h ≫ X.restrictHomOfLE k = X.restrictHomOfLE (h.trans k) :=
  InducedCategory.hom_ext (X.toLocallyRingedSpace.restrictHomOfLE_comp h k)

/-- Restricting a global section along `X.ofRestrict U` at `op ⊤` applies `Γ(X, ⊤) → Γ(X, U)`
followed by `restrictTopSectionsIso`. -/
theorem ofRestrict_c_app_top_apply (U : Opens X) (s : X.presheaf.obj (op ⊤)) :
    (forgetToLocallyRingedSpace.map (X.ofRestrict U)).c.app (op ⊤) s =
      (X.toPresheafedSpace.restrictTopSectionsIso U).hom
        (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) := by
  rw [forgetToLocallyRingedSpace_map_ofRestrict]
  exact ConcreteCategory.congr_hom (X.toPresheafedSpace.ofRestrict_c_app_top U) s

end TauCeti.FormalScheme
