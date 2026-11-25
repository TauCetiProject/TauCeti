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
with `ofRestrict` and `forgetToLocallyRingedSpace`, and `TauCeti.FormalScheme.restrictRestrictIso`
lifts `LocallyRingedSpace.restrictRestrictIso` to identify `(X.restrict U).restrict V` with
`X.restrict (U.isOpenEmbedding.functor.obj V)`. We also record the global-section restriction
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

/-- Iterated open restriction `(X.restrict U).restrict V` is canonically isomorphic to
`X.restrict (U.isOpenEmbedding.functor.obj V)`. -/
noncomputable def restrictRestrictIso (U : Opens X) (V : Opens (X.restrict U)) :
    (X.restrict U).restrict V ≅ X.restrict (U.isOpenEmbedding.functor.obj V) :=
  InducedCategory.isoMk (X.toLocallyRingedSpace.restrictRestrictIso U V)

@[simp]
theorem forgetToLocallyRingedSpace_map_restrictRestrictIso_hom (U : Opens X)
    (V : Opens (X.restrict U)) :
    forgetToLocallyRingedSpace.map (X.restrictRestrictIso U V).hom =
      (X.toLocallyRingedSpace.restrictRestrictIso U V).hom := (rfl)

@[simp]
theorem forgetToLocallyRingedSpace_map_restrictRestrictIso_inv (U : Opens X)
    (V : Opens (X.restrict U)) :
    forgetToLocallyRingedSpace.map (X.restrictRestrictIso U V).inv =
      (X.toLocallyRingedSpace.restrictRestrictIso U V).inv := (rfl)

/-- Composing `restrictRestrictIso.hom` with `X.ofRestrict (U(V))` gives the composite
inclusion `(X.restrict U).ofRestrict V ≫ X.ofRestrict U`. -/
@[reassoc (attr := simp)]
theorem restrictRestrictIso_hom_ofRestrict (U : Opens X) (V : Opens (X.restrict U)) :
    (X.restrictRestrictIso U V).hom ≫ X.ofRestrict (U.isOpenEmbedding.functor.obj V) =
      (X.restrict U).ofRestrict V ≫ X.ofRestrict U :=
  fullyFaithfulForgetToLocallyRingedSpace.map_injective <| by
    simp only [Functor.map_comp, forgetToLocallyRingedSpace_map_restrictRestrictIso_hom,
      forgetToLocallyRingedSpace_map_ofRestrict]
    exact X.toLocallyRingedSpace.restrictRestrictIso_hom_ofRestrict U V

/-- Composing `restrictRestrictIso.hom` with `X.restrictHomOfLE` gives
`(X.restrict U).ofRestrict V`. -/
@[reassoc (attr := simp)]
theorem restrictRestrictIso_hom_restrictHomOfLE (U : Opens X) (V : Opens (X.restrict U))
    (h : U.isOpenEmbedding.functor.obj V ≤ U := fun _ ⟨x, _, hx⟩ ↦ hx ▸ x.property) :
    (X.restrictRestrictIso U V).hom ≫ X.restrictHomOfLE h = (X.restrict U).ofRestrict V :=
  fullyFaithfulForgetToLocallyRingedSpace.map_injective <| by
    simp only [Functor.map_comp, forgetToLocallyRingedSpace_map_restrictRestrictIso_hom,
      forgetToLocallyRingedSpace_map_restrictHomOfLE, forgetToLocallyRingedSpace_map_ofRestrict]
    exact X.toLocallyRingedSpace.restrictRestrictIso_hom_restrictHomOfLE U V h

/-- Composing `restrictRestrictIso.inv` with `(X.restrict U).ofRestrict V` gives
`X.restrictHomOfLE`. -/
@[reassoc (attr := simp)]
theorem restrictRestrictIso_inv_ofRestrict (U : Opens X) (V : Opens (X.restrict U))
    (h : U.isOpenEmbedding.functor.obj V ≤ U := fun _ ⟨x, _, hx⟩ ↦ hx ▸ x.property) :
    (X.restrictRestrictIso U V).inv ≫ (X.restrict U).ofRestrict V = X.restrictHomOfLE h :=
  fullyFaithfulForgetToLocallyRingedSpace.map_injective <| by
    simp only [Functor.map_comp, forgetToLocallyRingedSpace_map_restrictRestrictIso_inv,
      forgetToLocallyRingedSpace_map_ofRestrict, forgetToLocallyRingedSpace_map_restrictHomOfLE]
    exact X.toLocallyRingedSpace.restrictRestrictIso_inv_ofRestrict U V h

/-- Restricting a global section along `X.ofRestrict U` at `op ⊤` applies `Γ(X, ⊤) → Γ(X, U)`
followed by `restrictTopSectionsIso`. -/
theorem ofRestrict_c_app_top_apply (U : Opens X) (s : X.presheaf.obj (op ⊤)) :
    (forgetToLocallyRingedSpace.map (X.ofRestrict U)).c.app (op ⊤) s =
      (X.toPresheafedSpace.restrictTopSectionsIso U).hom
        (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) := by
  rw [forgetToLocallyRingedSpace_map_ofRestrict]
  exact ConcreteCategory.congr_hom (X.toPresheafedSpace.ofRestrict_c_app_top U) s

end TauCeti.FormalScheme
