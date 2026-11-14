/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import TauCeti.Geometry.RingedSpace.PresheafedSpace.Restrict

import TauCeti.Geometry.RingedSpace.OpenImmersion

/-!
# Inclusions between restrictions of a locally ringed space to nested opens

For opens `V ≤ W` of a locally ringed space `X`, the presheafed-space inclusion `X|_V ⟶ X|_W`
(`AlgebraicGeometry.PresheafedSpace.restrictHomOfLE`) is an open immersion of locally ringed spaces
compatible with the inclusions into `X`. We also record the canonical identification of `Γ(X, U)`
with `Γ(X|_U, ⊤)` and its compatibility with restriction maps.

## Main definitions

* `AlgebraicGeometry.LocallyRingedSpace.restrictHomOfLE`: the open immersion `X|_V ⟶ X|_W` of
  locally ringed spaces for `V ≤ W`.
* `AlgebraicGeometry.LocallyRingedSpace.restrictTopSectionsIso`: the canonical isomorphism
  `Γ(X, U) ≅ Γ(X|_U, ⊤)`.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.restrictHomOfLE_ofRestrict`: composing `X|_V ⟶ X|_W` with
  `X|_W ⟶ X` gives `X|_V ⟶ X`.
* `AlgebraicGeometry.LocallyRingedSpace.restrictHomOfLE_refl`,
  `AlgebraicGeometry.LocallyRingedSpace.restrictHomOfLE_comp`: functoriality of restriction
  inclusions.
* `AlgebraicGeometry.LocallyRingedSpace.ofRestrict_c_app_le`,
  `AlgebraicGeometry.LocallyRingedSpace.restrictTopSectionsIso_hom_restrictHomOfLE_c_app_top`:
  compatibility of `restrictTopSectionsIso` with `ofRestrict` and `restrictHomOfLE`.
-/

public section

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.LocallyRingedSpace

universe u

variable (X : LocallyRingedSpace.{u})

private theorem range_ofRestrict_subset {V W : Opens X} (h : V ≤ W) :
    Set.range (X.ofRestrict V.isOpenEmbedding).base ⊆
      Set.range (X.ofRestrict W.isOpenEmbedding).base := by
  rintro _ ⟨x, rfl⟩
  exact ⟨⟨x.1, h x.2⟩, rfl⟩

private theorem restrictHomOfLE_eq_lift {V W : Opens X} (h : V ≤ W) :
    X.toPresheafedSpace.restrictHomOfLE h =
      (IsOpenImmersion.lift (X.ofRestrict W.isOpenEmbedding)
        (X.ofRestrict V.isOpenEmbedding) (range_ofRestrict_subset X h)).toHom := by
  refine (cancel_mono (X.toPresheafedSpace.ofRestrict W.isOpenEmbedding)).mp ?_
  rw [PresheafedSpace.restrictHomOfLE_ofRestrict]
  exact (congrArg Hom.toHom (IsOpenImmersion.lift_fac (X.ofRestrict W.isOpenEmbedding)
    (X.ofRestrict V.isOpenEmbedding) (range_ofRestrict_subset X h))).symm

/-- Stalk maps of `PresheafedSpace.restrictHomOfLE` are local ring homomorphisms. -/
theorem isLocalHom_restrictHomOfLE {V W : Opens X} (h : V ≤ W)
    (x : X.restrict V.isOpenEmbedding) :
    IsLocalHom ((X.toPresheafedSpace.restrictHomOfLE h).stalkMap x).hom := by
  rw [restrictHomOfLE_eq_lift X h]
  exact (IsOpenImmersion.lift (X.ofRestrict W.isOpenEmbedding)
    (X.ofRestrict V.isOpenEmbedding) (range_ofRestrict_subset X h)).prop x

/-- For opens `V ≤ W` of `X`, the open immersion `X|_V ⟶ X|_W` of locally ringed spaces. -/
@[expose]
def restrictHomOfLE {V W : Opens X} (h : V ≤ W) :
    X.restrict V.isOpenEmbedding ⟶ X.restrict W.isOpenEmbedding where
  toHom := X.toPresheafedSpace.restrictHomOfLE h
  prop := isLocalHom_restrictHomOfLE X h

@[simp]
theorem restrictHomOfLE_toHom {V W : Opens X} (h : V ≤ W) :
    (X.restrictHomOfLE h).toHom = X.toPresheafedSpace.restrictHomOfLE h := (rfl)

theorem restrictHomOfLE_base {V W : Opens X} (h : V ≤ W) :
    (X.restrictHomOfLE h).base = (Opens.toTopCat X.toTopCat).map (homOfLE h) := (rfl)

/-- The inclusion `X|_V ⟶ X|_W` followed by `X|_W ⟶ X` is `X|_V ⟶ X`. -/
@[reassoc (attr := simp)]
theorem restrictHomOfLE_ofRestrict {V W : Opens X} (h : V ≤ W) :
    X.restrictHomOfLE h ≫ X.ofRestrict W.isOpenEmbedding = X.ofRestrict V.isOpenEmbedding :=
  Hom.ext' (X.toPresheafedSpace.restrictHomOfLE_ofRestrict h)

/-- Each inclusion `X|_V ⟶ X|_W` is an open immersion of locally ringed spaces. -/
instance isOpenImmersion_restrictHomOfLE {V W : Opens X} (h : V ≤ W) :
    IsOpenImmersion (X.restrictHomOfLE h) := by
  have heq : X.restrictHomOfLE h =
      IsOpenImmersion.lift (X.ofRestrict W.isOpenEmbedding)
        (X.ofRestrict V.isOpenEmbedding) (range_ofRestrict_subset X h) :=
    Hom.ext' (restrictHomOfLE_eq_lift X h)
  rw [heq]
  infer_instance

/-- The inclusion of a restriction into itself is the identity. -/
@[simp]
theorem restrictHomOfLE_refl (V : Opens X) :
    X.restrictHomOfLE (le_refl V) = 𝟙 (X.restrict V.isOpenEmbedding) :=
  Hom.ext' (X.toPresheafedSpace.restrictHomOfLE_refl V)

/-- Inclusions between restrictions to nested opens compose. -/
@[reassoc (attr := simp)]
theorem restrictHomOfLE_comp {U V W : Opens X} (h : U ≤ V) (k : V ≤ W) :
    X.restrictHomOfLE h ≫ X.restrictHomOfLE k = X.restrictHomOfLE (h.trans k) :=
  Hom.ext' (X.toPresheafedSpace.restrictHomOfLE_comp h k)

/-- The canonical identification `Γ(X, U) ≅ Γ(X|_U, ⊤)` between sections over an open `U` and
global sections of the restricted locally ringed space `X|_U`. -/
def restrictTopSectionsIso (U : Opens X) :
    X.presheaf.obj (op U) ≅ (X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) :=
  X.presheaf.mapIso (eqToIso (congrArg op U.isOpenEmbedding_obj_top.symm))

theorem restrictTopSectionsIso_hom (U : Opens X) :
    (X.restrictTopSectionsIso U).hom =
      X.presheaf.map (eqToHom (congrArg op U.isOpenEmbedding_obj_top.symm)) := (rfl)

theorem restrictTopSectionsIso_inv (U : Opens X) :
    (X.restrictTopSectionsIso U).inv =
      X.presheaf.map (eqToHom (congrArg op U.isOpenEmbedding_obj_top)) := (rfl)

/-- Restricting a section over `W` along `X|_V ⟶ X` (for `V ≤ W`) and then to `⊤` on `X|_V`
is the presheaf restriction `Γ(X, W) ⟶ Γ(X, V)` followed by `restrictTopSectionsIso`. -/
theorem ofRestrict_c_app_le {V W : Opens X} (h : V ≤ W) :
    (X.ofRestrict V.isOpenEmbedding).c.app (op W) ≫
        (X.restrict V.isOpenEmbedding).presheaf.map
          (homOfLE (fun x _ ↦ h x.2 : (⊤ : Opens _) ≤
            (Opens.map (X.ofRestrict V.isOpenEmbedding).base).obj W)).op =
      X.presheaf.map (homOfLE h).op ≫ (X.restrictTopSectionsIso V).hom := by
  have hc : (X.ofRestrict V.isOpenEmbedding).c.app (op W) =
      (X.toPresheafedSpace.ofRestrict V.isOpenEmbedding).c.app (op W) := rfl
  rw [hc, PresheafedSpace.ofRestrict_c_app, restrictTopSectionsIso_hom]
  -- Unfold `PresheafedSpace.restrict` so both sides are compositions of `X.presheaf.map` on opens.
  erw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
  rfl

/-- Under `restrictTopSectionsIso`, the global-section map of `X|_V ⟶ X|_W` is the presheaf
restriction `Γ(X, W) ⟶ Γ(X, V)`. -/
@[reassoc (attr := simp)]
theorem restrictTopSectionsIso_hom_restrictHomOfLE_c_app_top {V W : Opens X} (h : V ≤ W) :
    (X.restrictTopSectionsIso W).hom ≫ (X.restrictHomOfLE h).c.app (op ⊤) =
      X.presheaf.map (homOfLE h).op ≫ (X.restrictTopSectionsIso V).hom := by
  have hc : (X.restrictHomOfLE h).c.app (op ⊤) =
      (X.toPresheafedSpace.restrictHomOfLE h).c.app (op ⊤) := rfl
  rw [restrictTopSectionsIso_hom, restrictTopSectionsIso_hom, hc,
    PresheafedSpace.restrictHomOfLE_c_app]
  -- Unfold `PresheafedSpace.restrict` so both sides are compositions of `X.presheaf.map` on opens.
  erw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
  rfl

end AlgebraicGeometry.LocallyRingedSpace
