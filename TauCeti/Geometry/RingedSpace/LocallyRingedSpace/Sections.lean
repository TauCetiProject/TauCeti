/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace

/-!
# Sections of locally ringed spaces under restriction and composition

This file records general section-map identities for locally ringed spaces:

* `AlgebraicGeometry.LocallyRingedSpace.restrictTopSectionsIso`: the canonical isomorphism
  `Γ(U, O_X) ≅ Γ(⊤, O_{X|_U})` identifying sections over an open `U` with global sections of the
  restriction `X|_U`.
* `AlgebraicGeometry.LocallyRingedSpace.ofRestrict_c_app_comp_eqToHom`: compatibility of
  `ofRestrict.c.app` with `restrictTopSectionsIso`.
* `AlgebraicGeometry.LocallyRingedSpace.comp_c_app_of_map_eq_top` and
  `AlgebraicGeometry.LocallyRingedSpace.comp_c_app_comp_eqToHom_of_map_eq_top`: the factorization of
  the section map `(k ≫ j).c.app (op U)` through `k.c.app (op ⊤)` when `j⁻¹ U = ⊤`.
-/

public section

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.LocallyRingedSpace

universe u

/-- For an open `U` of a locally ringed space `X`, sections of `X` over `U` are canonically
isomorphic to global sections of the restriction `X|_U`. -/
@[expose]
noncomputable def restrictTopSectionsIso (X : LocallyRingedSpace.{u}) (U : Opens X) :
    X.presheaf.obj (op U) ≅ (X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) :=
  X.presheaf.mapIso (eqToIso (congrArg op (Opens.isOpenEmbedding_obj_top U).symm))

/-- For an open `W ≤ U` of `X`, the sheaf component of `X.ofRestrict W` at `U`, transported from
`W⁻¹ U = ⊤` to `⊤`, equals restriction `Γ(U, O_X) → Γ(W, O_X)` followed by
`(X.restrictTopSectionsIso W).hom`. -/
theorem ofRestrict_c_app_comp_eqToHom (X : LocallyRingedSpace.{u}) {W U : Opens X} (hWU : W ≤ U)
    (hpre : (Opens.map (X.ofRestrict W.isOpenEmbedding).base).obj U = ⊤) :
    (X.ofRestrict W.isOpenEmbedding).c.app (op U) ≫
        (X.restrict W.isOpenEmbedding).presheaf.map (eqToHom (congrArg op hpre)) =
      X.presheaf.map (homOfLE hWU).op ≫ (X.restrictTopSectionsIso W).hom := by
  -- `erw`: `ofRestrict.c.app`, `restrict.presheaf.map`, and `restrictTopSectionsIso` all unfold
  -- to `X.presheaf.map` on `Opens X`.
  erw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
  exact congrArg X.presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _))

/-- For morphisms `k : X ⟶ Y` and `j : Y ⟶ Z` of locally ringed spaces and an open `U` of `Z`
whose preimage under `j` is `⊤`, the section map `(k ≫ j).c.app (op U)` factors through
`j.c.app (op U)`, the identification on `⊤`, and `k.c.app (op ⊤)`. -/
theorem comp_c_app_of_map_eq_top {X Y Z : LocallyRingedSpace.{u}} (k : X ⟶ Y) (j : Y ⟶ Z)
    {U : Opens Z} (hU : (Opens.map j.base).obj U = ⊤) :
    (k ≫ j).c.app (op U) = j.c.app (op U) ≫ Y.presheaf.map (eqToHom (congrArg op hU)) ≫
      k.c.app (op ⊤) ≫ X.presheaf.map (eqToHom (congrArg op (by
        rw [comp_base, Opens.map_comp_obj, hU, Opens.map_top]))) := by
  have hU' : (Opens.map k.base).obj ⊤ = (Opens.map k.base).obj ((Opens.map j.base).obj U) :=
    congrArg (Opens.map k.base).obj hU.symm
  rw [comp_c_app]
  refine congrArg (j.c.app (op U) ≫ ·) ?_
  rw [← Category.assoc, k.c.naturality (eqToHom (congrArg op hU)), Category.assoc]
  have hmap : ((TopCat.Presheaf.pushforward CommRingCat k.base).obj X.presheaf).map
        (eqToHom (congrArg op hU)) ≫ X.presheaf.map (eqToHom (congrArg op hU')) = 𝟙 _ := by
    have hid : (Opens.map k.base).op.map (eqToHom (congrArg op hU)) ≫
        eqToHom (congrArg op hU') = 𝟙 _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    -- `erw`: `pushforward` functor map unfolds to `X.presheaf.map` on `(Opens.map k.base).op.map`.
    erw [← X.presheaf.map_comp, hid, X.presheaf.map_id]; rfl
  exact (Category.comp_id _).symm.trans (congrArg (k.c.app _ ≫ ·) hmap.symm)

/-- Variant of `comp_c_app_of_map_eq_top` absorbing the trailing restriction back to `⊤`. -/
theorem comp_c_app_comp_eqToHom_of_map_eq_top {X Y Z : LocallyRingedSpace.{u}}
    (k : X ⟶ Y) (j : Y ⟶ Z) {U : Opens Z} (hU : (Opens.map j.base).obj U = ⊤)
    (hkj : (Opens.map (k ≫ j).base).obj U = ⊤) :
    (k ≫ j).c.app (op U) ≫ X.presheaf.map (eqToHom (congrArg op hkj)) =
      j.c.app (op U) ≫ Y.presheaf.map (eqToHom (congrArg op hU)) ≫ k.c.app (op ⊤) := by
  rw [comp_c_app_of_map_eq_top k j hU, Category.assoc, Category.assoc, Category.assoc,
    ← X.presheaf.map_comp]
  -- `erw`: `(Opens.map k.base).obj ⊤` is defeq to `⊤` (`Opens.map_top`), matching `k.c.app (op ⊤)`.
  erw [(Quiver.Hom.unop_inj (Subsingleton.elim _ _) :
    eqToHom _ ≫ eqToHom (congrArg op hkj) = 𝟙 (op ((Opens.map k.base).obj ⊤))),
    X.presheaf.map_id, Category.comp_id]; rfl

end AlgebraicGeometry.LocallyRingedSpace
