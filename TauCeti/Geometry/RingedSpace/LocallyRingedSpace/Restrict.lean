/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.ResidueField
public import TauCeti.Geometry.RingedSpace.PresheafedSpace.Restrict

import TauCeti.Geometry.RingedSpace.OpenImmersion
import TauCeti.Topology.Sheaves.Presheaf

/-!
# Inclusions between restrictions of a locally ringed space to nested opens

For opens `V ≤ W` of a locally ringed space `X`, `AlgebraicGeometry.PresheafedSpace.restrictHomOfLE`
lifts to an open immersion `X|_V ⟶ X|_W` of locally ringed spaces compatible with `ofRestrict`. We
also record the isomorphism `Γ(X, U) ≅ Γ(X|_U, ⊤)` and its compatibility with restrictions,
isomorphisms on global sections, factorizations, and residue-field evaluation.

## Main definitions

* `AlgebraicGeometry.LocallyRingedSpace.restrictHomOfLE`: the open immersion `X|_V ⟶ X|_W` for
  `V ≤ W`.
* `AlgebraicGeometry.LocallyRingedSpace.restrictTopSectionsIso`: the isomorphism
  `Γ(X, U) ≅ Γ(X|_U, ⊤)`.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.restrictHomOfLE_ofRestrict`,
  `AlgebraicGeometry.LocallyRingedSpace.restrictHomOfLE_refl`,
  `AlgebraicGeometry.LocallyRingedSpace.restrictHomOfLE_comp`: functoriality and compatibility with
  `ofRestrict`.
* `AlgebraicGeometry.LocallyRingedSpace.iso_inv_c_app_top_comp_hom`,
  `AlgebraicGeometry.LocallyRingedSpace.iso_hom_c_app_top_comp_inv`: global-section cancellations
  for an isomorphism of locally ringed spaces.
* `AlgebraicGeometry.LocallyRingedSpace.ofRestrict_c_app_le`,
  `AlgebraicGeometry.LocallyRingedSpace.ofRestrict_c_app_self`,
  `AlgebraicGeometry.LocallyRingedSpace.ofRestrict_c_app_top`,
  `AlgebraicGeometry.LocallyRingedSpace.restrictTopSectionsIso_hom_restrictHomOfLE_c_app_top`,
  `AlgebraicGeometry.LocallyRingedSpace.restrictTopSectionsIso_hom_c_app_top_of_fac_le`,
  `AlgebraicGeometry.LocallyRingedSpace.restrictTopSectionsIso_hom_c_app_top_of_fac`,
  `AlgebraicGeometry.LocallyRingedSpace.evaluation_eq_zero_iff_restrict_Γevaluation_eq_zero`:
  compatibility of `restrictTopSectionsIso` with `ofRestrict`, `restrictHomOfLE`, morphisms, and
  residue-field evaluation.
-/

public section

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.LocallyRingedSpace

universe u

variable (X : LocallyRingedSpace.{u})

private theorem range_ofRestrict_subset {V W : Opens X} (h : V ≤ W) :
    Set.range (X.ofRestrict V.isOpenEmbedding).base ⊆
      Set.range (X.ofRestrict W.isOpenEmbedding).base := by
  rintro _ ⟨x, rfl⟩; exact ⟨⟨x.1, h x.2⟩, rfl⟩

private theorem restrictHomOfLE_eq_lift {V W : Opens X} (h : V ≤ W) :
    X.toPresheafedSpace.restrictHomOfLE h =
      (IsOpenImmersion.lift (X.ofRestrict W.isOpenEmbedding)
        (X.ofRestrict V.isOpenEmbedding) (range_ofRestrict_subset X h)).toHom :=
  (cancel_mono (X.toPresheafedSpace.ofRestrict W.isOpenEmbedding)).mp <|
    (PresheafedSpace.restrictHomOfLE_ofRestrict _ h).trans
      (congrArg Hom.toHom (IsOpenImmersion.lift_fac (X.ofRestrict W.isOpenEmbedding)
        (X.ofRestrict V.isOpenEmbedding) (range_ofRestrict_subset X h))).symm

/-- Stalk maps of `PresheafedSpace.restrictHomOfLE` are local ring homomorphisms. -/
theorem isLocalHom_restrictHomOfLE {V W : Opens X} (h : V ≤ W)
    (x : X.restrict V.isOpenEmbedding) :
    IsLocalHom ((X.toPresheafedSpace.restrictHomOfLE h).stalkMap x).hom := by
  rw [restrictHomOfLE_eq_lift X h]
  exact (IsOpenImmersion.lift _ _ (range_ofRestrict_subset X h)).prop x

/-- For opens `V ≤ W` of `X`, the open immersion `X|_V ⟶ X|_W` of locally ringed spaces. -/
def restrictHomOfLE {V W : Opens X} (h : V ≤ W) :
    X.restrict V.isOpenEmbedding ⟶ X.restrict W.isOpenEmbedding :=
  ⟨X.toPresheafedSpace.restrictHomOfLE h, isLocalHom_restrictHomOfLE X h⟩

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
  rw [show X.restrictHomOfLE h = _ from Hom.ext' (restrictHomOfLE_eq_lift X h)]; infer_instance

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

/-- Global-section maps of an isomorphism of locally ringed spaces cancel on the left. -/
@[reassoc (attr := simp)]
theorem iso_inv_c_app_top_comp_hom {Y₁ Y₂ : LocallyRingedSpace.{u}} (e : Y₁ ≅ Y₂) :
    (e.inv.c.app (op ⊤) : Y₁.presheaf.obj (op ⊤) ⟶ Y₂.presheaf.obj (op ⊤)) ≫
        e.hom.c.app (op ⊤) =
      𝟙 (Y₁.presheaf.obj (op ⊤)) :=
  (LocallyRingedSpace.Γ.map_comp e.inv.op e.hom.op).symm.trans <|
    (congrArg LocallyRingedSpace.Γ.map (congrArg Quiver.Hom.op e.hom_inv_id)).trans
      (LocallyRingedSpace.Γ.map_id _)

/-- Global-section maps of an isomorphism of locally ringed spaces cancel on the right. -/
@[reassoc (attr := simp)]
theorem iso_hom_c_app_top_comp_inv {Y₁ Y₂ : LocallyRingedSpace.{u}} (e : Y₁ ≅ Y₂) :
    (e.hom.c.app (op ⊤) : Y₂.presheaf.obj (op ⊤) ⟶ Y₁.presheaf.obj (op ⊤)) ≫
        e.inv.c.app (op ⊤) =
      𝟙 (Y₂.presheaf.obj (op ⊤)) :=
  iso_inv_c_app_top_comp_hom e.symm

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
      X.presheaf.map (homOfLE h).op ≫ (X.restrictTopSectionsIso V).hom :=
  (X.presheaf.map_comp _ _).symm.trans <|
    (congrArg X.presheaf.map (Subsingleton.elim _ _)).trans (X.presheaf.map_comp _ _)

/-- Restricting a section over `U` along `X|_U ⟶ X` and then to `⊤` on `X|_U` is
`restrictTopSectionsIso`. -/
@[reassoc]
theorem ofRestrict_c_app_self (U : Opens X) :
    (X.ofRestrict U.isOpenEmbedding).c.app (op U) ≫
        (X.restrict U.isOpenEmbedding).presheaf.map
          (homOfLE (fun x _ ↦ x.2 : (⊤ : Opens _) ≤
            (Opens.map (X.ofRestrict U.isOpenEmbedding).base).obj U)).op =
      (X.restrictTopSectionsIso U).hom := by
  rw [X.ofRestrict_c_app_le (le_refl U), TopCat.Presheaf.map_eq_id, Category.id_comp]

/-- Restricting a global section along `X|_U ⟶ X` at `op ⊤` is the presheaf restriction
`Γ(X, ⊤) ⟶ Γ(X, U)` followed by `restrictTopSectionsIso`. -/
@[simp, reassoc]
theorem ofRestrict_c_app_top (U : Opens X) :
    ((X.ofRestrict U.isOpenEmbedding).c.app (op ⊤) :
        X.presheaf.obj (op ⊤) ⟶ (X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) =
      X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ (X.restrictTopSectionsIso U).hom :=
  (Category.comp_id _).symm.trans <|
    (congrArg (_ ≫ ·) (TopCat.Presheaf.map_eq_id (X.restrict U.isOpenEmbedding).presheaf
      (homOfLE (fun _ _ ↦ trivial : (⊤ : Opens _) ≤
        (Opens.map (X.ofRestrict U.isOpenEmbedding).base).obj ⊤)).op).symm).trans
      (X.ofRestrict_c_app_le le_top)

/-- Under `restrictTopSectionsIso`, the global-section map of `X|_V ⟶ X|_W` is the presheaf
restriction `Γ(X, W) ⟶ Γ(X, V)`. -/
@[reassoc (attr := simp)]
theorem restrictTopSectionsIso_hom_restrictHomOfLE_c_app_top {V W : Opens X} (h : V ≤ W) :
    (X.restrictTopSectionsIso W).hom ≫ (X.restrictHomOfLE h).c.app (op ⊤) =
      X.presheaf.map (homOfLE h).op ≫ (X.restrictTopSectionsIso V).hom :=
  (X.presheaf.map_comp _ _).symm.trans <|
    (congrArg X.presheaf.map (Subsingleton.elim _ _)).trans (X.presheaf.map_comp _ _)

/-- If `l : Z ⟶ Y|_V` and `h : Z ⟶ X|_U` satisfy `l ≫ Y|_V = h ≫ X|_U ≫ f` with `V ≤ W` and
`U ≤ f⁻¹ W`, then under `restrictTopSectionsIso` the restriction `Γ(Y, W) ⟶ Γ(Y, V) ⟶ Γ(Z, ⊤)`
equals `f.c.app (op W)` followed by `Γ(X, f⁻¹ W) ⟶ Γ(X, U) ⟶ Γ(Z, ⊤)`. -/
@[reassoc]
theorem restrictTopSectionsIso_hom_c_app_top_of_fac_le {X Y Z : LocallyRingedSpace.{u}}
    (f : X ⟶ Y) {V W : Opens Y} (hVW : V ≤ W) {U : Opens X}
    (hUW : U ≤ (Opens.map f.base).obj W)
    (l : Z ⟶ Y.restrict V.isOpenEmbedding) (h : Z ⟶ X.restrict U.isOpenEmbedding)
    (hfac : l ≫ Y.ofRestrict V.isOpenEmbedding = h ≫ X.ofRestrict U.isOpenEmbedding ≫ f) :
    Y.presheaf.map (homOfLE hVW).op ≫ (Y.restrictTopSectionsIso V).hom ≫
        (l.c.app (op ⊤) : (Y.restrict V.isOpenEmbedding).presheaf.obj (op ⊤) ⟶
          Z.presheaf.obj (op ⊤)) =
      f.c.app (op W) ≫ X.presheaf.map (homOfLE hUW).op ≫ (X.restrictTopSectionsIso U).hom ≫
        (h.c.app (op ⊤) : (X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) ⟶
          Z.presheaf.obj (op ⊤)) := by
  let jU := X.ofRestrict U.isOpenEmbedding
  let jV := Y.ofRestrict V.isOpenEmbedding
  have hleV : (⊤ : Opens _) ≤ (Opens.map jV.base).obj W := fun y _ ↦ hVW y.2
  have hleU : (⊤ : Opens _) ≤ (Opens.map jU.base).obj ((Opens.map f.base).obj W) :=
    fun x _ ↦ hUW x.2
  have hleZ₁ : (⊤ : Opens _) ≤ (Opens.map (l ≫ jV).base).obj W := fun z _ ↦ hVW (l.base z).2
  have hleZ₂ : (⊤ : Opens _) ≤ (Opens.map (h ≫ jU ≫ f).base).obj W := fun z _ ↦ hUW (h.base z).2
  have hmid : ∀ {k₁ k₂ : Z ⟶ Y} (_ : k₁ = k₂)
      (h₁ : (⊤ : Opens _) ≤ (Opens.map k₁.base).obj W)
      (h₂ : (⊤ : Opens _) ≤ (Opens.map k₂.base).obj W),
      k₁.c.app (op W) ≫ Z.presheaf.map (homOfLE h₁).op =
        k₂.c.app (op W) ≫ Z.presheaf.map (homOfLE h₂).op := by
    rintro k _ rfl _ _; rfl
  have hlhs : (l ≫ jV).c.app (op W) ≫ Z.presheaf.map (homOfLE hleZ₁).op =
      Y.presheaf.map (homOfLE hVW).op ≫ (Y.restrictTopSectionsIso V).hom ≫ l.c.app (op ⊤) := by
    have hnat : l.c.app (op ((Opens.map jV.base).obj W)) ≫ Z.presheaf.map (homOfLE hleZ₁).op =
        (Y.restrict V.isOpenEmbedding).presheaf.map (homOfLE hleV).op ≫ l.c.app (op ⊤) :=
      (congrArg (_ ≫ Z.presheaf.map ·) (Subsingleton.elim _ _)).trans
        (l.c.naturality (homOfLE hleV).op).symm
    exact (Category.assoc _ _ _).trans <| (congrArg (jV.c.app (op W) ≫ ·) hnat).trans <|
      (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ l.c.app (op ⊤)) (Y.ofRestrict_c_app_le hVW)).trans (Category.assoc _ _ _)
  have hrhs : (h ≫ jU ≫ f).c.app (op W) ≫ Z.presheaf.map (homOfLE hleZ₂).op =
      f.c.app (op W) ≫ X.presheaf.map (homOfLE hUW).op ≫ (X.restrictTopSectionsIso U).hom ≫
        h.c.app (op ⊤) := by
    have hnat : h.c.app (op ((Opens.map (jU ≫ f).base).obj W)) ≫ Z.presheaf.map (homOfLE hleZ₂).op =
        (X.restrict U.isOpenEmbedding).presheaf.map (homOfLE hleU).op ≫ h.c.app (op ⊤) :=
      (congrArg (_ ≫ Z.presheaf.map ·) (Subsingleton.elim _ _)).trans
        (h.c.naturality (homOfLE hleU).op).symm
    exact (Category.assoc _ _ _).trans <| (Category.assoc _ _ _).trans <|
      congrArg (f.c.app (op W) ≫ ·) <| (Category.assoc _ _ _).trans <|
        (congrArg (jU.c.app (op ((Opens.map f.base).obj W)) ≫ ·) hnat).trans <|
          (Category.assoc _ _ _).symm.trans <|
            (congrArg (· ≫ h.c.app (op ⊤)) (X.ofRestrict_c_app_le hUW)).trans (Category.assoc _ _ _)
  exact hlhs.symm.trans ((hmid hfac hleZ₁ hleZ₂).trans hrhs)

/-- If `fUV : X|_U ⟶ Y|_V` restricts `f : X ⟶ Y` (so `fUV ≫ Y|_V = X|_U ≫ f`), then under
`restrictTopSectionsIso` the global-section map of `fUV` is `f.c.app (op V)` followed by
restriction `Γ(X, f⁻¹ V) ⟶ Γ(X, U)`. -/
@[reassoc]
theorem restrictTopSectionsIso_hom_c_app_top_of_fac {X Y : LocallyRingedSpace.{u}}
    (f : X ⟶ Y) {V : Opens Y} {U : Opens X} (hUV : U ≤ (Opens.map f.base).obj V)
    (fUV : X.restrict U.isOpenEmbedding ⟶ Y.restrict V.isOpenEmbedding)
    (hfac : fUV ≫ Y.ofRestrict V.isOpenEmbedding = X.ofRestrict U.isOpenEmbedding ≫ f) :
    (Y.restrictTopSectionsIso V).hom ≫
        (fUV.c.app (op ⊤) : (Y.restrict V.isOpenEmbedding).presheaf.obj (op ⊤) ⟶
          (X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) =
      f.c.app (op V) ≫ X.presheaf.map (homOfLE hUV).op ≫ (X.restrictTopSectionsIso U).hom := by
  have h := restrictTopSectionsIso_hom_c_app_top_of_fac_le f (le_refl V) hUV fUV (𝟙 _)
    (hfac.trans (Category.id_comp _).symm)
  rw [TopCat.Presheaf.map_eq_id, Category.id_comp] at h
  exact h.trans <| congrArg (_ ≫ _ ≫ ·) <|
    (congrArg (_ ≫ ·) (LocallyRingedSpace.Γ.map_id _)).trans (Category.comp_id _)

/-- A section `s ∈ Γ(X, U)` vanishes in the residue field of `X` at `x ∈ U` if and only if its
image under `restrictTopSectionsIso U` vanishes in the residue field of `X|_U` at `x`. -/
theorem evaluation_eq_zero_iff_restrict_Γevaluation_eq_zero (U : Opens X) (x : U)
    (s : X.presheaf.obj (op U)) :
    X.evaluation x s = 0 ↔
      (X.restrict U.isOpenEmbedding).Γevaluation x ((X.restrictTopSectionsIso U).hom s) = 0 := by
  let j := X.ofRestrict U.isOpenEmbedding
  let x' : (Opens.map j.base).obj U := ⟨x, x.2⟩
  have hle : (⊤ : Opens (X.restrict U.isOpenEmbedding)) ≤ (Opens.map j.base).obj U := fun y _ ↦ y.2
  have hres : (X.restrict U.isOpenEmbedding).evaluation x' (j.c.app (op U) s) =
      (X.restrict U.isOpenEmbedding).Γevaluation x ((X.restrictTopSectionsIso U).hom s) := by
    rw [← ofRestrict_c_app_self X U, ConcreteCategory.comp_apply]
    exact (congrArg ((X.restrict U.isOpenEmbedding).residue x)
      (TopCat.Presheaf.germ_res_apply (X.restrict U.isOpenEmbedding).presheaf
        (homOfLE hle) x trivial (j.c.app (op U) s))).symm
  exact ((residueFieldMap j x'.1).hom.map_eq_zero_iff).symm.trans
    (congrArg (· = 0) ((evaluation_naturality_apply j x' s).trans hres)).to_iff

end AlgebraicGeometry.LocallyRingedSpace
