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
lifts to an open immersion `restrictHomOfLE : X|_V ⟶ X|_W` of locally ringed spaces compatible with
`ofRestrict` and functorial in inclusions. We also record global-section cancellations for
isomorphisms (`iso_inv_c_app_top_comp_hom`, `iso_hom_c_app_top_comp_inv`) and the canonical
isomorphism `restrictTopSectionsIso : Γ(X, U) ≅ Γ(X|_U, ⊤)` together with its compatibilities with
restrictions (`ofRestrict_c_app_le`, `ofRestrict_c_app_self`, `ofRestrict_c_app_top`,
`comp_ofRestrict_c_app_le`), nested opens, factorizations
(`restrictTopSectionsIso_hom_c_app_top_of_fac_le`, `restrictTopSectionsIso_hom_c_app_top_of_fac`),
and residue evaluation.
-/

public section

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.LocallyRingedSpace

universe u

variable (X : LocallyRingedSpace.{u})

private theorem range_ofRestrict_subset {V W : Opens X} (h : V ≤ W) :
    Set.range (X.ofRestrict V.isOpenEmbedding).base ⊆
      Set.range (X.ofRestrict W.isOpenEmbedding).base :=
  fun _ ⟨x, hx⟩ ↦ ⟨⟨x.1, h x.2⟩, hx⟩

private theorem restrictHomOfLE_eq_lift {V W : Opens X} (h : V ≤ W) :
    X.toPresheafedSpace.restrictHomOfLE h = (IsOpenImmersion.lift (X.ofRestrict W.isOpenEmbedding)
        (X.ofRestrict V.isOpenEmbedding) (range_ofRestrict_subset X h)).toHom :=
  (cancel_mono (X.toPresheafedSpace.ofRestrict W.isOpenEmbedding)).mp <|
    (PresheafedSpace.restrictHomOfLE_ofRestrict _ h).trans
      (congrArg Hom.toHom (IsOpenImmersion.lift_fac (X.ofRestrict W.isOpenEmbedding)
        (X.ofRestrict V.isOpenEmbedding) (range_ofRestrict_subset X h))).symm

/-- Stalk maps of `PresheafedSpace.restrictHomOfLE` are local ring homomorphisms. -/
theorem isLocalHom_restrictHomOfLE {V W : Opens X} (h : V ≤ W) (x : X.restrict V.isOpenEmbedding) :
    IsLocalHom ((X.toPresheafedSpace.restrictHomOfLE h).stalkMap x).hom := by
  rw [restrictHomOfLE_eq_lift X h]; exact (IsOpenImmersion.lift _ _ _).prop x

/-- For opens `V ≤ W` of `X`, the open immersion `X|_V ⟶ X|_W` of locally ringed spaces. -/
def restrictHomOfLE {V W : Opens X} (h : V ≤ W) :
    X.restrict V.isOpenEmbedding ⟶ X.restrict W.isOpenEmbedding :=
  ⟨X.toPresheafedSpace.restrictHomOfLE h, isLocalHom_restrictHomOfLE X h⟩

@[simp] theorem restrictHomOfLE_toHom {V W : Opens X} (h : V ≤ W) :
    (X.restrictHomOfLE h).toHom = X.toPresheafedSpace.restrictHomOfLE h := (rfl)
theorem restrictHomOfLE_base {V W : Opens X} (h : V ≤ W) :
    (X.restrictHomOfLE h).base = (Opens.toTopCat X.toTopCat).map (homOfLE h) := (rfl)

/-- The inclusion `X|_V ⟶ X|_W` followed by `X|_W ⟶ X` is `X|_V ⟶ X`. -/
@[reassoc (attr := simp)] theorem restrictHomOfLE_ofRestrict {V W : Opens X} (h : V ≤ W) :
    X.restrictHomOfLE h ≫ X.ofRestrict W.isOpenEmbedding = X.ofRestrict V.isOpenEmbedding :=
  Hom.ext' (X.toPresheafedSpace.restrictHomOfLE_ofRestrict h)

/-- Each inclusion `X|_V ⟶ X|_W` is an open immersion of locally ringed spaces. -/
instance isOpenImmersion_restrictHomOfLE {V W : Opens X} (h : V ≤ W) :
    IsOpenImmersion (X.restrictHomOfLE h) := by
  have heq : X.restrictHomOfLE h = IsOpenImmersion.lift (X.ofRestrict W.isOpenEmbedding)
      (X.ofRestrict V.isOpenEmbedding) (range_ofRestrict_subset X h) :=
    Hom.ext' (restrictHomOfLE_eq_lift X h)
  rw [heq]; infer_instance

/-- The inclusion of a restriction into itself is the identity. -/
@[simp] theorem restrictHomOfLE_refl (V : Opens X) :
    X.restrictHomOfLE (le_refl V) = 𝟙 (X.restrict V.isOpenEmbedding) :=
  Hom.ext' (X.toPresheafedSpace.restrictHomOfLE_refl V)

/-- Inclusions between restrictions to nested opens compose. -/
@[reassoc (attr := simp)] theorem restrictHomOfLE_comp {U V W : Opens X} (h : U ≤ V) (k : V ≤ W) :
    X.restrictHomOfLE h ≫ X.restrictHomOfLE k = X.restrictHomOfLE (h.trans k) :=
  Hom.ext' (X.toPresheafedSpace.restrictHomOfLE_comp h k)

/-- Global-section maps of an isomorphism of locally ringed spaces cancel on the left. -/
@[reassoc (attr := simp)]
theorem iso_inv_c_app_top_comp_hom {Y₁ Y₂ : LocallyRingedSpace.{u}} (e : Y₁ ≅ Y₂) :
    (e.inv.c.app (op ⊤) : Y₁.presheaf.obj (op ⊤) ⟶ Y₂.presheaf.obj (op ⊤)) ≫ e.hom.c.app (op ⊤) =
      𝟙 (Y₁.presheaf.obj (op ⊤)) := by
  have h := LocallyRingedSpace.Γ.map_comp e.inv.op e.hom.op
  rw [← op_comp, e.hom_inv_id, op_id, LocallyRingedSpace.Γ.map_id] at h; exact h.symm

/-- Global-section maps of an isomorphism of locally ringed spaces cancel on the right. -/
@[reassoc (attr := simp)]
theorem iso_hom_c_app_top_comp_inv {Y₁ Y₂ : LocallyRingedSpace.{u}} (e : Y₁ ≅ Y₂) :
    (e.hom.c.app (op ⊤) : Y₂.presheaf.obj (op ⊤) ⟶ Y₁.presheaf.obj (op ⊤)) ≫ e.inv.c.app (op ⊤) =
      𝟙 (Y₂.presheaf.obj (op ⊤)) :=
  iso_inv_c_app_top_comp_hom e.symm

/-- The canonical identification `Γ(X, U) ≅ Γ(X|_U, ⊤)` between sections over an open `U` and
global sections of the restricted locally ringed space `X|_U`. -/
def restrictTopSectionsIso (U : Opens X) :
    X.presheaf.obj (op U) ≅ (X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) :=
  X.presheaf.mapIso (eqToIso (congrArg op U.isOpenEmbedding_obj_top.symm))

theorem restrictTopSectionsIso_hom (U : Opens X) : (X.restrictTopSectionsIso U).hom =
    X.presheaf.map (eqToHom (congrArg op U.isOpenEmbedding_obj_top.symm)) := (rfl)
theorem restrictTopSectionsIso_inv (U : Opens X) : (X.restrictTopSectionsIso U).inv =
    X.presheaf.map (eqToHom (congrArg op U.isOpenEmbedding_obj_top)) := (rfl)

/-- Restricting a section over `W` along `X|_V ⟶ X` (for `V ≤ W`) and then to `⊤` on `X|_V`
is the presheaf restriction `Γ(X, W) ⟶ Γ(X, V)` followed by `restrictTopSectionsIso`. -/
@[reassoc] theorem ofRestrict_c_app_le {V W : Opens X} (h : V ≤ W) :
    (X.ofRestrict V.isOpenEmbedding).c.app (op W) ≫ (X.restrict V.isOpenEmbedding).presheaf.map
        (homOfLE (fun x _ ↦ h x.2 : (⊤ : Opens _) ≤
          (Opens.map (X.ofRestrict V.isOpenEmbedding).base).obj W)).op =
      X.presheaf.map (homOfLE h).op ≫ (X.restrictTopSectionsIso V).hom := by
  -- `ofRestrict.c` and `restrict.presheaf.map` are `X.presheaf.map` up to unfolding `restrict`.
  erw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
  exact congrArg X.presheaf.map (Subsingleton.elim _ _)

/-- Restricting a section over `U` along `X|_U ⟶ X` and then to `⊤` on `X|_U` is
`restrictTopSectionsIso`. -/
@[reassoc] theorem ofRestrict_c_app_self (U : Opens X) :
    (X.ofRestrict U.isOpenEmbedding).c.app (op U) ≫ (X.restrict U.isOpenEmbedding).presheaf.map
        (homOfLE (fun x _ ↦ x.2 : (⊤ : Opens _) ≤
          (Opens.map (X.ofRestrict U.isOpenEmbedding).base).obj U)).op =
      (X.restrictTopSectionsIso U).hom := by
  simpa using X.ofRestrict_c_app_le (le_refl U)

/-- Restricting a global section along `X|_U ⟶ X` at `op ⊤` is the presheaf restriction
`Γ(X, ⊤) ⟶ Γ(X, U)` followed by `restrictTopSectionsIso`. -/
@[simp, reassoc] theorem ofRestrict_c_app_top (U : Opens X) :
    ((X.ofRestrict U.isOpenEmbedding).c.app (op ⊤) :
        X.presheaf.obj (op ⊤) ⟶ (X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) =
      X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ (X.restrictTopSectionsIso U).hom := by
  have h := X.ofRestrict_c_app_le (V := U) (W := ⊤) le_top
  -- `Opens.map _ ⊤ = ⊤`, so the restriction map on the restricted space is the identity.
  erw [TopCat.Presheaf.map_eq_id, Category.comp_id] at h; exact h

/-- Under `restrictTopSectionsIso`, the global-section map of `X|_V ⟶ X|_W` is the presheaf
restriction `Γ(X, W) ⟶ Γ(X, V)`. -/
@[reassoc (attr := simp)]
theorem restrictTopSectionsIso_hom_restrictHomOfLE_c_app_top {V W : Opens X} (h : V ≤ W) :
    (X.restrictTopSectionsIso W).hom ≫ (X.restrictHomOfLE h).c.app (op ⊤) =
      X.presheaf.map (homOfLE h).op ≫ (X.restrictTopSectionsIso V).hom := by
  -- Both sides are composites of `X.presheaf.map` up to unfolding `restrictHomOfLE`.
  erw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
  exact congrArg X.presheaf.map (Subsingleton.elim _ _)

/-- For `k : Z ⟶ X|_U` and opens `U ≤ W`, restricting a section over `W` along
`k ≫ X.ofRestrict U` and then to `⊤` on `Z` factors as
`Γ(X, W) ⟶ Γ(X, U) ≅ Γ(X|_U, ⊤) ⟶ Γ(Z, ⊤)`. -/
@[reassoc] theorem comp_ofRestrict_c_app_le {X Z : LocallyRingedSpace.{u}} {U W : Opens X}
    (hUW : U ≤ W) (k : Z ⟶ X.restrict U.isOpenEmbedding)
    (hleZ : (⊤ : Opens Z) ≤ (Opens.map (k ≫ X.ofRestrict U.isOpenEmbedding).base).obj W) :
    (k ≫ X.ofRestrict U.isOpenEmbedding).c.app (op W) ≫ Z.presheaf.map (homOfLE hleZ).op =
      X.presheaf.map (homOfLE hUW).op ≫ (X.restrictTopSectionsIso U).hom ≫ k.c.app (op ⊤) := by
  have hleU : (⊤ : Opens _) ≤ (Opens.map (X.ofRestrict U.isOpenEmbedding).base).obj W :=
    fun x _ ↦ hUW x.2
  have hnat : k.c.app (op ((Opens.map (X.ofRestrict U.isOpenEmbedding).base).obj W)) ≫
        Z.presheaf.map (homOfLE hleZ).op =
      (X.restrict U.isOpenEmbedding).presheaf.map (homOfLE hleU).op ≫ k.c.app (op ⊤) := by
    have hn := (k.c.naturality (homOfLE hleU).op).symm
    -- `homOfLE hleZ` and `(Opens.map k.base).map (homOfLE hleU)` are equal up to `pushforward`.
    erw [← hn]; exact congrArg (_ ≫ Z.presheaf.map ·) (Subsingleton.elim _ _)
  -- Unfold composition of `LocallyRingedSpace` morphisms on `c.app`, then rewrite by `hnat`.
  erw [Category.assoc, hnat, X.ofRestrict_c_app_le_assoc hUW]; rfl

/-- Compatibility of `restrictTopSectionsIso` with factorizations `l ≫ Y|_V = h ≫ X|_U ≫ f`
for opens `V ≤ W` and `U ≤ f⁻¹ W`. -/
@[reassoc] theorem restrictTopSectionsIso_hom_c_app_top_of_fac_le {X Y Z : LocallyRingedSpace.{u}}
    (f : X ⟶ Y) {V W : Opens Y} (hVW : V ≤ W) {U : Opens X} (hUW : U ≤ (Opens.map f.base).obj W)
    (l : Z ⟶ Y.restrict V.isOpenEmbedding) (h : Z ⟶ X.restrict U.isOpenEmbedding)
    (hfac : l ≫ Y.ofRestrict V.isOpenEmbedding = h ≫ X.ofRestrict U.isOpenEmbedding ≫ f) :
    Y.presheaf.map (homOfLE hVW).op ≫ (Y.restrictTopSectionsIso V).hom ≫
        (l.c.app (op ⊤) : (Y.restrict V.isOpenEmbedding).presheaf.obj (op ⊤) ⟶
          Z.presheaf.obj (op ⊤)) =
      f.c.app (op W) ≫ X.presheaf.map (homOfLE hUW).op ≫ (X.restrictTopSectionsIso U).hom ≫
        (h.c.app (op ⊤) : (X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) ⟶
          Z.presheaf.obj (op ⊤)) := by
  have hmid : ∀ {k₁ k₂ : Z ⟶ Y} (_ : k₁ = k₂)
      (h₁ : (⊤ : Opens _) ≤ (Opens.map k₁.base).obj W)
      (h₂ : (⊤ : Opens _) ≤ (Opens.map k₂.base).obj W),
      k₁.c.app (op W) ≫ Z.presheaf.map (homOfLE h₁).op =
        k₂.c.app (op W) ≫ Z.presheaf.map (homOfLE h₂).op := by rintro k _ rfl _ _; rfl
  have hleZ₁ : (⊤ : Opens _) ≤ (Opens.map (l ≫ Y.ofRestrict V.isOpenEmbedding).base).obj W :=
    fun z _ ↦ hVW (l.base z).2
  have hleZ₂ : (⊤ : Opens _) ≤ (Opens.map ((h ≫ X.ofRestrict U.isOpenEmbedding) ≫ f).base).obj W :=
    fun z _ ↦ hUW (h.base z).2
  rw [← comp_ofRestrict_c_app_le hVW l hleZ₁, hmid (by rw [hfac, Category.assoc]) hleZ₁ hleZ₂]
  -- Reassociate `((h ≫ X|_U) ≫ f).c.app` past `f.c.app` up to `pushforward` unfolding.
  erw [Category.assoc, comp_ofRestrict_c_app_le hUW h hleZ₂]; rfl

/-- Compatibility of `restrictTopSectionsIso` with a restriction `fUV ≫ Y|_V = X|_U ≫ f`. -/
@[reassoc] theorem restrictTopSectionsIso_hom_c_app_top_of_fac {X Y : LocallyRingedSpace.{u}}
    (f : X ⟶ Y) {V : Opens Y} {U : Opens X} (hUV : U ≤ (Opens.map f.base).obj V)
    (fUV : X.restrict U.isOpenEmbedding ⟶ Y.restrict V.isOpenEmbedding)
    (hfac : fUV ≫ Y.ofRestrict V.isOpenEmbedding = X.ofRestrict U.isOpenEmbedding ≫ f) :
    (Y.restrictTopSectionsIso V).hom ≫
        (fUV.c.app (op ⊤) : (Y.restrict V.isOpenEmbedding).presheaf.obj (op ⊤) ⟶
          (X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) =
      f.c.app (op V) ≫ X.presheaf.map (homOfLE hUV).op ≫ (X.restrictTopSectionsIso U).hom := by
  simpa using restrictTopSectionsIso_hom_c_app_top_of_fac_le f (le_refl V) hUV fUV (𝟙 _)
    (hfac.trans (Category.id_comp _).symm)

/-- `s ∈ Γ(X, U)` vanishes in the residue field at `x ∈ U` iff its image under
`restrictTopSectionsIso U` vanishes in the residue field of `X|_U` at `x`. -/
theorem evaluation_eq_zero_iff_restrict_Γevaluation_eq_zero (U : Opens X) (x : U)
    (s : X.presheaf.obj (op U)) :
    X.evaluation x s = 0 ↔
      (X.restrict U.isOpenEmbedding).Γevaluation x ((X.restrictTopSectionsIso U).hom s) = 0 := by
  let j := X.ofRestrict U.isOpenEmbedding; let x' : (Opens.map j.base).obj U := ⟨x, x.2⟩
  have hle : (⊤ : Opens (X.restrict U.isOpenEmbedding)) ≤ (Opens.map j.base).obj U := fun y _ ↦ y.2
  have hres : (X.restrict U.isOpenEmbedding).evaluation x' (j.c.app (op U) s) =
      (X.restrict U.isOpenEmbedding).Γevaluation x ((X.restrictTopSectionsIso U).hom s) := by
    rw [← ofRestrict_c_app_self X U, ConcreteCategory.comp_apply]
    exact (congrArg ((X.restrict U.isOpenEmbedding).residue x)
      (TopCat.Presheaf.germ_res_apply _ (homOfLE hle) x trivial (j.c.app (op U) s))).symm
  have hval : (residueFieldMap j x'.1) (X.evaluation x s) =
      (X.restrict U.isOpenEmbedding).Γevaluation x ((X.restrictTopSectionsIso U).hom s) :=
    (evaluation_naturality_apply j x' s).trans hres
  exact ((residueFieldMap j x'.1).hom.map_eq_zero_iff (x := X.evaluation x s)).symm.trans
    (iff_of_eq (congrArg (· = 0) hval))

end AlgebraicGeometry.LocallyRingedSpace
