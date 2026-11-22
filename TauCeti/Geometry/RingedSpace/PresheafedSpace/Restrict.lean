/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import TauCeti.Topology.Category.TopCat.Opens

import TauCeti.Topology.Sheaves.Presheaf

/-!
# Inclusions between restrictions of a presheafed space to nested opens

For opens `V ≤ W` of a presheafed space `X`, the restriction of `X` to `V` includes into its
restriction to `W`, compatibly with the inclusions into `X`. This is the presheafed-space analogue
of Mathlib's `AlgebraicGeometry.Scheme.homOfLE`.

## Main definitions

* `AlgebraicGeometry.PresheafedSpace.restrictHomOfLE`: the inclusion `X|_V ⟶ X|_W` for `V ≤ W`.
* `AlgebraicGeometry.PresheafedSpace.pullbackRestrictIso`:
  `pullback (X.ofRestrict U) (X.ofRestrict V) ≅ X|_{U ⊓ V}`.
* `AlgebraicGeometry.PresheafedSpace.restrictTopSectionsIso`: `Γ(X, U) ≅ Γ(X|_U, ⊤)`.

## Main results

* `AlgebraicGeometry.PresheafedSpace.restrictHomOfLE_ofRestrict`: composing with the inclusion
  `X|_W ⟶ X` gives the inclusion `X|_V ⟶ X`.
* `AlgebraicGeometry.PresheafedSpace.restrictHomOfLE_refl`,
  `AlgebraicGeometry.PresheafedSpace.restrictHomOfLE_comp`: the inclusions are functorial.
* `AlgebraicGeometry.PresheafedSpace.pullback_comp_iff_restrictHomOfLE`: pullback vs intersection
  compatibility.
* `AlgebraicGeometry.PresheafedSpace.ofRestrict_c_app_le`,
  `c_app_comp_homOfLE_of_eq`, `restrictTopSectionsIso_hom_c_app_top_of_fac`: section-restriction,
  congruence, and factorization rules.
-/

public section

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.PresheafedSpace

universe w v u

variable {C : Type u} [Category.{v} C] (X : PresheafedSpace.{v, u, w} C)

/-- Restriction maps of `X.restrict h` are restriction maps of `X` between the image opens. -/
theorem restrict_presheaf_map {U : TopCat} {f : U ⟶ (X : TopCat)} (h : Topology.IsOpenEmbedding f)
    {V W : (Opens U)ᵒᵖ} (i : V ⟶ W) :
    (X.restrict h).presheaf.map i = X.presheaf.map (h.functor.map i.unop).op := (rfl)

/-- For opens `V ≤ W` of `X`, the inclusion of the restriction of `X` to `V` into its restriction
to `W`. Its components are restriction maps of the presheaf of `X`. -/
@[expose, simps]
def restrictHomOfLE {V W : Opens X} (h : V ≤ W) :
    X.restrict V.isOpenEmbedding ⟶ X.restrict W.isOpenEmbedding where
  base := (Opens.toTopCat X).map (homOfLE h)
  c :=
    { app Q := X.presheaf.map (homOfLE (Opens.functor_obj_map_homOfLE_obj_le h Q.unop)).op
      naturality _ _ _ :=
        (X.presheaf.map_comp _ _).symm.trans <|
          (congrArg X.presheaf.map (Subsingleton.elim _ _)).trans (X.presheaf.map_comp _ _) }

/-- The inclusion `X|_V ⟶ X|_W` followed by the inclusion `X|_W ⟶ X` is the inclusion
`X|_V ⟶ X`. -/
@[reassoc (attr := simp)]
theorem restrictHomOfLE_ofRestrict {V W : Opens X} (h : V ≤ W) :
    X.restrictHomOfLE h ≫ X.ofRestrict W.isOpenEmbedding = X.ofRestrict V.isOpenEmbedding := by
  have hbase : (X.restrictHomOfLE h ≫ X.ofRestrict W.isOpenEmbedding).base =
      (X.ofRestrict V.isOpenEmbedding).base := by
    rw [comp_base, ofRestrict_base, ofRestrict_base, restrictHomOfLE_base]
    rfl
  refine PresheafedSpace.ext _ _ hbase ?_
  ext Q
  rw [NatTrans.comp_app, comp_c_app, Functor.whiskerRight_app, eqToHom_app,
    ofRestrict_c_app, ofRestrict_c_app, restrictHomOfLE_c_app]
  exact (congrArg (· ≫ _) (X.presheaf.map_comp _ _).symm).trans <|
    (X.presheaf.map_comp _ _).symm.trans (congrArg X.presheaf.map (Subsingleton.elim _ _))

/-- The inclusion of a restriction into itself is the identity. -/
@[simp]
theorem restrictHomOfLE_refl (V : Opens X) :
    X.restrictHomOfLE (le_refl V) = 𝟙 (X.restrict V.isOpenEmbedding) := by
  rw [← cancel_mono (X.ofRestrict V.isOpenEmbedding), restrictHomOfLE_ofRestrict, Category.id_comp]

/-- Inclusions between restrictions to nested opens compose. -/
@[reassoc (attr := simp)]
theorem restrictHomOfLE_comp {U V W : Opens X} (h : U ≤ V) (k : V ≤ W) :
    X.restrictHomOfLE h ≫ X.restrictHomOfLE k = X.restrictHomOfLE (h.trans k) := by
  rw [← cancel_mono (X.ofRestrict W.isOpenEmbedding), Category.assoc, restrictHomOfLE_ofRestrict,
    restrictHomOfLE_ofRestrict, restrictHomOfLE_ofRestrict]

private theorem range_pullback_fst_subset (U V : Opens X) :
    Set.range (pullback.fst (X.ofRestrict U.isOpenEmbedding)
        (X.ofRestrict V.isOpenEmbedding) ≫ X.ofRestrict U.isOpenEmbedding).base ⊆
      Set.range (X.ofRestrict (U ⊓ V).isOpenEmbedding).base := by
  rintro _ ⟨p, rfl⟩
  let ιU := X.ofRestrict U.isOpenEmbedding; let ιV := X.ofRestrict V.isOpenEmbedding
  exact ⟨⟨(pullback.fst ιU ιV ≫ ιU).base p, ((pullback.fst ιU ιV).base p).2,
    congrArg (fun k ↦ k.base p) (pullback.condition : pullback.fst ιU ιV ≫ ιU =
      pullback.snd ιU ιV ≫ ιV) ▸ ((pullback.snd ιU ιV).base p).2⟩, rfl⟩

/-- The pullback of two open inclusions `X|_U ⟶ X` and `X|_V ⟶ X` is canonically isomorphic to
the restriction `X|_{U ⊓ V}`. -/
noncomputable def pullbackRestrictIso (U V : Opens X) :
    pullback (X.ofRestrict U.isOpenEmbedding) (X.ofRestrict V.isOpenEmbedding) ≅
      X.restrict (U ⊓ V).isOpenEmbedding where
  hom := IsOpenImmersion.lift (X.ofRestrict (U ⊓ V).isOpenEmbedding)
    (pullback.fst _ _ ≫ X.ofRestrict U.isOpenEmbedding) (range_pullback_fst_subset X U V)
  inv := pullback.lift (X.restrictHomOfLE inf_le_left) (X.restrictHomOfLE inf_le_right) (by simp)
  hom_inv_id := pullback.hom_ext
    (by rw [Category.assoc, pullback.lift_fst, Category.id_comp, ← cancel_mono (X.ofRestrict _),
      Category.assoc, restrictHomOfLE_ofRestrict, IsOpenImmersion.lift_fac])
    (by rw [Category.assoc, pullback.lift_snd, Category.id_comp, ← cancel_mono (X.ofRestrict _),
      Category.assoc, restrictHomOfLE_ofRestrict, IsOpenImmersion.lift_fac, pullback.condition])
  inv_hom_id := (cancel_mono (X.ofRestrict (U ⊓ V).isOpenEmbedding)).mp <| by
    rw [Category.assoc, IsOpenImmersion.lift_fac, Category.id_comp, pullback.lift_fst_assoc,
      restrictHomOfLE_ofRestrict]

/-- Composing `pullbackRestrictIso.hom` with the left inclusion gives `pullback.fst`. -/
@[reassoc (attr := simp)] theorem pullbackRestrictIso_hom_restrictHomOfLE_left (U V : Opens X) :
    (X.pullbackRestrictIso U V).hom ≫ X.restrictHomOfLE inf_le_left =
      pullback.fst (X.ofRestrict U.isOpenEmbedding) (X.ofRestrict V.isOpenEmbedding) :=
  (cancel_mono (X.ofRestrict U.isOpenEmbedding)).mp <| by
    rw [Category.assoc, restrictHomOfLE_ofRestrict]
    dsimp [pullbackRestrictIso]; rw [IsOpenImmersion.lift_fac]

/-- Composing `pullbackRestrictIso.hom` with the right inclusion gives `pullback.snd`. -/
@[reassoc (attr := simp)] theorem pullbackRestrictIso_hom_restrictHomOfLE_right (U V : Opens X) :
    (X.pullbackRestrictIso U V).hom ≫ X.restrictHomOfLE inf_le_right =
      pullback.snd (X.ofRestrict U.isOpenEmbedding) (X.ofRestrict V.isOpenEmbedding) :=
  (cancel_mono (X.ofRestrict V.isOpenEmbedding)).mp <| by
    rw [Category.assoc, restrictHomOfLE_ofRestrict]
    dsimp [pullbackRestrictIso]; rw [IsOpenImmersion.lift_fac, pullback.condition]

/-- Composing `pullbackRestrictIso.inv` with `pullback.fst` gives the left inclusion. -/
@[reassoc (attr := simp)] theorem pullbackRestrictIso_inv_fst (U V : Opens X) :
    (X.pullbackRestrictIso U V).inv ≫ pullback.fst (X.ofRestrict U.isOpenEmbedding)
        (X.ofRestrict V.isOpenEmbedding) = X.restrictHomOfLE inf_le_left := pullback.lift_fst _ _ _

/-- Composing `pullbackRestrictIso.inv` with `pullback.snd` gives the right inclusion. -/
@[reassoc (attr := simp)] theorem pullbackRestrictIso_inv_snd (U V : Opens X) :
    (X.pullbackRestrictIso U V).inv ≫ pullback.snd (X.ofRestrict U.isOpenEmbedding)
        (X.ofRestrict V.isOpenEmbedding) = X.restrictHomOfLE inf_le_right := pullback.lift_snd _ _ _

/-- Agreement on the pullback of two open restrictions `X|_U` and `X|_V` is equivalent to
agreement on the intersection `X|_{U ⊓ V}`. -/
theorem pullback_comp_iff_restrictHomOfLE {Y : PresheafedSpace.{v, u, w} C} {U V : Opens X}
    (f : X.restrict U.isOpenEmbedding ⟶ Y) (g : X.restrict V.isOpenEmbedding ⟶ Y) :
    pullback.fst (X.ofRestrict U.isOpenEmbedding) (X.ofRestrict V.isOpenEmbedding) ≫ f =
        pullback.snd (X.ofRestrict U.isOpenEmbedding) (X.ofRestrict V.isOpenEmbedding) ≫ g ↔
      X.restrictHomOfLE (inf_le_left : U ⊓ V ≤ U) ≫ f =
        X.restrictHomOfLE inf_le_right ≫ g :=
  ⟨fun h ↦ by rw [← pullbackRestrictIso_inv_fst, ← pullbackRestrictIso_inv_snd, Category.assoc,
    Category.assoc, h], fun h ↦ by rw [← pullbackRestrictIso_hom_restrictHomOfLE_left,
    ← pullbackRestrictIso_hom_restrictHomOfLE_right, Category.assoc, Category.assoc, h]⟩

/-- The canonical identification `Γ(X, U) ≅ Γ(X|_U, ⊤)` between sections over an open `U` and
global sections of the restricted presheafed space `X|_U`. -/
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
      X.presheaf.map (homOfLE h).op ≫ (X.restrictTopSectionsIso V).hom :=
  (congrArg (· ≫ (X.restrict V.isOpenEmbedding).presheaf.map (homOfLE (fun x _ ↦ h x.2 :
      (⊤ : Opens _) ≤ (Opens.map (X.ofRestrict V.isOpenEmbedding).base).obj W)).op)
    (X.ofRestrict_c_app V.isOpenEmbedding (op W))).trans <|
    (X.presheaf.map_comp _ _).symm.trans <|
      (congrArg X.presheaf.map (Subsingleton.elim _ _)).trans (X.presheaf.map_comp _ _)

/-- Restricting a section over `U` along `X|_U ⟶ X` and then to `⊤` on `X|_U` is
`restrictTopSectionsIso`. -/
@[reassoc] theorem ofRestrict_c_app_self (U : Opens X) :
    (X.ofRestrict U.isOpenEmbedding).c.app (op U) ≫ (X.restrict U.isOpenEmbedding).presheaf.map
        (homOfLE (fun x _ ↦ x.2 : (⊤ : Opens _) ≤
          (Opens.map (X.ofRestrict U.isOpenEmbedding).base).obj U)).op =
      (X.restrictTopSectionsIso U).hom := by simpa using X.ofRestrict_c_app_le (le_refl U)

/-- Restricting a global section along `X|_U ⟶ X` at `op ⊤` is the presheaf restriction
`Γ(X, ⊤) ⟶ Γ(X, U)` followed by `restrictTopSectionsIso`. -/
@[reassoc] theorem ofRestrict_c_app_top (U : Opens X) :
    ((X.ofRestrict U.isOpenEmbedding).c.app (op ⊤) :
        X.presheaf.obj (op ⊤) ⟶ (X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) =
      X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ (X.restrictTopSectionsIso U).hom := by
  rw [ofRestrict_c_app, restrictTopSectionsIso_hom]
  exact (congrArg X.presheaf.map (Subsingleton.elim _ _)).trans (X.presheaf.map_comp _ _)

/-- Under `restrictTopSectionsIso`, the global-section map of `X|_V ⟶ X|_W` is the presheaf
restriction `Γ(X, W) ⟶ Γ(X, V)`. -/
@[reassoc]
theorem restrictTopSectionsIso_hom_restrictHomOfLE_c_app_top {V W : Opens X} (h : V ≤ W) :
    (X.restrictTopSectionsIso W).hom ≫ (X.restrictHomOfLE h).c.app (op ⊤) =
      X.presheaf.map (homOfLE h).op ≫ (X.restrictTopSectionsIso V).hom := by
  have h1 : (X.restrictTopSectionsIso W).hom ≫ (X.restrictHomOfLE h).c.app (op ⊤) =
      X.presheaf.map (eqToHom (congrArg op W.isOpenEmbedding_obj_top.symm) ≫
        (homOfLE (Opens.functor_obj_map_homOfLE_obj_le h ⊤)).op) :=
    (X.presheaf.map_comp _ _).symm
  have h2 : X.presheaf.map (homOfLE h).op ≫ (X.restrictTopSectionsIso V).hom =
      X.presheaf.map ((homOfLE h).op ≫ eqToHom (congrArg op V.isOpenEmbedding_obj_top.symm)) :=
    (X.presheaf.map_comp _ _).symm
  exact h1.trans <| (congrArg X.presheaf.map (Subsingleton.elim _ _)).trans h2.symm

private theorem comp_c_app_comp_map {X Y Z : PresheafedSpace.{v, u, w} C}
    (k : Z ⟶ Y) (f : Y ⟶ X) {W : Opens X} {V : Opens Z}
    (hV : V ≤ (Opens.map (k ≫ f).base).obj W) :
    (k ≫ f).c.app (op W) ≫ Z.presheaf.map (homOfLE hV).op =
      f.c.app (op W) ≫ k.c.app (op ((Opens.map f.base).obj W)) ≫
        Z.presheaf.map (homOfLE (hV : V ≤ (Opens.map k.base).obj ((Opens.map f.base).obj W))).op :=
  Category.assoc _ _ _

/-- For `k : Z ⟶ X|_U` and opens `U ≤ W`, restricting a section over `W` along
`k ≫ X.ofRestrict U` and then to `⊤` on `Z` factors as
`Γ(X, W) ⟶ Γ(X, U) ≅ Γ(X|_U, ⊤) ⟶ Γ(Z, ⊤)`. -/
@[reassoc] theorem comp_ofRestrict_c_app_le {X Z : PresheafedSpace.{v, u, w} C} {U W : Opens X}
    (hUW : U ≤ W) (k : Z ⟶ X.restrict U.isOpenEmbedding)
    (hleZ : (⊤ : Opens Z) ≤ (Opens.map (k ≫ X.ofRestrict U.isOpenEmbedding).base).obj W) :
    (k ≫ X.ofRestrict U.isOpenEmbedding).c.app (op W) ≫ Z.presheaf.map (homOfLE hleZ).op =
      X.presheaf.map (homOfLE hUW).op ≫ (X.restrictTopSectionsIso U).hom ≫ k.c.app (op ⊤) := by
  have hleU : (⊤ : Opens (X.restrict U.isOpenEmbedding)) ≤
      (Opens.map (X.ofRestrict U.isOpenEmbedding).base).obj W := fun (x : U) _ ↦ hUW x.2
  have hnat : k.c.app (op ((Opens.map (X.ofRestrict U.isOpenEmbedding).base).obj W)) ≫
        Z.presheaf.map (homOfLE (hleZ : (⊤ : Opens Z) ≤
          (Opens.map k.base).obj ((Opens.map (X.ofRestrict U.isOpenEmbedding).base).obj W))).op =
      (X.restrict U.isOpenEmbedding).presheaf.map (homOfLE hleU).op ≫
        (k.c.app (op ⊤) : _ ⟶ Z.presheaf.obj (op ⊤)) :=
    (k.c.naturality (homOfLE hleU).op).symm
  have h1 : (X.ofRestrict U.isOpenEmbedding).c.app (op W) ≫
        (X.restrict U.isOpenEmbedding).presheaf.map (homOfLE hleU).op ≫
          (k.c.app (op ⊤) : _ ⟶ Z.presheaf.obj (op ⊤)) =
      X.presheaf.map (homOfLE hUW).op ≫ (X.restrictTopSectionsIso U).hom ≫
        (k.c.app (op ⊤) : _ ⟶ Z.presheaf.obj (op ⊤)) :=
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ (k.c.app (op ⊤) : _ ⟶ Z.presheaf.obj (op ⊤)))
        (X.ofRestrict_c_app_le hUW)).trans (Category.assoc _ _ _)
  exact (comp_c_app_comp_map k (X.ofRestrict U.isOpenEmbedding) hleZ).trans <|
    (congrArg ((X.ofRestrict U.isOpenEmbedding).c.app (op W) ≫ ·) hnat).trans h1

/-- Equal morphisms of presheafed spaces induce equal maps after restricting to a common open `V`
of the source. -/
@[reassoc] theorem c_app_comp_homOfLE_of_eq {X Y : PresheafedSpace.{v, u, w} C}
    {k₁ k₂ : X ⟶ Y} (hk : k₁ = k₂) {W : Opens Y} {V : Opens X}
    (h₁ : V ≤ (Opens.map k₁.base).obj W) (h₂ : V ≤ (Opens.map k₂.base).obj W) :
    k₁.c.app (op W) ≫ X.presheaf.map (homOfLE h₁).op =
      k₂.c.app (op W) ≫ X.presheaf.map (homOfLE h₂).op := by
  subst hk; rfl

/-- Compatibility of `restrictTopSectionsIso` with factorizations `l ≫ Y|_V = h ≫ X|_U ≫ f`
for opens `V ≤ W` and `U ≤ f⁻¹ W`. -/
@[reassoc] theorem restrictTopSectionsIso_hom_c_app_top_of_fac_le
    {X Y Z : PresheafedSpace.{v, u, w} C} (f : X ⟶ Y) {V W : Opens Y} (hVW : V ≤ W)
    {U : Opens X} (hUW : U ≤ (Opens.map f.base).obj W)
    (l : Z ⟶ Y.restrict V.isOpenEmbedding) (h : Z ⟶ X.restrict U.isOpenEmbedding)
    (hfac : l ≫ Y.ofRestrict V.isOpenEmbedding = h ≫ X.ofRestrict U.isOpenEmbedding ≫ f) :
    Y.presheaf.map (homOfLE hVW).op ≫ (Y.restrictTopSectionsIso V).hom ≫
        (l.c.app (op ⊤) : _ ⟶ Z.presheaf.obj (op ⊤)) =
      f.c.app (op W) ≫ X.presheaf.map (homOfLE hUW).op ≫ (X.restrictTopSectionsIso U).hom ≫
        (h.c.app (op ⊤) : _ ⟶ Z.presheaf.obj (op ⊤)) := by
  have hl := comp_ofRestrict_c_app_le hVW l (fun (z : Z) _ ↦ hVW (l.base z).2)
  have h1 := c_app_comp_homOfLE_of_eq (V := (⊤ : Opens Z))
    (hfac.trans (Category.assoc _ _ _).symm)
    (fun (z : Z) _ ↦ hVW (l.base z).2) (fun (z : Z) _ ↦ hUW (h.base z).2)
  have h2 := comp_c_app_comp_map (V := (⊤ : Opens Z))
    (h ≫ X.ofRestrict U.isOpenEmbedding) f (fun (z : Z) _ ↦ hUW (h.base z).2)
  have hh := comp_ofRestrict_c_app_le hUW h (fun (z : Z) _ ↦ hUW (h.base z).2)
  exact hl.symm.trans <| h1.trans <| h2.trans (congrArg (f.c.app (op W) ≫ ·) hh)

/-- Compatibility of `restrictTopSectionsIso` with a restriction `fUV ≫ Y|_V = X|_U ≫ f`. -/
@[reassoc] theorem restrictTopSectionsIso_hom_c_app_top_of_fac {X Y : PresheafedSpace.{v, u, w} C}
    (f : X ⟶ Y) {V : Opens Y} {U : Opens X} (hUV : U ≤ (Opens.map f.base).obj V)
    (fUV : X.restrict U.isOpenEmbedding ⟶ Y.restrict V.isOpenEmbedding)
    (hfac : fUV ≫ Y.ofRestrict V.isOpenEmbedding = X.ofRestrict U.isOpenEmbedding ≫ f) :
    (Y.restrictTopSectionsIso V).hom ≫
        (fUV.c.app (op ⊤) : _ ⟶ (X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) =
      f.c.app (op V) ≫ X.presheaf.map (homOfLE hUV).op ≫ (X.restrictTopSectionsIso U).hom := by
  simpa using restrictTopSectionsIso_hom_c_app_top_of_fac_le f (le_refl V) hUV fUV (𝟙 _)
    (hfac.trans (Category.id_comp _).symm)

end AlgebraicGeometry.PresheafedSpace
