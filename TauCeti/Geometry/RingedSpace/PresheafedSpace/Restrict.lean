/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import TauCeti.Geometry.RingedSpace.PresheafedSpace.Basic
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
* `AlgebraicGeometry.PresheafedSpace.ofRestrict_appLE`,
  `AlgebraicGeometry.PresheafedSpace.comp_ofRestrict_appLE`,
  `AlgebraicGeometry.PresheafedSpace.restrictTopSectionsIso_hom_c_app_top_of_fac`:
  section-restriction and factorization rules.
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
      naturality _ _ i := by
        exact (congrArg (· ≫ _) (X.restrict_presheaf_map W.isOpenEmbedding i)).trans <|
          (TopCat.Presheaf.map_comp_eq_map_comp X.presheaf _ _ _ _).trans <|
            congrArg (_ ≫ ·) (X.restrict_presheaf_map V.isOpenEmbedding _).symm }

/-- The inclusion `X|_V ⟶ X|_W` followed by the inclusion `X|_W ⟶ X` is the inclusion
`X|_V ⟶ X`. -/
@[reassoc (attr := simp)]
theorem restrictHomOfLE_ofRestrict {V W : Opens X} (h : V ≤ W) :
    X.restrictHomOfLE h ≫ X.ofRestrict W.isOpenEmbedding = X.ofRestrict V.isOpenEmbedding := by
  have hbase : (X.restrictHomOfLE h ≫ X.ofRestrict W.isOpenEmbedding).base =
      (X.ofRestrict V.isOpenEmbedding).base := by
    rw [comp_base, ofRestrict_base, ofRestrict_base, restrictHomOfLE_base]
    exact Opens.toTopCat_map_comp_inclusion' (homOfLE h)
  refine PresheafedSpace.ext _ _ hbase ?_
  ext Q
  rw [NatTrans.comp_app, comp_c_app, Functor.whiskerRight_app, eqToHom_app,
    ofRestrict_c_app, ofRestrict_c_app, restrictHomOfLE_c_app]
  refine (congrArg₂ (· ≫ ·) (X.presheaf.map_comp _ _).symm
    (X.restrict_presheaf_map V.isOpenEmbedding _)).trans ?_
  exact TopCat.Presheaf.map_comp_map_eq X.presheaf _ _ _

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
  exact ⟨⟨(pullback.fst ιU ιV ≫ ιU).base p, ((pullback.fst ιU ιV).base p).property,
    congrArg (fun k ↦ k.base p) (pullback.condition : pullback.fst ιU ιV ≫ ιU =
      pullback.snd ιU ιV ≫ ιV) ▸ ((pullback.snd ιU ιV).base p).property⟩, rfl⟩

/-- The pullback of two open inclusions `X|_U ⟶ X` and `X|_V ⟶ X` is canonically isomorphic to
the restriction `X|_{U ⊓ V}`. -/
noncomputable def pullbackRestrictIso (U V : Opens X) :
    pullback (X.ofRestrict U.isOpenEmbedding) (X.ofRestrict V.isOpenEmbedding) ≅
      X.restrict (U ⊓ V).isOpenEmbedding where
  hom := IsOpenImmersion.lift (X.ofRestrict (U ⊓ V).isOpenEmbedding)
    (pullback.fst _ _ ≫ X.ofRestrict U.isOpenEmbedding) (range_pullback_fst_subset X U V)
  inv := pullback.lift (X.restrictHomOfLE inf_le_left) (X.restrictHomOfLE inf_le_right) (by simp)
  hom_inv_id := pullback.hom_ext
    (by
      rw [← cancel_mono (X.ofRestrict U.isOpenEmbedding)]
      simp [IsOpenImmersion.lift_fac])
    (by
      rw [← cancel_mono (X.ofRestrict V.isOpenEmbedding)]
      simp [IsOpenImmersion.lift_fac, pullback.condition])
  inv_hom_id := (cancel_mono (X.ofRestrict (U ⊓ V).isOpenEmbedding)).mp <| by
    simp [IsOpenImmersion.lift_fac]

/-- Composing `pullbackRestrictIso.hom` with the left inclusion gives `pullback.fst`. -/
@[reassoc (attr := simp)] theorem pullbackRestrictIso_hom_restrictHomOfLE_left (U V : Opens X) :
    (X.pullbackRestrictIso U V).hom ≫ X.restrictHomOfLE inf_le_left =
      pullback.fst (X.ofRestrict U.isOpenEmbedding) (X.ofRestrict V.isOpenEmbedding) :=
  (cancel_mono (X.ofRestrict U.isOpenEmbedding)).mp <| by
    simp [pullbackRestrictIso, IsOpenImmersion.lift_fac]

/-- Composing `pullbackRestrictIso.hom` with the right inclusion gives `pullback.snd`. -/
@[reassoc (attr := simp)] theorem pullbackRestrictIso_hom_restrictHomOfLE_right (U V : Opens X) :
    (X.pullbackRestrictIso U V).hom ≫ X.restrictHomOfLE inf_le_right =
      pullback.snd (X.ofRestrict U.isOpenEmbedding) (X.ofRestrict V.isOpenEmbedding) :=
  (cancel_mono (X.ofRestrict V.isOpenEmbedding)).mp <| by
    simp [pullbackRestrictIso, IsOpenImmersion.lift_fac, pullback.condition]

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
@[reassoc] theorem ofRestrict_appLE {V W : Opens X} (h : V ≤ W)
    (hle : (⊤ : Opens _) ≤ (Opens.map (X.ofRestrict V.isOpenEmbedding).base).obj W :=
      fun x _ ↦ h x.property) :
    (X.ofRestrict V.isOpenEmbedding).appLE W ⊤ hle =
      X.presheaf.map (homOfLE h).op ≫ (X.restrictTopSectionsIso V).hom := by
  rw [Hom.appLE_def, ofRestrict_c_app, restrictTopSectionsIso_hom]
  exact (congrArg (_ ≫ ·) (X.restrict_presheaf_map V.isOpenEmbedding (homOfLE hle).op)).trans
    (TopCat.Presheaf.map_comp_eq_map_comp X.presheaf _ _ _ _)

/-- Restricting a section over `U` along `X|_U ⟶ X` and then to `⊤` on `X|_U` is
`restrictTopSectionsIso`. -/
@[reassoc] theorem ofRestrict_appLE_self (U : Opens X)
    (hle : (⊤ : Opens _) ≤ (Opens.map (X.ofRestrict U.isOpenEmbedding).base).obj U :=
      fun x _ ↦ x.property) :
    (X.ofRestrict U.isOpenEmbedding).appLE U ⊤ hle = (X.restrictTopSectionsIso U).hom := by
  simpa using X.ofRestrict_appLE (le_refl U) hle

/-- Restricting a global section along `X|_U ⟶ X` at `op ⊤` is the presheaf restriction
`Γ(X, ⊤) ⟶ Γ(X, U)` followed by `restrictTopSectionsIso`. -/
@[reassoc] theorem ofRestrict_c_app_top (U : Opens X) :
    ((X.ofRestrict U.isOpenEmbedding).c.app (op ⊤) :
        X.presheaf.obj (op ⊤) ⟶ (X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) =
      X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ (X.restrictTopSectionsIso U).hom := by
  rw [ofRestrict_c_app, restrictTopSectionsIso_hom]
  exact (TopCat.Presheaf.map_comp_map_eq X.presheaf (homOfLE (le_top : U ≤ ⊤)).op
    (eqToHom (congrArg op U.isOpenEmbedding_obj_top.symm)) _).symm

/-- Under `restrictTopSectionsIso`, the global-section map of `X|_V ⟶ X|_W` is the presheaf
restriction `Γ(X, W) ⟶ Γ(X, V)`. -/
@[reassoc]
theorem restrictTopSectionsIso_hom_restrictHomOfLE_c_app_top {V W : Opens X} (h : V ≤ W) :
    (X.restrictTopSectionsIso W).hom ≫ (X.restrictHomOfLE h).c.app (op ⊤) =
      X.presheaf.map (homOfLE h).op ≫ (X.restrictTopSectionsIso V).hom := by
  rw [restrictTopSectionsIso_hom, restrictHomOfLE_c_app]
  exact TopCat.Presheaf.map_comp_eq_map_comp X.presheaf _ _ _ _

/-- For `k : Z ⟶ X|_U` and opens `U ≤ W`, restricting a section over `W` along
`k ≫ X.ofRestrict U` and then to `⊤` on `Z` factors as
`Γ(X, W) ⟶ Γ(X, U) ≅ Γ(X|_U, ⊤) ⟶ Γ(Z, ⊤)`. -/
@[reassoc] theorem comp_ofRestrict_appLE {X Z : PresheafedSpace.{v, u, w} C} {U W : Opens X}
    (hUW : U ≤ W) (k : Z ⟶ X.restrict U.isOpenEmbedding)
    (hleZ : (⊤ : Opens Z) ≤ (Opens.map (k ≫ X.ofRestrict U.isOpenEmbedding).base).obj W :=
      fun z _ ↦ hUW (k.base z).property) :
    (k ≫ X.ofRestrict U.isOpenEmbedding).appLE W ⊤ hleZ =
      X.presheaf.map (homOfLE hUW).op ≫ (X.restrictTopSectionsIso U).hom ≫ k.c.app (op ⊤) := by
  have hleU : (⊤ : Opens (X.restrict U.isOpenEmbedding)) ≤
      (Opens.map (X.ofRestrict U.isOpenEmbedding).base).obj W := fun (x : U) _ ↦ hUW x.property
  have hnat : k.appLE ((Opens.map (X.ofRestrict U.isOpenEmbedding).base).obj W) ⊤
      (hleZ.trans (eqToHom (by rw [comp_base, Opens.map_comp_obj])).le) =
      (X.restrict U.isOpenEmbedding).presheaf.map (homOfLE hleU).op ≫ k.c.app (op ⊤) := by
    rw [Hom.appLE_def]
    refine .trans ?_ (k.c.naturality (homOfLE hleU).op).symm
    exact congrArg (k.c.app _ ≫ Z.presheaf.map ·) (Subsingleton.elim _ _)
  rw [Hom.comp_appLE, hnat]
  refine (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ k.c.app (op ⊤))
      ((Hom.appLE_def _ _ _ _).symm.trans (X.ofRestrict_appLE hUW hleU))).trans
      (Category.assoc _ _ _)

/-- Compatibility of `restrictTopSectionsIso` with factorizations `l ≫ Y|_V = h ≫ X|_U ≫ f`
for opens `V ≤ W` and `U ≤ f⁻¹ W`. -/
@[reassoc] theorem restrictTopSectionsIso_hom_c_app_top_of_fac_le
    {X Y Z : PresheafedSpace.{v, u, w} C} (f : X ⟶ Y) {V W : Opens Y} (hVW : V ≤ W)
    {U : Opens X} (hUW : U ≤ (Opens.map f.base).obj W)
    (l : Z ⟶ Y.restrict V.isOpenEmbedding) (h : Z ⟶ X.restrict U.isOpenEmbedding)
    (hfac : l ≫ Y.ofRestrict V.isOpenEmbedding = h ≫ X.ofRestrict U.isOpenEmbedding ≫ f) :
    Y.presheaf.map (homOfLE hVW).op ≫ (Y.restrictTopSectionsIso V).hom ≫
        (l.c.app (op ⊤) : _ ⟶ Z.presheaf.obj (op ⊤)) =
      f.appLE W U hUW ≫ (X.restrictTopSectionsIso U).hom ≫
        (h.c.app (op ⊤) : _ ⟶ Z.presheaf.obj (op ⊤)) := by
  have hleL : (⊤ : Opens Z) ≤ (Opens.map (l ≫ Y.ofRestrict V.isOpenEmbedding).base).obj W :=
    fun z _ ↦ hVW (l.base z).property
  have hleH : (⊤ : Opens Z) ≤ (Opens.map ((h ≫ X.ofRestrict U.isOpenEmbedding) ≫ f).base).obj W :=
    fun z _ ↦ hUW (h.base z).property
  rw [← comp_ofRestrict_appLE hVW l hleL, Hom.congr_appLE (hfac.trans (Category.assoc _ _ _).symm)
    hleL hleH, Hom.comp_appLE, comp_ofRestrict_appLE hUW h hleH]
  simp only [Hom.appLE_def, Category.assoc]
  -- `comp_ofRestrict_appLE` produces `h.c.app (op ⊤)` with codomain at `(Opens.map h.base).obj ⊤`,
  -- which is definitionally equal to `⊤` (`Opens.map_top`).
  rfl

/-- Compatibility of `restrictTopSectionsIso` with a restriction `fUV ≫ Y|_V = X|_U ≫ f`. -/
@[reassoc] theorem restrictTopSectionsIso_hom_c_app_top_of_fac {X Y : PresheafedSpace.{v, u, w} C}
    (f : X ⟶ Y) {V : Opens Y} {U : Opens X} (hUV : U ≤ (Opens.map f.base).obj V)
    (fUV : X.restrict U.isOpenEmbedding ⟶ Y.restrict V.isOpenEmbedding)
    (hfac : fUV ≫ Y.ofRestrict V.isOpenEmbedding = X.ofRestrict U.isOpenEmbedding ≫ f) :
    (Y.restrictTopSectionsIso V).hom ≫
        (fUV.c.app (op ⊤) : _ ⟶ (X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) =
      f.appLE V U hUV ≫ (X.restrictTopSectionsIso U).hom := by
  simpa using restrictTopSectionsIso_hom_c_app_top_of_fac_le f (le_refl V) hUV fUV (𝟙 _)
    (hfac.trans (Category.id_comp _).symm)

end AlgebraicGeometry.PresheafedSpace
