/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.ResidueField
public import TauCeti.Geometry.RingedSpace.PresheafedSpace.Restrict

import TauCeti.Geometry.RingedSpace.OpenImmersion

/-!
# Inclusions between restrictions of a locally ringed space to nested opens

For opens `V ≤ W` of a locally ringed space `X`, `AlgebraicGeometry.PresheafedSpace.restrictHomOfLE`
lifts to an open immersion `restrictHomOfLE : X|_V ⟶ X|_W` of locally ringed spaces compatible with
`ofRestrict` and functorial in inclusions, and `restrictRestrictIso` identifies an iterated
restriction `(X|_U)|_V` with `X|_{U(V)}`. We also record residue-field compatibility with
`PresheafedSpace.restrictTopSectionsIso` (`evaluation_eq_zero_iff_restrict_Γevaluation_eq_zero`).
-/

public section
open CategoryTheory TopologicalSpace Opposite
namespace AlgebraicGeometry.LocallyRingedSpace
universe u
variable (X : LocallyRingedSpace.{u})

private theorem range_ofRestrict_subset {V W : Opens X} (h : V ≤ W) :
    Set.range (X.ofRestrict V.isOpenEmbedding).base ⊆
      Set.range (X.ofRestrict W.isOpenEmbedding).base := fun _ ⟨x, hx⟩ ↦ ⟨⟨x.val, h x.property⟩, hx⟩

private theorem restrictHomOfLE_eq_lift {V W : Opens X} (h : V ≤ W) :
    X.toPresheafedSpace.restrictHomOfLE h = (IsOpenImmersion.lift (X.ofRestrict W.isOpenEmbedding)
        (X.ofRestrict V.isOpenEmbedding) (range_ofRestrict_subset X h)).toHom :=
  (cancel_mono _).mp <| (PresheafedSpace.restrictHomOfLE_ofRestrict _ h).trans
    (congrArg Hom.toHom (IsOpenImmersion.lift_fac _ _ (range_ofRestrict_subset X h))).symm

/-- Stalk maps of `PresheafedSpace.restrictHomOfLE` are local ring homomorphisms. -/
theorem isLocalHom_stalkMap_restrictHomOfLE {V W : Opens X} (h : V ≤ W)
    (x : X.restrict V.isOpenEmbedding) :
    IsLocalHom ((X.toPresheafedSpace.restrictHomOfLE h).stalkMap x).hom :=
  restrictHomOfLE_eq_lift X h ▸ (IsOpenImmersion.lift _ _ _).prop x

/-- For opens `V ≤ W` of `X`, the open immersion `X|_V ⟶ X|_W` of locally ringed spaces. -/
def restrictHomOfLE {V W : Opens X} (h : V ≤ W) :
    X.restrict V.isOpenEmbedding ⟶ X.restrict W.isOpenEmbedding :=
  ⟨X.toPresheafedSpace.restrictHomOfLE h, isLocalHom_stalkMap_restrictHomOfLE X h⟩

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
    IsOpenImmersion (X.restrictHomOfLE h) :=
  (Hom.ext' (restrictHomOfLE_eq_lift X h) : X.restrictHomOfLE h = IsOpenImmersion.lift
    (X.ofRestrict W.isOpenEmbedding) (X.ofRestrict V.isOpenEmbedding) _) ▸ inferInstance

/-- The inclusion of a restriction into itself is the identity. -/
@[simp] theorem restrictHomOfLE_refl (V : Opens X) : X.restrictHomOfLE (le_refl V) =
    𝟙 (X.restrict V.isOpenEmbedding) := Hom.ext' (X.toPresheafedSpace.restrictHomOfLE_refl V)

/-- Inclusions between restrictions to nested opens compose. -/
@[reassoc (attr := simp)] theorem restrictHomOfLE_comp {U V W : Opens X} (h : U ≤ V) (k : V ≤ W) :
    X.restrictHomOfLE h ≫ X.restrictHomOfLE k = X.restrictHomOfLE (h.trans k) :=
  Hom.ext' (X.toPresheafedSpace.restrictHomOfLE_comp h k)

private theorem range_comp_ofRestrict (U : Opens X)
    (V : Opens (X.restrict U.isOpenEmbedding)) :
    Set.range ((X.restrict U.isOpenEmbedding).ofRestrict V.isOpenEmbedding ≫
        X.ofRestrict U.isOpenEmbedding).base =
      Set.range (X.ofRestrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding).base := by
  rw [comp_base, TopCat.coe_comp, Set.range_comp]
  exact (congrArg (Subtype.val '' ·) Subtype.range_coe).trans Subtype.range_coe.symm

/-- Iterated restriction `(X|_U)|_V` is canonically isomorphic to the restriction `X|_{U(V)}`
to the image open of `V` in `X`. -/
noncomputable def restrictRestrictIso (U : Opens X)
    (V : Opens (X.restrict U.isOpenEmbedding)) :
    (X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding ≅
      X.restrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding :=
  LocallyRingedSpace.isoOfSheafedSpaceIso <| SheafedSpace.isoMk <|
    PresheafedSpace.IsOpenImmersion.isoOfRangeEq
      ((X.restrict U.isOpenEmbedding).ofRestrict V.isOpenEmbedding ≫
        X.ofRestrict U.isOpenEmbedding).toHom
      (X.ofRestrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding).toHom
      (range_comp_ofRestrict X U V)

/-- Composing `restrictRestrictIso.hom` with `ofRestrict (U(V))` gives the composite inclusion
`(X|_U)|_V ⟶ X|_U ⟶ X`. -/
@[reassoc (attr := simp)]
theorem restrictRestrictIso_hom_ofRestrict (U : Opens X)
    (V : Opens (X.restrict U.isOpenEmbedding)) :
    (X.restrictRestrictIso U V).hom ≫
        X.ofRestrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding =
      (X.restrict U.isOpenEmbedding).ofRestrict V.isOpenEmbedding ≫
        X.ofRestrict U.isOpenEmbedding :=
  Hom.ext' <| PresheafedSpace.IsOpenImmersion.lift_fac _ _ (range_comp_ofRestrict X U V).le

/-- Composing `restrictRestrictIso.hom` with `restrictHomOfLE` gives `(X|_U).ofRestrict V`. -/
@[reassoc (attr := simp)]
theorem restrictRestrictIso_hom_restrictHomOfLE (U : Opens X)
    (V : Opens (X.restrict U.isOpenEmbedding))
    (h : U.isOpenEmbedding.functor.obj V ≤ U := fun _ ⟨x, _, hx⟩ ↦ hx ▸ x.property) :
    (X.restrictRestrictIso U V).hom ≫ X.restrictHomOfLE h =
      (X.restrict U.isOpenEmbedding).ofRestrict V.isOpenEmbedding := by
  rw [← cancel_mono (X.ofRestrict U.isOpenEmbedding), Category.assoc, restrictHomOfLE_ofRestrict,
    restrictRestrictIso_hom_ofRestrict]

/-- Composing `restrictRestrictIso.inv` with `(X|_U).ofRestrict V` gives `restrictHomOfLE`. -/
@[reassoc (attr := simp)]
theorem restrictRestrictIso_inv_ofRestrict (U : Opens X)
    (V : Opens (X.restrict U.isOpenEmbedding))
    (h : U.isOpenEmbedding.functor.obj V ≤ U := fun _ ⟨x, _, hx⟩ ↦ hx ▸ x.property) :
    (X.restrictRestrictIso U V).inv ≫
        (X.restrict U.isOpenEmbedding).ofRestrict V.isOpenEmbedding =
      X.restrictHomOfLE h := by
  rw [← cancel_mono (X.ofRestrict U.isOpenEmbedding), Category.assoc,
    ← restrictRestrictIso_hom_ofRestrict, Iso.inv_hom_id_assoc, restrictHomOfLE_ofRestrict]

/-- `s ∈ Γ(X, U)` vanishes in the residue field at `x ∈ U` iff its image under
`PresheafedSpace.restrictTopSectionsIso` vanishes in the residue field of `X|_U` at `x`. -/
theorem evaluation_eq_zero_iff_restrict_Γevaluation_eq_zero (U : Opens X) (x : U)
    (s : X.presheaf.obj (op U)) : X.evaluation x s = 0 ↔
      (X.restrict U.isOpenEmbedding).Γevaluation x
        ((X.toPresheafedSpace.restrictTopSectionsIso U).hom s) = 0 := by
  let j := X.ofRestrict U.isOpenEmbedding; let x' : (Opens.map j.base).obj U := ⟨x, x.property⟩
  have hres : (X.restrict U.isOpenEmbedding).evaluation x' (j.c.app (op U) s) =
      (X.restrict U.isOpenEmbedding).Γevaluation x
        ((X.toPresheafedSpace.restrictTopSectionsIso U).hom s) := by
    have hsec :
        (X.restrict U.isOpenEmbedding).presheaf.map
            (homOfLE (fun y _ ↦ y.property : (⊤ : Opens _) ≤ (Opens.map j.base).obj U)).op
            (j.c.app (op U) s) =
          (X.toPresheafedSpace.restrictTopSectionsIso U).hom s :=
      ConcreteCategory.congr_hom
        ((PresheafedSpace.Hom.appLE_def _ _ _ _).symm.trans
          (X.toPresheafedSpace.ofRestrict_appLE_self U)) s
    rw [← hsec]
    exact (congrArg ((X.restrict U.isOpenEmbedding).residue x)
      (TopCat.Presheaf.germ_res_apply (X.restrict U.isOpenEmbedding).presheaf
        (homOfLE (fun y _ ↦ y.property : (⊤ : Opens _) ≤ (Opens.map j.base).obj U)) x trivial
        (j.c.app (op U) s))).symm
  exact ((residueFieldMap j x'.val).hom.map_eq_zero_iff (x := X.evaluation x s)).symm.trans
    (iff_of_eq (congrArg (· = 0) ((evaluation_naturality_apply j x' s).trans hres)))
end AlgebraicGeometry.LocallyRingedSpace
