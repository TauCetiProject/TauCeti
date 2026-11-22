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
`ofRestrict` and functorial in inclusions. We also record global-section cancellations for
isomorphisms (`iso_inv_c_app_top_comp_hom`, `iso_hom_c_app_top_comp_inv`) and residue-field
compatibility with `PresheafedSpace.restrictTopSectionsIso`
(`evaluation_eq_zero_iff_restrict_Γevaluation_eq_zero`).
-/

public section
open CategoryTheory TopologicalSpace Opposite
namespace AlgebraicGeometry.LocallyRingedSpace
universe u
variable (X : LocallyRingedSpace.{u})

private theorem range_ofRestrict_subset {V W : Opens X} (h : V ≤ W) :
    Set.range (X.ofRestrict V.isOpenEmbedding).base ⊆
      Set.range (X.ofRestrict W.isOpenEmbedding).base := fun _ ⟨x, hx⟩ ↦ ⟨⟨x.1, h x.2⟩, hx⟩

private theorem restrictHomOfLE_eq_lift {V W : Opens X} (h : V ≤ W) :
    X.toPresheafedSpace.restrictHomOfLE h = (IsOpenImmersion.lift (X.ofRestrict W.isOpenEmbedding)
        (X.ofRestrict V.isOpenEmbedding) (range_ofRestrict_subset X h)).toHom :=
  (cancel_mono _).mp <| (PresheafedSpace.restrictHomOfLE_ofRestrict _ h).trans
    (congrArg Hom.toHom (IsOpenImmersion.lift_fac _ _ (range_ofRestrict_subset X h))).symm

/-- Stalk maps of `PresheafedSpace.restrictHomOfLE` are local ring homomorphisms. -/
theorem isLocalHom_restrictHomOfLE {V W : Opens X} (h : V ≤ W) (x : X.restrict V.isOpenEmbedding) :
    IsLocalHom ((X.toPresheafedSpace.restrictHomOfLE h).stalkMap x).hom :=
  restrictHomOfLE_eq_lift X h ▸ (IsOpenImmersion.lift _ _ _).prop x

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

/-- Global-section maps of an isomorphism of locally ringed spaces cancel on the left. -/
@[reassoc (attr := simp)]
theorem iso_inv_c_app_top_comp_hom {Y₁ Y₂ : LocallyRingedSpace.{u}} (e : Y₁ ≅ Y₂) :
    (e.inv.c.app (op ⊤) : Y₁.presheaf.obj (op ⊤) ⟶ Y₂.presheaf.obj (op ⊤)) ≫ e.hom.c.app (op ⊤) =
      𝟙 (Y₁.presheaf.obj (op ⊤)) :=
  (LocallyRingedSpace.Γ.map_comp e.inv.op e.hom.op).symm.trans <| by
    rw [← op_comp, e.hom_inv_id, op_id, LocallyRingedSpace.Γ.map_id]; rfl

/-- Global-section maps of an isomorphism of locally ringed spaces cancel on the right. -/
@[reassoc (attr := simp)]
theorem iso_hom_c_app_top_comp_inv {Y₁ Y₂ : LocallyRingedSpace.{u}} (e : Y₁ ≅ Y₂) :
    (e.hom.c.app (op ⊤) : Y₂.presheaf.obj (op ⊤) ⟶ Y₁.presheaf.obj (op ⊤)) ≫ e.inv.c.app (op ⊤) =
      𝟙 (Y₂.presheaf.obj (op ⊤)) := iso_inv_c_app_top_comp_hom e.symm

/-- `s ∈ Γ(X, U)` vanishes in the residue field at `x ∈ U` iff its image under
`PresheafedSpace.restrictTopSectionsIso` vanishes in the residue field of `X|_U` at `x`. -/
theorem evaluation_eq_zero_iff_restrict_Γevaluation_eq_zero (U : Opens X) (x : U)
    (s : X.presheaf.obj (op U)) : X.evaluation x s = 0 ↔
      (X.restrict U.isOpenEmbedding).Γevaluation x
        ((X.toPresheafedSpace.restrictTopSectionsIso U).hom s) = 0 := by
  let j := X.ofRestrict U.isOpenEmbedding; let x' : (Opens.map j.base).obj U := ⟨x, x.2⟩
  have hres : (X.restrict U.isOpenEmbedding).evaluation x' (j.c.app (op U) s) =
      (X.restrict U.isOpenEmbedding).Γevaluation x
        ((X.toPresheafedSpace.restrictTopSectionsIso U).hom s) := by
    rw [← X.toPresheafedSpace.ofRestrict_c_app_self U, ConcreteCategory.comp_apply]
    exact (congrArg ((X.restrict U.isOpenEmbedding).residue x)
      (TopCat.Presheaf.germ_res_apply (X.restrict U.isOpenEmbedding).presheaf
        (homOfLE (fun y _ ↦ y.2 : (⊤ : Opens _) ≤ (Opens.map j.base).obj U)) x trivial
        (j.c.app (op U) s))).symm
  exact ((residueFieldMap j x'.1).hom.map_eq_zero_iff (x := X.evaluation x s)).symm.trans
    (iff_of_eq (congrArg (· = 0) ((evaluation_naturality_apply j x' s).trans hres)))
end AlgebraicGeometry.LocallyRingedSpace
