/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Pushforward and restriction of modules on schemes

Pushforward along a scheme isomorphism agrees with restriction along its inverse. This
identification transports local properties of module sheaves through affine normalizations.
Restriction of a pushforward to an open of the base agrees with pushforward of the restriction
to its preimage. Both comparisons have formulas on sections.

These comparisons use Mathlib's module pushforward and restriction API.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

open _root_.AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- Pushforward along an isomorphism agrees with restriction along its inverse. -/
def pushforwardIsoRestrictFunctor (e : X ≅ Y) : pushforward e.hom ≅ restrictFunctor e.inv := by
  refine SheafOfModules.pushforwardCongr₂ _
    (NatIso.ofComponents (fun V ↦ eqToIso (Scheme.Hom.inv_image e V)) (fun _ ↦ rfl)) ?_
  ext V x
  -- `pushforwardCongr₂` states coherence using ring-sheaf components; express these
  -- as scheme section maps so the open-immersion API applies.
  change (e.hom.app V.unop ≫ X.presheaf.map (eqToHom (Scheme.Hom.inv_image e V.unop)).op) x =
    (e.inv.appIso V.unop).inv x
  have h : e.hom.app V.unop = (e.inv.appIso V.unop).inv ≫
      X.presheaf.map (eqToHom (Scheme.Hom.inv_image e V.unop).symm).op := by
    refine (IsOpenImmersion.app_eq_appIso_inv_app_of_comp_eq e.hom e.inv (𝟙 X)
      e.hom_inv_id.symm V.unop).trans ?_
    -- The identity scheme's section map is definitionally the identity. Write the
    -- restriction with `inv_image` so its dependent source no longer contains `𝟙 X`.
    change (e.inv.appIso V.unop).inv ≫ (𝟙 _ ≫
      X.presheaf.map (eqToHom (Scheme.Hom.inv_image e V.unop).symm).op) = _
    rw [Category.id_comp]
  have hh : e.hom.app V.unop ≫
      X.presheaf.map (eqToHom (Scheme.Hom.inv_image e V.unop)).op =
      (e.inv.appIso V.unop).inv := by
    rw [h, Category.assoc, ← Functor.map_comp,
      Subsingleton.elim (_ ≫ _) (𝟙 _), CategoryTheory.Functor.map_id, Category.comp_id]
  exact congrArg (fun g : Γ(Y, V.unop) ⟶ Γ(X, e.inv ''ᵁ V.unop) ↦ g x) hh

/-- On sections, pushforward along an isomorphism is restriction along the equality
between the image under its inverse and the preimage under the forward map. -/
@[simp]
theorem pushforwardIsoRestrictFunctor_hom_app_val_app_apply (e : X ≅ Y) (M : X.Modules)
    (V : Y.Opens) (x : Γ((pushforward e.hom).obj M, V)) :
    (((pushforwardIsoRestrictFunctor e).hom.app M).val.app (.op V)) x =
      M.val.map (eqToHom (Scheme.Hom.inv_image e V)).op x := by
  -- `pushforwardCongr₂` restricts sections along the components of `eqToIso`,
  -- whose underlying maps are `eqToHom`.
  rfl

/-- The inverse pushforward--restriction comparison uses the inverse equality of opens. -/
@[simp]
theorem pushforwardIsoRestrictFunctor_inv_app_val_app_apply (e : X ≅ Y) (M : X.Modules)
    (V : Y.Opens) (x : Γ(M.restrict e.inv, V)) :
    (((pushforwardIsoRestrictFunctor e).inv.app M).val.app (.op V)) x =
      M.val.map (eqToHom (Scheme.Hom.inv_image e V).symm).op x := by
  -- The inverse components of `eqToIso` use the symmetric equality.
  rfl

/-- Restricting a pushforward to an open of the base agrees with pushing forward the
restriction to its preimage, naturally in the module sheaf. -/
def restrictPushforwardIso (f : X ⟶ Y) (U : Y.Opens) :
    pushforward f ⋙ restrictFunctor U.ι ≅
      restrictFunctor (f ⁻¹ᵁ U).ι ⋙ pushforward (f ∣_ U) := by
  -- Each composite is continuous via its intermediate open-scheme site; supplying these
  -- instances lets `SheafOfModules.pushforwardComp` elaborate the two composites.
  letI : (U.ι.opensFunctor ⋙ TopologicalSpace.Opens.map f.base).IsContinuous
      (Opens.grothendieckTopology U.toScheme) (Opens.grothendieckTopology X) :=
    Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology Y) _
  letI : (TopologicalSpace.Opens.map (f ∣_ U).base ⋙ (f ⁻¹ᵁ U).ι.opensFunctor).IsContinuous
      (Opens.grothendieckTopology U.toScheme) (Opens.grothendieckTopology X) :=
    Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology (f ⁻¹ᵁ U).toScheme) _
  refine (SheafOfModules.pushforwardComp _ _) ≪≫ ?_ ≪≫
    (SheafOfModules.pushforwardComp _ _).symm
  refine SheafOfModules.pushforwardCongr₂ _
    (NatIso.ofComponents (fun V ↦ eqToIso (image_morphismRestrict_preimage f U V))
      (fun _ ↦ rfl)) ?_
  ext V x
  simp only [Scheme.Opens.ι_appIso]
  exact congrArg (fun g ↦ g x) (morphismRestrict_app f U V.unop).symm

-- Unfold `Functor.comp_obj` in the term: otherwise Lean cannot identify the section type
-- of the composite functor with that of the object-level restriction.
-- The components of `pushforwardComp` are identities on sections, and
-- `pushforwardCongr₂` with `eqToIso` is restriction along `eqToHom`, definitionally.
/-- On sections, open restriction of pushforward is the restriction along the equality
of the two inverse-image opens. -/
@[simp]
theorem restrictPushforwardIso_hom_app_val_app_apply (f : X ⟶ Y) (U : Y.Opens)
    (M : X.Modules) (V : U.toScheme.Opens)
    (x : Γ(((pushforward f).obj M).restrict U.ι, V)) :
    dsimp% only [Functor.comp_obj] (((restrictPushforwardIso f U).hom.app M).val.app (.op V)) x =
      M.val.map (eqToHom (image_morphismRestrict_preimage f U V)).op x :=
  (rfl)

/-- The inverse comparison restricts along the inverse equality of inverse-image opens. -/
@[simp]
theorem restrictPushforwardIso_inv_app_val_app_apply (f : X ⟶ Y) (U : Y.Opens)
    (M : X.Modules) (V : U.toScheme.Opens)
    (x : Γ((pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι), V)) :
    dsimp% only [Functor.comp_obj] (((restrictPushforwardIso f U).inv.app M).val.app (.op V)) x =
      M.val.map (eqToHom (image_morphismRestrict_preimage f U V).symm).op x :=
  (rfl)

end

end TauCeti.AlgebraicGeometry
