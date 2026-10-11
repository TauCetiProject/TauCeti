/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Monoidal.Basic
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Identity

/-!
# Monoidal identity coherence of quasicoherent pullback

The canonical isomorphism from pullback along the identity scheme morphism to the identity
functor on quasicoherent sheaves respects the strong symmetric monoidal structures. Identifying
identity pullback with the original sheaf therefore also identifies the tensor and unit
comparisons. This is the identity normalization needed to transport tensor products and duality
across changes of base.

The isomorphism is the existing module-pullback identity comparison, restricted to
quasicoherent sheaves. Its compatibility is inherited from the tensor and structure-sheaf
equations for module pullback, with no flatness or finiteness hypothesis.
-/

public section

open CategoryTheory MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal

namespace TauCeti.AlgebraicGeometry.QuasicoherentSheaf

open _root_.AlgebraicGeometry

universe u

noncomputable section

/-- The inverse unit comparison of identity pullback is its canonical identity isomorphism
at the structure sheaf. -/
@[simp]
theorem pullback_id_η (X : Scheme.{u}) :
    η (pullback (𝟙 X)) = (pullbackId X).hom.app (𝟙_ (QuasicoherentSheaf X)) := by
  apply ObjectProperty.hom_ext
  rw [pullback_η_hom, pullbackId_hom_app_hom, Scheme.Modules.pullbackObjUnitIso_id]
  rfl

/-- The inverse tensor comparison of identity pullback is compatible with the canonical
identification with the identity functor. -/
@[reassoc (attr := simp)]
theorem pullback_id_δ (X : Scheme.{u}) (E F : QuasicoherentSheaf X) :
    δ (pullback (𝟙 X)) E F ≫
        ((pullbackId X).hom.app E ⊗ₘ (pullbackId X).hom.app F) =
      (pullbackId X).hom.app (E ⊗ F) := by
  -- Instance search does not unfold `Scheme.Modules` when the full-subcategory API exposes
  -- its underlying sheaf type. Use the same monoidal structure locally at that type.
  let : MonoidalCategory (_root_.SheafOfModules X.ringCatSheaf) :=
    Scheme.Modules.instMonoidalCategory X
  apply ObjectProperty.hom_ext
  -- Read full-subcategory composition and tensor on the underlying modules. This avoids
  -- mixing the category instances for `X.Modules` and its unfolded sheaf type during rewriting.
  change (δ (pullback (𝟙 X)) E F).hom ≫
      (tensorHom (C := X.Modules) ((pullbackId X).hom.app E).hom
        ((pullbackId X).hom.app F).hom) =
    ((pullbackId X).hom.app (E ⊗ F)).hom
  erw [pullback_δ_hom, pullbackId_hom_app_hom, pullbackId_hom_app_hom,
    pullbackId_hom_app_hom]
  let eE := eqToIso (C := X.Modules) (pullback_obj_obj (𝟙 X) E)
  let eF := eqToIso (C := X.Modules) (pullback_obj_obj (𝟙 X) F)
  let p := eqToHom (C := X.Modules) (pullback_obj_obj (𝟙 X) (E ⊗ F))
  let a := (Scheme.Modules.pullbackId X).hom.app E.obj
  let b := (Scheme.Modules.pullbackId X).hom.app F.obj
  have ht : (eE.inv ⊗ₘ eF.inv) ≫ ((eE.hom ≫ a) ⊗ₘ (eF.hom ≫ b)) = a ⊗ₘ b :=
    (congrArg ((eE.inv ⊗ₘ eF.inv) ≫ ·)
      (tensorHom_comp_tensorHom eE.hom eF.hom a b).symm).trans
        ((tensorIso eE eF).inv_hom_id_assoc (a ⊗ₘ b))
  calc
    _ = p ≫ δ (Scheme.Modules.pullback (𝟙 X)) E.obj F.obj ≫
        (eE.inv ⊗ₘ eF.inv) ≫ ((eE.hom ≫ a) ⊗ₘ (eF.hom ≫ b)) :=
      (Category.assoc _ _ _).trans (congrArg (p ≫ ·) (Category.assoc _ _ _))
    _ = p ≫ δ (Scheme.Modules.pullback (𝟙 X)) E.obj F.obj ≫ (a ⊗ₘ b) :=
      congrArg (p ≫ δ (Scheme.Modules.pullback (𝟙 X)) E.obj F.obj ≫ ·) ht
    _ = _ := congrArg (p ≫ ·) (Scheme.Modules.pullback_id_δ X E.obj F.obj)

/-- The identity isomorphism of quasicoherent pullback is monoidal. -/
instance isMonoidal_pullbackId_hom (X : Scheme.{u}) :
    NatTrans.IsMonoidal (pullbackId X).hom where
  unit := by
    rw [← pullback_id_η X]
    exact Functor.Monoidal.ε_η _
  tensor E F := by
    rw [← cancel_epi (δ (pullback (𝟙 X)) E F)]
    simp [pullback_id_δ]

end

end TauCeti.AlgebraicGeometry.QuasicoherentSheaf
