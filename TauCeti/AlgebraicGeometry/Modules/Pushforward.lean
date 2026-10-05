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
The construction uses Mathlib's pushforward composition comparisons and restriction adjunction.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

open Scheme.Modules

variable {X Y : Scheme.{u}}

/-- Pushforward along an isomorphism agrees with restriction along its inverse.

This is the comparison obtained by cancelling inverse pushforwards and applying the
restriction adjunction's counit. -/
def pushforwardIsoRestrict (e : X ≅ Y) : pushforward e.hom ≅ restrictFunctor e.inv :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (restrictFunctorAdjCounitIso e.inv).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (pushforwardComp e.hom e.inv ≪≫ pushforwardCongr e.hom_inv_id ≪≫ pushforwardId X) _ ≪≫
    Functor.leftUnitor _

/-- The pushforward--restriction comparison is the composite of the canonical counit
and cancellation comparisons. -/
theorem pushforwardIsoRestrict_def (e : X ≅ Y) :
    pushforwardIsoRestrict e =
      (Functor.rightUnitor _).symm ≪≫
        Functor.isoWhiskerLeft _ (restrictFunctorAdjCounitIso e.inv).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (pushforwardComp e.hom e.inv ≪≫ pushforwardCongr e.hom_inv_id ≪≫ pushforwardId X) _ ≪≫
        Functor.leftUnitor _ :=
  (rfl)

/-- Restricting a pushforward to an open of the base agrees with pushing forward the
restriction to its preimage, naturally in the module sheaf. -/
def restrictPushforwardIso (f : X ⟶ Y) (U : Y.Opens) :
    pushforward f ⋙ restrictFunctor U.ι ≅
      restrictFunctor (f ⁻¹ᵁ U).ι ⋙ pushforward (f ∣_ U) := by
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

/-- On sections, open restriction of pushforward is the restriction along the equality
of the two inverse-image opens. -/
@[simp]
theorem restrictPushforwardIso_hom_app_val_app (f : X ⟶ Y) (U : Y.Opens)
    (M : X.Modules) (V : U.toScheme.Opens)
    (x : Γ(((pushforward f).obj M).restrict U.ι, V)) :
    (((restrictPushforwardIso f U).hom.app M).val.app (.op V)) x =
      M.val.map (eqToHom (image_morphismRestrict_preimage f U V)).op x :=
  (rfl)

/-- The inverse comparison restricts along the inverse equality of inverse-image opens. -/
@[simp]
theorem restrictPushforwardIso_inv_app_val_app (f : X ⟶ Y) (U : Y.Opens)
    (M : X.Modules) (V : U.toScheme.Opens)
    (x : Γ((pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι), V)) :
    (((restrictPushforwardIso f U).inv.app M).val.app (.op V)) x =
      M.val.map (eqToHom (image_morphismRestrict_preimage f U V).symm).op x :=
  (rfl)

end

end TauCeti.AlgebraicGeometry
