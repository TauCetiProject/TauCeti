/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic

/-!
# Affine pushforward and restriction of scalars

For a ring map `φ : R → S`, the sheaf associated with an `S`-module considered as an
`R`-module is canonically the pushforward of its associated sheaf along `Spec φ`.
This identifies module sequences obtained by restriction of scalars with sequences
of direct-image sheaves, for example the normalization sequence of an affine curve.

The comparison uses Mathlib's `Scheme.Modules.fromTildeΓ` and the global-sections
comparison `pushforwardCompModuleSpecΓFunctorIso`.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.2(d).
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : ModuleCat.{u} S)

/-- Associated sheaves turn restriction of scalars into direct image along a
morphism of affine schemes. -/
def tildeRestrictScalarsIsoPushforward :
    tilde ((ModuleCat.restrictScalars φ.hom).obj M) ≅
      (Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M) := by
  have h : IsIso (Scheme.Modules.fromTildeΓ (R := R)
      ((Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M))) :=
    isIso_fromTildeΓ_pushforward φ (tilde M)
  exact (tilde.functor R).mapIso
      ((ModuleCat.restrictScalars φ.hom).mapIso ((tilde.toTildeΓNatIso (R := S)).app M)) ≪≫
    (tilde.functor R).mapIso
      (((pushforwardCompModuleSpecΓFunctorIso φ).app (tilde M)).symm) ≪≫
    @asIso _ _ _ _ (Scheme.Modules.fromTildeΓ (R := R)
      ((Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M))) h

/-- The affine pushforward comparison preserves the global section associated
with an element of the module. -/
@[simp]
theorem tildeRestrictScalarsIsoPushforward_hom_toOpen (m : M) :
    ((tildeRestrictScalarsIsoPushforward φ M).hom.val.app (.op ⊤))
        (tilde.toOpen ((ModuleCat.restrictScalars φ.hom).obj M) ⊤ m) =
      tilde.toOpen M ⊤ m := by
  dsimp only [tildeRestrictScalarsIsoPushforward, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_hom]
  -- Full transparency identifies scheme modules with their underlying sheaf category.
  erw [modules_comp_val_app_apply, modules_comp_val_app_apply,
    tilde_map_val_app_toOpen (R := R)
      ((ModuleCat.restrictScalars φ.hom).map ((tilde.toTildeΓNatIso (R := S)).hom.app M)) ⊤ m,
    tilde_map_val_app_toOpen (R := R)
      ((pushforwardCompModuleSpecΓFunctorIso φ).app (tilde M)).inv ⊤,
    fromTildeΓ_val_app_toOpen_top (R := R)]
  exact pushforwardCompModuleSpecΓFunctorIso_inv_app_apply φ (tilde M)
    (((ModuleCat.restrictScalars φ.hom).map ((tilde.toTildeΓNatIso (R := S)).hom.app M)) m)

end TauCeti.AlgebraicGeometry
